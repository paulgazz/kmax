import sys
import os
import argparse
import z3
import regex
import pickle

def info(msg, ending="\n"):
  sys.stderr.write("INFO: %s%s" % (msg, ending))

def warning(msg, ending="\n"):
  sys.stderr.write("WARNING: %s%s" % (msg, ending))

def error(msg, ending="\n"):
  sys.stderr.write("ERROR: %s%s" % (msg, ending))

def get_kclause_constraints(kclause_file):  
  with open(kclause_file, 'r') as fp:
    kclause = pickle.load(fp)

    kclause_constraints = {}
    for var in kclause.keys():
      kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in kclause[var] ]
    kclause = None
    return kclause_constraints

def get_kmax_constraints(kmax_file, compilation_unit):
  if not compilation_unit.endswith(".o"):
    compilation_unit = os.path.splitext(compilation_unit)[0] + ".o"
    warning("Forcing file extension to be .o, since lookup is by compilation unit: %s" % (compilation_unit))

  with open(kmax_file, 'r') as fp:
    kmax = pickle.load(fp)
    # todo: support multiple compilation units

    if compilation_unit not in kmax.keys():
      error("%s not found in %s.  Please check that the compilation unit is in the kmax file." % (compilation_unit, kmax_file))
      return []
    else:
      kmax_constraints = []
      if compilation_unit in kmax.keys():
        # add the condition for the compilation unit and each of its parent directories
        kmax_constraints.append(z3.parse_smt2_string(kmax[compilation_unit]))
        subpath, basename = compilation_unit.rsplit('/', 1)
        elems = subpath.rsplit('/')
        for i in reversed(range(0, len(elems))):
          subarray = elems[0:(len(elems) - i)]
          subsubpath = '/'.join(subarray) + "/"
          if subsubpath in kmax.keys():
            kmax_constraints.append(z3.parse_smt2_string(kmax[subsubpath]))
          else:
            info("%s not found in %s, assuming it is always included." % (subsubpath, kmax_file))
      kmax = None
      return kmax_constraints

def get_constraints(kclause_file, kmax_file=None, compilation_unit=None, constraints_file=None, define=[], undefine=[]):
  constraints = []

  if constraints_file:
    ad_hoc_constraints = get_ad_hoc_constraints(constraints_file)
    constraints.extend(ad_hoc_constraints)

  # add kmax constraints
  if kmax_file is not None:
    if compilation_unit is not None:
      kmax_constraints = get_kmax_constraints(kmax_file, compilation_unit)
      for constraint in kmax_constraints:
        constraints.extend(constraint)
    else:
      info("No compilation unit given.  Not using kmax constraints.")

  # add kclause constraints
  kclause_constraints = get_kclause_constraints(kclause_file)
  for var in kclause_constraints.keys():
    for z3_clause in kclause_constraints[var]:
      constraints.extend(z3_clause)

  # add user-specified constraints
  for define in define:
    constraints.append(z3.Bool(define))
  for undefine in undefine:
    constraints.append(z3.Not(z3.Bool(undefine)))

  return constraints

def klocalize(constraints, show_unsat_core):
  """returns a model from the sat solver"""
  solver = z3.Solver()
  solver.set(unsat_core=show_unsat_core)

  if (solver.check(constraints) == z3.unsat):
    # todo: better reporting to the user
    sys.stderr.write("ERROR: The compilation unit's constraints are unsatisfiable, so no configuration can be generated.  This could be because (1) the compilation unit is only available in another architecture or (2) the logical formulas are wrong (overconstrained).\n")
    # todo: need to add assumptions to checker in order to get a core.  try using a separate formula for each configuration option
    if show_unsat_core:
      info("The following constraint(s) prevented satisfiability:\n%s" % (str(solver.unsat_core())))
    else:
      info("Try running again with --show-unsat-core to see what constraints prevented satisfiability.")
    return None
  else:
    info("The compilation unit's constraints are satisfiable.")
    return solver.model()

def print_model_as_config(model):
  info("Printing model in .config format to stdout.")
  if model is not None:
    # print the model in .config format
    token_pattern = regex.compile("CONFIG_[A-Za-z0-9_]+")
    for entry in model:
      str_entry = str(entry)
      matches = token_pattern.match(str_entry)
      if matches:
        if model[entry]:
          print("%s=y" % (str_entry))
          # if str_entry not in kclause_constraints.keys():
          #   sys.stderr.write("warning: %s was not defined in the kconfig spec, but may be required for this unit.\n" % (str_entry))
        else:
          print("# %s is not set" % (str_entry))
      # else:
      #   sys.stderr.write("omitting non-config var %s\n" % (str_entry))
  else:
    warning("model is None.  Not printing.")

def optimize_model(optimize, constraints):
  solver = z3.Solver()
  solver.set(unsat_core=True)
  for constraint in constraints:
    solver.add(constraint)

  # try to match the given .config file as much as possible.
  # there are two approaches to try: (1) add the .config has
  # constraints, get the unsat core and try to remove assumptions
  # until we get something sat, (2) add the .config has soft
  # assertions.

  assumptions = get_config_file_constraints(optimize)

  # (1) unsat core approach. keep removing assumptions until the formula is satisfiable
  res = solver.check(assumptions)
  if res == z3.sat:
    info("Already satisfiable.  No optimization needed.")
    return solver.model()
  else:
    info("Optimizing via unsat core approach.")
    info("%d assumptions left to try removing." % (len(assumptions)), ending="\r")
    while res == z3.unsat:
      core = solver.unsat_core()
      # remove all assumptions that in the core.  todo, try randomizing this or removing only some assumptions each iteration.
      assumptions = [ assumption for assumption in assumptions if assumption not in core ]
      info(len(assumptions), ending="\r")
      res = solver.check(assumptions)
      core = solver.unsat_core()
      res = solver.check(assumptions)
    info("\nFound satisfying config.")
    return solver.model()
  
  # (2) soft assertion approach. (todo)

on_pattern = regex.compile("^(CONFIG_[A-Za-z0-9_]+)=[ym]")
off_pattern = regex.compile("^# (CONFIG_[A-Za-z0-9_]+) is not set")
def get_config_file_constraints(config_file):
  # todo: don't allow invisible defaults to be turned off (get them from kclause), reduces size of constraints

  constraints = []
  # add the .config as constraints
  with open(config_file, 'r') as optimize_fp:
    lines = optimize_fp.readlines()
    for line in lines:
      line = line.strip()
      off = off_pattern.match(line)
      if off:
        constraint = z3.Not(z3.Bool(off.group(1)))
        constraints.append(constraint)
      else:
        on = on_pattern.match(line)
        if on:
          constraint = z3.Bool(on.group(1))
          constraints.append(constraint)

    return constraints
  
ad_hoc_on_pattern = regex.compile("^(CONFIG_[A-Za-z0-9_]+)$")
ad_hoc_off_pattern = regex.compile("^!(CONFIG_[A-Za-z0-9_]+)$")
def get_ad_hoc_constraints(config_file):
  constraints = []
  with open(config_file, 'r') as fp:
    lines = fp.readlines()
    for line in lines:
      line = line.strip()
      off = ad_hoc_off_pattern.match(line)
      if off:
        constraint = z3.Not(z3.Bool(off.group(1)))
        constraints.append(constraint)
      else:
        on = ad_hoc_on_pattern.match(line)
        if on:
          constraint = z3.Bool(on.group(1))
          constraints.append(constraint)

    return constraints
