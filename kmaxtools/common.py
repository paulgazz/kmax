import sys
import pickle
import z3

quiet = False

def info(msg, ending="\n"):
  if not quiet: sys.stderr.write("INFO: %s%s" % (msg, ending))

def get_kmax_constraints(kmax_formulas, kbuild_path, view=False):
  """Returns an array of z3 formulas that, ANDed together, represent conditions under which the unit is included in a build, as specified by Kbuild.  Note that this excludes any Kconfig constraints, which are handled by kclause instead."""
  if kbuild_path in kmax_formulas.keys():
    kmax_constraints = []
    # add the condition for the compilation unit and each of its parent directories
    comp_unit_constraint = z3.parse_smt2_string(kmax_formulas[kbuild_path])
    kmax_constraints.extend(comp_unit_constraint)
    if view:
      print("%s\n%s\n" % (kbuild_path, comp_unit_constraint))
    if '/' in kbuild_path:
      subpath, basename = kbuild_path.rsplit('/', 1)
      elems = subpath.rsplit('/')
      for i in range(0, len(elems)):
        subarray = elems[0:(len(elems) - i)]
        subsubpath = '/'.join(subarray) + "/"
        if subsubpath in kmax_formulas.keys():
          subsubpath_constraint = z3.parse_smt2_string(kmax_formulas[subsubpath])
          kmax_constraints.extend(subsubpath_constraint)
          if view:
            print("%s\n%s\n" % (subsubpath, subsubpath_constraint))
        else:
          info("%s has no kmax formula, assuming it is unconstrained." % (subsubpath))
    return kmax_constraints
  else:
    return None
  
def unpickle_kmax_file(kmax_file):
  with open(kmax_file, 'rb') as fp:
    kmax = pickle.load(fp)
    return kmax
