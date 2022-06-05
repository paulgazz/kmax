import sys
import os
import argparse
import z3
import re
import regex
import pickle
import random
import kmax.about
import subprocess
# import kmax.alg # Run()
import pprint
import enum
import z3
import time
from kmax.arch import Arch
from kmax.common import get_kmax_constraints, unpickle_kmax_file
from kmax.vcommon import getLogLevel, getLogger, run

# TODO(necip): automated testing

def __parse_cb(cb_string_rep: str):
  """Parse and return a conditional block group.

  Arguments:
  cb_string_rep -- string representation of a conditional block.

  Returns ConditionalBlock.
  """
  # TODO: change these
  cb = Klocalizer.ConditionalBlock()
  cb.start_line = int(cb_string_rep["StartLine"])
  cb.end_line = int(cb_string_rep["EndLine"])
  # Config options come as |(defined CONFIG_A)| from SuperC. Convert
  # them to CONFIG_A format for compatibility with kclause.
  pc_string = cb_string_rep["PC"]
  pc_string = re.sub(r'\|\(defined (CONFIG_[a-zA-Z0-9_]*)\)\|', r'\1', pc_string)
  z3_solver = z3.Solver()
  z3_solver.from_string(pc_string) # TODO: make this an expression instead?
  cb.pc = z3_solver
  cb.sub_block_groups = Klocalizer.ConditionalBlock.__parse_sub(cb_string_rep["Sub"], cb)

  return cb


try:
  from subprocess import DEVNULL  # Python 3.
except ImportError:
  DEVNULL = open(os.devnull, 'wb')

class VoidLogger:
  """A quiet logger satisfying the attribute requirements."""
  def info(self, msg):
    pass
  def warning(self, msg):
    pass
  def error(self, msg):
    pass
  def debug(self, msg):
    pass

class Klocalizer:
  def __init__(self):
    self.__logger = VoidLogger()
    self.__ksrc = os.curdir # defaults to current directory

    # Kmax formulas related state variables
    # If self.__is_kmax_formulas_cache is set and kmax formulas for some unit
    # can't be found, kmax will be run to query.
    self.__is_kmax_formulas_cache=True
    self.__kmax_formulas={}

    self.__include_compilation_units=[]
    self.__exclude_compilation_units=[]
    self.__kmax_constraints=[]

    self.__additional_constraints=[]

    self.unmet_free = False
    self.unmet_free_except_for = []
  
  def set_logger(self, logger):
    """Set logger.
    
    Logger must have info(msg: str), warning(msg: str), and error(msg: str) attributes.
    
    Also, it is assumed that the logger won't implicity print newline since klocalizer might print carriage return to update ongoing progress.

    Set logger to None to disable logging.
    """
    if logger == None:
      self.__logger = VoidLogger()
    else:    
      for m in ['info', 'error', 'warning']:
        assert m in dir(logger)
      
      self.__logger = logger

  def set_unmet_free(self, unmet_free=True, except_for=[]):
    """Include unmet direct dependency free constraints in the compiled constraints.

    Arguments:
    unmet_free -- If set, include the constraints. If unset, reset the state
    to not include the constraints.
    except_for -- Don't include the unmet free constraints for this list of
    kconfig symbols. This can be used to single out unmet direct dependencies
    for some symbols.
    """

    assert type(except_for) is list
    self.unmet_free = unmet_free
    self.unmet_free_except_for = except_for[:]
    # TODO: warn if unmet free is set to False while except for is non empty


  def update_kmax_cache_file(self, kmax_cache_file):
    """Update the kmax cache file with the content of current cache.

    If kmax_cache_file exists, its content will be updated, i.e., not completely
    overwritten.

    Arguments:
    kmax_cache_file -- Path to kmax cache file to update.
    """
    filepath = os.path.realpath(kmax_cache_file)
    assert os.path.isfile(filepath) or not os.path.exists(filepath)

    old_kmax_formulas = unpickle_kmax_file(filepath) if os.path.exists(filepath) else {}
    
    old_kmax_formulas.update(self.__kmax_formulas)
    
    with open(filepath, 'wb') as f:
      pickle.dump(self.__kmax_formulas, f, 0)
  
  def load_kmax_formulas(self, kmax_file: str, is_cache=False):
    """Load kmax formulas from a kmax formulas file.

    This will overwrite any previously loaded/generated kmax formulas.
    
    If is_cache is unset, it will assume the loaded kmax formulas are full,
    thus, the Klocalizer instance will raise an exception without querying
    kmax if it can't find formulas for a unit.

    If is_cache is set, it will account for the missing kmax formulas by querying
    kmax if a formula can't be found. 

    Arguments:
    kmax_file -- Path to the kmax formulas file.
    is_cache -- If set, the loaded kmax formulas will be treated as cache,
    thus, kmax will be queried for missing formulas.
    """
    filepath = os.path.realpath(kmax_file)
    if not os.path.exists(filepath) or os.path.isdir(filepath):
      raise Klocalizer.KmaxFileNotFound(kmax_file)

    self.__is_kmax_formulas_cache=is_cache
    self.__kmax_cache_file=None
    self.__logger.debug("Loading Kmax formulas from file: %s\n" % kmax_file)
    self.__kmax_formulas = unpickle_kmax_file(filepath)
    self.__logger.debug("Kmax formulas was loaded.\n")

  def get_kmax_formulas(self):
    return self.__kmax_formulas
  
  def add_constraints(self, constraints: list):
    """Add to the list of additional constraints.

    Arguments:
    constraints -- list of constraints with each element of type z3.BoolRef.
    """
    if constraints == None or constraints == []:
      return
    
    # The following check is disabled since the constraints are allowed to be
    # instances of other types such as an z3.ASTVector.
    # TODO: fix and enable the constraints type check
    #assert type(constraints) == list and type(constraints[0]) == z3.BoolRef
    self.__additional_constraints.extend(constraints)

  def set_constraints(self, constraints: list):
    """Set the list of additional constraints.

    Different than add_constraints(), this method will reset any earlier additional constraints accumulated/set.

    Arguments:
    constraints -- list of constraints with each element of type z3.BoolRef.
    """
    if constraints == None or constraints == []:
      self.__additional_constraints = []

    assert type(constraints) == list and type(constraints[0]) == z3.BoolRef

    self.__additional_constraints = constraints[:]

  def reset_constraints(self):
    """Reset the additional constraints.
    """
    self.__additional_constraints = []

  def __query_kmax(self, path):
    """Query kmax for kbuild path `path` and return the related kmax formulas.

    Returns kmax formulas for related paths as a mapping from path to formula.

    Arguments:
    path -- kbuild path.
    """
    command = ['kmax', '-z', ('-Dsrctree=./'), ('-Dsrc=%s' % (os.path.dirname(path))), path]
    self.__logger.debug("Running kmax: %s\n" % (" ".join(command)))
    output = subprocess.check_output(command, stderr=DEVNULL, cwd=self.__ksrc) # todo: save error output to a log
    formulas = pickle.loads(output)
    return formulas
          
    # TODO: Use the following instead to avoid running seperate process
    # This will be more useful in a few ways, including that any exception/error
    # with kmax will be reflected to runtime of this python module as well
    # There is a bug with the following though, it doesn't work properly for
    # some reason? Maybe the states for kmax accumulate and cause some problems?
    # kmax.settings.output_smtlib2 = True
    # kmax.settings.output_all_unit_types = False
    # kmax.settings.do_boolean_configs = True
    # # TODO: Can't set the logger level of kmax, maybe kmax should have an interface for this?
    # kmax.settings.logger_level = getLogLevel(1)

    # kmax.settings.defines = [("srctree=%s" % self.__ksrc), ("src=%s" % os.path.dirname(path))]
    # print("defines: '%s'" % kmax.settings.defines)
    # print("inp: '%s'" % path)
    # kmax_run=kmax.alg.Run()
    # kmax_run.run([path])
    # print("results from query: '%s'" % str(kmax_run.results))
    # formulas = pickle.loads(str(kmax_run.results).encode())
    # return formulas

  def __fetch_kmax_constraints(self, path):
    """Fetch kmax constraints for the given path and update the internal kmax_formulas mapping.
    
    If no kmax formula can be found, the path is assumed to be unconstrained.

    Arguments:
    path -- kbuild path.
    """
    # add the condition for the compilation unit and each of its parent
    # directories.  this assumes the path is relative.
    if '/' in path:
      elems = path.rsplit('/')
      current_path = elems[0] + "/"
      for i in range(1, len(elems)):
        elem = elems[i]
        parent_path = current_path  # trailing / is important for kbuild
        current_path = os.path.join(parent_path, elem)
        if i < len(elems) - 1:
          current_path = current_path + "/"
        if current_path not in list(self.__kmax_formulas.keys()):
          # run kmax on the parent to find the constraint
          paths_to_try = []
          # paths are relative to ksrc
          path_to_kbuild = os.path.join(parent_path, "Kbuild")
          path_to_makefile = os.path.join(parent_path, "Makefile")
          if os.path.exists(os.path.join(self.__ksrc, path_to_kbuild)):
            paths_to_try.append(path_to_kbuild)
          if os.path.exists(os.path.join(self.__ksrc, path_to_makefile)):
            paths_to_try.append(path_to_makefile)
          if len(paths_to_try) == 0:
            self.__logger.warning("There is no Kbuild Makefile in %s\n" % (parent_path))
          for path_to_try in paths_to_try:
            new_formulas = self.__query_kmax(path_to_try)
            self.__kmax_formulas.update(new_formulas)
        if current_path not in self.__kmax_formulas:
          self.__logger.debug("%s has no kmax formula, assuming it is unconstrained.\n" % (current_path))

  def __resolve_kbuild_path(self, unit: str):
    """Resolve the kbuild paths for unit.

    Arguments:
    unit -- compilation unit.
    """
    kbuild_paths = []
    for key in self.__kmax_formulas:
      resolved_filename = os.path.relpath(os.path.abspath(key))
      if key.endswith("/"):
        # preserve the ending slash, which signals a subdirectory
        # instead of a compilation unit in kbuild
        resolved_filename = resolved_filename + "/"
      if resolved_filename == unit:
        kbuild_paths.append(key)
    return kbuild_paths
  
  @staticmethod
  def get_config_file_constraints(config_file):
    """Given a path to a Kconfig configuration file, parse and return the list
    of constraints the config file yields. Each element of the returned list
    is a z3.BoolRef instance.

    Only boolean and tristate options are considered. Tristate options are
    interpreted `on` if y or m, `off` otherwise.

    Arguments:
    config_file -- Path to a Kconfig config file.
    """
    assert os.path.isfile(config_file)
    on_pattern = regex.compile("^(CONFIG_[A-Za-z0-9_]+)=[ym]")
    off_pattern = regex.compile("^# (CONFIG_[A-Za-z0-9_]+) is not set")
    
    # todo: don't allow invisible defaults to be turned off (get them from kclause), reduces size of constraints

    constraints = []
    with open(config_file, 'r') as approximate_fp:
      lines = approximate_fp.readlines()
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
  
  @staticmethod
  def get_config_from_model(model: z3.Model, arch: Arch, set_tristate_m, allow_non_visibles: bool, logger=None) -> str:
    """Given a z3_model, return a Kconfig config in string representation,
    which can be later dumped as a Kconfig config file and used against Kbuild
    build system.

    Arguments:
    model -- A z3 model of the configurations possibly obtained from a z3 Solver.
    arch -- An Arch instance to query kextract information. If set to None,
    it will be ignored. If querying kextract fails with exception Arch.MissingLinuxSource,
    it will be interpreted as not having kextract information available, and
    the exception will be ignored with a warning message.
    set_tristate_m -- If set, set tristate symbols to `m` if on.
    allow_non_visibles -- Allow non-visible Kconfig configuration options to
    be set in the resulting config file.
    logger -- Logger.
    
    """
    assert model != None

    token_pattern = regex.compile("CONFIG_[A-Za-z0-9_]+")
    
    configfile_content = []

    write_to_content = lambda x: configfile_content.append(x)

    try:
      kconfig_visible = arch.get_kconfig_visible() if allow_non_visibles and arch else None
      kconfig_types = arch.get_kconfig_types() if arch else None
      kconfig_has_def_nonbool = arch.get_kconfig_has_def_nonbool() if arch else None
    except Arch.MissingLinuxSource:
      # if kextract can't be found, arch will try to generate it and this will fail when linux_ksrc is unset
      # it is okay since we don't expect kextract to exist at all times
      if logger: logger.warning("Can't use architecture kextract while generating config: neither kextract nor linux kernel source to generate kextract was set.\n")
      kconfig_visible = None
      kconfig_types = None
      kconfig_has_def_nonbool = None

    for entry in model: # the model has some problem, we can't get the entry
      str_entry = str(entry)
      matches = token_pattern.match(str_entry)
      if matches:
        if kconfig_visible is None or str_entry in kconfig_visible:
          # if str_entry not in kclause_constraints.keys():
          #   sys.stderr.write("warning: %s was not defined in the kconfig spec, but may be required for this unit.\n" % (str_entry))
          if model[entry]:
            if kconfig_types is None:
              # if no types provided, assume all are Boolean
              write_to_content( "%s=y\n" % (str_entry) )
            elif kconfig_has_def_nonbool != None and str_entry in kconfig_has_def_nonbool:
              # write placeholder values for visible nonboolean options.
              # we assume that "make olddefconfig" will fill in the proper default values for the nonvisible ones.
              # NOTE: adding all of the default value expressions to the z3 solver requires too much memory for practical usage.
              all_vars = model.decls()
              # checks the model's value for the nonbool's corresponding visibility variable
              for var in all_vars:
                if str(var) == "__VISIBILITY__" + str_entry:
                  if model.get_interp(var):
                    if kconfig_types[str_entry] == "bool":
                      write_to_content( "%s=y\n" % (str_entry) )
                    elif kconfig_types[str_entry] == "tristate":
                      write_to_content( "%s=%s\n" % (str_entry, "y" if not set_tristate_m else "m") )
                    elif kconfig_types[str_entry] == "string":
                      write_to_content( "%s=\n" % (str_entry) )
                    elif kconfig_types[str_entry] == "number":
                      write_to_content( "%s=0\n" % (str_entry) )
                    elif kconfig_types[str_entry] == "hex":
                      write_to_content( "%s=0x0\n" % (str_entry) )
                    else:
                      assert(False)
                  break
            elif str_entry not in kconfig_types:
              if str_entry not in Arch.ARCH_CONFIGS:
                # TODO: change this maybe
                if logger: logger.warning("%s is not defined by Kconfig for this architecture.\n" % (str_entry))
            elif kconfig_types[str_entry] == "bool":
              write_to_content( "%s=y\n" % (str_entry) )
            elif kconfig_types[str_entry] == "tristate":
              write_to_content( "%s=%s\n" % (str_entry, "y" if not set_tristate_m else "m") )
            elif kconfig_types[str_entry] == "string":
              write_to_content( "%s=\n" % (str_entry) )
            elif kconfig_types[str_entry] == "number":
              write_to_content( "%s=0\n" % (str_entry) )
            elif kconfig_types[str_entry] == "hex":
              write_to_content( "%s=0x0\n" % (str_entry) )
            else:
              assert(False)
          else:
            if kconfig_types is None or str_entry in kconfig_types:
              write_to_content( "# %s is not set\n" % (str_entry) )
            else:
              if str_entry not in Arch.ARCH_CONFIGS:
                if logger: logger.warning("%s is not defined by Kconfig for this architecture.\n" % (str_entry))
      # else:
      #   sys.stderr.write("omitting non-config var %s\n" % (str_entry))
    
    return "".join(configfile_content)

  @staticmethod
  def get_kclause_cache_url(linux_tag_version):
    """Get the URL that holds the index to the cached formula's for the given linux version tag."""
    return "https://configtools.org/klocalizer/cache/%s" % (linux_tag_version)
  
  class Z3ModelSampler:
    """Given constraints, check SAT and sample models using z3 solver.

    Internally, checks the SAT of constraints using a z3.Solver, and returns
    the model or the unsat core depending on the outcome. For multisampling,
    calls check() method on the z3 Solver again.

    Arguments:
    constraints -- list of core constraints.
    approximate_constraints -- list of constraints to approximate. Only one
    model can be sampled when approximating (for now). Subsequent sample_model()
    calls will return the same model.
    random_seed -- random seed to be used by the internal z3 solver.
    logger -- Logger.
    """
    def __init__(self, constraints: list, approximate_constraints=None, random_seed=None, logger=None):
      self.set_logger(logger)

      self.__solver = z3.Solver()
      self.__solver.set(unsat_core=True)

      if random_seed != None:
        self.__solver.set(random_seed=random_seed)
      
      # TODO: It is unsafe to change the constraints outside, should we copy here?
      self.__constraints = constraints
      self.__approximate_constraints = approximate_constraints
      
      # When seen unsat, no further model can be created. Optimize by not
      # doing any additional checks after then.
      self.__unsat_core = None

      # keep this to remember if sat check is done or not
      self.__is_sat = None
    
    def set_logger(self, logger):
      """Set logger.
      
      Logger must have info(msg: str), warning(msg: str), and error(msg: str) attributes.
      
      Also, it is assumed that the logger won't implicity print newline since klocalizer might print carriage return to update ongoing progress.

      Set logger to None to disable logging.
      """
      if logger == None:
        self.__logger = VoidLogger()
      else:
        for m in ['info', 'error', 'warning']:
          assert m in dir(logger)
        
        self.__logger = logger
      
    def __approximate_model(self):
      """Assumptions:
        * the constraints are already sat.
        * called only once (since solver state is changed with addition of new constraints as assertions).

      Updates self.__model
      """
      # try to match the given .config file as much as possible.
      # there are two approaches to try: (1) add the .config has
      # constraints, get the unsat core and try to remove assumptions
      # until we get something sat, (2) add the .config has soft
      # assertions.
      solver = self.__solver
      assumptions = self.__approximate_constraints
      solver.add(self.__constraints)

      is_sat = solver.check(assumptions) == z3.sat
      if is_sat:
        self.__logger.info("Already satisfiable when constraining with given config.  No approximatation needed.\n")
      else:
        self.__logger.info("Approximating via unsat core approach.\n")
        total_assumptions_to_match = len(assumptions)
        self.__logger.debug("%d assumptions left to try removing.\r" % (total_assumptions_to_match))
        while not is_sat:
          core = solver.unsat_core()
          # remove all assumptions that in the core, except those specifically given as user-constraints.  potential optmization: try randomizing this or removing only some assumptions each iteration.
          # print(core)
          # update: user-constraints are no longer handled differently
          assumptions = [ assumption for assumption in assumptions if assumption not in core ]
          self.__logger.debug("%s\r" % len(assumptions))
          is_sat = solver.check(assumptions) == z3.sat
        self.__logger.debug("\r")
        self.__logger.info("Found satisfying config by removing %d assumptions.\n" % (total_assumptions_to_match - len(assumptions)))

    def sample_model(self):
      """If sat, return (True, z3_model)
      If unsat, return (False, unsat_core)

      Consecutive calls to sample_model will return different z3 models.

      If approximating, multisampling is not supported, thus, the same z3 model
      will be returned for any call.
      """
      first_check = self.__is_sat == None
      if first_check:
        self.__is_sat = z3.sat == self.__solver.check(self.__constraints)
        
        if not self.__is_sat:
          self.__unsat_core = self.__solver.unsat_core()

      if not self.__is_sat:
        # UNSAT
        assert self.__unsat_core != None
        return False, self.__unsat_core
      elif self.__is_sat:
        # SAT
        if not self.__approximate_constraints and first_check:
          pass
        elif not self.__approximate_constraints and not first_check:
          assert(z3.sat == self.__solver.check(self.__constraints)) # renew model
        elif self.__approximate_constraints and first_check:
          self.__approximate_model()
        elif self.__approximate_constraints and not first_check:
          pass # TODO: log that it is not possible to multisample for approximate at this time
        
        return True, self.__solver.model()
        
      assert False # should've returned above

  def set_linux_krsc(self, ksrc_dir):
    self.__ksrc=ksrc_dir

  def compile_constraints(self, arch: Arch):
    """Compile and return the constraints.
    
    The return value is a list of z3 constructs which can be directly passed
    to a z3 solver.

    The constraints are inclusive of the followings:
      * kmax constraints due to included/excluded compilation units
      * kclause constraints due to architecture
      * architecture specific constraints, if not custom arch
      * constraints to disable boolean configurations not defined in the architecture
      * unmet free constraints, if set
      * any additional constraints, if set
    """
    constraints = []

    # check based on the included compilation units' directory hierarchy. this is linux specific.
    for unit in self.__include_compilation_units:
      if unit.startswith("arch/"):
        unit_archs = Arch.get_archs_from_subdir(unit)
        if not arch.name in unit_archs:
          self.__logger.warning("Resolved compilation unit (%s) is architecture-specific (%s), unsat for the provided architecture (%s).\n" % (unit, " ".join(unit_archs), arch.name))
          return [z3.BoolVal(False)]

    # add kmax constraints
    constraints.extend(self.__kmax_constraints)

    # disable any Boolean configuration options not defined in this architecture
    if self.__kmax_constraints:
      try:
        kconfig_types = arch.get_kconfig_types()
      except Arch.MissingLinuxSource:
        # if kextract can't be found, arch will try to generate it and this will fail when linux_ksrc is unset
        # it is okay since we don't expect kextract to exist at all times
        self.__logger.warning("Can't use architecture kextract to disable undefined boolean configs: neither kextract nor linux kernel source to generate kextract was set.\n")
        kconfig_types = None
      if kconfig_types:
        token_pattern = regex.compile("CONFIG_[A-Za-z0-9_]+")
        for kmax_constraint in self.__kmax_constraints:
          used_vars = z3.z3util.get_vars(kmax_constraint)
          vars_not_in_arch = [ used_var for used_var in used_vars if str(used_var) not in list(kconfig_types.keys()) and token_pattern.match(str(used_var)) ]
          for used_var in vars_not_in_arch:
            constraints.append(z3.Not(used_var))

    # add kclause constraints
    # TODO: do we need to parse smt2 string all the time?
    # update: tried with kismet and looks like parsing smt2 string all the time is time consuming, so, have a solution for this
    # maybe arch can keep track of both smt2 string and the z3 format
    # create a wrapper class for pulling the results -- that will keep it in
    # z3, smt2 string formats etc. just the constraints will be kept in this format
    constraints.extend(z3.parse_smt2_string(arch.get_kclause_composite()))

    # add kclause direct dependency constraints, if needed
    if self.unmet_free:
      constraints.extend(arch.get_unmet_free_constraints(except_for=self.unmet_free_except_for))

    # add arch specific constraints
    if arch.name in Arch.ARCHS:
      constraints.extend(arch.get_arch_specific_constraints())

    # add any additional constraints
    constraints.extend(self.__additional_constraints)
    return constraints

  class __CompUnitInclusionProp(enum.Enum):
    EXCLUDE=0
    INCLUDE=1
  
  def get_compilation_unit_constraints(self, unit: str):
    """Given a compilation unit, fetch and return the inclusion constraints
    using kmax.

    May raise NoFormulaFoundForCompilationUnit or MultipleCompilationUnitsMatch exception.

    Arguments:
    unit -- compilation unit or directory.
    """
    #
    # Format the unit name
    #
    # There must be '.o' extension for units, '/' suffix for directories
    if not unit.endswith(".o") and not unit.endswith('/'):
      # Try to understand whether it was directory or unit
      bname = unit.split('/')[-1]
      assert bname
      ext = os.path.splitext(bname)[-1]
      if ext and ext.lower() in ['.c', '.s', '.o']:
        # This must be a single unit rather than a directory
        self.__logger.warning("Forcing file extension to be .o, since lookup is by compilation unit: %s\n" % (unit))
        unit = os.path.splitext(unit)[0] + ".o"
      else:
        # This must be a directory
        unit = unit + '/'
      
    is_top_level_dir = unit.endswith('/') and unit.count('/') == 1
    
    #
    # Process the unit name get all the paths for which to pull the kmax formulas
    #
    # Two possibilities: use the content of the kmax_file or the on-the-fly kmax_cache
    if self.__is_kmax_formulas_cache: # kmax_formulas is cache
      # TODO: We call resolve_kbuild_path() for complete formulas, but not for this?
      # Maybe we should just do the same for all? Maybe that's the reason for the issue Jeho experienced.
      self.__fetch_kmax_constraints(unit)
      if unit not in self.__kmax_formulas:
        if is_top_level_dir:
          # This is a top-level directory, which is controlled by a
          # non-kbuild Makefile that kmax cannot work on. These are mostly
          # unconstrained. The constrained top-level directories are
          # handled through hard-coding of the constraints below.
          pass
        else:
          raise Klocalizer.NoFormulaFoundForCompilationUnit(unit)
    else: # kmax_formulas is not cache but complete
      if unit not in self.__kmax_formulas:
        kbuild_paths = self.__resolve_kbuild_path(unit)
        if len(kbuild_paths) == 0:
          raise Klocalizer.NoFormulaFoundForCompilationUnit(unit)
        elif len(kbuild_paths) > 1:
          raise Klocalizer.MultipleCompilationUnitsMatch(unit, kbuild_paths)
        kbuild_path = kbuild_paths[0]
        assert unit != kbuild_path
        self.__logger.debug("Using full path from Kbuild: %s\n" % (kbuild_path))
        unit = kbuild_path
    
    #
    # Add the constraints to the kmax constraints accumulator
    #
    kmax_constraints_for_unit = get_kmax_constraints(self.__kmax_formulas, unit) # TODO: this one is not quiet

    # The top makefile in the Linux kernel introduces additional constraints
    # on the inclusion of net/ and samples/ directories. Since this is not a
    # Kbuild makefile, kmax does not process and cannot capture the constraints.
    # Add the missing constraints for those directories.
    top_makefile_constraints = {
      # Since 5.1.0-rc3 (the commit d93a18f27e3701a8cdc2228aee1c22451d1292e4)
      "samples" : z3.Bool("CONFIG_SAMPLES"),
      # Since 5.11.0-rc4 (the commit 8b5f4eb3ab700046b9f41d53544791fa02852551)
      "net" : z3.Bool("CONFIG_NET")
    }
    if unit:
      top_dir = unit.split('/')[0]
      if top_dir in top_makefile_constraints:
        if not kmax_constraints_for_unit: 
          kmax_constraints_for_unit = []
        kmax_constraints_for_unit.append(top_makefile_constraints[top_dir])
    
    if kmax_constraints_for_unit is None:
      # "None" is allowed only for top level directories, which are outside
      # kbuild makefiles.
      assert is_top_level_dir
      kmax_constraints_for_unit = []

    return kmax_constraints_for_unit

  def __add_compilation_unit(self, unit: str, inclusion_prop: __CompUnitInclusionProp):
    """Given a compilation unit, fetch the inclusion constraints using kmax,
    and add these constraints to kmax constraints based on inclusion property.

    May raise NoFormulaFoundForCompilationUnit or MultipleCompilationUnitsMatch exception.

    Arguments:
    unit -- compilation unit.
    inclusion_prop -- Inclusion property, i.e., include or exclude the unit.
    """
    kmax_constraints_for_unit = self.get_compilation_unit_constraints(unit)

    if inclusion_prop == Klocalizer.__CompUnitInclusionProp.INCLUDE:
      self.__include_compilation_units.append(unit)
      self.__kmax_constraints.extend(kmax_constraints_for_unit)
    elif inclusion_prop == Klocalizer.__CompUnitInclusionProp.EXCLUDE:
      self.__exclude_compilation_units.append(unit)
      self.__kmax_constraints.extend(z3.Not(z3.And(kmax_constraints_for_unit)))
    else:
      assert False

  def include_compilation_unit(self, unit: str):
    """Given a compilation unit, fetch the inclusion constraints using kmax,
    and add these constraints to for inclusion of the unit.

    May raise NoFormulaFoundForCompilationUnit or MultipleCompilationUnitsMatch exception.

    Arguments:
    unit -- compilation unit.
    """
    self.__add_compilation_unit(unit, Klocalizer.__CompUnitInclusionProp.INCLUDE)

  def exclude_compilation_unit(self, unit: str):
    """Given a compilation unit, fetch the inclusion constraints using kmax,
    and add these constraints to for exclusion of the unit.

    May raise NoFormulaFoundForCompilationUnit or MultipleCompilationUnitsMatch exception.

    Arguments:
    unit -- compilation unit.
    """
    self.__add_compilation_unit(unit, Klocalizer.__CompUnitInclusionProp.EXCLUDE)
    
  def reset_compilation_units(self):
    """Reset any inclusion/exclusion of compilation units set earlier.
    """
    self.__kmax_constraints=[]
    self.__include_compilation_units=[]
    self.__exclude_compilation_units=[]

  class ConditionalBlock:
    """A node of tree-like representation of source code for conditional blocks
    defined by conditional preprocessor directives.
    """
    def __init__(self):
      # Line number where the conditional block starts in the source code.
      # A conditional block starts with a`#if` or `#elif` directive. Thus,
      # the corresponding line in the source code contains one of these directives.
      self.start_line = -1

      # Line number where the conditional block ends in the source code. A
      # conditional block ends with a `#elif` (the beginning of the next conditional
      # block) or `#endif` directive. Thus, the corresponding line in the source
      # code contains one of these directives.
      self.end_line = -1

      # List of sub conditional block groups contained. A conditional block
      # group is a conditional ladder (#if [#elif]* #endif), which might contain
      # one or more conditional blocks.
      self.sub_block_groups = []

      # Complete presence condition for the conditional block. A z3.Solver instance.
      self.pc = None

      # Parent conditional block.
      self.parent = None
    
    def dumps(self) -> str:
      """Return string representation of conditional block.
      """
      return self.__repr__()
    
    @staticmethod
    def loads(cb_string: str):
      """Parse conditional block from its string representation.

      Arguments:
      cb_string -- string representation of conditional block.

      Returns an instance of ConditionalBlock.
      """
      from ast import literal_eval
      return Klocalizer.ConditionalBlock._ConditionalBlock__parse_cb(literal_eval(cb_string))

    def __repr__(self):
      pc_repr = ""
      if self.pc: pc_repr = self.pc.to_smt2().replace("\n", "\\n")
      return "{\"StartLine\": %d, \"EndLine\": %d, \"PC\": \"%s\", \"Sub\": %s}" % (self.start_line, self.end_line, pc_repr, self.sub_block_groups)

    def get_deepest_blocks(self, lines):
      """Given a line number, returns the unique set of deepest conditional
      blocks that contains these lines. The return value is equivalent to what
      would be obtained by calling get_deepest_block() for each line and deduplicating.
      However, this method is faster.

      Arguments:
      lines -- List of lines to query the deepest conditional blocks for.

      Returns `None` if a block for some line can't be found."""
      # TODO: optimize: do a single traversal on the tree.
      # Use a list to preserve the order for replicability.
      cbs = []
      for line in lines:
        cb = self.get_deepest_block(line)
        if cb == None: return None
        if cb not in cbs: cbs.append(cb)
      start_line_cbs = [(cb.start_line, cb) for cb in cbs]
      start_line_cbs.sort()
      return [x[1] for x in start_line_cbs]
      
      return cbs

    def get_deepest_block(self, line: int):
      """Given a line number, returns the deepest conditional block that contains
      the line.

      Arguments:
      line -- Line number to query the deepest conditional block for.

      Returns `None` if line is not included within the block."""
      if not (self.start_line <= line < self.end_line):
        return None
      
      # visit children
      for cbgroup in self.sub_block_groups:
        for cb in cbgroup:
          ret = cb.get_deepest_block(line)
          if ret != None:
            return ret
      
      # no children covers but the self does -- return self
      return self

    @staticmethod
    def __parse_sub(sub_string_rep: str, parent):
      """Parse and return conditional block groups This may be any intermediate
      conditional block group as well.

      Arguments:
      sub_string_rep -- string representation of conditional block groups.
      parent -- Parent ConditionalBlock instance. The parent of top-level conditional
      block groups parsed by the method will be set to this.

      Returns [[ConditionalBlock]], i.e., a list of conditional block groups.
      """
      groups = []
      for cbgroup_str in sub_string_rep:
        group = []
        for cb_str in cbgroup_str:
          cb = Klocalizer.ConditionalBlock._ConditionalBlock__parse_cb(cb_str)
          cb.parent = parent
          group.append(cb)
        groups.append(group)
      return groups

    @staticmethod
    def __parse_cb(cb_string_rep: str):
      """Parse and return a conditional block group.

      Arguments:
      cb_string_rep -- string representation of a conditional block.

      Returns ConditionalBlock.
      """
      # TODO: change these
      cb = Klocalizer.ConditionalBlock()
      cb.start_line = int(cb_string_rep["StartLine"])
      cb.end_line = int(cb_string_rep["EndLine"])
      # Config options come as |(defined CONFIG_A)| from SuperC. Convert
      # them to CONFIG_A format for compatibility with kclause.
      pc_string = cb_string_rep["PC"]
      pc_string = re.sub(r'\|\(defined (CONFIG_[a-zA-Z0-9_]*)\)\|', r'\1', pc_string)
      z3_solver = z3.Solver()
      z3_solver.from_string(pc_string) # TODO: make this an expression instead?
      cb.pc = z3_solver
      cb.sub_block_groups = Klocalizer.ConditionalBlock.__parse_sub(cb_string_rep["Sub"], cb)

      return cb

    # TODO: impl method: given pc and line ranges, return configs

  @staticmethod
  def __check_args_get_sourceline_pc( \
      srcfile: str, srcdir: str, is_linux: bool, \
      archs, superc_linux_script, makecross_script, \
      skip_kconfig_config_gen, skip_building_unit, skip_superc_config_gen):
    """Check arguments of for sourceline presence condition localization methods
    through assertions.
    """
    from shutil import which
    def is_success(command_to_run: list):
      return 0 == run(command_to_run, capture_stdout=True, capture_stderr=True)[2]
    
    def check_java():
      return which("java") != None

    def check_superc():
      return is_success(["java", "superc.SuperC"])
    
    def check_superc_linux_script():
      return which(superc_linux_script) != None
    
    def check_makecross_script():
      return which(makecross_script) != None
    
    # TODO: raise specific exceptions instead of assertion failures
    assert srcfile
    if srcdir: assert os.path.isdir(srcdir) and os.path.isfile(os.path.join(srcdir, srcfile))
    if not srcdir: os.path.isfile(srcfile)
    assert check_java()
    assert check_superc()
    if is_linux:
      assert srcdir # TODO: check if dir is linux ksrc
      assert skip_building_unit or check_makecross_script()
      assert check_superc_linux_script()
      assert archs
      for arch in archs:
        assert type(arch) is Arch

  class Ret_LocalizeConfig(enum.Enum):
    SUCCESS=0       #< All success.
    ERROR_UNSAT=1   #< Given archs do not compile the unit.
    ERROR_KMAX_EXCEPTION=2       #< A Klocalizer.KmaxException was thrown for one of the units.
    ERROR_KLOCALIZER_EXCEPTION=3 #< A Klocalizer.KlocalizerException was thrown.

  @staticmethod
  def localize_config(unit_paths: list, output_config_path: str,
    linux_ksrc: str, archs: list, logger):
    """Localize a linux configuration file that compiles the given units.

    This is a simplified version of what klocalizer command line tool does:
    it searches for an architecture one by one, and when found a SAT one,
    creates a configuration file (takes a random solution).

    Returns a tuple of 3 values:
    * Ret_LocalizeConfig: An instance of Ret_LocalizeConfig, representing
    success/error.
    * Arch: The first Arch instance that compiles the units from the input
    archs list. May be None on error.
    * Exception: The exception thrown if the status is ERROR_KMAX_EXCEPTION
    or ERROR_KLOCALIZER_EXCEPTION, which can be used for diagnostic.

    Also, writes the output configuration file to output_config_path on
    success. This is as obtained from klocalizer: may need olddefconfig.
    A config file might be created even on error.

    Arguments:
    * unit_paths -- List of unit paths (e.g., ['kernel/fork.o', 'kernel/cpu.o'])
    * output_config_path -- Path to non-existing output configuration file.
    * linux_ksrc -- Path to top linux source directory.
    * archs -- Architectures to try as a list of Arch instances.
    * logger -- Logger that implements common.VoidLogger interface.
    """
    try:
      return Klocalizer.__localize_config(unit_paths, output_config_path, linux_ksrc, archs, logger)
    except Klocalizer.KmaxException as e:
      logger.debug("Exception in localize_config(): \"%s\"\n" % e.message)
      ret_status = Klocalizer.Ret_LocalizeConfig.ERROR_KMAX_EXCEPTION
      ret_arch = None
      ret_exception = e
      return ret_status, ret_arch, ret_exception
    except Klocalizer.KlocalizerException as e:
      logger.debug("Exception in localize_config(): \"%s\"\n" % e.message)
      ret_status = Klocalizer.Ret_LocalizeConfig.ERROR_KLOCALIZER_EXCEPTION
      ret_arch = None
      ret_exception = e
      return ret_status, ret_arch, ret_exception


  @staticmethod
  def __localize_config(unit_paths: list, output_config_path: str,
    linux_ksrc: str, archs: list, logger):
    """Helper to Klocalizer.localize_config(). May throw exception to be
    caught by Klocalizer.localize_config().
    """
    #
    # Check arguments
    #
    assert unit_paths
    for u in unit_paths:
        assert u.endswith(".o")
    assert os.path.isdir(linux_ksrc)
    assert archs
    assert logger

    #
    # Create a klocalizer instance
    #
    logger.debug("Creating the klocalizer instance.\n")
    kloc = Klocalizer()
    kloc.set_linux_krsc(linux_ksrc)
    kloc.add_constraints([z3.Not(z3.Bool("CONFIG_BROKEN"))])
    
    #
    # Add compilation units (also retrives kmax formulas)
    #
    logger.debug("Adding the compilation units to klocalizer.\n")
    for u in unit_paths:
      kloc.include_compilation_unit(u)

    #
    # Find an architecture that compiles the unit
    #
    logger.debug("Detecting the architecture.\n")
    time_start = time.time()
    for arch in archs:
      logger.debug("Trying \"%s\"\n" % arch.name)
      full_constraints = kloc.compile_constraints(arch)
      model_sampler = Klocalizer.Z3ModelSampler(full_constraints)
      is_sat, z3_model = model_sampler.sample_model()
      if is_sat:
        break
    time_elapsed = time.time() - time_start
    logger.debug("TIME: Time elapsed(sec) for architecture search: %.2f\n" % time_elapsed)
    if not is_sat: #< Not possible to compile with the given set of archs
      logger.debug("Could not find an architecture that compiles the unit.\n")
      return Klocalizer.Ret_LocalizeConfig.ERROR_UNSAT, None, None
    else:          #< Compiles for arch
      assert arch
      logger.debug("The unit compiles for the architecture: \"%s\"\n" % arch.name)

    #
    # Create a config file that compiles the unit
    #
    logger.debug("Creating config file to compile the unit.\n")
    time_start = time.time()
    assert is_sat and (z3_model is not None)
    config_content = Klocalizer.get_config_from_model(z3_model, arch, set_tristate_m=False, allow_non_visibles=False)
    assert config_content
    with open(output_config_path, "w") as f:
      f.write(config_content)
    assert os.path.isfile(output_config_path)
    time_elapsed = time.time() - time_start
    logger.debug("TIME: Time elapsed(sec) for creating the config file: %.2f\n" % time_elapsed)

    return Klocalizer.Ret_LocalizeConfig.SUCCESS, arch, None

  @staticmethod
  def get_sourceline_pc_standalone_file(srcfile: str):
    """Get sourceline presence conditions for a stand-alone source file.

    Requires SuperC.

    Arguments:
    srcfile -- Path to the source file.

    Returns ConditionalBlock.
    """
    # TODO: let user choose whether to restrict to CONFIG_ prefixed options
    Klocalizer.__check_args_get_sourceline_pc(srcfile=srcfile, srcdir=None, is_linux=False, \
      superc_linux_script=None, makecross_script=None,
      skip_kconfig_config_gen=True, skip_building_unit=True, skip_superc_config_gen=True)
  
    #
    # Run SuperC
    #
    import tempfile
    with tempfile.NamedTemporaryFile() as tmpfile:
      tmpfilename = tmpfile.name
      superc_cmd = ["java", "superc.SuperC", "-sourcelinePC", tmpfilename, srcfile]
      _, _, ret, _ = run(superc_cmd, capture_stdout=True, capture_stderr=True)
      assert ret == 0
      from ast import literal_eval
      return Klocalizer.ConditionalBlock._ConditionalBlock__parse_cb(literal_eval(tmpfile.read().decode()))

  class SourcelinePcResult(enum.Enum):
    SUCCESS=0       #< All success.
    ERROR_UNSAT=1   #< Given archs do not compile the unit.
    ERROR_MAKE=2    #< Make results in error while trying to compile the unit.
    ERROR_SUPERC=3  #< SuperC fails to create sourceline presence conditions,
                    #< or SuperC cannot be found. The returned architecture
                    #< is still valid to compile the unit.
    ERROR_MAKE_TIMEOUT=4   #< Make timed-out while trying to compile the unit.
    ERROR_SUPERC_TIMEOUT=5 #< SuperC timed-out while creating sourceline
                    #< presence conditions. The returned architecture is
                    #< still valid to compile the unit.


  @staticmethod
  def get_sourceline_pc_linux_file(srcfile: str, linux_ksrc: str, archs, \
      superc_linux_script: str, makecross_script: str, \
      build_target: str,
      restrict_to_config_prefix=True, \
      superc_configs_dir="superc_configs/", \
      skip_kconfig_config_gen=False, skip_building_unit=False, skip_superc_config_gen=False, \
      make_out_path=None, make_err_path=None, \
      superc_out_path=None, superc_err_path=None, \
      make_timeout=None, superc_timeout=None,
      logger=VoidLogger()):
    """Get sourceline presence conditions for a source file within a Linux
    kernel source.

    Requires SuperC.

    The routine is as follows:
    1. Create a config file that compiles the unit using Klocalizer.
    2. Compile the unit using the compiler script (makecross_script).
    3. Create SuperC config file for the unit using SuperC Linux script (superc_linux_script).
    4. Clear autoconf.h ($LINUX_KSRC/include/generated/autoconf.h)
    5. Run SuperC using SuperC Linux script (superc_linux_script).
    6. Parse SuperC's output and and return (arch, [[ConditionalBlock]]).

    Arguments:
    srcfile -- Path to the source file. This must be relative to the top directory
    of the Linux kernel source, specified with linux_ksrc argument.
    linux_ksrc -- Path to the Linux kernel source.
    arch -- A list of Arch instances. The first arch that compiles the unit
    will be used.
    superc_linux_script -- Path to the superc_linux script to be used to obtain
    SuperC configs for the source file and to run SuperC. This can be found
    at $SUPERC_SRC/scripts/superc_linux.sh.
    makecross_script -- Path to the make script for cross compilation. For
    Linux source files, SuperC needs the source file to be built. If not
    cross-compiling, having this set to `make` is enough if it is in PATH.
    restrict_to_config_prefix -- If set, `-restrictConfigToPrefix` is set to 
    `CONFIG_` for SuperC. This boosts the performance and results in focusing
    on config macros, while setting the rest to their default values.
    build_target -- Build target for the given source file (srcfile).
    Usually, replacing the source file extension with .o (src/file.c -> src/file.o)
    is enough, but there are cases where parent or different directories need
    to be built.
    superc_configs_dir -- Directory to read/write SuperC configs. See `skip_superc_config_gen`.
    skip_kconfig_config_gen -- Set to skip Kconfig config generation for the unit.
    skip_building_unit -- Set to skip building the unit.
    skip_superc_config_gen -- Set to skip SuperC config generation for the
    unit to reuse existing configs. If not set, a config is always generated.
    make_out_path -- Path to the file where to write make's stdout while
    compiling the unit. Created if the unit cannot be compiled, i.e., 
    when status is ERROR_MAKE.
    make_err_path -- Path to the file where to write make's stderr while
    compiling the unit. Created if the unit cannot be compiled, i.e.,
    when status is ERROR_MAKE.
    superc_out_path -- Path to the file where to write superc's stdout
    while computing sourceline pc. Created if it fails, i.e., when status
    is ERROR_SUPERC.
    superc_err_path -- Path to the file where to write superc's stderr
    while computing sourceline pc. Created if it fails, i.e., when status
    is ERROR_SUPERC.
    make_timeout -- Timeout in seconds for make.
    superc_timeout -- Timeout in seconds for SuperC.
    logger -- Logger.

    Returns a tuple of three values:
      - An instance of SourcelinePcResult, representing the success/error.
      - An Arch instance, representing the architecture that compiles the
        unit. May be None in error cases, e.g., ERROR_UNSAT.
      - A ConditionalBlock instance, representing the sourceline presence
        conditions for the sourcefile. May be None in error cases.
    """
    # TODO: take additional flags to SuperC
    # TODO: any existing .config file is overwritten. write new Kconfig configs to a path different than linux_ksrc/.config?
    # TODO: don't create superc_configs if exists already? add a flag such as create_if_no_config
    superc_configs_dir=os.path.realpath(superc_configs_dir)

    # Check the arguments.
    Klocalizer.__check_args_get_sourceline_pc(srcfile, linux_ksrc, True, \
      archs, superc_linux_script, makecross_script, \
      skip_kconfig_config_gen, skip_building_unit, skip_superc_config_gen)

    def write_content_to_file(content : str, fpath : str):
      if fpath is None:
        return False
      os.makedirs(os.path.dirname(fpath), exist_ok=True)
      with open(fpath, 'w') as f:
        f.write(content)
      return True

    #
    # Detect the architecture
    #
    logger.info("Detecting the architecture.")
    time_start = time.time()
    kloc = Klocalizer()
    kloc.set_linux_krsc(linux_ksrc)
    kloc.add_constraints([z3.Not(z3.Bool("CONFIG_BROKEN"))])
    kloc.include_compilation_unit(srcfile)

    #
    # Find an architecture that compiles the unit
    #
    for arch in archs:
      logger.info("Trying \"%s\"" % arch.name)
      full_constraints = kloc.compile_constraints(arch)
      model_sampler = Klocalizer.Z3ModelSampler(full_constraints)
      is_sat, z3_model = model_sampler.sample_model()
      if is_sat:
        break
    time_elapsed = time.time() - time_start
    logger.info("TIME: Time elapsed(sec) for architecture search: %.2f" % time_elapsed)
    # Not possible to compile with the given set of architectures
    if not is_sat:
      logger.warning("Could not find an architecture that compiles the unit.")
      return Klocalizer.SourcelinePcResult.ERROR_UNSAT, None, None
    else:
      assert arch
      logger.info("The unit compiles for the architecture: \"%s\"" % arch.name)
      

    #
    # Create a config file that compiles the unit
    #
    config_filepath = os.path.join(linux_ksrc, ".config")
    if not skip_kconfig_config_gen:
      logger.info("Creating config file to compile the unit.")
      time_start = time.time()
      assert is_sat and (z3_model != None)
      config_content = Klocalizer.get_config_from_model(z3_model, arch, set_tristate_m=False, allow_non_visibles=False)
      with open(config_filepath, "w") as f:
        f.write(config_content)
      assert os.path.isfile(config_filepath)
      time_elapsed = time.time() - time_start
      logger.info("TIME: Time elapsed(sec) for creating the config file: %.2f" % time_elapsed)

    else:
      logger.info("Skipped: creating config file to compile the unit.")

    #
    # Compile the unit
    #
    unit_name = srcfile[:-len(".c")] + ".o"
    if not skip_building_unit:
      logger.info("Compiling the unit.")
      olddefconf_cmd = ["make", "ARCH=%s" % arch.name, "olddefconfig"]
      assert srcfile.endswith(".c") # TODO: what if this is not a sourcefile but a header file?

      compile_cmd = [makecross_script, "ARCH=%s" % arch.name, "clean", build_target]
      compile_cmd_str = " ".join(compile_cmd)

      _, _, _, time_elapsed = run(olddefconf_cmd, cwd=linux_ksrc)
      logger.info("TIME: Time elapsed(sec) for running make olddefconfig: %.2f" % time_elapsed)
      try:
        make_out, make_err, ret, time_elapsed = run(compile_cmd, cwd=linux_ksrc, timeout=make_timeout)
        logger.info("TIME: Time elapsed(sec) for running make: %0.2f" % time_elapsed)

        # Write make's stdout and stderr
        if ret != 0:
          # Might happen with warnings like unmet dependency bug. Make is
          # said to fail if the unit cannot be found compiled.
          logger.warning("Make returned non-zero(%s)" % ret)
        unit_path = os.path.join(linux_ksrc, unit_name)
        if not os.path.isfile(unit_path):
          logger.error("Cannot find a compiled unit at \"%s\"" % unit_path)
          write_content_to_file(compile_cmd_str +"\n"+ make_out.decode('utf-8'), make_out_path)
          write_content_to_file(compile_cmd_str +"\n"+ make_err.decode('utf-8'), make_err_path)
          return Klocalizer.SourcelinePcResult.ERROR_MAKE, None, None
      except subprocess.TimeoutExpired:
        logger.error("Timeout expired for make, duration(sec): %.2f" % make_timeout)
        write_content_to_file(compile_cmd_str +"\n"+ "Timeout expired, duration(sec): %.2f" % make_timeout, make_out_path)
        write_content_to_file(compile_cmd_str +"\n"+ "Timeout expired, duration(sec): %.2f" % make_timeout, make_err_path)
        return Klocalizer.SourcelinePcResult.ERROR_MAKE_TIMEOUT, None, None
    else:
      logger.info("Skipped: compiling the unit.")

    #
    # Create superc config for srcfile
    #
    superc_config_path = os.path.join(superc_configs_dir, srcfile+".configs_superc")
    if not skip_superc_config_gen:
      logger.info("Creating SuperC config file.")
      # use superc_linux_script
      # /usr/bin/time bash $superc_linux_script -S"$superc_args" -w -L configs/ ${source_file} < /dev/null
      import pathlib
      pathlib.Path(superc_configs_dir).mkdir(parents=True, exist_ok=True)
      assert os.path.isdir(superc_configs_dir)
      config_gen_cmd = [superc_linux_script, "-w", "-x", makecross_script, "-a", arch.name, "-L", superc_configs_dir, srcfile]
      logger.info("SuperC config gen command: \"%s\"" % " ".join(config_gen_cmd))
      _, _, _, time_elapsed = run(config_gen_cmd, cwd=linux_ksrc)
      logger.info("TIME: Time elapsed(sec) for SuperC config generation: %.2f" % time_elapsed)
      assert os.path.isfile(superc_config_path)
    else:
      logger.info("Skipped: creating SuperC config file.")
    
    #
    # Clear autoconf.h
    #
    logger.info("Clearing autoconf.h.")
    autoconf_path = os.path.join(linux_ksrc, "include/generated/autoconf.h")
    with open(autoconf_path, "w") as f: pass
    assert os.path.isfile(autoconf_path)
    with open(autoconf_path, "r") as f: assert not f.readlines()

    #
    # Create header file to handle IS_ENABLED() with SuperC
    #
    options_header_file = os.path.join(linux_ksrc, "config_options.h")
    logger.info("Creating a temporary header file of config options at \"%s\" to handle IS_ENABLED macro." % options_header_file)

    def get_superc_header_content(config_options):
      """Given a list of config options, create and return the header
      content to handle IS_ENABLED macro for SuperC.
      """
      def get_for_option(option):
        assert option.startswith("CONFIG_")
        ret =     "#ifdef %s" % option
        ret += "\n#define %s 1" % option
        ret += "\n#else"
        ret += "\n#undef %s" % option
        ret += "\n#endif\n"
        return ret
      return "\n".join([get_for_option(option) for option in config_options])

    config_options = arch.get_bool_tristate_options()
    header_content = get_superc_header_content(config_options)
    with open(options_header_file, 'w') as f:
      f.write(header_content)
    assert os.path.isfile(options_header_file)

    #
    # Run SuperC
    #
    logger.info("Running SuperC.")
    import tempfile
    with tempfile.NamedTemporaryFile() as tmpfile:
      tmpfilename = tmpfile.name

      restrict_flag = " -restrictConfigToPrefix CONFIG_ " if restrict_to_config_prefix else ""
      superc_flags = "%s -sourcelinePC %s" % (restrict_flag, tmpfilename)
      superc_flags += " -include %s" % options_header_file
      superc_sourcelinepc_cmd = [superc_linux_script, "-S%s" % superc_flags, "-L%s" % superc_configs_dir, srcfile]
      superc_sourcelinepc_cmd_str = " ".join(superc_sourcelinepc_cmd)
      logger.info("SuperC command: \"%s\"" % " ".join(superc_sourcelinepc_cmd))
      try:
        superc_out, superc_err, ret, time_elapsed = run(superc_sourcelinepc_cmd, cwd=linux_ksrc, timeout=superc_timeout)
        logger.info("TIME: Time elapsed(sec) for SuperC sourceline pc computation: %0.2f" % time_elapsed)

        if ret != 0:
          # Might happen with warnings/errors where we still get some results.
          logger.warning("SuperC returned non-zero(%s)" % ret)

        superc_pcfile_content = tmpfile.read().decode()
        if not superc_pcfile_content:
          logger.error("Empty SuperC output.")
          write_content_to_file(superc_sourcelinepc_cmd_str +"\n"+ superc_out.decode('utf-8'), superc_out_path)
          write_content_to_file(superc_sourcelinepc_cmd_str +"\n"+ superc_err.decode('utf-8'), superc_err_path)
          return Klocalizer.SourcelinePcResult.ERROR_SUPERC, arch, None
      except subprocess.TimeoutExpired:
        logger.error("Timeout expired for SuperC, duration(sec): %.2f" % superc_timeout)
        write_content_to_file(superc_sourcelinepc_cmd_str +"\n"+ "Timeout expired, duration(sec): %.2f" % superc_timeout, superc_out_path)
        write_content_to_file(superc_sourcelinepc_cmd_str +"\n"+ "Timeout expired, duration(sec): %.2f" % superc_timeout, superc_err_path)
        return Klocalizer.SourcelinePcResult.ERROR_SUPERC_TIMEOUT, arch, None

    assert superc_pcfile_content
    assert arch
    from ast import literal_eval
    # return __parse_cb(literal_eval(superc_pcfile_content))
    ret_code = Klocalizer.SourcelinePcResult.SUCCESS
    pc = Klocalizer.ConditionalBlock._ConditionalBlock__parse_cb(literal_eval(superc_pcfile_content))
    return ret_code, arch, pc

  #
  # Exceptions
  #
  class KlocalizerException(Exception):
    pass

  class KmaxException(KlocalizerException):
    pass

  class KmaxFileNotFound(KmaxException, FileNotFoundError):
    def __init__(self, filepath):
      self.filepath = filepath
      self.message = "Can't file kmax formulas file at %s" % filepath
      super().__init__(self.message)

  class NoFormulaFoundForCompilationUnit(KmaxException):
    def __init__(self, unit):
      self.unit = unit
      self.message = "Kmax can't find formula for the compilation unit: %s" % unit
      super().__init__(self.message)
    
  class MultipleCompilationUnitsMatch(KmaxException):
    def __init__(self, unit, matching_units):
      self.unit = unit
      self.matching_units = matching_units
      self.message = "There are multiple compilation units that match %s.  One of the below Kbuild paths should be provided instead:\n%s" % (unit, "\n".join(matching_units))
      super().__init__(self.message)
