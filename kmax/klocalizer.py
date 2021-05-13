import sys
import os
import argparse
import z3
import regex
import pickle
import random
import kmax.about
import subprocess
# import kmax.alg # Run()
import pprint
import enum
import z3
from kmax.arch import Arch
from kmax.common import get_kmax_constraints, unpickle_kmax_file
from kmax.vcommon import getLogLevel, getLogger

# TODO(necip): automated testing

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
    self.__logger.info("Loading Kmax formulas from file: %s\n" % kmax_file)
    self.__kmax_formulas = unpickle_kmax_file(filepath)
    self.__logger.info("Kmax formulas was loaded.\n")

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
    self.__logger.info("Running kmax: %s\n" % (" ".join(command)))
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
        if current_path not in self.__kmax_formulas.keys():
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
          self.__logger.info("%s has no kmax formula, assuming it is unconstrained.\n" % (current_path))

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
        self.__logger.info("%d assumptions left to try removing.\r" % (total_assumptions_to_match))
        while not is_sat:
          core = solver.unsat_core()
          # remove all assumptions that in the core, except those specifically given as user-constraints.  potential optmization: try randomizing this or removing only some assumptions each iteration.
          # print(core)
          # update: user-constraints are no longer handled differently
          assumptions = [ assumption for assumption in assumptions if assumption not in core ]
          self.__logger.info("%s\r" % len(assumptions))
          is_sat = solver.check(assumptions) == z3.sat
        self.__logger.info("\r")
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
          vars_not_in_arch = [ used_var for used_var in used_vars if str(used_var) not in kconfig_types.keys() and token_pattern.match(str(used_var)) ]
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

  def __add_compilation_unit(self, unit: str, inclusion_prop: __CompUnitInclusionProp):
    """Given a compilation unit, fetch the inclusion constraints using kmax,
    and add these constraints to kmax constraints based on inclusion property.

    May raise NoFormulaFoundForCompilationUnit or MultipleCompilationUnitsMatch exception.

    Arguments:
    unit -- compilation unit.
    inclusion_prop -- Inclusion property, i.e., include or exclude the unit.
    """
    #
    # Format the unit name
    #
    if not unit.endswith(".o"):
      self.__logger.warning("Forcing file extension to be .o, since lookup is by compilation unit: %s\n" % (unit))
      unit = os.path.splitext(unit)[0] + ".o"
    
    #
    # Process the unit name get all the paths for which to pull the kmax formulas
    #
    # Two possibilities: use the content of the kmax_file or the on-the-fly kmax_cache
    if self.__is_kmax_formulas_cache: # kmax_formulas is cache
      # TODO: We call resolve_kbuild_path() for complete formulas, but not for this?
      # Maybe we should just do the same for all? Maybe that's the reason for the issue Jeho experienced.
      self.__fetch_kmax_constraints(unit)
      if unit not in self.__kmax_formulas:
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
        self.__logger.info("Using full path from Kbuild: %s\n" % (kbuild_path))
        unit = kbuild_path
    
    #
    # Add the constraints to the kmax constraints accumulator
    #
    kmax_constraints_for_unit = get_kmax_constraints(self.__kmax_formulas, unit) # TODO: this one is not quiet

    if inclusion_prop == Klocalizer.__CompUnitInclusionProp.INCLUDE:
      self.__include_compilation_units.append(unit)
      self.__kmax_constraints.extend(kmax_constraints_for_unit)
    elif inclusion_prop == Klocalizer.__CompUnitInclusionProp.EXCLUDE:
      self.__exclude_compilation_units.append(unit)
      self.__kmax_constraints.extend([z3.Not(c) for c in kmax_constraints_for_unit])
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
