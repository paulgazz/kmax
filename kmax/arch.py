
import os
import re
import subprocess
import random
import string
import pickle
import z3
import logging
from kmax.vcommon import getLogger, run
import kmax.kextractcommon

# TODO(necip): test: test compatibility with the existing file formats
# TODO(necip): test: test exceptions
# TODO(necip): test: Load all types and try to use
# TODO(necip): test: Generate all types and try to use
# TODO(necip): impl: reoder methods, reorganize code
# TODO(necip): docs: better define in documentation what resets different states of an Arch instance
# TODO(necip): impl: do the seperation of read and load to ensure you can load kextract independent of the file (or other formulas)
# TODO(necip): impl: some methods return smt2 string while some return z3 bools. should we keep one way only or is the current way fine?

class Arch:
  """Architecture Formulas Handler

  This class allows to manage kextract/kclause formulas and any architecture
  specific constructs.

  For any type of formula, there are typically 4 types of operations.

    * load -- Load formulas from file. Load can be delayed by setting delay_loading
    keyword argument. This will delay the load until the formula is needed
    (i.e., requested using getter). If formula is never requested, the load
    will never happen, so that, unnecessary IO overhead is avoided.

    * generate -- Generate formulas, set, and return. kextract is generated
    using the Linux kernel source, and kclause is generated using kextract.

    * get -- Get formulas. If formulas is not ready, figure out a way to obtain
    them. If the load is delayed, get request will trigger the delayed load.
    If formulas are needed to be generated, get request will trigger the generation.
    
    * dump -- Dump formulas to file. Formulas can be loaded from these files
    later.
  
  Arch.ARCHS contains the list of known architecture names, for which kextract
  and kclause tools can extract formulas given valid linux kernel source. Additionaly,
  architecture specific constructs such as arch specific constructs can be obtained
  for them. Besides these, custom architectures can be created and custom formulas
  can be loaded into them. While kextract can't be generated for custom architectures,
  once kextract is loaded, kclause formulas can be generated from kextract.

  """
  # known linux architecture names -- ordered from most popular to least
  # TODO: kextract doesn't work for um32 (error msg: "arch/Kconfig:10: can't open file "arch/um64/Kconfig"")
  ARCHS = ["x86_64", "i386", "arm", "arm64", "sparc64", "sparc", "powerpc", "mips", "alpha", "arc", "c6x", "csky", "h8300", "hexagon", "ia64", "m68k", "microblaze", "nds32", "nios2", "openrisc", "parisc", "riscv", "s390", "sh", "sh64", "um", "unicore32",  "xtensa"]
  CUSTOM_ARCH_NAME = "CUSTOM_ARCH"
  # architecture-specific configs for known linux architectures
  ARCH_CONFIGS = set([ "CONFIG_ALPHA", "CONFIG_ARC", "CONFIG_ARM", "CONFIG_ARM64", "CONFIG_C6X", "CONFIG_CSKY", "CONFIG_H8300", "CONFIG_HEXAGON", "CONFIG_IA64", "CONFIG_M68K", "CONFIG_MICROBLAZE", "CONFIG_MIPS", "CONFIG_NDS32", "CONFIG_NIOS2", "CONFIG_OPENRISC", "CONFIG_PARISC", "CONFIG_PPC64", "CONFIG_PPC32", "CONFIG_PPC", "CONFIG_RISCV", "CONFIG_S390", "CONFIG_SUPERH64", "CONFIG_SUPERH32", "CONFIG_SUPERH", "CONFIG_SPARC64", "CONFIG_SPARC32", "CONFIG_SPARC", "CONFIG_UML", "CONFIG_UNICORE32", "CONFIG_X86_64", "CONFIG_X86_32", "CONFIG_X86", "CONFIG_XTENSA" ])

  @staticmethod
  def get_archs_from_subdir(kbuild_path: str) -> list:
    """Get the architectures associated with the given arch/ subdirectory."""
    assert(kbuild_path.startswith("arch/"))
    elems = kbuild_path.split("/")
    if (len(elems) < 3):
      # warning("need at least three elements, i.e., arch/NAME/unit.o to get arch name.")
      return []
    else:
      subdir = elems[1]
      # todo: handle um archs
      if subdir == "um" or elems[2] == "um":
        archs = [ "um", "um32" ]
      elif subdir == "x86":
        archs = [ "x86_64", "i386" ]
      elif subdir == "sh":
        archs = [ "sh", "sh64" ]
      elif subdir == "sparc":
        archs = [ "sparc", "sparc64" ]
      else:
        # arch matches subdir name
        archs = [ subdir ]
      return archs

  def get_arch_specific_constraints(self):
    """ Get the architecture specific constraints as list[z3.Bool].

    The architecture name is used to form the constraints. For custom architectures
    with names not included in Arch.ARCHS, the constraints may be incorrect.
    """
    arch=self.name

    if arch == "x86_64":
      constraints = [ z3.Bool("CONFIG_X86"), z3.Bool("CONFIG_X86_64"), z3.Not(z3.Bool("CONFIG_X86_32")), z3.Bool("BITS=64"), z3.Not(z3.Bool("BITS=32")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_X86", "CONFIG_X86_64", "CONFIG_X86_32"]))
    elif arch == "i386":
      constraints = [ z3.Bool("CONFIG_X86"), z3.Bool("CONFIG_X86_32"), z3.Not(z3.Bool("CONFIG_X86_64")), z3.Bool("BITS=32"), z3.Not(z3.Bool("BITS=64")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_X86", "CONFIG_X86_64", "CONFIG_X86_32"]))
    elif arch == "powerpc":
      constraints = [ z3.Bool("CONFIG_PPC") ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_PPC", "CONFIG_PPC32", "CONFIG_PPC64"]))
    elif arch == "sh":
      constraints = [ z3.Bool("CONFIG_SUPERH"), z3.Bool("CONFIG_SUPERH32"), z3.Not(z3.Bool("CONFIG_SUPERH64")), z3.Bool("BITS=32"), z3.Not(z3.Bool("BITS=64")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_SUPERH", "CONFIG_SUPERH32", "CONFIG_SUPERH64"]))
    elif arch == "sh64":
      constraints = [ z3.Bool("CONFIG_SUPERH"), z3.Bool("CONFIG_SUPERH64"), z3.Not(z3.Bool("CONFIG_SUPERH32")), z3.Bool("BITS=64"), z3.Not(z3.Bool("BITS=32")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_SUPERH", "CONFIG_SUPERH32", "CONFIG_SUPERH64"]))
    elif arch == "sparc":
      constraints = [ z3.Bool("CONFIG_SPARC"), z3.Bool("CONFIG_SPARC32"), z3.Not(z3.Bool("CONFIG_SPARC64")), z3.Bool("BITS=32"), z3.Not(z3.Bool("BITS=64")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_SPARC", "CONFIG_SPARC32", "CONFIG_SPARC64"]))
    elif arch == "sparc64":
      constraints = [ z3.Bool("CONFIG_SPARC"), z3.Bool("CONFIG_SPARC64"), z3.Not(z3.Bool("CONFIG_SPARC32")), z3.Bool("BITS=64"), z3.Not(z3.Bool("BITS=32")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_SPARC", "CONFIG_SPARC32", "CONFIG_SPARC64"]))
    elif arch == "um":
      constraints = [ z3.Bool("UML"), z3.Bool("CONFIG_X86"), z3.Bool("CONFIG_X86_64"), z3.Not(z3.Bool("CONFIG_X86_32")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_UML", "CONFIG_X86", "CONFIG_X86_64", "CONFIG_X86_32"]))
    elif arch == "um32":
      constraints = [ z3.Bool("UML"), z3.Bool("CONFIG_X86"), z3.Bool("CONFIG_X86_32"), z3.Not(z3.Bool("CONFIG_X86_64")) ]
      disabled = Arch.ARCH_CONFIGS.difference(set(["CONFIG_UML", "CONFIG_X86", "CONFIG_X86_64", "CONFIG_X86_32"]))
    else:
      arch_var = "CONFIG_%s" % (arch.upper())
      constraints = [ z3.Bool(arch_var) ]
      disabled = Arch.ARCH_CONFIGS.difference(set([ arch_var ]))
    disabled_z3 = [ z3.Not(z3.Bool(var)) for var in sorted(disabled) ]
    return constraints + disabled_z3

  def __load_available_formulas_files_from_arch_dir(self, arch_dir, is_kclause_composite, delayed=True):
    """Load available formulas from an Arch directory.

    Use Arch.load_arch() to create an arch instance this way through Arch's
    interface.

    The naming convention for files is as follows (formulas: filename)
    kextract          : kextract
    kclause           : kclause
    direct dependency : kclause.normal_dep
    reverse dependency: kclause.rev_dep
    selects           : kclause.selects

    Arguments:
    arch_dir -- The path to the architecture directory containing formula files.
    is_kclause_composite -- Set if the kclause formula file is in composite format.
    delayed -- If set, the paths to formula files within arch_dir
    are saved but read only when needed. Can be used to increase performance
    by avoiding unnecessary IO.
    """
    pathjoin = lambda x : os.path.join(arch_dir, x) 
    kextract_path = pathjoin("kextract")
    kclause_path  = pathjoin("kclause")
    dir_dep_path  = pathjoin("kclause.normal_dep")
    rev_dep_path  = pathjoin("kclause.rev_dep")
    selects_path  = pathjoin("kclause.selects")

    def do_load(filepath, load_method):
      if os.path.isfile(filepath):
        load_method(filepath, delay_loading=delayed)
    
    # workaround kclause is_kclause_composite argument
    def kclause_load_method(filepath, delay_loading):
      return self.load_kclause(filepath, is_composite=is_kclause_composite, delay_loading=delay_loading)
    
    do_load(kextract_path, self.load_kextract)
    do_load(kclause_path,  kclause_load_method)
    do_load(dir_dep_path,  self.load_dir_dep)
    do_load(rev_dep_path,  self.load_rev_dep)
    do_load(selects_path,  self.load_selects)

  # if there is no formulas file, keep the candidate name for generating and dumping later if needed
  def __gendump_nonavailable_formulas_files_to_arch_dir(self, arch_dir, is_kclause_composite, delayed=True):    
    """Generate and dump formulas that are not available in an Arch directory.

    The naming convention for files is as follows (formulas: filename)
    kextract          : kextract
    kclause           : kclause
    direct dependency : kclause.normal_dep
    reverse dependency: kclause.rev_dep
    selects           : kclause.selects

    Arguments:
    arch_dir -- The path to the architecture directory to dump the formula files.
    is_kclause_composite -- Dump kclause in composite format.
    delayed -- If set, the paths where to create the formula files within arch_dir
    are saved but the dump process is delayed until the formulas are needed
    by the Arch instance. If the formulas are never needed, they will be neither
    generated nor dumped. Can be used to increase performance by avoiding unnecessary
    IO.
    """
    pathjoin = lambda x : os.path.join(arch_dir, x) 
    kextract_path = pathjoin("kextract")
    kclause_path  = pathjoin("kclause")
    dir_dep_path  = pathjoin("kclause.normal_dep")
    rev_dep_path  = pathjoin("kclause.rev_dep")
    selects_path  = pathjoin("kclause.selects")

    def set_if_nofile(filepath):
      if not os.path.exists(filepath):
        return filepath
      else:
        return None
    
    if delayed:
      self.__kextract_file_delayed_dump = set_if_nofile(kextract_path)
      self.__kclause_file_delayed_dump = set_if_nofile(kclause_path)
      self.__kclause_file_delayed_dump_is_composite=is_kclause_composite
      self.__dir_dep_file_delayed_dump = set_if_nofile(dir_dep_path)
      self.__rev_dep_file_delayed_dump = set_if_nofile(rev_dep_path)
      self.__selects_file_delayed_dump = set_if_nofile(selects_path)
    else: # not delayed -- dump now
      # workaround on additional parameter
      def dump_kclause_method(kclause_file):
        self.dump_kclause(kclause_file=kclause_file, dump_composite=is_kclause_composite)

      def ensure_then_dump(filepath, get_method, dump_method):
        if filepath:
          get_method() # ensure formulas are there
          dump_method(filepath)
      
      ensure_then_dump(kextract_path, self.get_kextract, self.dump_kextract)
      ensure_then_dump(kclause_path,  self.get_kclause, dump_kclause_method)
      ensure_then_dump(dir_dep_path,  self.get_dir_dep,  self.dump_dir_dep)
      ensure_then_dump(rev_dep_path,  self.get_rev_dep,  self.dump_rev_dep)
      ensure_then_dump(selects_path,  self.get_selects,  self.dump_selects)

  def __init__(self, name: str, linux_ksrc=None, arch_dir=None, is_kclause_composite=False, verify_linux_ksrc=True, kextract_version=None, loggerLevel=logging.INFO):
    """Create an Arch instance.

    Arguments:
    name -- Name of the architecture.
    linux_ksrc -- Path to the linux kernel source directory. Used for generating
    kextract formulas if needed.
    arch_dir -- Path to the architecture directory. The formula files available
    within this directory will be loaded as needed, and formulas not available
    will be dumped to this directory as generated.
    verify_linux_ksrc -- Set to verify linux_ksrc.
    kextract_version -- Kextract module version to use for generating kextract formulas.
    If not set, the latest possible version suitable for the kernel version is automatically
    detected and used.
    is_kclause_composite -- When an arch_dir is provided and it contains a
    kclause formulas file, it will be treated as composite or not dependending
    on this flag. If kclause file doesn't exist, the delayed dump will be composite
    or not depending on the flag.
    loggerLevel -- Logger level.
    """
    self.__logger=getLogger(name="Arch(%s)" % name, level=loggerLevel)
    self.name=name
    
    #
    # Formulas
    #

    # in string format
    self.__kextract=None
    # kextract module version
    self.__kextract_version=kextract_version
    # a mapping from symbol name in str to clauses in smt2 str
    self.__kclause_formulas=None
    # a mapping from symbol name in str to its direct dependencies in smt2 str
    self.__dir_dep_formulas=None
    # a mapping from symbol name in str to its reverse dependencies in smt2 str
    self.__rev_dep_formulas=None
    # a mapping from selected symbol name in str to a list, which containts
    # info about its selecters. each entry in the list is a mapping from selecter
    # symbol name in str to a visibility clause in smt2 str
    self.__selects=None
    # composite kclause formulas: an smt2 str
    self.__composite_kclause_formulas=None 

    if linux_ksrc != None and verify_linux_ksrc and not self.__verify_linux_ksrc(linux_ksrc):
      raise Arch.InvalidLinuxSource(linux_ksrc)
    
    self.__linux_ksrc = os.path.realpath(linux_ksrc) if linux_ksrc else None
    
    # if the load is delayed until needed, the formulas filepaths will be kept to be pickled later
    # delayed until needed
    self.__kextract_file_delayed_load = None
    self.__kclause_file_delayed_load = None
    self.__kclause_file_delayed_load_is_composite=None
    self.__dir_dep_file_delayed_load = None
    self.__rev_dep_file_delayed_load = None
    self.__selects_file_delayed_load = None

    # generation will use this to dump
    self.__kextract_file_delayed_dump = None
    self.__kclause_file_delayed_dump = None
    self.__kclause_file_delayed_dump_is_composite=None
    self.__dir_dep_file_delayed_dump = None
    self.__rev_dep_file_delayed_dump = None
    self.__selects_file_delayed_dump = None

    # kextract summary cache
    self.__kconfig_bool_tristate_options=None
    self.__kconfig_types=None
    self.__kconfig_visible=None
    self.__kconfig_has_def_nonbool=None

    # if an arch directory is specified, use it for loading/dumping
    if arch_dir != None:
      self.__load_available_formulas_files_from_arch_dir(arch_dir, is_kclause_composite, delayed=True)
      self.__gendump_nonavailable_formulas_files_to_arch_dir(arch_dir, is_kclause_composite, delayed=True)

  @staticmethod
  def load_arch(arch_name: str, arch_dir: str, is_kclause_composite=False, wait_until_needed=False):
    """ Create an Arch instance and load available formulas from an Arch directory.

    The naming convention for files is as follows (formulas: filename)
    kextract          : kextract
    kclause           : kclause
    direct dependency : kclause.normal_dep
    reverse dependency: kclause.rev_dep
    selects           : kclause.selects

    Arguments:
    arch_name -- The name of the architecture.
    arch_dir -- The path to the architecture directory containing formula files.
    is_kclause_composite -- Set if the kclause formula file is in composite format.
    wait_until_needed -- If set, the paths to formula files within arch_dir
    are saved but read only when needed. Can be used to increase performance
    by avoiding unnecessary IO.
    """
    arch = Arch(arch_name)
    
    arch.__load_available_formulas_files_from_arch_dir(arch_dir, is_kclause_composite=is_kclause_composite, delayed=wait_until_needed)
    return arch

  def dump_arch(self, arch_dir: str, dump_composite_kclause=False, overwrite_files=False):
    """Dump the available formulas as formula files to a architecture directory.

    Use generate_formulas() to ensure the formulas desired to be dumped to
    files are available.

    The naming convention for files is as follows (formulas: filename)
    kextract          : kextract
    kclause           : kclause
    direct dependency : kclause.normal_dep
    reverse dependency: kclause.rev_dep
    selects           : kclause.selects

    Arguments:
    arch_dir -- Path to the architecture directory to dump the formula files.
    dump_composite_kclause -- Set to dump kclause file in composite format.
    overwrite_files -- If set, overwrites the existing formula files.
    """
    assert not os.path.isfile(arch_dir)
    os.makedirs(os.path.realpath(arch_dir), exist_ok=True)

    def kclause_dump_method(filename):
      self.dump_kclause(filename, dump_composite_kclause)

    def do_dump(content, filename, dump_method):
      fullpath = os.path.join(arch_dir, filename)
      if content != None and (overwrite_files or (not os.path.exists(fullpath))):
        dump_method(content)

    do_dump(self.__kextract, "kextract", self.dump_kextract)
    do_dump(self.__kclause_formulas, "kclause", kclause_dump_method)
    do_dump(self.__dir_dep_formulas, "kclause.normal_dep", self.dump_dir_dep)
    do_dump(self.__rev_dep_formulas, "kclause.rev_dep", self.dump_rev_dep)
    do_dump(self.__selects, "kclause.selects", self.dump_selects)
    
  # only a helper combining the call to multiple generate methods
  def generate_formulas(self, generate_kextract=False, generate_kclause=False,
   generate_dir_dep=False, generate_rev_dep=False, generate_selects=False, overwrite=False):
    """Generate formulas.

    Use keyword arguments to select which formulas to generate.

    This method can be used to replace call to multiple generate methods.

    Arguments:
    overwrite -- If set, generates the formulas even if they are already set.
    """

    if generate_kextract and (overwrite or self.__kextract == None)        : self.generate_kextract()
    if generate_kclause  and (overwrite or self.__kclause_formulas == None): self.generate_kclause()
    if generate_dir_dep  and (overwrite or self.__dir_dep_formulas == None): self.generate_dir_dep()
    if generate_rev_dep  and (overwrite or self.__rev_dep_formulas == None): self.generate_rev_dep()
    if generate_selects  and (overwrite or self.__selects == None)         : self.generate_selects()
  
  def __check_arch_name(self):
    """Helper for checking if the architecture name is valid.
    """
    return self.name != None
    # TODO: further checks

  @staticmethod
  def __run_command(command, stdin=None, capture_stdout=True, capture_stderr=True, cwd=None):
    """Helper for running an external command.

    Shouldn't be needed when kmax/kclause can be used directly as a Python
    module.

    Returns a tuple of (stdout, stderr, return_code) for the process.

    Arguments:
    command -- Command to run, a list to pass to subprocess.Popen.
    stdin -- The content to be passed as stdin to the process.
    capture_stdout -- If set, caoture stdout to be returned by the method. Otherwise, keep it at stdout.
    capture_stderr -- If set, caoture stderr to be returned by the method. Otherwise, keep it at stdin.
    cwd -- Current working directory for the process.
    """
    stdout_param = subprocess.PIPE if capture_stdout else None
    stderr_param = subprocess.PIPE if capture_stderr else None
    popen = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=stdout_param, stderr=stderr_param, cwd=cwd)
    if stdin != None: popen.stdin.write(stdin)
    captured_stdout, captured_stderr = popen.communicate()
    popen.stdin.close()
    
    return captured_stdout, captured_stderr, popen.returncode
  
  @staticmethod
  def __verify_linux_ksrc(linux_ksrc_dir):
    """Verify if the given path is a linux kernel source directory.

    Returns True if so, False otherwise.

    The followings are done for verification:
      - Check if the path is an existing directory.
    TODO: more will be done for verification

    Arguments:
    linux_ksrc_dir -- Path to the directory to verify as linux kernel source.
    """
    return linux_ksrc_dir != None and os.path.isdir(linux_ksrc_dir)# TODO: additional checks

  @staticmethod
  def __get_tmp_file(prefix: str, suffix: str):
    """Get a filename with the given prefix and suffix that doesn't exist
    in the current directory, so that, it can be used to write temporary content.
    """
    genrndfname = lambda : ''.join(random.choice(string.ascii_lowercase) for i in range(5))
    tmp_kextract_file = prefix + genrndfname() + suffix
    while os.path.exists(tmp_kextract_file):
      tmp_kextract_file = prefix + genrndfname() + suffix
    return tmp_kextract_file

  @staticmethod
  def __dump_str_to_file(filepath, content, binary=True):
    """Dump to content to the file.

    Arguments:
    binary -- If set, use 'wb' mode. Otherwise, use 'w' mode.
    """
    assert content != None
    assert not os.path.isdir(filepath)

    filepath=os.path.realpath(filepath)
    os.makedirs(os.path.dirname(filepath), exist_ok=True)

    file_mode = 'wb' if binary else 'w'
    with open(filepath, file_mode) as f:
      f.write(content)

  @staticmethod
  def __pickle_dump_to_file(filepath, obj, binary=True):
    """Pickle dump the object to the file.

    Arguments:
    binary -- If set, use 'wb' mode. Otherwise, use 'w' mode.
    """
    assert obj != None
    assert not os.path.isdir(filepath)

    filepath=os.path.realpath(filepath)
    os.makedirs(os.path.dirname(filepath), exist_ok=True)

    file_mode = 'wb' if binary else 'w'
    with open(filepath, file_mode) as f:
      pickle.dump(obj, f)
  
  @staticmethod
  def __pickle_bin_dict(filepath):
    """Pickle binary dictionary.
    """
    assert os.path.isfile(filepath)
    with open(filepath, "rb") as f:
      return pickle.load(f)

  # used for any type of kclause formulas (kclause, dir_dep, rev_dep, selects)
  # ensure that the formulas are there
  def __ensure_formulas(self, formula_content, formula_delayed_file,  formula_load_method, formula_generation_method):
    """Helper to make sure that the formulas are set in the Arch instance.

    If the formula is already set, return.
    Else if there is a delayed formula load from a file, load right now.
    Else, generate the formulas.
    """
    if formula_content != None:
      # the formulas are already there
      return
    elif formula_delayed_file != None:
      # the load is delayed: now is the time to load
      formula_load_method(formula_delayed_file, delay_loading=False)     
    else:
      # generate
      formula_generation_method()
  
  def __ensure_kextract_summary(self):
    """Helper to make sure that the kextract summary info is set in the Arch instance.

    There are three pieces of information extracted from kextract (other than
    any type of kclause formulas), which are:
      - kconfig types
      - kconfig visible
      - kconfig has def nonbool
    """
    if self.__kconfig_types is not None and self.__kconfig_visible is not None and \
       self.__kconfig_has_def_nonbool is not None and self.__kconfig_bool_tristate_options is not None:
      # the formulas are already there
      return

    # ensure kextract formulas
    self.get_kextract()

    # generate kextract_summary
    self.__generate_kextract_summary()

  def __generate_kextract_summary(self):
    """Generate and set kextract summary (kconfig_types, kconfig_visible,
    kconfig_has_def_nonbool, and kconfig_bool_tristate_options) from kextract.
    """
    kextract = self.get_kextract() # ensure kextract
    if kextract == None:
      return (None, None, None)
    
    kconfig_types = {}
    kconfig_visible = set()
    kconfig_has_def_nonbool = set()
    kconfig_bool_tristate_options = set()
    for kconfig_line in kextract.splitlines():
      kconfig_line = kconfig_line.split(" ")
      # see docs/kextract_format.md for more info
      if kconfig_line[0] == "config":
        kconfig_types[kconfig_line[1]] = kconfig_line[2]
        if kconfig_line[2] in {'bool', 'tristate'}:
          kconfig_bool_tristate_options.add(kconfig_line[1])
      if kconfig_line[0] == "prompt":
        kconfig_visible.add(kconfig_line[1])
      if kconfig_line[0] == "def_nonbool":
        kconfig_has_def_nonbool.add(kconfig_line[1])
    
    self.__kconfig_bool_tristate_options = kconfig_bool_tristate_options
    self.__kconfig_types = kconfig_types
    self.__kconfig_visible = kconfig_visible
    self.__kconfig_has_def_nonbool = kconfig_has_def_nonbool

  def get_bool_tristate_options(self):
    """Get the set of all bool or tristate configuration options.
    """
    self.__ensure_kextract_summary()
    return self.__kconfig_bool_tristate_options

  def get_kconfig_types(self):
    """Get the mapping of kconfig symbols to their types extracted from kextract.
    """
    self.__ensure_kextract_summary()
    return self.__kconfig_types
  
  def get_kconfig_visible(self):
    """Get the set of visible kconfig symbols extracted from kextract.
    """
    self.__ensure_kextract_summary()
    return self.__kconfig_visible

  def get_kconfig_has_def_nonbool(self):
    """Get the set of kconfig symbols that has default nonbool extracted from kextract.
    """
    self.__ensure_kextract_summary()
    return self.__kconfig_has_def_nonbool

  def get_kextract(self):
    """Get kextract.

    If kextract is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kextract using kextract tool on linux kernel source. If
    the linux kernel source is not set, MissingLinuxSource() exception is raised.

    This method can also be used to prefetch kextract.
    """
    self.__ensure_formulas(self.__kextract, self.__kextract_file_delayed_load, self.load_kextract, self.generate_kextract)
    assert self.__kextract != None
    return self.__kextract

  def get_kclause_composite(self):
    """Get composite kclause formulas.

    A single smt2 string is returned.

    When compared to kclause formulas, which is a mapping from symbols to clauses,
    composite kclause formulas is the whole batch of kclause formulas in a 
    single list. Most applications would need composite kclause formulas.

    If kclause formulas is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kclause using kclause tool. Kclause tool uses kextract as
    input. Therefore, get_kextract() must succeed to have this method succeed.

    This method can also be used to prefetch the formulas.
    """
    delayed_file = self.__kclause_file_delayed_load if self.__kclause_file_delayed_load_is_composite else None
    
    def load_method(filepath, delay_loading):
      return self.load_kclause(filepath, is_composite=True, delay_loading=delay_loading)

    
    self.__ensure_formulas(self.__composite_kclause_formulas, delayed_file, load_method, self.__generate_composite_kclause_formulas)
    
    assert self.__composite_kclause_formulas != None
    return self.__composite_kclause_formulas

  def get_kclause(self):
    """Get kclause formulas.

    A mapping of symbol names in string to clauses in smt2 string is returned.

    If kclause formulas is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kclause using kclause tool. Kclause tool uses kextract as
    input. Therefore, get_kextract() must succeed to have this method succeed.

    This method can also be used to prefetch the formulas.
    """
    # workaround for additional parameter: is_kclause_composite
    def load_method(filepath, delay_loading):
      return self.load_kclause(filepath, is_composite=self.__kclause_file_delayed_load_is_composite, delay_loading=delay_loading)

    self.__ensure_formulas(self.__kclause_formulas, self.__kclause_file_delayed_load, load_method, self.generate_kclause)
    assert self.__kclause_formulas != None
    return self.__kclause_formulas

  def get_dir_dep(self):
    """Get kclause direct dependency formulas.

    A mapping of symbol names in string to direct dependency clauses in smt2
    string is returned.

    If kclause direct dependency formulas is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kclause direct dependency using kclause tool. Kclause tool
    uses kextract as input. Therefore, get_kextract() must succeed to have
    this method succeed.

    This method can also be used to prefetch the formulas.
    """
    self.__ensure_formulas(self.__dir_dep_formulas, self.__dir_dep_file_delayed_load, self.load_dir_dep, self.generate_dir_dep)
    assert self.__dir_dep_formulas != None
    return self.__dir_dep_formulas

  def get_rev_dep(self):
    """Get kclause reverse dependency formulas.

    A mapping of symbol names in string to reverse dependency clauses in smt2
    string is returned.

    If kclause reverse dependency formulas is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kclause reverse dependency using kclause tool. Kclause tool
    uses kextract as input. Therefore, get_kextract() must succeed to have
    this method succeed.

    This method can also be used to prefetch the formulas.
    """
    self.__ensure_formulas(self.__rev_dep_formulas, self.__rev_dep_file_delayed_load, self.load_rev_dep, self.generate_rev_dep)
    assert self.__rev_dep_formulas != None
    return self.__rev_dep_formulas

  def get_selects(self):
    """Get kclause selects formulas.

    A mapping of selected symbol names in string to a list is returned. Each
    element in the string is a mapping from selecter symbol names in string
    to visibility conditions in smt2 string.

    If kclause selects formulas is already set, return.
    Else if there is a delayed load from a file, load right now, and return.
    Else, generate kclause selects formulas using kclause tool. Kclause tool
    uses kextract as input. Therefore, get_kextract() must succeed to have
    this method succeed.

    This method can also be used to prefetch the formulas.
    """
    self.__ensure_formulas(self.__selects, self.__selects_file_delayed_load, self.load_selects, self.generate_selects)
    assert self.__selects != None
    return self.__selects

  def __reset_kextract_summary(self):
    self.__kconfig_bool_tristate_options=None
    self.__kconfig_types=None
    self.__kconfig_visible=None
    self.__kconfig_has_def_nonbool=None

  def set_kextract_version(self, version: str):
    """Set kextract module version.
    
    If set to None, the latest possible version suitable for the kernel version is automatically detected and used.
    """
    self.__kextract_version=version
  
  def __detect_kextract_version(self):
    """Detect the latest possible kextract module version for the Linux kernel version.
    """
    command=["make", "kernelversion"]
    stdout, _, ret_code = self.__run_command(command, capture_stderr=False, cwd=self.__linux_ksrc)
    
    # If can't detect the kernelversion, use latest kextract module
    if ret_code != 0:
      return "latest"
    
    kernel_version = stdout.decode("ascii").strip()
    major, minor, patch = kernel_version.split('.')
    major, minor = int(major), int(minor)

    return kmax.kextractcommon.pick_version(kernel_version)

  def generate_kextract(self):
    """Generate kextract using kextract tool, set, and return.

    This will overwrite any existing kextract formulas, and reset any kextract
    summary generated. However, kclause formulas will stay as is. To overwrite
    existing kclause formulas using the newly generated kextract, use generate
    methods.
    """
    if not self.__linux_ksrc:
      self.__logger.error("Can't generate kextract: missing linux kernel source.")
      raise Arch.MissingLinuxSource()

    if not self.__check_arch_name():
      self.__logger.error("Can't generate kextract: unknown architecture name.")
      raise Arch.UnknownArchitectureName(self.name)

    if not self.__kextract_version:
      self.__logger.debug("Automatically detecting the kextract module version suitable for the kernel.")
      kextract_version=self.__detect_kextract_version()
      self.__logger.debug("Using kextract module version: %s" % kextract_version)
    elif self.__kextract_version not in list(kmax.kextractcommon.module_versions.keys()):
      raise Arch.UnknownKextractVersion(self.__kextract_version)
    else:
      kextract_version=self.__kextract_version

    # reset kextract summary
    self.__reset_kextract_summary()
  
    # TODO: reset the other formulas since generating kextract should do so?
    # For now, ignore this and assume the user will be careful of the state
    # of the arch instance. 

    # TODO: let kextract tool to produce results to stdout, instead of only operating with files

    # currently, kextract can only output to a file. to keep generation and
    # dumping to file apart from each other, use a temporary file, read the
    # content, then remove. the user can save the content using dump_kextract()
    # TODO: use OS provided tmp files instead
    kextract_file = self.__get_tmp_file("kextract_", ".tmp")
    kextract_file=os.path.realpath(kextract_file)
    os.makedirs(os.path.dirname(kextract_file), exist_ok=True)
    
    # TODO: Use the python package instead of running the executable?
    # Try multiple kextract module versions unless version is explicitly set
    if not self.__kextract_version:
      # Give the priority to the detected version
      kextract_module_versions=[a for a in kmax.kextractcommon.module_versions if a != kextract_version] + [kextract_version]
    else:
      # Version is explicity set
      kextract_module_versions=[kextract_version]

    assert kextract_module_versions

    missing_kconfig_files = []
    def get_missing_kconfig_file_messages(make_stderr: str) -> list:
      """Example: drivers/media/platform/Kconfig:69: can't open file "drivers/media/platform/am437x/Kconfig"

      For instance, the Linux kernel version at the commit 012e3ca3cb4d7f
      has this issue.
      """
      ret = []
      for l in make_stderr.split('\n'): 
        l = l.strip()
        found = re.findall(r"^.*: can't open file \".*$", l)
        if found:
          ret.extend(found)
      return ret

    while kextract_module_versions:
      kextract_version=kextract_module_versions.pop() # pop the next version to try
      command = [ "kextractlinux", self.name, kextract_file, "--module-version", kextract_version]
      self.__logger.debug("Running kextract tool to generate kextract (module version: %s)." % kextract_version)
      _, ke_stderr_bytes, ret_code = self.__run_command(command, cwd=self.__linux_ksrc)
      if ret_code == 0:
        break
      if ret_code == 2:
        self.__logger.error("Architecture directory for \"%s\" is not available, so kextract not generated." % (self.name))
        raise Arch.ArchitectureUnavailableError()
      else:
        self.__logger.debug("Kextract failed (module version: %s, return code: %d)." % (kextract_version, ret_code))
        # Check for missing Kconfig files.  Only report missing Kconfig
        # files after all kextract versions are tried to give all versions
        # a chance.
        ke_stderr_str = str(ke_stderr_bytes.decode('utf-8'))
        missing_files = get_missing_kconfig_file_messages(ke_stderr_str)
        if missing_files:
          self.__logger.debug("Detected missing Kconfig files: %s" % missing_files)
          missing_kconfig_files = missing_files
        if kextract_module_versions:
          self.__logger.debug("Trying next latest kextract module version: %s" % kextract_module_versions[-1])
        os.remove(kextract_file)
    

    if ret_code != 0:
      assert not kextract_module_versions
      if missing_kconfig_files: #< Known reason: Kconfig files were missing
        raise Arch.CantOpenKconfigFiles(missing_kconfig_files)
      else: #< Unknown reason, raise a generic assertion.
        self.__logger.error("Error running kextract: kextract file couldn't be generated.")
        raise Arch.KextractFormulaGenerationError()
    else:
      self.__logger.debug("kextract was successfully generated.")

    # Load after generation
    with open(kextract_file, "r") as f:
      self.__kextract = f.read()

    # Remove the temporary file
    os.remove(kextract_file)

    if self.__kextract_file_delayed_dump != None:
      self.dump_kextract(self.__kextract_file_delayed_dump)
      self.__kextract_file_delayed_dump = None
    
    return self.__kextract

  def dump_kextract(self, kextract_file):
    """Dump kextract to file.

    Arguments:
    kextract_file -- Path to the file to dump kextract.
    """
    self.__logger.debug("Dumping kextract to file '%s'" % kextract_file)
    self.__dump_str_to_file(kextract_file, self.get_kextract(), binary=False)

  def load_kextract(self, kextract_file, delay_loading=False):
    """Load kextract from file.

    Arguments:
    kextract_file -- Path to the kextract file.
    delay_loading -- Set to delay loading the formulas until needed.
    """
    if not os.path.isfile(kextract_file):
      raise Arch.KextractFormulaFileNotFound(kextract_file)

    # reset kextract summary
    self.__reset_kextract_summary()

    if delay_loading:
      self.__kextract_file_delayed_load=kextract_file
    else:
      self.__logger.debug("Loading kextract from file '%s'" % kextract_file)
      self.__kextract_file_delayed_load=None
      with open(kextract_file, "r") as f:
        self.__kextract = f.read()
      self.__logger.debug("Successfully loaded the kextract.")
      # TODO: verify if the content is right  

  def dump_kclause(self, kclause_file, dump_composite=False):
    """Dump kclause formulas to file.

    Arguments:
    kclause_file -- Path to the file to dump kclause formulas.
    """
    self.__logger.debug("Dumping kclause formulas to file '%s'" % kclause_file)
    if dump_composite:
      self.__pickle_dump_to_file(kclause_file, self.get_kclause_composite())
    else:
      self.__pickle_dump_to_file(kclause_file, self.get_kclause())
  
  def __generate_composite_kclause_formulas(self):
    """Assuming self.kclause_formula is not composite, transform self.__kclause_formulas
    into composite format and fill self.__composite_kclause_formulas with that.

    The composite formulas is what is returned by get_kclause() since it is
    really what is used.
    """
    self.__composite_kclause_formulas = None

    self.get_kclause() # ensure kclause formulas
    assert self.__kclause_formulas != None

    # get_kclause might already fill the field
    if self.__composite_kclause_formulas != None:
      return self.__composite_kclause_formulas
    
    self.__logger.debug("Transforming kclause formulas into composite format..")
    kclause_constraints = {}
    for var in self.__kclause_formulas:
      kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in self.__kclause_formulas[var] ]

    constraints = []
    for var in kclause_constraints:
      for z3_clause in kclause_constraints[var]:
        constraints.extend(z3_clause)
    
    self.__logger.debug("Transforming kclause formulas into composite format succeeded.")

    # keep in smt2 string format for consistency with the other formulas
    s = z3.Solver()
    s.add(constraints)
    smt2_str = s.to_smt2()
    
    self.__composite_kclause_formulas = smt2_str

  def load_kclause(self, kclause_file, is_composite, delay_loading=False):
    """Load kclause formulas from file.

    Arguments:
    kclause_file -- Path to the kclause formulas file.
    is_composite -- Set if the kclause formulas file is composite.
    delay_loading -- Set to delay loading the formulas until needed.
    """
    if not os.path.isfile(kclause_file):
      raise Arch.KclauseFormulaFileNotFound(kclause_file)

    if delay_loading:
      self.__kclause_file_delayed_load=kclause_file
      self.__kclause_file_delayed_load_is_composite=is_composite
    else:
      self.__kclause_file_delayed_load=None
      self.__kclause_file_delayed_load_is_composite=None
      if is_composite:
        self.__logger.debug("Loading composite kclause formulas from file '%s'" % kclause_file)
        self.__kclause_formulas = None
        with open(kclause_file, "r") as f:
          self.__composite_kclause_formulas = f.read()
        self.__logger.debug("Successfully loaded the composite kclause formulas.")
      else:
        self.__logger.debug("Loading kclause formulas from file '%s'" % kclause_file)
        self.__kclause_formulas = Arch.__pickle_bin_dict(kclause_file)
        self.__generate_composite_kclause_formulas()
        self.__logger.debug("Successfully loaded the kclause formulas.")
      # TODO: verify content

  # Can use the kextract_file, or the kextract loaded in the architecture
  def generate_kclause(self):
    """Generate kclause formulas, set, and return.

    Kextract is needed for generating kclause formulas. To obtain kextract,
    get_kextract() is used, which tries to obtain kextract in one of few possible
    ways. Refer to its documentation for further reference.
    """
    assert self.__check_arch_name()
    if self.__kextract == None: self.__kextract = self.get_kextract()
    assert self.__kextract != None

    command = ["kclause", "--remove-orphaned-nonvisible" ]
    self.__logger.debug("Running kclause tool to generate kclause formulas.")
    proc_stdout, _, ret_code = self.__run_command(command, self.__kextract.encode(), capture_stderr=False)
    
    if ret_code != 0:
      self.__logger.error("Error running kclause: return code %d" % (ret_code))
      raise Arch.KclauseFormulaGenerationError()
    else:
      self.__logger.debug("kclause formulas was successfully generated.")

    self.__kclause_formulas=pickle.loads(proc_stdout)

    if self.__kclause_file_delayed_dump != None:
      self.dump_kclause(self.__kclause_file_delayed_dump)
      self.__kclause_file_delayed_dump = None
    
    self.__generate_composite_kclause_formulas()
    
    return self.__kclause_formulas

  def load_dir_dep(self, dir_dep_file, delay_loading=False):
    """Load kclause direct dependency formulas from file.

    Arguments:
    dir_dep_file -- Path to the kclause direct dependency formulas file.
    delay_loading -- Set to delay loading the formulas until needed.
    """
    if not os.path.isfile(dir_dep_file):
      raise Arch.DirDepFormulaFileNotFound(dir_dep_file)

    if delay_loading:
      self.__dir_dep_file_delayed_load=dir_dep_file
    else:
      self.__logger.debug("Loading kclause direct dependency formulas from file '%s'" % dir_dep_file)
      self.__dir_dep_file_delayed_load=None
      self.__dir_dep_formulas = Arch.__pickle_bin_dict(dir_dep_file)
      self.__logger.debug("Successfully loaded the kclause direct dependency formulas.")
      # TODO: verify content
  
  def dump_dir_dep(self, dir_dep_file):
    """Dump kclause direct dependency formulas to file.

    Arguments:
    dir_dep_file -- Path to the file to dump kclause direct dependency formulas.
    """
    self.__logger.debug("Dumping kclause direct dependency formulas to file '%s'" % dir_dep_file)
    self.__pickle_dump_to_file(dir_dep_file, self.get_dir_dep())

  def generate_dir_dep(self):
    """Generate kclause direct dependency formulas, set, and return.

    Kextract is needed for generating kclause formulas. To obtain kextract,
    get_kextract() is used, which tries to obtain kextract in one of few possible
    ways. Refer to its documentation for further reference.
    """
    assert self.__check_arch_name()
    if self.__kextract == None: self.__kextract = self.get_kextract()
    assert self.__kextract != None

    command = ["kclause", "--normal-dependencies-only" ]
    self.__logger.debug("Running kclause tool to generate kclause direct dependency formulas.")
    proc_stdout, _, ret_code = self.__run_command(command, self.__kextract.encode(), capture_stderr=False)
    
    if ret_code != 0:
      self.__logger.error("Error running kclause: return code %d" % (ret_code))
      raise Arch.KclauseDirDepFormulaGenerationError()
    else:
      self.__logger.debug("kclause direct dependency formulas was successfully generated.")

    self.__dir_dep_formulas = pickle.loads(proc_stdout)

    if self.__dir_dep_file_delayed_dump != None:
      self.dump_dir_dep(self.__dir_dep_file_delayed_dump)
      self.__dir_dep_file_delayed_dump = None
    
    return self.__dir_dep_formulas

  def load_rev_dep(self, rev_dep_file, delay_loading=False):
    """Load kclause reverse dependency formulas from file.

    Arguments:
    rev_dep_file -- Path to the kclause reverse dependency formulas file.
    delay_loading -- Set to delay loading the formulas until needed.
    """
    if not os.path.isfile(rev_dep_file):
      raise Arch.RevDepFormulaFileNotFound(rev_dep_file)

    if delay_loading:
      self.__rev_dep_file_delayed_load=rev_dep_file
    else:
      self.__logger.debug("Loading kclause reverse dependency formulas from file '%s'" % rev_dep_file)
      self.__rev_dep_file_delayed_load=None
      self.__rev_dep_formulas = Arch.__pickle_bin_dict(rev_dep_file)
      self.__logger.debug("Successfully loaded the kclause reverse dependency formulas.")
      # TODO: verify content
  
  def dump_rev_dep(self, rev_dep_file):
    """Dump kclause reverse dependency formulas to file.

    Arguments:
    rev_dep_file -- Path to the file to dump kclause reverse dependency formulas.
    """
    self.__logger.debug("Dumping kclause reverse dependency formulas to file '%s'" % rev_dep_file)
    self.__pickle_dump_to_file(rev_dep_file, self.get_rev_dep())

  def generate_rev_dep(self):
    """Generate kclause reverse dependency formulas, set, and return.

    Kextract is needed for generating kclause formulas. To obtain kextract,
    get_kextract() is used, which tries to obtain kextract in one of few possible
    ways. Refer to its documentation for further reference.
    """
    assert self.__check_arch_name()
    if self.__kextract == None: self.__kextract = self.get_kextract()
    assert self.__kextract != None

    command = ["kclause", "--reverse-dependencies-only" ]
    self.__logger.debug("Running kclause tool to generate kclause reverse dependency formulas.")
    proc_stdout, _, ret_code = self.__run_command(command, self.__kextract.encode(), capture_stderr=False)
    
    if ret_code != 0:
      self.__logger.error("Error running kclause: return code %d" % (ret_code))
      raise Arch.KclauseRevDepFormulaGenerationError()
    else:
      self.__logger.debug("kclause reverse dependency formulas was successfully generated.")
    
    self.__rev_dep_formulas = pickle.loads(proc_stdout)

    if self.__rev_dep_file_delayed_dump != None:
      self.dump_rev_dep(self.__rev_dep_file_delayed_dump)
      self.__rev_dep_file_delayed_dump = None
    
    return self.__rev_dep_formulas
  
  def load_selects(self, selects_file, delay_loading=False):
    """Load kclause selects formulas from file.

    Arguments:
    selects_file -- Path to the kclause selects formulas file.
    delay_loading -- Set to delay loading the formulas until needed.
    """
    if not os.path.isfile(selects_file):
      raise Arch.SelectsFormulaFileNotFound(selects_file)

    if delay_loading:
      self.__selects_file_delayed_load=selects_file
    else:
      self.__logger.debug("Loading kclause selects formulas from file '%s'" % selects_file)
      self.__selects_file_delayed_load=None
      self.__selects = Arch.__pickle_bin_dict(selects_file)
      self.__logger.debug("Successfully loaded the kclause selects formulas.")
      # TODO: verify content
    
  def dump_selects(self, selects_file):
    """Dump kclause selects formulas to file.

    Arguments:
    selects_file -- Path to the file to dump kclause selects formulas.
    """
    self.__logger.debug("Dumping kclause selects formulas to file '%s'" % selects_file)
    self.__pickle_dump_to_file(selects_file, self.get_selects())

  def generate_selects(self):
    """Generate kclause selects formulas, set, and return.

    Kextract is needed for generating kclause formulas. To obtain kextract,
    get_kextract() is used, which tries to obtain kextract in one of few possible
    ways. Refer to its documentation for further reference.
    """
    assert self.__check_arch_name()
    if self.__kextract == None: self.__kextract = self.get_kextract()
    assert self.__kextract != None

    command = ["kclause", "--selects-only" ]
    self.__logger.debug("Running kclause tool to generate kclause selects formulas.")
    proc_stdout, _, ret_code = self.__run_command(command, self.__kextract.encode(), capture_stderr=False)
    
    if ret_code != 0:
      self.__logger.error("Error running kclause: return code %d" % (ret_code))
      raise Arch.KclauseSelectsFormulaGenerationError()
    else:
      self.__logger.debug("kclause selects formulas was successfully generated.")

    self.__selects = pickle.loads(proc_stdout)

    if self.__selects_file_delayed_dump != None:
      self.dump_selects(self.__selects_file_delayed_dump)
      self.__selects_file_delayed_dump = None
    
    return self.__selects
  
  def get_unmet_free_constraints(self, except_for=[]):
    """Get unmet free constraints as list[z3.Bool].

    Kclause direct dependency formulas are required for this. get_dir_dep()
    must succeed to have this method succeed.

    For a kconfig symbol, the unmet free constraint is computed as (C -> dir_dep_C).

    However, this is complete only when combined with kclause formulas.
    
    Arguments:
    except_for -- Don't include the unmet free constraints for this list of
    kconfig symbols. If a symbol can't be consumed, a warning message is produced
    on the logger.
    """

    assert type(except_for) is list

    # helper
    def flatten_z3_vector(z3_vector):
      if len(z3_vector) == 0:
        return z3.BoolVal("True")
      elif len(z3_vector) == 1:
        return z3_vector[0]
      else:
        assert len(z3_vector) <= 1

    # keep track of consumed except_fors to warn about not processed ones later
    except_for = set(except_for)
    consumed_except_for = set()

    # compile the constraints
    # to avoid unmet direct dependency for a symbol C, (C -> dir_dep_C) must hold true
    implication = lambda x, y: z3.Or(z3.Not(x), y)

    dir_deps = self.get_dir_dep()

    constraints = []
    for var in self.get_dir_dep():
      if var in except_for:
        consumed_except_for.add(var)
        continue

      c = implication(z3.Bool(var), flatten_z3_vector(z3.parse_smt2_string(dir_deps[var])))
      constraints.append(c)
    
    # warn for the unconsumed except_for symbols
    unconsumed_except_for = except_for.difference(consumed_except_for)
    for var in sorted(list(unconsumed_except_for)):
      self.__logger.warning("Couldn't find the symbol '%s' for which to allow unmet direct dependency." % var)
    
    return constraints

  #
  # Exceptions
  #
  class ArchException(Exception):
    """Arch related exceptions
    """
    pass

  # This should be common among Arch, Klocalizer, and so on.
  # A path to linux kernel source is supplied but not valid.
  class InvalidLinuxSource(ArchException):
    def __init__(self, linux_ksrc_dir):
      self.linux_ksrc_dir = linux_ksrc_dir
      self.message = "Invalid Linux kernel source at %s" % linux_ksrc_dir
      super().__init__(self.message)

  class MissingLinuxSource(ArchException):
    def __init__(self):
      self.message = "Missing Linux kernel source, required for the computation"
      super().__init__(self.message)

  class UnknownArchitectureName(ArchException):
    def __init__(self, arch_name):
      self.arch_name = arch_name
      self.message = "Unknown architecture name: %s" % arch_name
      super().__init__(self.message)

  class UnknownKextractVersion(ArchException):
    def __init__(self, kextract_version):
      self.kextract_version = kextract_version
      self.message = "Unknown kextract version: %s" % kextract_version
      super().__init__(self.message)

  class FormulaError(ArchException):
    pass

  class FormulaFileError(FormulaError):
    pass

  ### Formula file can't be found
  class FormulaFileNotFound(FormulaFileError, FileNotFoundError):
    """Exception raised for errors when a formula file can't be found in the
    specified path.

    Attributes:
      filepath -- the filepath where the formula file was expected to be.
      formula_type -- the type of the formula (e.g., kextract, kclause etc.).
    """

    def __init__(self, filepath, formula_type):
      self.filepath=filepath
      self.formula_type=formula_type
      self.message="%s formula file can't be found at %s" % (formula_type, filepath)
      super().__init__(self.message)

  #### Formula file can't be found: kextract
  class KextractFormulaFileNotFound(FormulaFileNotFound):
    def __init__(self, filepath):
      super().__init__(filepath=filepath, formula_type="kextract")

  #### Formula file can't be found: kclause
  class KclauseFormulaFileNotFound(FormulaFileNotFound):
    def __init__(self, filepath):
      super().__init__(filepath=filepath, formula_type="kclause")

  #### Formula file can't be found: direct dependency
  class DirDepFormulaFileNotFound(FormulaFileNotFound):
    def __init__(self, filepath):
      super().__init__(filepath=filepath, formula_type="direct dependency")

  #### Formula file can't be found: reverse dependency
  class RevDepFormulaFileNotFound(FormulaFileNotFound):
    def __init__(self, filepath):
      super().__init__(filepath=filepath, formula_type="reverse dependency")

  #### Formula file can't be found: selects
  class SelectsFormulaFileNotFound(FormulaFileNotFound):
    def __init__(self, filepath):
      super().__init__(filepath=filepath, formula_type="selects")

  ## Can't generate formula
  class FormulaGenerationError(ArchException):
    """Exception raised for errors when formulas can't be generated.

    Attributes:
      formula_type -- the type of the formula (e.g., kextract, kclause etc.).
    """
    def __init__(self, formula_type):
      self.formula_type=formula_type
      self.message="%s formulas couldn't be generated." % (formula_type)
      super().__init__(self.message)

  ### Can't generate formula: kextract
  class ArchitectureUnavailableError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kextract")

  ### Can't generate formula: kextract
  class KextractFormulaGenerationError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kextract")

  class CantOpenKconfigFiles(KextractFormulaGenerationError):
    def __init__(self, kextract_complaints):
      super().__init__()
      self.kextract_complaints = kextract_complaints
      self.message = "kextract formulas couldn't be generated: can't open Kconfig files: %s" % kextract_complaints

  ### Can't generate formula: kclause
  class KclauseFormulaGenerationError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kclause")

  ### Can't generate formula: kclause direct dependency
  class KclauseDirDepFormulaGenerationError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kclause direct dependency")

  ### Can't generate formula: kclause reverse dependency
  class KclauseRevDepFormulaGenerationError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kclause reverse dependency")

  ### Can't generate formula: kclause selects
  class KclauseSelectsFormulaGenerationError(FormulaGenerationError):
    def __init__(self):
      super().__init__(formula_type="kclause selects")
