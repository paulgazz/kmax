from .common import BasicLogger
from .vcommon import run, write_content_to_file, check_if_compiles
from kmax.arch import Arch
import os
import pathlib
from shutil import which
from kmax.klocalizer import Klocalizer
import subprocess
import shutil

class SuperC:
  class SuperC_Exception(Exception):
    pass
  class SuperC_ChecksFailed(SuperC_Exception):
    def __init__(self, reason):
      self.reason = reason
      super().__init__(self.reason)

  def __init__(self, superc_linux_script_path = None, logger = BasicLogger()):
    """Arguments:
    * superc_linux_script_path -- SuperC linux script, which is found at
    superc/scripts/superc_linux.sh, where superc/ is the top SuperC source
    directory. Searches "superc_linux.sh" in PATH by default.
    """
    self.logger = logger

    # Set SuperC linux script path
    if superc_linux_script_path:
      self.superc_linux_script_path = superc_linux_script_path
    else: #< Searches in PATH by default.
      self.superc_linux_script_path = "superc_linux.sh"
    assert self.superc_linux_script_path

    self.__check_superc() #< Check SuperC
  
  def __check_superc(self):
    """Check and whether SuperC can be used for getting sourceline presence
    conditions for Linux files.
    
    Returns on success.
    Raises SuperC_ChecksFailed exception on error.

    Followings checks are done:
    * java exists
    * java runs
    * SuperC runs
    * SuperC -sourcelinePC runs
    * SuperC linux script exists
    * SuperC linux script runs
    """
    def is_success(command_to_run: list):
      return 0 == run(command_to_run, capture_stdout=True, capture_stderr=True)[2]
    
    self.logger.debug("Starting SuperC checks.\n")

    #
    # Check java
    #
    if not which("java"):
      raise SuperC.SuperC_ChecksFailed("java could not be found")

    cmd = ["java", "--help"]
    if not is_success(cmd):
      raise SuperC.SuperC_ChecksFailed("Running java (\"%s\") failed" % " ".join(cmd))

    #
    # Check SuperC
    #
    cmd = ["java", "superc.SuperC"]
    if not is_success(cmd):
      raise SuperC.SuperC_ChecksFailed("Running SuperC (\"%s\") failed" % " ".join(cmd))

    cmd = ["java", "superc.SuperC", "-sourcelinePC", os.devnull, os.devnull]
    if not is_success(cmd):
      raise SuperC.SuperC_ChecksFailed("Running SuperC -sourcelinePC (\"%s\") failed" % " ".join(cmd))
    
    #
    # Check SuperC linux script
    #
    if not which(self.superc_linux_script_path):
      raise SuperC.SuperC_ChecksFailed(
        """SuperC linux script executable cannot be found: either set """
        """path to the script or have script in PATH.""")

    cmd = [self.superc_linux_script_path]
    if not is_success(cmd):
      raise SuperC.SuperC_ChecksFailed("Executing SuperC linux script (\"%s\") failed" % cmd)
    
    # None failed: checks passed
    self.logger.debug("SuperC checks passed.\n")
    return True

  @staticmethod
  def get_superc_basepath_for_file(srcfile: str, superc_formulas_dir: str) -> str:
    """The basepath, which is concat with extensions to create any kind
    of files specific to the srcfile.
    """
    return os.path.join(superc_formulas_dir, srcfile)
  
  @staticmethod
  def get_superc_logs_dir_for_file(srcfile: str, superc_formulas_dir: str) -> str:
    """The directory, which is concat with log filenames to create any kind
    of logs files specific to the given srcfile.
    """
    return os.path.join(superc_formulas_dir, "%s_superc_logs/" % srcfile)

  @staticmethod
  def get_superc_configs_for_file(srcfile: str, superc_formulas_dir: str) -> str:
    """Compute and return the path to the SuperC config file for the given
    source file.
    """
    return os.path.join(superc_formulas_dir, "%s.configs_superc" % srcfile)

  @staticmethod
  def get_superc_formulas_dir(formulas: str, arch_name: str) -> str:
    """Given formulas directory and the architecture name, return the
    path to SuperC formulas directory.

    For example, formulas=".kmax/v5.13" and arch_name="x86_64" returns
    ".kmax/v5.13/superc/x86_64/configs/".
    
    While this is a simple string concatenation, any changes to directory
    structure will be maintained through this method.
    """
    assert arch_name
    return os.path.join(formulas, "superc", arch_name, "configs")
  
  @staticmethod
  def get_superc_pc_path(srcfile: str, superc_formulas_dir: str) -> str:
    """Compute and return the path to the presence conditions file for the
    given source file. Notice that we have no (efficient) way of checking
    whether the given presence conditions file is up-to-date. Therefore,
    this file is always recomputed/replaced as needed, and should be used
    for diagnostic purposes only.

    Otherwise, the path structure is maintained here.
    """
    return os.path.join(superc_formulas_dir, "%s.pc" % srcfile)
  
  @staticmethod
  def get_superc_header_path(superc_formulas_dir: str) -> str:
    """Get the path to the SuperC header file.
    """
    return os.path.join(superc_formulas_dir, "config_options.h")
  
  @staticmethod
  def get_superc_header_content(config_options: list):
    """Given a list of config options, create and return the header
    content to handle IS_ENABLED macro for SuperC.
    TODO: document more
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

  def get_pc(self,
    srcfile_path: str, arch: Arch, linux_ksrc: str,
    superc_formulas_dir: str, superc_timeout_sec: int,
    logger) -> Klocalizer.ConditionalBlock:
    """
    Compute the presence conditions (pc) using SuperC, and return it as a
    ConditionalBlock instance.

    Arguments:
    * srcfile_path -- Path to the source file to compute the pc for.
    Relative to the top Linux source directory.
    * arch -- Target architecture as an instance of kmax.Arch.
    * linux_ksrc -- Top Linux source directory.
    * superc_formulas_dir -- Path to the SuperC formulas directory. To use
    the cache dir structure, get it using SuperC.get_superc_formulas_dir().
    * superc_timeout_sec -- Timeout amount for running SuperC in seconds.
    * logger -- Logger that implements common.VoidLogger interface.
    
    Returns:
    * On success: A ConditionalBlock instance, which is a dummy root that
    encapsulates the conditional blocks in the source file. The root has
    special start/end line values (0 and line_count + 1).
    * On error: None. Check the log messages for info. For advanced
    diagnostics, check the diagnostic files created in the SuperC formulas
    directory.

    Creates the following files for diagnostics (for full path, prefix each
    with "superc/formulas/dir///source/file/path"):
    * Always:
       * PREFIX.superc_sourcelinepc_cmd: SuperC command.
    * On completion without timeout:
       * PREFIX.superc_sourcelinepc_exit_code: SuperC exit code.
       * PREFIX.superc_sourcelinepc_out: SuperC stdout.
       * PREFIX.superc_sourcelinepc_err: SuperC stderr.
       * PREFIX.superc_sourcelinepc_time_elapsed: SuperC time elapsed in sec.
    * On time out:
       * PREFIX.superc_sourcelinepc_timed_out: Timeout duration in sec.

    Notes:
    * SuperC config files must exist for the source file in the SuperC
    formulas directory. Otherwise, it is error (returns None).
    * Retrieves the config options header file (or creates it at if does
    not exist) from the path produced by SuperC.get_superc_header_path().
    * We have no (efficient) way of knowing whether an existing pc file
    is up-to-date. Therefore, we don't keep a cache, and always replace
    the pc file that may exists in the formulas directory, and keep the old
    one with .old suffix. This file must be used for diagnostic purposes
    only.
    * "include/generated/autoconf.h" is cleared in the Linux source, and
    not restored.
    """
    assert os.path.isfile(os.path.join(linux_ksrc, srcfile_path))
    # Check that configs exist
    configs_file = self.get_superc_configs_for_file(srcfile_path, superc_formulas_dir)
    if not os.path.isfile(configs_file):
      logger.error("Cannot find SuperC configs file at \"%s\"." % configs_file)
      return None #< Error

    assert os.path.isfile(configs_file)
    logs_dir = SuperC.get_superc_logs_dir_for_file(srcfile_path, superc_formulas_dir)
    def logpath(f: str):
      return os.path.join(logs_dir, f)
    pathlib.Path(logs_dir).mkdir(parents=True, exist_ok=True)

    #
    # Clear autoconf.h
    #
    logger.debug("Clearing autoconf.h.\n")
    autoconf_path = os.path.join(linux_ksrc, "include/generated/autoconf.h")
    with open(autoconf_path, "w") as f:
      pass #< Remove the content but keep the file
    assert os.path.isfile(autoconf_path)
    with open(autoconf_path, "r") as f:
      assert not f.readlines() #< Verify that file is empty.

    #
    # Retrieve or create header file to handle IS_ENABLED() with SuperC
    #
    options_header_file = SuperC.get_superc_header_path(linux_ksrc)
    if os.path.isfile(options_header_file):
      logger.debug("Options header file for handling IS_ENABLED macro is found at \"%s\"\n" % options_header_file)
    else:
      logger.debug("Computing options header file content to handle IS_ENABLED macro.\n")
      config_options = arch.get_bool_tristate_options()
      header_content = SuperC.get_superc_header_content(config_options)
      assert header_content
      logger.debug("Writing the options header file to \"%s\".\n" % options_header_file)
      with open(options_header_file, 'w') as f:
        f.write(header_content)
      assert os.path.isfile(options_header_file)

    #
    # SuperC sourcelinePC
    #
    pc_file_path = SuperC.get_superc_pc_path(srcfile_path, superc_formulas_dir)
    logger.debug("Presence conditions file will be created at \"%s\".\n" % pc_file_path)

    # If a pc file already exists, rename it to have .old extension
    if os.path.isfile(pc_file_path):
      old_pc_file_path = pc_file_path + ".old"
      logger.debug("Moving the existing presence conditions file to \"%s\".\n" % old_pc_file_path)
      assert pathlib.Path(pc_file_path).rename(old_pc_file_path)
      assert not os.path.isfile(pc_file_path)
      assert os.path.isfile(old_pc_file_path)
    
    # Prepare the SuperC command
    superc_flags = "-sourcelinePC %s" % pc_file_path
    superc_flags += " -include %s" % options_header_file
    # TODO: restrict to the list of config options instead of given prefix
    restrict_flag = " -restrictConfigToPrefix CONFIG_ "
    superc_flags += restrict_flag
    superc_sourcelinepc_cmd = [self.superc_linux_script_path, "-S%s" % superc_flags, "-L%s" % superc_formulas_dir, srcfile_path]
    superc_sourcelinepc_cmd_str = " ".join(superc_sourcelinepc_cmd)
    logger.debug("SuperC command: \"%s\"\n" % " ".join(superc_sourcelinepc_cmd))
    write_content_to_file(logpath("superc_sourcelinepc_cmd"), str(superc_sourcelinepc_cmd_str) + '\n')

    # Run SuperC
    try:
      logger.debug("Running SuperC sourcelinePC.\n")
      out, err, ret, time_elapsed = run(superc_sourcelinepc_cmd, cwd=linux_ksrc, timeout=superc_timeout_sec)
      logger.debug("Finished running SuperC sourcelinePC.\n")

      # Write diagnostic information
      write_content_to_file(logpath("superc_sourcelinepc_exit_code"), str(ret) + '\n')
      write_content_to_file(logpath("superc_sourcelinepc_out"), str(out.decode('UTF-8')) + '\n')
      write_content_to_file(logpath("superc_sourcelinepc_err"), str(err.decode('UTF-8')) + '\n')
      write_content_to_file(logpath("superc_sourcelinepc_time_elapsed"), str(time_elapsed) + '\n')
      logger.debug("SuperC config creation diagnostic info was written to files.\n")

      # Did SuperC create a presence conditions file?
      if not os.path.isfile(pc_file_path):
        logger.debug("SuperC failed to create presence conditions file at \"%s\".\n" % pc_file_path)
        return None #< Error
      
      # Read the presence conditions file
      with open(pc_file_path, 'r') as f:
        superc_pcfile_content = f.read()
      
      # If file is empty, error
      if not superc_pcfile_content:
        logger.debug("Empty SuperC presence conditions file at \"%s\".\n")
        return None #< Error
      
      # Parse the ConditionalBlock instance and return
      from ast import literal_eval
      pc = Klocalizer.ConditionalBlock._ConditionalBlock__parse_cb(literal_eval(superc_pcfile_content))
      assert pc
      return pc
    except subprocess.TimeoutExpired: #< SuperC timed out
      logger.debug("Timeout expired for SuperC, duration(sec): %.2f\n" % superc_timeout_sec)

      # Write diagnostic information
      write_content_to_file(logpath("superc_sourcelinepc_timed_out"), str(superc_timeout_sec) + '\n')

      return None #< Error
    
    assert False #< Unreachable

  def create_superc_config_on_built_unit(self,
    srcfile_path: str, output_superc_configs_dir_path: str,
    linux_ksrc: str, arch_name: str, cross_compiler: str) -> list:
    """Create SuperC configs files for the given source file where the unit
    is already built and building configuration is in the Linux source.

    This method only runs the SuperC linux script for creating the SuperC
    configuration files, and assumes the Linux source is already ready
    for this operation. Here are the requirements:
    * A compiled binary for the source file must exist in the same
    directory as the source file.
    * The linux configuration file that compiled the source file must exist
    at linux_ksrc/.config.

    The method Klocalizer.localize_config() can help setting up the Linux
    source before running this method. Alternatively, use
    SuperC.create_linux_superc_configs_from_scratch() that handles both the
    setup and the SuperC configuration creation.

    Arguments:
    * srcfile_path -- A linux source file with '.c' extension. It must be
    already compiled, i.e., corresponding binary with '.o' extension must
    exist. Relative to linux_ksrc.
    * output_superc_configs_dir_path -- Output SuperC configs directory
    path. Convention is to use SuperC.get_superc_configs_dir() to obtain
    this. Configs are created as src/file/path.configs_{all,superc}. Config
    must not already exist.
    * linux_ksrc -- Path to the top Linux source directory.
    * arch_name -- Architecture name, e.g., "x86_64".
    * cross_compiler -- Executable cross_compiler, e.g., "make.cross".

    Returns a tuple of 5 values:
    * bool: Whether SuperC config files were successfully created.
    * int : SuperC linux script return code.
    * str : SuperC linux script stdout.
    * str : SuperC linux script stderr.
    * int : Time elapsed (sec) to run SuperC linux script.
    """
    #
    # Check arguments
    #
    assert srcfile_path
    assert srcfile_path.endswith(".c")
    assert os.path.isfile(os.path.join(linux_ksrc, srcfile_path))
    assert os.path.isdir(output_superc_configs_dir_path)
    assert os.path.isdir(linux_ksrc)
    assert arch_name
    assert isinstance(arch_name, str)
    assert which(cross_compiler)
    # The linux configuration file that compiled the source file must exist
    # at linux_ksrc/.config
    assert os.path.isfile(os.path.join(linux_ksrc, ".config"))
    superc_config_path = os.path.join(output_superc_configs_dir_path, "%s.configs_superc" % srcfile_path)
    assert not os.path.isfile(superc_config_path) #< SuperC config does not already exist.

    # Check that unit is compiled
    unit_path = "%s.o" % srcfile_path[:-len('.c')]
    assert os.path.isfile(os.path.join(linux_ksrc, unit_path))

    # Create the SuperC configs.
    self.logger.debug("Creating SuperC configs for \"%s\"\n" % srcfile_path)
    # use superc_linux_script
    # /usr/bin/time bash $superc_linux_script -S"$superc_args" -w -L configs/ ${source_file} < /dev/null
    config_gen_cmd = [self.superc_linux_script_path, "-w",
      "-x", cross_compiler, "-a", arch_name,
      "-L", output_superc_configs_dir_path, srcfile_path]
    self.logger.debug("SuperC config generation command: \"%s\"\n" % " ".join(config_gen_cmd))
    out, err, ret, time_elapsed = run(config_gen_cmd, cwd=linux_ksrc)
    self.logger.debug("TIME: Time elapsed(sec) for SuperC config generation: %.2f\n" % time_elapsed)
    config_created = os.path.isfile(superc_config_path)
    if config_created:
      self.logger.debug("SuperC configs creation was successful for \"%s\"\n" % srcfile_path)
    else:
      self.logger.debug("Failed to create SuperC configs for \"%s\"\n" % srcfile_path)

    return config_created, ret, out.decode('UTF-8'), err.decode('UTF-8'), time_elapsed

  def ensure_superc_config(self,
    srcfile: str, output_superc_configs_dir_path: str, linux_ksrc: str,
    arch: Arch, cross_compiler, build_targets, compile_jobs, build_timeout,
    logger):
    """
    Ensure that SuperC configs exist for the input sourcefile.

    First, check if it already exists.  Otherwise, attempt to create it by
    following the below steps:
    * Localize a .config file that builds the unit,
    * Compile the unit,
    * Create SuperC configuration for the unit.

    If the config is found, or otherwise successfully created, returns True.
    Otherwise, returns False.
    """
    assert os.path.exists(os.path.join(linux_ksrc, srcfile))
    assert srcfile.endswith('.c')
    unit = srcfile[:-len('.c')] + '.o'

    logs_dir = SuperC.get_superc_logs_dir_for_file(srcfile, output_superc_configs_dir_path)
    def logpath(f: str):
      return os.path.join(logs_dir, f)
    pathlib.Path(logs_dir).mkdir(parents=True, exist_ok=True)
    superc_config_file = SuperC.get_superc_configs_for_file(srcfile, output_superc_configs_dir_path)
    config_exists = os.path.isfile(superc_config_file)
    if config_exists:
      # All have their SuperC configuration files.
      logger.debug("SuperC config exists for \"%s\".\n" % srcfile)
      return True
    else:
      logger.debug("Creating SuperC config file for \"%s\".\n" % srcfile)

      #
      # Localize a building configuration file.
      #
      output_config_file = logpath("kloc_localized_config")
      ret_status, ret_arch, ret_exception = Klocalizer.localize_config([unit], output_config_file, linux_ksrc, [arch], logger)
      # Write diagnostic info
      write_content_to_file(logpath("kloc_config_loc_status"), str(ret_status) + '\n')
      # no need to write ret_arch: there is already a single architecture
      write_content_to_file(logpath("kloc_config_loc_exception"), repr(ret_exception) + '\n')

      is_config_created = ret_status == Klocalizer.Ret_LocalizeConfig.SUCCESS
      if not is_config_created:
        logger.debug("Failed to localize a building Linux .config file.\n")
        return False
      else:
        assert os.path.isfile(output_config_file)
        logger.debug("A building Linux .config file was localized.\n")
      
      # Check if the unit compiles (also build them to prep for SuperC config creation)
      logger.debug("Attempting to build the unit.\n")
      ret = check_if_compiles([unit], output_config_file, arch.name, linux_ksrc,
        build_targets, cross_compiler, compile_jobs, build_timeout, True, logger)
      is_unit_compiled, make_timed_out, make_ret, make_out, make_err, time_elapsed = ret
      write_content_to_file(logpath("build_unit_status"), str(is_unit_compiled) + '\n')
      write_content_to_file(logpath("build_unit_make_timed_out"), str(make_timed_out) + '\n')
      write_content_to_file(logpath("build_unit_make_ret"), str(make_ret) + '\n')
      write_content_to_file(logpath("build_unit_make_out"), str(make_out) + '\n')
      write_content_to_file(logpath("build_unit_make_err"), str(make_err) + '\n')
      write_content_to_file(logpath("build_unit_time_elapsed"), str(time_elapsed) + '\n')
      if not is_unit_compiled:
        logger.debug("Unit could not be compiled.\n")
        return False
      else:
        logger.debug("Unit was successfully compiled.\n")

      # Create missing SuperC config files
      logger.debug("Creating the missing SuperC config file.\n")
      pathlib.Path(output_superc_configs_dir_path).mkdir(parents=True, exist_ok=True)
      assert shutil.copy(output_config_file, os.path.join(linux_ksrc, ".config"))
      ret = self.create_superc_config_on_built_unit(srcfile, output_superc_configs_dir_path, linux_ksrc, arch.name, cross_compiler)
      config_created, superc_ret, superc_out, superc_err, time_elapsed = ret
      write_content_to_file(logpath("superc_config_gen_status"), str(config_created) + '\n')
      write_content_to_file(logpath("superc_config_gen_ret"), str(superc_ret) + '\n')
      write_content_to_file(logpath("superc_config_gen_out"), str(superc_out) + '\n')
      write_content_to_file(logpath("superc_config_gen_err"), str(superc_err) + '\n')
      write_content_to_file(logpath("superc_config_gen_time_elapsed"), str(time_elapsed) + '\n')
      if not config_created:
        logger.error("SuperC configuration generation failed\n")
        return False

      # All succeeded.
      config_exists = os.path.isfile(superc_config_file)
      assert config_exists
      return True

###########################################################################

#
# Static analysis of C source files without SuperC
#
class SyntaxAnalysis:
    # taken from plocalizer/scripts/create_validation_conditions.py
    # TODO: merge this ConditionalBlock implementation with Klocalizer.ConditionalBlock
    class ConditionalBlock:
      """For capturing the start/end of preprocessor conditional blocks."""
      def __init__(self):
        self.start_line = -1
        self.end_line   = -1
        self.sub_block_groups = []
      
      def getdict(self):
        """Get a dictionary representation of the conditional block.
        
        May be used for debugging purposes."""
        r = {}
        r["StartLine"] = self.start_line
        r["EndLine"] = self.end_line
        r["Sub"] = []
        for s in self.sub_block_groups:
          r["Sub"].append([k.getdict() for k in s])
        return r

      def retrieve_deepest_block(self, line : int): # -> ConditionalBlock
        """Retrieve the end line of the deepest encapsulating conditional block
        for the given line.

        If there is no such block (line is out of range of the conditional
        blocks), return None.

        This should always return valid values when called with a valid line
        number on a conditional block tree with a dummy root for covering the
        overall file.
        """
        # TODO: Search for multiple lines can be optimized by doing a
        # traversal for all lines.
        assert line >= 0

        # For the given line, retrieve the end-of-block line that it belongs to.
        if self.start_line <= line < self.end_line:
          # Search within the sub blocks
          ret_from_sub_blocks = []
          for s in self.sub_block_groups:
            for k in s:
              r = k.retrieve_deepest_block(line)
              if r is not None:
                ret_from_sub_blocks.append(r)
          # It may belong to at most one sub block
          assert len(ret_from_sub_blocks) <= 1

          if ret_from_sub_blocks:
            # Belongs to a sub block
            return ret_from_sub_blocks[0]
          else:
            # Belongs to self, not in any nested sub block
            return self
        else:
          return None

    # taken from plocalizer/scripts/eval_common.py
    @staticmethod
    def get_tokens(s):
        """
        TODO: document
        takes a string, and returns a list of (token, line #)
        """
        buf = ""
        token_list = []
        line_num = 1
        prev_char = ''
        for c in s:
            # append the existing buffered token when we reach a space or tab
            if c == ' ' or c == '\t':
                if buf != "":
                    token_list.append((buf, line_num))
                    buf = ""
            else:
                # append the existing token if we reach a newline character, and increment the line number counter.
                if c == '\n':
                    if buf != "":
                        token_list.append((buf, line_num))
                        buf = ""
                    line_num += 1 # TODO: make this function return a list of tokens with their line numbers.
                # logic for special characters (comments, strings, and preprocessor directives)
                # appends the existing buffered token, then appends the special character(s) as new tokens.
                elif c == '#' or c == '\'' or c == '"' or c == '\\' or (c == '/' and prev_char == '/') or (prev_char == '/' and c == '*') or (prev_char == '*' and c == '/'):
                    if buf != '/' and buf != '*' and buf != "":
                        token_list.append((buf, line_num))
                        buf = ""
                    buf += c
                    token_list.append((buf, line_num))
                    buf = ""
                # the next character could be /, so we want to start a new token just for this.
                elif c == '*' or c == '/':
                    if buf != "":
                        token_list.append((buf, line_num))
                        buf = ""
                    buf += c
                # if the current character is not special in any way, then we just add it to the buffer.
                else:
                    buf += c
            # keep track of the previous character, so we can determine when we have /*, */, or //
            prev_char = c

        # ensure that we catch the final string
        if buf != "":
            token_list.append((buf, line_num))
        return token_list

    @staticmethod
    def analyze_c_tokens(tokens_w_line_nums):
        """
        TODO: document
        determines what kind of code each token is (c, comment, or preprocessor).
        returns a map between line number and a list of (token mapped to type of code)
        """
        analyzed_tokens = {}

        in_quotes = False
        in_single_line_comment = False
        in_preprocessor = False
        prev_line_num = 0
        in_comment = False
        continued_preprocessor = False
        for token, line_num in tokens_w_line_nums:
            if len(token) < 1:
                continue
            if line_num == prev_line_num:
                pass
            else:
                if not continued_preprocessor:
                    in_preprocessor = False
                if in_single_line_comment:
                    in_comment = False
                    in_single_line_comment = False
                analyzed_tokens[line_num] = []

            # preprocessor check
            if (not in_comment) and (not in_quotes) and token[0] == '#':
                in_preprocessor = True

            # NOTE: this gets tricky.
            # 1. if we start quotes while already in a comment or preprocessor, then it's still a comment.
            # 2. if we start a comment or preprocessor while already in quotes, then it's still quotes.

            # invert the quote status whenever we reach a new quote
            if (not in_preprocessor) and (not in_comment) and ("\"" in token):
                in_quotes = not in_quotes

            if (not in_quotes) and (not in_comment) and ("//" in token):
                in_single_line_comment = True
                in_comment = True

            if (not in_quotes) and (not in_comment) and ("/*" in token):
                in_comment = True

            # add the token with code type
            if in_comment:
                analyzed_tokens[line_num].append({token: "comment"})
            elif in_preprocessor:
                analyzed_tokens[line_num].append({token: "preprocessor"})
            else:
                analyzed_tokens[line_num].append({token: "c"})

            if in_comment and ("*/" in token):
                in_comment = False

            if token == '\\':
                continued_preprocessor = True
            else:
                continued_preprocessor = False

            prev_line_num = line_num
        return analyzed_tokens

    # taken from plocalizer/scripts/create_validation_conditions.py
    @staticmethod
    def get_conditional_blocks(src_content, line_count):
        """Output conditional block is the dummy root with special start/end
        values, which covers any conditional blocks in the file.
        """
        assert src_content

        # Analyze the tokens to get preprocessor tokens
        tokens = SyntaxAnalysis.get_tokens(src_content)
        categorized_tokens = SyntaxAnalysis.analyze_c_tokens(tokens)

        # Root is the one that is not due to any preprocessor directives, but the
        # encapsulating block with condition 1. 
        root_conditional_block = SyntaxAnalysis.ConditionalBlock()
        root_conditional_block.start_line = 0 #< Special value
        root_conditional_block.end_line = line_count + 1 #< Special value
        stack = [root_conditional_block]

        # Conditional blocks have a stack-like structure. The above stack helps
        # us to keep track of the current context. For example, if a opening for
        # a conditional block is seen, it is nested under the block at the
        # top the stack.

        for linenum in categorized_tokens:
          for i, token_to_type in enumerate(categorized_tokens[linenum]):
            # Get the token and its type
            assert len(token_to_type) == 1 #< One token mapped to its type.
            token = list(token_to_type.keys())[0]
            token_type = token_to_type[token]

            # Check if it is a conditional preprocessor directive
            if token == '#' and token_type == 'preprocessor':
              # Beginning of a new preprocessor directive, read the next token
              # to see if it is a conditional preprocessor directive.
              # Assumption: preprocessor directives like #if are not broken into
              # two lines right after the # sign (# \ if).
              next_token_to_type = categorized_tokens[linenum][i + 1]
              assert len(next_token_to_type) == 1
              next_token = list(next_token_to_type.keys())[0]
              next_token_type = next_token_to_type[next_token]
              assert next_token_type == "preprocessor"
              if next_token not in ['if', 'ifdef', 'ifndef', 'elif', 'else', 'endif']:
                # Not a conditional preprocessor directive
                continue
              
              if next_token in ['if', 'ifdef', 'ifndef']:
                # Open a new conditional block
                new_cb = SyntaxAnalysis.ConditionalBlock()
                new_cb.start_line = linenum
                stack[-1].sub_block_groups.append([new_cb])
                stack.append(new_cb)
              elif next_token in ['elif', 'else']:
                # Close the currently open conditional block.
                last_cb = stack[-1]
                last_cb.end_line = linenum
                stack.pop()

                # Open a new one in the same block group as the closed one.
                new_cb = SyntaxAnalysis.ConditionalBlock()
                new_cb.start_line = linenum
                parent_cb = stack[-1]
                parent_cb.sub_block_groups[-1].append(new_cb)
                stack.append(new_cb)
              elif next_token == 'endif':
                # Close the currently open conditional block.
                last_cb = stack[-1]
                last_cb.end_line = linenum
                stack.pop()
              else:
                assert False

        # There must remain only one element, which is the dummy root
        assert len(stack) == 1
        return stack[0]
    
    @staticmethod
    def get_conditional_blocks_of_file(srcfile_path: str) -> ConditionalBlock:
      """Returns a ConditionalBlock instance with the dummy root. Anything
      inside the root node is unconditional.  Children nodes depict blocks
      under conditional preprocessor directives, but the actual conditions
      are not set since this is only a syntax analysis.
      """
      assert os.path.isfile(srcfile_path)

      # Read the source file.
      with open(srcfile_path, 'r') as f:
        content = f.read()
      # Read the line count
      # Old method was to count the '\n' in source content but this failed
      # for a file (commit 88f8575bca5f, drivers/gpu/drm/amd/amdgpu/gfx_v9_4_2.c)
      # probably because there was no newline at the end of the file. Use
      # the file system to count the lines as below, which is safer.
      with open(srcfile_path, 'r') as f:
        line_count = len(f.readlines())

      # Get the conditional blocks (start-end lines).
      # Root has the special start/end values: 0 and line_count+1
      cb = SyntaxAnalysis.get_conditional_blocks(content, line_count)

      return cb
