import tempfile
import os.path
import itertools
import subprocess as sp
import operator
import inspect
from shutil import which

import logging
from functools import reduce

def write_content_to_file(filepath: str, content: str):
    with open(filepath, 'w') as f:
        f.write(content)

def get_build_system_id(linux_ksrc: str) -> str:
    """Given path to the top Linux source directory, compute a 12 chars
    build system identifier.

    Following command is run in linux_ksrc:
    find . -type f -regex '.*\(Makefile\|Kconfig\|Kbuild\).*' -exec md5sum {} \; | sort | md5sum | head -c 12
    """
    # Check arguments
    assert os.path.isdir(linux_ksrc)
    assert which("find")
    assert which("sort")
    assert which("md5sum")
    assert which("head")

    # Compute build system id
    cmd = "find . -type f -regex '.*\(Makefile\|Kconfig\|Kbuild\).*' -exec md5sum {} \; | sort | md5sum | head -c 12"
    out, _, ret, _ = run(cmd, cwd=linux_ksrc, shell=True)
    assert ret == 0
    id = out.decode('utf-8').lower()
    assert len(id) == 12
    assert id.isalnum()
    return id

def run(args, stdin=None, capture_stdout=True, capture_stderr=True, cwd=None, timeout=None, shell=False):
  """Helper for running an external process.
  Returns a tuple of (stdout, stderr, return_code, time_elapsed) for the process.
  Arguments:
  args -- args, a list to pass to subprocess.Popen.
  stdin -- The content to be passed as stdin to the process.
  capture_stdout -- If set, capture stdout to be returned by the method. Otherwise, keep it at stdout.
  capture_stderr -- If set, capture stderr to be returned by the method. Otherwise, keep it at stdin.
  cwd -- Current working directory for the process.
  timeout -- timeout in seconds. If expires, raises an subprocess.TimeoutExpired exception.
  """
  import subprocess
  import time
  stdout_param = subprocess.PIPE if capture_stdout else None
  stderr_param = subprocess.PIPE if capture_stderr else None
  time_start = time.time()
  popen = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=stdout_param, stderr=stderr_param, cwd=cwd, shell=shell)
  if stdin != None: popen.stdin.write(stdin)
  captured_stdout, captured_stderr = popen.communicate(timeout=timeout)
  time_elapsed = time.time() - time_start
  popen.stdin.close()
  
  return captured_stdout, captured_stderr, popen.returncode, time_elapsed

def is_linux_dir(linux_ksrc: str) -> bool:
    """Return whether the given is a path to a top Linux source directory.

    Checks are incomplete but good for sanity checks.
    TODO: improve checks (check for certain files, attempt make kernelversion)
    """
    return os.path.isdir(linux_ksrc)

# TODO: improvement idea: decouple everything about compilation checks including the line checker.
def check_if_compiles(unit_paths: list, config_path: str, arch_name: str,
    linux_ksrc: str, build_targets: dict, cross_compiler: str, jobs: int,
    build_timeout_sec, use_olddefconfig_target: bool, logger) -> bool:
    """Check whether the given units compile with the given configuration
    file.

    Arguments:
    * unit_paths -- List of unit paths (e.g., ['kernel/fork.o', 'kernel/cpu.o']).
    Paths are relative to the top Linux source directory.
    * config_path -- Path to input Linux configuration file to use.
    * arch_name -- Name of the architecture (e.g., x86_64)
    * linux_ksrc -- Path to a top linux source directory.
    * build_targets -- Unit path to build target mapping. Defaults to unit path.
    * cross_compiler -- Executable cross compiler script (e.g., make.cross)
    * jobs -- Num jobs for make (passed with -j). None or <=0 are infinite.
    * build_timeout_sec -- Timeout in seconds for compilation. Pass None
    for no timeout constraints.
    * use_olddefconfig_target -- Whether to include olddefconfig in the
    build targets.
    * logger -- Logger that implements common.VoidLogger interface.

    Returns: a tuple of 6 values:
    1. List[bool] : Whether the units could be found at unit paths after
    compilation. One bool value per unit path. If all are True, it means
    compiled binaries can be found for all units.
    2. bool : Whether make timed out.
    3. int  : make return code. None if make timed out.
    4. str  : make stdout. None if make timed out.
    5. str  : make stderr. None if make timed out.
    6. float: Time elapsed for running make. None if make timed out.

    Whether the units could be compiled with the config file.
    The signal for successful compilation is whether units exist at unit
    path.  

    Notes:
    * The make target "clean" is included as the first target.
    * The Linux source directory is NOT cleaned after the compilation,
    i.e., the built binaries can still be found.
    * olddefconfig is NOT run on the configuration file.
    * -i is used on make to ignore errors thus to try all targets.
    """
    #
    # Check arguments
    #

    # Check unit_paths
    assert unit_paths
    for u in unit_paths:
        assert u.endswith(".o")

    assert os.path.isfile(config_path) #< Check config file.
    assert isinstance(arch_name, str) and len(arch_name) > 0 #< Check arch.
    assert is_linux_dir(linux_ksrc)    #< Check linux source directory.
    assert which(cross_compiler)       #< Check cross compiler.
    assert jobs is None or isinstance(jobs, int) #< Check jobs.

    # Prepare jobs parameter
    if jobs is None or jobs <= 0:
        jobs_param="-j" #< Infinite.
    else:
        jobs_param="-j%s" % jobs

    #
    # Prepare build targets
    #
    targets = ["clean"]  #< clean is the first target.
    if use_olddefconfig_target:
        targets.append("olddefconfig")
    for u in unit_paths: #< Map units into build targets.
        target = build_targets.get(u, u) #< Default is the unit path.
        if target not in targets: #< Don't include duplicates.
            targets.append(target)
    assert len(targets) > 1 #< At least one target other than clean.
    logger.debug("Build targets are: \"[%s]\"\n" % ", ".join(targets))

    #
    # Prepare compilation command
    #
    config_abspath = os.path.abspath(config_path) #< Command will run in linux as cwd.
    assert os.path.isfile(config_abspath)
    compile_cmd = [cross_compiler, jobs_param, "-i", "KCONFIG_CONFIG=%s" % config_abspath, "ARCH=%s" % arch_name]
    compile_cmd.extend(targets)  #< Add the targets.
    logger.debug("Compilation command: \"%s\"\n" % " ".join(compile_cmd))

    # Function definition for preparing the first return value: whether
    # units were found after compilation.
    def are_units_compiled():
        full_unit_paths = [os.path.join(linux_ksrc, u) for u in unit_paths]
        ret = [os.path.isfile(fpath) for fpath in full_unit_paths]
        assert len(ret) == len(unit_paths)
        return ret

    #
    # Run the compilation command
    #
    logger.debug("Running the compilation command.\n")
    from subprocess import TimeoutExpired
    try:
        make_out, make_err, ret, time_elapsed = run(
            compile_cmd, cwd=linux_ksrc, timeout=build_timeout_sec)
        logger.debug("Compilation finished in %.2f seconds, make exit code: %s\n" % (time_elapsed, ret))

        # Check the method docs for what each return value mean.
        make_out = make_out.decode('UTF-8')
        make_err = make_err.decode('UTF-8')
        return are_units_compiled(), False, ret, make_out, make_err, time_elapsed
    except TimeoutExpired:
        logger.debug("Timeout expired for compilation, duration(sec): %.2f\n" % build_timeout_sec)

        # Check the method docs for what each return value mean.
        return are_units_compiled(), True, None, None, None, None

def pause(s=None):
    try: #python2
        input("Press any key to continue ..." if s is None else s)
    except NameError:
        eval(input("Press any key to continue ..." if s is None else s))


def whoami():
    return inspect.stack()[1][3]

def vcmd(cmd, inp=None, shell=True):
    proc = sp.Popen(cmd,shell=shell,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=inp)
        
def vload(filename,mode='rb'):
    try:
        import pickle as pickle
    except ImportError:  #Python3
        import pickle

    with open(filename,mode) as fh:
        pickler = pickle.Unpickler(fh)
        sobj = pickler.load()
    return sobj

def vsave(filename,sobj,mode='wb'):
    try:
        import pickle as pickle
    except ImportError:  #Python3
        import pickle
        
    with open(filename,mode) as fh:
        pickler = pickle.Pickler(fh,-1)
        pickler.dump(sobj)

def vread(filename):
    with open(filename, 'r') as fh:
        return fh.read()

def iread(filename):
    """ return a generator """
    with open(filename, 'r') as fh:
        for line in fh:
            yield line

def strip_contents(lines, strip_c='#'):
    lines = (l.strip() for l in lines)
    lines = (l for l in lines if l)
    if strip_c:
        lines = (l for l in lines if not l.startswith(strip_c))
    return lines
    
def iread_strip(filename, strip_c='#'):
    """
    like iread but also strip out comments and empty line
    """
    return strip_contents(iread(filename), strip_c)


vmul = lambda l: reduce(operator.mul, l, 1)

getpath = lambda f: os.path.realpath(os.path.expanduser(f))
file_basename = lambda filename: os.path.splitext(filename)[0]

iflatten = lambda l: itertools.chain.from_iterable(l) #return a generator

# log utils
def getLogger(name, level):
    logger = logging.getLogger(name)
    logger.setLevel(logging.DEBUG)
    ch = logging.StreamHandler()
    ch.setLevel(level)
    formatter = logging.Formatter("%(levelname)s:%(name)s: %(message)s")
    ch.setFormatter(formatter)
    logger.addHandler(ch)
    return logger

def getLogLevel(level):
    assert level in set(range(5))
    
    if level == 0:
        return logging.CRITICAL
    elif level == 1:
        return logging.ERROR
    elif level == 2:
        return logging.WARNING
    elif level == 3:
        return logging.INFO
    else:
        return logging.DEBUG

