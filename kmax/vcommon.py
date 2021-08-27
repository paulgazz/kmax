import tempfile
import os.path
import itertools
import subprocess as sp
import operator
import inspect

import logging

def run(args, stdin=None, capture_stdout=True, capture_stderr=True, cwd=None):
  """Helper for running an external process.
  Returns a tuple of (stdout, stderr, return_code) for the process.
  Arguments:
  args -- args, a list to pass to subprocess.Popen.
  stdin -- The content to be passed as stdin to the process.
  capture_stdout -- If set, caoture stdout to be returned by the method. Otherwise, keep it at stdout.
  capture_stderr -- If set, caoture stderr to be returned by the method. Otherwise, keep it at stdin.
  cwd -- Current working directory for the process.
  """
  import subprocess
  stdout_param = subprocess.PIPE if capture_stdout else None
  stderr_param = subprocess.PIPE if capture_stderr else None
  popen = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=stdout_param, stderr=stderr_param, cwd=cwd)
  if stdin != None: popen.stdin.write(stdin)
  captured_stdout, captured_stderr = popen.communicate()
  popen.stdin.close()
  
  return captured_stdout, captured_stderr, popen.returncode

def pause(s=None):
    try: #python2
        raw_input("Press any key to continue ..." if s is None else s)
    except NameError:
        input("Press any key to continue ..." if s is None else s)


def whoami():
    return inspect.stack()[1][3]

def vcmd(cmd, inp=None, shell=True):
    proc = sp.Popen(cmd,shell=shell,stdin=sp.PIPE,stdout=sp.PIPE,stderr=sp.PIPE)
    return proc.communicate(input=inp)
        
def vload(filename,mode='rb'):
    try:
        import cPickle as pickle
    except ImportError:  #Python3
        import pickle

    with open(filename,mode) as fh:
        pickler = pickle.Unpickler(fh)
        sobj = pickler.load()
    return sobj

def vsave(filename,sobj,mode='wb'):
    try:
        import cPickle as pickle
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

