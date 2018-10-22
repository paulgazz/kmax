import tempfile
import os.path
import itertools
import subprocess as sp
import operator
import inspect

import logging

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
    formatter = logging.Formatter("%(name)s:%(levelname)s:%(message)s")
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

