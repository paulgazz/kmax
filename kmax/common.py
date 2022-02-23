import sys
import pickle
import z3

quiet = False
verbose = False

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

class BasicLogger:
  """A simple logger."""
  def __init__(self, quiet=False, verbose=False, flush=True):
    assert (not (quiet and verbose))
    self.quiet = quiet
    self.verbose = verbose
    self.flush = flush
  
  def __flush(self):
    if self.flush: sys.stderr.flush()

  def info(self, msg):
    if not self.quiet:
      sys.stderr.write("INFO: %s" % msg)
      self.__flush()
    
  def warning(self, msg):
    sys.stderr.write("WARNING: %s" % msg)
    self.__flush()
    
  def error(self, msg):
    sys.stderr.write("ERROR: %s" % msg)
    self.__flush()
    
  def debug(self, msg):
    if self.verbose:
      sys.stderr.write("DEBUG: %s" % msg)
      self.__flush()

def info(msg, ending="\n"):
  if not quiet: sys.stderr.write("INFO: %s%s" % (msg, ending))

def debug(msg, ending="\n"):
  if verbose: sys.stderr.write("DEBUG: %s%s" % (msg, ending))

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
          debug("%s has no kmax formula, assuming it is unconstrained." % (subsubpath))
    return kmax_constraints
  else:
    return None
  
def unpickle_kmax_file(kmax_file):
  with open(kmax_file, 'rb') as fp:
    kmax = pickle.load(fp)
    return kmax
