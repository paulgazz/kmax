import sys
import pickle
import z3
import enum

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
  if kbuild_path in list(kmax_formulas.keys()):
    kmax_constraints = []
    # add the condition for the compilation unit and each of its parent directories
    comp_unit_constraint = z3.parse_smt2_string(kmax_formulas[kbuild_path])
    kmax_constraints.extend(comp_unit_constraint)
    if view:
      print(("%s\n%s\n" % (kbuild_path, comp_unit_constraint)))
    if '/' in kbuild_path:
      subpath, basename = kbuild_path.rsplit('/', 1)
      elems = subpath.rsplit('/')
      for i in range(0, len(elems)):
        subarray = elems[0:(len(elems) - i)]
        subsubpath = '/'.join(subarray) + "/"
        if subsubpath in list(kmax_formulas.keys()):
          subsubpath_constraint = z3.parse_smt2_string(kmax_formulas[subsubpath])
          kmax_constraints.extend(subsubpath_constraint)
          if view:
            print(("%s\n%s\n" % (subsubpath, subsubpath_constraint)))
        else:
          debug("%s has no kmax formula, assuming it is unconstrained." % (subsubpath))
    return kmax_constraints
  else:
    return None
  
def unpickle_kmax_file(kmax_file):
  with open(kmax_file, 'rb') as fp:
    kmax = pickle.load(fp)
    return kmax

class SourceFileType(enum.Enum):
  SOURCE = 1 # .c
  HEADER = 2 # .h
  MAKEFILE = 3 # Makefile/Kbuild
  KCONFIG = 4 # Kconfig
  OTHER = 5 # anything else

  @classmethod
  def get_file_type(cls, filename: str):
    assert filename != None

    if filename.endswith('.c'):
      return SourceFileType.SOURCE
    elif filename.endswith('.h'):
      return SourceFileType.HEADER
    elif filename.startswith("Makefile") or filename.startswith("Kbuild"):
      return SourceFileType.MAKEFILE
    elif filename.startswith("Kconfig"):
      return SourceFileType.KCONFIG
    else: 
      return SourceFileType.OTHER

class FileChangeType(enum.Enum):
	CREATED = 1
	REMOVED = 2
	MOVED_ONLY = 3 # file was moved but the content didn't change
	MOVED_MODIFIED = 4 # file was moved and the content was modified
	MODIFIED_ONLY = 5 # content was modified but the file wasn't moved

	@classmethod
	def getType(cls, diff):
		none_file="/dev/null"
		assert not (diff.header.old_path == none_file and diff.header.new_path == none_file)
		
		if diff.header.old_path == none_file:
			return FileChangeType.CREATED
		elif diff.header.new_path == none_file:
			return FileChangeType.REMOVED
		elif diff.header.old_path != diff.header.new_path:
			# filename changed
			if diff.changes:
				return FileChangeType.MOVED_MODIFIED
			else:
				return FileChangeType.MOVED_ONLY
		elif diff.header.old_path == diff.header.new_path and diff.changes:
			return FileChangeType.MODIFIED_ONLY
		elif "deleted file" in diff.text:
			# When deleted a file, some patches might have the same file path for
			# both before and after instead of none_file name. See
			# e8bf1f522aee3b3e1e7658e8f224dca1d88c3338 for the Linux kernel.
			return FileChangeType.REMOVED
		else: assert False # all cases are covered above
