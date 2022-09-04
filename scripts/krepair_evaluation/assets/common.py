import whatthepatch
import pprint
import enum
import argparse
import os, sys
from kmax.vcommon import run
import z3

class BasicLogger:
  def __init__(self, quiet=False):
    self.quiet = quiet
  
  def info(self, msg):
    if not self.quiet: sys.stderr.write("INFO: %s\n" % msg)
  def warning(self, msg):
    sys.stderr.write("WARNING: %s\n" % msg)
  def error(self, msg):
    sys.stderr.write("ERROR: %s\n" % msg)

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

class Patcher:
  def __init__(self, diff_content, srcdir, is_patch_applied):
    from shutil import which
    assert which("patch")
    self.__diff_content = diff_content
    self.__srcdir = srcdir
    self.__is_patch_applied = is_patch_applied
  
  def is_applied(self):
    return self.__is_patch_applied
  
  # TODO: more meaningful return vals to distinguish different errors (already applied, can't check, can't apply etc.), maybe exceptions
  def apply(self):
    if not self.__is_patch_applied:
      ret = self.__apply()
      if ret: self.__is_patch_applied = True
      return ret
    else:
      return False

  def reverse(self):
    if self.__is_patch_applied:
      ret = self.__reverse()
      if ret: self.__is_patch_applied = False
      return ret
    else:
      return False
  
  def __patch(self, check: bool, reverse: bool):
    patch_cmd = ["patch", "--forward", "-p1"] # TODO: take strip flag
    if check: patch_cmd.append("--dry-run")
    if reverse: patch_cmd.append("--reverse")

    # Write the patch to a temporary file and pass the patch file
    # In theory, we shouldn't need to create a file for the patch.
    # Instead, writing the patch content for stdin of the patch command
    # should work. Though, it didn't work for patches with special char
    # (e.g., check linux commit 99092a976c8c). Therefore, we do this
    # trick here.
    import tempfile
    with tempfile.NamedTemporaryFile(mode='w') as tmpfile:
        patchfilepath = tmpfile.name
        tmpfile.write(self.__diff_content)
        tmpfile.flush()
        shell_cmd = " ".join(patch_cmd) + " < " + patchfilepath
        _, _, ret, _ = run(shell_cmd, cwd=self.__srcdir, shell=True)
    return ret == 0

  def __apply(self):
    return self.__patch(check=True, reverse=False) and self.__patch(check=False, reverse=False)
    
  def __reverse(self):
    return self.__patch(check=True, reverse=True) and self.__patch(check=False, reverse=True)

def summarize_patch(patch: str, str_change_type=False) -> list:
	"""Summarize a patch and return the summary as a list of diff summary dictionaries.
	
	Each summary is in the following format:
	"change_type": an instance of FileChangeType enum describing how file was changed
	"old_path": path to the old path of the changed file (unset if change_type is CREATED)
	"new_path": path to the new path of the changed file (unset if change_type is REMOVED)
	"added_lines": added lines as a list of integers (unset if none)
	"removed_lines": removed lines as a list of integers (unset if none)

	Removed lines are in terms of their position in the old file while added
	lines are in terms of their position in the new file.

	Arguments:
	patch -- Patch string to parse and summarize.
	"""
	diff = whatthepatch.parse_patch(patch)

	diff_summaries = []
	for d in diff:
		old_path = d.header.old_path
		new_path = d.header.new_path
		change_type = FileChangeType.getType(d)

		added_lines = []
		removed_lines = []
		if d.changes:
			for c in d.changes:
				if c.old == None:
					assert c.new != None
					added_lines.append(c.new)
				elif c.new == None:
					assert c.old != None
					if change_type != FileChangeType.CREATED:
					  removed_lines.append(c.old)
				else:
					# no change in the line, just the mapping from old to new line number
					assert c.new != None and c.old != None
			
		diff_summary = {}
		diff_summary["change_type"] = change_type.name if str_change_type else change_type
		none_file = "/dev/null"
		# TODO: due to https://github.com/cscorley/whatthepatch/issues/43 we are
		# stripping the a/ and b/ prefixes, which might cause inaccuracies if the
		# file is really in such folder.
		def try_remove_prefix(s, prefix):
			if s == None or prefix == None:
				return s
			if s.startswith(prefix):
				return s[len(prefix):]
			else:
				return s
    # old path is none_file?
		if old_path != none_file: 
			diff_summary["old_path"] = try_remove_prefix(old_path, "a/")
			old_path = diff_summary["old_path"]
		else:
			old_path = None

		if new_path != none_file:
			diff_summary["new_path"] = try_remove_prefix(new_path, "b/")
			new_path = diff_summary["new_path"]
		else:
			new_path = None

		if added_lines: diff_summary["added_lines"] = added_lines
		if removed_lines: diff_summary["removed_lines"] = removed_lines

		if old_path and new_path:
		  assert SourceFileType.get_file_type(old_path) == SourceFileType.get_file_type(new_path)

		# set file type
		if old_path:
		  diff_summary["file_type"] = SourceFileType.get_file_type(old_path)
		elif new_path:
		  diff_summary["file_type"] = SourceFileType.get_file_type(new_path)
		else:
		  assert False

		diff_summaries.append(diff_summary)
	
	return diff_summaries

def get_line_mappings(added_lines, removed_lines, old_line_count, new_line_count):
  """Returns new2old and old2new mappings.

  Value of -1 means there is no mapping on the other end, e.g., line is removed or added."""
  # TODO: can be optimized. O(file size) space&time even for a change on only one line
  added_lines = set(added_lines)
  removed_lines = set(removed_lines)

  old_line = 1
  new_line = 1

  new2old = {}
  old2new = {}

  while old_line <= old_line_count or new_line <= new_line_count:
    while old_line in removed_lines:
      old2new[old_line] = -1
      old_line += 1

    while new_line in added_lines:
      new2old[new_line] = -1
      new_line += 1
    
    if old_line > old_line_count and new_line > new_line_count:
      break
    
    assert (old_line not in removed_lines) and (new_line not in added_lines) \
        and (old_line <= old_line_count) and (new_line <= new_line_count)
    
    old2new[old_line] = new_line
    new2old[new_line] = old_line

    old_line += 1
    new_line += 1
  
  assert old_line > old_line_count and new_line > new_line_count
    
  return new2old, old2new

def are_bool_formulas_equal(f1, f2, hashtable):
  """Check if two boolean formulas are equivalent.

  Arguments:
  f1 -- an instance of z3.Solver representing a boolean formula.
  f2 -- an instance of z3.Solver representing a boolean formula.
  hashtable -- a dictionary instance mapping formula pairs to their equivalence comparison.
  If a mapping for (f1, f2) is found hashtable, it is returned immediately. Otherwise,
  the hashtable is updated with result obtained by the comparison for equivalence for (f1, f2).
  """
  if hashtable != None and (f1, f2) in hashtable:
    return hashtable[(f1, f2)]
  
  s = z3.Solver()
  s.add(z3.Not(z3.And(f1.assertions()) == z3.And(f2.assertions())))
  is_eq = s.check() == z3.unsat

  if hashtable != None: hashtable[(f1, f2)] = is_eq
  
  return is_eq

def is_maybe_kernel(diff) -> bool:
  """Check whether the patch is to a non-kernel file based on the directory
  it is included.

  If the return value is False, it is guaranteed to be non-kernel.
  Otherwise, it may be kernel (needs to be checked by klocalizer).
  """
  assert diff
  old_path = diff.get('old_path', None)
  new_path = diff.get('new_path', None)
  non_kernel_dirs = ["tools", "Documentation", "usr", "LICENSES", "scripts"]
  for non_kernel_dir in non_kernel_dirs:
    if old_path and old_path.startswith(non_kernel_dir):
      return False
    if new_path and new_path.startswith(non_kernel_dir):
      return False
  return True

def is_interesting_patch(diff) -> bool:
  """Check whether the diff is an interesting change based on:
  * C source (has .c or .h file extension)
  * Change type (created, modified_only, or moved_modified)
  * Kernel file (based on directory, checked with is_maybe_kernel())
  """
  assert diff
  file_type = diff['file_type']
  if file_type != SourceFileType.SOURCE and file_type != SourceFileType.HEADER:
    return False

  change_type = diff['change_type']
  if change_type != FileChangeType.CREATED        and \
     change_type != FileChangeType.MODIFIED_ONLY  and \
     change_type != FileChangeType.MOVED_MODIFIED:
    # otherwise, it is REMOVED or MOVED_ONLY; for which we don't create configs
    return False

  return is_maybe_kernel(diff)

def is_interesting_c_patch(diff) -> bool:
  """Check whether the diff is an interesting C patch for which plocalizer
  will create configs for. Also check whether this is a non-kernel file
  based on directory.

  Similar to is_interesting_patch, but only returns True if diff belongs to
  a .c file.

  Deprecated: is_interesting_patch can be used instead together with
  SourceFileType check.
  """
  return is_interesting_patch(diff) and diff['file_type'] == SourceFileType.SOURCE

def is_filetype_patched(patch_summary, filetype : SourceFileType) -> bool:
  """Check if there are any modifications to a file in the given filetype"""
  for diff in patch_summary:
    old_path = diff.get('old_path', None)
    new_path = diff.get('new_path', None)

    def is_type(filepath, _type):
      return filepath != None and SourceFileType.get_file_type(filepath) == _type
    
    if is_type(old_path, filetype) or is_type(new_path, filetype):
      return True
  return False

class StatusGenPatchFiles(enum.Enum):
  SUCCESS = "SUCCESS"
  ERROR_SUPERC = "ERROR_SUPERC"
  ERROR_SUPERC_TIMEOUT = "ERROR_SUPERC_TIMEOUT"
  ERROR_UNSAT = "ERROR_UNSAT"
  ERROR_MAKE = "ERROR_MAKE"
  ERROR_MAKE_TIMEOUT = "ERROR_MAKE_TIMEOUT"
  ERROR_KLOCALIZER = "ERROR_KLOCALIZER"
  ERROR_KMAX = "ERROR_KMAX"

  def read_status(status_fpath):
    """Read the status from the first line of the status file."""
    str2enum = {
      "SUCCESS" : StatusGenPatchFiles.SUCCESS,
      "ERROR_SUPERC": StatusGenPatchFiles.ERROR_SUPERC,
      "ERROR_SUPERC_TIMEOUT": StatusGenPatchFiles.ERROR_SUPERC_TIMEOUT,
      "ERROR_UNSAT": StatusGenPatchFiles.ERROR_UNSAT,
      "ERROR_MAKE": StatusGenPatchFiles.ERROR_MAKE,
      "ERROR_MAKE_TIMEOUT" : StatusGenPatchFiles.ERROR_MAKE_TIMEOUT,
      "ERROR_KLOCALIZER": StatusGenPatchFiles.ERROR_KLOCALIZER,
      "ERROR_KMAX": StatusGenPatchFiles.ERROR_KMAX
    }
    assert status_fpath
    assert os.path.isfile(status_fpath)
    with open(status_fpath, 'r') as f:
      status_str = f.readline().strip()
    assert status_str in str2enum
    return str2enum[status_str]

  def does_file_compile(status):
    return status == StatusGenPatchFiles.SUCCESS or \
           status == StatusGenPatchFiles.ERROR_SUPERC or \
           status == StatusGenPatchFiles.ERROR_SUPERC_TIMEOUT
  
  def is_pc_available(status):
    return status == StatusGenPatchFiles.SUCCESS
