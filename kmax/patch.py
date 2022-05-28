from .common import SourceFileType, FileChangeType
import whatthepatch

def is_maybe_kernel(filepath) -> bool:
  """Check whether the file is a kernel file based on the directory it is
  included.

  If the return value is False, it is guaranteed to be non-kernel.
  Otherwise, it may be kernel.
  """
  assert filepath
  non_kernel_dirs = ["tools", "Documentation", "usr", "LICENSES", "scripts"]
  for non_kernel_dir in non_kernel_dirs:
    if filepath.startswith(non_kernel_dir):
      return False
  return True

def is_interesting_diff(diff) -> bool:
  """Check whether the diff is an interesting change based on:
  * C source with .c/.h extension
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

  return is_maybe_kernel(diff['new_path'])

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

def get_lines_to_build_for_removed(added_lines, removed_lines):
  """Get the list of lines that need building due to removed lines.
  
  These are the unchanged lines that used to be just above the removed lines.

  As in unified diff format, added lines is the line numbers after the patch
  is applied, and removed lines is the line numbers before the patch is applied.
  """
  if not removed_lines:
    return []
  added_lines = sorted(list(set(added_lines)))
  removed_lines = sorted(list(set(removed_lines)))

  # First, map the removed lines to the unchanged lines that need building,
  # but line numbers in the unpatched state.
  lines2build_unpatched = []
  for i, line_num in enumerate(removed_lines):
    # If the line before line_num is also removed, then they require the
    # same unchanged line to be built. In this case, no need to add any
    # additional line.
    if i > 0 and removed_lines[i-1] == (line_num - 1):
      continue
    else:
      # Map to the unchanged line just before this line.
      lines2build_unpatched.append(line_num - 1)
  
  # lines2build_unpatched includes the line numbers "before the patch is
  # applied". However, removing/adding lines change their position in the
  # new file. Map them to their position in the new file.
  # To achieve this, traverse three lists at the same time: added_lines,
  # removed_lines, and lines2build_unpatched. Added lines require to shift
  # forwards while removed lines require to shift backwards.
  lines2build = []
  shift = 0
  added_lines_idx = 0
  removed_lines_idx = 0
  for l in lines2build_unpatched:
    # For each removed line above l, shift l backwards.
    while removed_lines_idx < len(removed_lines) and removed_lines[removed_lines_idx] < l:
      shift -= 1
      removed_lines_idx += 1
    # For each line added at this point on, shift l forwards.
    while added_lines_idx < len(added_lines) and added_lines[added_lines_idx] <= (l + shift):
      shift += 1
      added_lines_idx += 1
    # Add the line by applying the shift
    lines2build.append(l + shift)
  assert len(lines2build) > 0 and lines2build[0] >= 0

  # Edge case: if the first line is removed, it maps to line 0, which does
  # not exist. Map it to the first line in the new file.
  if lines2build[0] == 0:
    lines2build[0] = 1
  
  return lines2build

def get_target_lines(patch_txt: str):
  """Given a patch file content, compute and return the C and header lines
  that need building for covering the patch.

  These lines are based only on parse of the patch. They include the
  added lines, and the lines with closest proximity to the removed lines.
  
  Filter out files if:
  * The file is NOT a C or header file (source file with .c/.h extension)
  * The change removes the file completely or only moves it without line changes
  * The file is non-kernel code (based on directory they are in)

  Returned mapping has the following structure:
  {
    "sourcefile_loc": {
      "path/to/sourcefile1": [line2build_1,],
    },
    "headerfile_loc": {
      "path/to/headerfile1": [line2build_1,],
    }
  }
  """
  # Summarize the patch
  patch_summary = summarize_patch(patch_txt)
  assert patch_summary

  ret = {}

  for diff in patch_summary:
    if not is_interesting_diff(diff):
      continue

    added_lines = diff.get('added_lines', [])
    removed_lines = diff.get('removed_lines', [])
    lines_to_build_for_removed = get_lines_to_build_for_removed(added_lines, removed_lines)
    lines_to_build = sorted(list(set(added_lines + lines_to_build_for_removed)))
    assert len(lines_to_build) > 0

    # Add the file:lines to the results
    patched_path = diff['new_path']

    file_type = diff['file_type']
    if file_type == SourceFileType.SOURCE:
      ret["sourcefile_loc"] = ret.get("sourcefile_loc", {})
      ret["sourcefile_loc"][patched_path] = lines_to_build
    elif file_type == SourceFileType.HEADER:
      ret["headerfile_loc"] = ret.get("headerfile_loc", {})
      ret["headerfile_loc"][patched_path] = lines_to_build
    else:
      assert False

  return ret

def get_target_c_lines(patch_txt: str):
  """Given a patch file content, compute and return the C lines with .c
  extension, excluding header files, that need building for covering
  the patch.

  This only differs from patch.get_target_lines() by excluding header files.

  Returned mapping has the following structure:
  {
    "path/to/sourcefile1": [line2build_1, line2build_2, ...],
    ...
  }

  """
  r = get_target_lines(patch_txt)
  return r.get("sourcefile_loc", {})
