from common import SourceFileType, BasicLogger
from common import summarize_patch, is_interesting_patch
import os
import argparse
import json

logger = BasicLogger()

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

def gen_patch_loc_conditions(patch_file: str):
  """Given a patch file, compute and return the patch conditions.

  Patch conditions are based on parsing the patch only. They include the
  added lines, and the lines with closest proximity to the removed lines.
  
  Filter out files if:
  * The file is NOT a source/header file with .c or .h extension
  * The change removes the file completely or only moves it without line changes
  * The file is non-kernel code (based on directory they are in)

  Overall, the patch conditions is empty if there is no conditions for at
  least one .c file (even if there are header files).

  Returned mapping has the following structure:
  {
    "sourcefile_loc":
      {
        "path/to/sourcefile1": [line2build_1, line2build_2, ...],
        ...
      },
    "headerfile_loc":
      {
        "path/to/headerfile1": [line2build_1, line2build_2, ...],
        ...
      }
  }
  """
  ret = {}
  # Summarize the patch
  logger.info("Summarizing the patch.")
  with open(patch_file, 'r') as f: patch_txt = f.read()
  patch_summary = summarize_patch(patch_txt)
  assert patch_summary

  sourcefile_loc = {}
  headerfile_loc = {}

  for diff in patch_summary:
    if not is_interesting_patch(diff):
      continue

    added_lines = diff.get('added_lines', [])
    removed_lines = diff.get('removed_lines', [])
    lines_to_build_for_removed = get_lines_to_build_for_removed(added_lines, removed_lines)
    lines_to_build = sorted(list(set(added_lines + lines_to_build_for_removed)))
    assert len(lines_to_build) > 0

    # Decide which condition to update based on source/header
    file_type = SourceFileType.get_file_type(diff['new_path'])
    if file_type == SourceFileType.SOURCE:
      condition_to_update = sourcefile_loc
      pass
    elif file_type == SourceFileType.HEADER:
      condition_to_update = headerfile_loc
      pass
    else:
      assert False
    
    # Update the conditions to include this file and its conditions
    patched_path = diff['new_path']
    condition_to_update[patched_path] = lines_to_build

  patch_conditions = {}
  # Patch conditions must include at least one compilation unit (sourcefile_loc)
  # besides from any headerfile_loc.
  if sourcefile_loc:
    patch_conditions["sourcefile_loc"] = sourcefile_loc

    if headerfile_loc:
      patch_conditions["headerfile_loc"] = headerfile_loc
    else:
      # No problem. It just does not exist.
      pass
  else:
    logger.warning("Patch conditions is empty since there are no interesting .c file changes.")

  return patch_conditions

def main():
  argparser = argparse.ArgumentParser()

  argparser.add_argument('--patch',
                  type=str,
                  required=True,
                  help="""Patch file containing the diff.""")
  argparser.add_argument('-o', '--output',
                  type=str,
                  default="patch_conditions.txt",
                  help="""Path to the output file to store patch conditions.  Defaults to \"patch_conditions.txt\".""")
  args = argparser.parse_args()
  patch_file = args.patch
  output_file = args.output

  assert os.path.isfile(patch_file)

  patch_conditions = gen_patch_loc_conditions(patch_file)

  # Dump the patch conditions
  logger.info("Writing the patch conditions to \"%s\"." % output_file)
  with open(output_file, 'w') as f:
    json.dump(patch_conditions, f, sort_keys=True, indent=2)

if __name__ == "__main__":
  main()
