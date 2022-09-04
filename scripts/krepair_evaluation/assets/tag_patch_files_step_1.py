import argparse
import os
import json
from common import BasicLogger, FileChangeType, SourceFileType
from common import summarize_patch

logger = BasicLogger()

def get_tags(patch_file):
  # Maps 'file modified by patch' to 'patch tag'
  patch_tags = {}

  # Summarize the patch
  logger.info("Summarizing the patch.")
  with open(patch_file, 'r') as f:
    patch_txt = f.read()
  patch_summary = summarize_patch(patch_txt)
  assert patch_summary

  for diff in patch_summary:
    # Filename
    if 'new_path' in diff: #< True except when file is removed
      filename = diff['new_path']
    elif 'old_path' in diff: #< When file is removed
      filename = diff['old_path']
    else:
      assert False

    # File type
    file_type = diff['file_type']
    if file_type not in [SourceFileType.SOURCE, SourceFileType.HEADER]:
      patch_tags[filename] = "NON_C"
      continue

    # Change type
    change_type = diff['change_type']
    if change_type == FileChangeType.REMOVED:
      patch_tags[filename] = "REMOVED"
      continue
    elif change_type == FileChangeType.MOVED_ONLY:
      patch_tags[filename] = "MOVED_ONLY"
      continue
  
    # Is non kernel by directory?
    non_kernel_dirs = ["tools", "Documentation", "usr", "LICENSES", "scripts"]
    if any([filename.startswith(x) for x in non_kernel_dirs]):
      patch_tags[filename] = "NON_KERNEL_DIR"
      continue
    
    # Is header with .h extension?
    if file_type == SourceFileType.HEADER:
      patch_tags[filename] = "HEADER_H"
      continue

    # Is non x86 arch dir?
    if filename.startswith("arch/") and not filename.startswith("arch/x86"): #< arch/x86/ or arch/x86_64/
      patch_tags[filename] = "NON_X86_ARCH_DIR"
      continue

    # If we couldn't assign a tag so far, this file is definitely a file
    # with .c extension that possibly compiles for x86_64. But to make sure,
    # we need further input from klocalizer experiments and the manual
    # analysis. Therefore, tag this as "NEEDS_FURTHER_ATTENTION", which is
    # to be resolved with additional data.
    patch_tags[filename] = "NEEDS_FURTHER_ATTENTION"

  return patch_tags

def main():
  argparser = argparse.ArgumentParser()

  argparser.add_argument('--patch',
                  type=str,
                  required=True,
                  help="""Patch file containing the diff.""")
  argparser.add_argument('--output',
                  type=str,
                  required=True,
                  help="""Path to the output file to store the tags for each file affected by the input patch.""")
  
  args = argparser.parse_args()
  patch_file = args.patch
  output_file = args.output

  assert os.path.isfile(patch_file)
  
  patch_tags = get_tags(patch_file)

  # Dump the patch conditions
  logger.info("Writing the patch tags to \"%s\"." % output_file)
  with open(output_file, 'w') as f:
    json.dump(patch_tags, f, sort_keys=True, indent=2)
  
  logger.info("All done.")

if __name__ == "__main__":
  main()
