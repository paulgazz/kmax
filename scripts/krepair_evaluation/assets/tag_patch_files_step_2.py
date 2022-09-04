import argparse
import os
import json
import csv
from common import BasicLogger

logger = BasicLogger()

def main():
  argparser = argparse.ArgumentParser()
  
  argparser.add_argument("--patch-tags",
    type=str,
    required=True,
    help="Patch tags file.  This is the input patch tags file that will be modified with kloc experiment and manual analysis results.")
  argparser.add_argument("--kloc-results",
    type=str,
    required=True,
    help="A .kloc file that contains the results for klocalizer experiment for this patch.  This is the output of run_kloc_c_files.py")
  # https://docs.google.com/spreadsheets/d/1YgGuUwiC1E3U2K8Jwen5D_uLIVfTsxMkRUUp5ygKU1E/edit#gid=1893341200
  # File > Download > Comma Seperated Values (.csv)
  argparser.add_argument("--hand-check-results",
    type=str,
    required=True,
    help="A .csv file that contains the results for manually checking the klocalizer experiment results.  We pull this from some Google Sheet where we recorded the manual analysis results.")
  argparser.add_argument("--output",
    type=str,
    required=True,
    help="Path to the output file to store the modified patch tags.")
  
  args = argparser.parse_args()
  patch_tags_file = args.patch_tags
  kloc_results_file = args.kloc_results
  hand_check_results_csv_file = args.hand_check_results
  output_file = args.output

  # Read the patch tags
  logger.info("Reading the input patch tags.")
  assert os.path.isfile(patch_tags_file)
  with open(patch_tags_file, 'r') as f:
    patch_tags = json.load(f)
  
  # Read the klocalizer experiment results
  # TODO: only run this if file had NEEDS_FURTHER_ATTENTION
  # because otherwise we never run klocalizer experiment or hand checked
  # the results for this patch.
  logger.info("Reading the input klocalizer experiment results.")
  assert os.path.isfile(kloc_results_file)
  with open(kloc_results_file, 'r') as f:
    kloc_exp_results = json.load(f)
  
  # Read the hand checking of klocalizer experiments results
  # Originally, the results include analysis for both x86_64 and arm.
  # However, the decision is to care about x86_64 only. We will take care
  # of this while interpreting the hand check results.
  logger.info("Reading the input hand check results.")
  hand_check_results = {}
  assert os.path.isfile(hand_check_results_csv_file)
  with open(hand_check_results_csv_file, 'r') as f:
    results = csv.reader(f)
    for i, row in enumerate(results):
      if i == 0:
        continue #< Title row.
      file, arch, label, build_target = row
      assert label in ['builds', 'builds_dir', 'compiler_error', 'needs_attention', 'header', 'cant_build', 'system_issue']
      hand_check_results[(file, arch)] = (label, build_target)
  
  new_patch_tags = patch_tags.copy()
  # Traverse the original patch tags, and look for "NEEDS_FURTHER_ATTENTION" cases
  for filename in patch_tags:
    tag = patch_tags[filename]
    if tag != "NEEDS_FURTHER_ATTENTION":
      continue #< Already tagged, no need for results from kloc experiments etc.
    else: #< Not yet tagged, tag by using the results from 
      # If kloc experiments say it can built the file for x86_64, it is indeed correct.
      if "x86_64" in kloc_exp_results[filename]:
        new_patch_tags[filename] = "X86_64_C"
      else:
        # If kloc experiments could not build the unit, it is either that the
        # unit cannot be built for x86_64, or klocalizer could not generate
        # building .config file although it could be built. At this point,
        # hand check results help decide.
        r = hand_check_results[(filename, 'x86_64')][0]
        if r == "builds":
          tag = "X86_64_C"
        elif r == "builds_dir":
          tag = "X86_64_C_SPECIAL_BUILD_TARGET"
        elif r == "compiler_error":
          tag = "X86_64_C_COMPILER_ERROR"
        elif r == "system_issue":
          tag = "X86_64_C_SYSTEM_ISSUE"
        elif r == "header":
          tag = "HEADER_C"
        elif r == "cant_build":
          tag = "NON_X86_64_C"
        elif r == "needs_attention":
          tag = "NEEDS_FURTHER_ATTENTION_2"
        else:
          assert False #< No other value is expected.

        new_patch_tags[filename] = tag

  # Dump the patch conditions
  logger.info("Writing the modified patch tags to \"%s\"." % output_file)
  with open(output_file, 'w') as f:
    json.dump(new_patch_tags, f, sort_keys=True, indent=2)
  
  logger.info("All done.")

if __name__ == '__main__':
  main()
