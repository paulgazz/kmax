# Inputs:
# 1. Patch conditions from loc_patch_conditions.py, which needed further filtering
# 2. Klocalizer experiment results, which tells what .c files klocalizer
#    can build in a patch.
# 3. Manual analysis results. The manual analysis of files which could not
#    be built by klocalizer experiment.
# Using all this data, we obtain the ground truth patch conditions per
# architecture, which we will use in our experiments.

import sys
class BasicLogger:
  def __init__(self, quiet=False, verbose=False):
    assert (not (quiet and verbose))
    self.quiet = quiet
    self.verbose = verbose
  
  def info(self, msg):
    if not self.quiet: sys.stderr.write("INFO: %s\n" % msg)
    
  def warning(self, msg):
    sys.stderr.write("WARNING: %s\n" % msg)
    
  def error(self, msg):
    sys.stderr.write("ERROR: %s\n" % msg)
    
  def debug(self, msg):
    if self.verbose: sys.stderr.write("DEBUG: %s\n" % msg)

logger=BasicLogger()

import argparse
import glob
import os
import json
import csv
def main():
  argparser = argparse.ArgumentParser()
  argparser.add_argument("--patch-conditions",
                          type=str,
                          required=True,
                          help="A directory containing patch conditions for each of the patches (ID-COMMITID.cond). This is the output of evaluation/create_patch_conditions.sh")
  argparser.add_argument("--kloc-results",
                          type=str,
                          required=True,
                          help="A directory containing klocalizer experiment results for each of the patches (ID-COMMITID.kloc). This is the output of run_kloc_c_files.py")
  argparser.add_argument("--hand-validation-results",
                          type=str,
                          required=True,
                          help="A csv file containing hand validation results for --kloc-results.")
  argparser.add_argument("--output-dir",
                          type=str,
                          required=True,
                          help="Output directory where patch conditions will be created in directories per architecture. Also, the build target mappings will be created for special cases (builds_dir).")

  # Parse the argument
  args = argparser.parse_args()
  patch_conditions_dir = args.patch_conditions
  kloc_results_dir = args.kloc_results
  hand_validation_csv_file = args.hand_validation_results
  output_dir = args.output_dir
  archs = ['arm', 'x86_64']

  assert os.path.isdir(patch_conditions_dir)
  assert os.path.isdir(kloc_results_dir)
  assert os.path.isfile(hand_validation_csv_file)

  # Read the patch conditions
  logger.info("Reading the patch conditions.")
  patch_conditions = {}
  patch_condition_files = glob.glob(patch_conditions_dir + "/*.cond")
  for cond_file in patch_condition_files:
    name = os.path.basename(cond_file).split('.cond')[0]
    with open(cond_file, 'r') as f:
      cond = json.load(f)
      patch_conditions[name] = cond
  
  # Read the klocalizer experiment results
  logger.info("Reading the klocalizer experiment results.")
  kloc_results = {}
  kloc_result_files = glob.glob(kloc_results_dir + "/*.kloc")
  for kloc_file in kloc_result_files:
    name = os.path.basename(kloc_file).split('.kloc')[0]
    with open(kloc_file, 'r') as f:
      kloc_result = json.load(f)
      kloc_results[name] = kloc_result
  
  # Read the hand validation results
  hand_validation_results = {} # (file,arch): (label,extra_results_if_needed)
  logger.info("Reading the hand validation results.")
  with open(hand_validation_csv_file, 'r') as f:
    results = csv.reader(f)
  
    for i, row in enumerate(results):
      if i == 0:
        continue # title row
      file, arch, label, build_target = row
      assert label in ['builds', 'builds_dir', 'compiler_error', 'needs_attention', 'header', 'cant_build', 'system_issue']
      hand_validation_results[(file, arch)] = (label, build_target)

  def does_file_build_kloc_exp(patch_name, srcfile, arch):
    return arch in kloc_results[name][srcfile]
  
  # Create the new patch conditions
  logger.info("Computing the new patch conditions")
  new_patch_conditions = {} # arch: patch_conditions
  build_targets = {} # sourcefile : build target
  seen_needs_attention = False
  for arch in archs:
    new_patch_conditions[arch] = {}
    
  for name in patch_conditions:
    old_cond = patch_conditions[name]

    # Create arch-specific patch conditions
    for arch in archs:
      new_patch_conditions[arch][name] = {}
      new_cond = new_patch_conditions[arch][name]
      new_cond['sourcefile_loc'] = {}
      new_cond['headerfile_loc'] = old_cond.get('headerfile_loc', {})

      for srcfile in old_cond.get('sourcefile_loc', {}):
        kloc_ret = does_file_build_kloc_exp(name, srcfile, arch)
        if kloc_ret: # If kloc can build the unit, safe to add to new patch conditions
          new_cond['sourcefile_loc'][srcfile] = old_cond['sourcefile_loc'][srcfile]
        else: # If kloc can't build, manual analysis results tell what to do
          key = (srcfile, arch)
          label, build_target = hand_validation_results.get(key, (None, None))
          if not label:
            # Exclude
            # Trivial cases like arch/s390/ never included in the manual
            # analysis. Therefore, the assumption is the file should be
            # excluded if manual analysis don't tell anything about it.
            pass
          elif label in ['cant_build', 'system_issue']:
            # Exclude
            pass
          elif label in ['builds', 'builds_dir', 'compiler_error', 'needs_attention']:
            # Include as sourcefile
            # Any of these cases mean a valid configuration can be created
            # that builds the unit in this current arch (despite build
            # target is different than the unit path or there are compiler
            # errors that are not related to system issues).
            # Also include the needs_attention cases, which will be manually
            # fixed in the output patch conditions.
            new_cond['sourcefile_loc'][srcfile] = old_cond['sourcefile_loc'][srcfile]
            if label == 'builds_dir':
              assert build_target
              build_targets[srcfile] = build_target
            if label == 'needs_attention':
              seen_needs_attention = True
          elif label in ['header']:
            # Include as headerfile
            new_cond['headerfile_loc'][srcfile] = old_cond['sourcefile_loc'][srcfile]
            pass
          else:
            assert False
          
      # If there is no headerfile_loc, delete the key
      if not new_cond['headerfile_loc']:
        del new_cond['headerfile_loc']

      # If there is no sourcefiles left in the patch conditions, delete
      if not new_patch_conditions[arch][name]['sourcefile_loc']:
        del new_patch_conditions[arch][name]
  
  if seen_needs_attention:
    logger.warning("\"needs_attention\" tags were seen in the manual analysis results. These files will included in the output patch conditions, which might require manual changes.")

  # Output architecture specific conditions
  logger.info("Creating the new patch conditions in \"%s\"." % output_dir)
  for arch in archs:
    arch_dir = os.path.join(output_dir, arch)
    os.makedirs(arch_dir, exist_ok=True)
    for name in new_patch_conditions[arch]:
      cond_path = os.path.join(arch_dir, "%s.cond" % name)
      with open(cond_path, 'w') as f:
        json.dump(new_patch_conditions[arch][name], f, sort_keys=True, indent=2)
  logger.info("Patch condition files were created.")

  fpath = os.path.join(output_dir, "build_targets.json")
  logger.info("Creating build target mappings in \"%s\"." % fpath)
  with open(fpath, 'w') as f:
    json.dump(build_targets, f, sort_keys=True, indent=2)
  logger.info("Build target mappings were created.")

  logger.info("All done.")

if __name__ == '__main__':
  main()
