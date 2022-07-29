# Measure the change between an original configuration file and a list of
# repaired configuration files. Result is printed in json format to the
# standard output.

# The format is:
# {
#    "original": { "assigned_config_options_count": INT },
#    "repaired": {
#       "repaired_cfg_file1_basename": {
#         "assigned_config_options_count": INT,
#         "change_wrt_original" : INT
#       }, ... (entries for other repaired config files)
#
#     }
# }
# "assigned_config_options_count" is in case we need it. Otherwise,
# "change_wrt_original" is possibly enough for presenting any results.

import argparse
import os
import json
from kmax.vcommon import run

import sys
class BasicLogger:
  def __init__(self, quiet=False):
    self.quiet = quiet
  
  def info(self, msg):
    if not self.quiet: sys.stderr.write("INFO: %s\n" % msg)
  def warning(self, msg):
    sys.stderr.write("WARNING: %s\n" % msg)
  def error(self, msg):
    sys.stderr.write("ERROR: %s\n" % msg)

logger = BasicLogger()

def main():
  argparser = argparse.ArgumentParser()

  argparser.add_argument('--original-config',
    type=str,
    required=True,
    help="""Path to the original (unrepaired) configuration file.""")
  argparser.add_argument("repaired_configs",
    nargs='*',
    help="""Path(s) to the repaired configuration file(s).""")

  args = argparser.parse_args()
  original_config_file = args.original_config
  repaired_configs_files = args.repaired_configs

  # Assumption: this script is in the same directory as "get_diff_count_between_two_config_files.sh"
  self_dir_path = os.path.dirname(os.path.realpath(sys.argv[0]))
  diff_count_script_path = os.path.join(self_dir_path, "get_diff_count_between_two_config_files.sh")
  if not os.path.isfile(diff_count_script_path):
    logger.error("Cannot file the script \"get_diff_count_between_two_config_files.sh\"")
    exit(-1)

  assert os.path.isfile(original_config_file)
  for f in repaired_configs_files:
    assert os.path.isfile(f)
  
  def count_assigned_config_options(cfg_file_path) -> int:
    """Counts the number of configuration options with some value assigned
    other than n (is not set)."""
    assert os.path.isfile(cfg_file_path)
    cmd = "grep \"^CONFIG\" %s | wc -l" % cfg_file_path
    stdout, _, ret_code, _ = run(cmd, shell=True)
    assert ret_code == 0
    return int(stdout.decode('utf-8'))
  
  def measure_change(cfg1_path, cfg2_path) -> int:
    """Measures the number of configuration options with some value assigned
    in one configuration while not in another. This is used as the metric of
    repair change.
    """
    assert os.path.isfile(cfg1_path)
    assert os.path.isfile(cfg2_path)
    cmd = "bash %s %s %s" % (diff_count_script_path, cfg1_path, cfg2_path)
    stdout, _, ret_code, _ = run(cmd, shell=True)
    assert ret_code == 0
    return int(stdout.decode('utf-8').strip())
  
  # Result is recorded in a dict instance, which will be json dump'd to stdout.
  result = {}

  # Record the count of assigned configuration options for the original config file.
  result["original"] = {}
  result["original"]["assigned_config_options_count"] = count_assigned_config_options(original_config_file)

  # Measure and record the difference between original and repaired(s)
  result["repaired"] = {}
  for repaired_config_file in sorted(repaired_configs_files):
    logger.info("Working on \"%s\"" % repaired_config_file)
    # Create an entry for the config file identified by the config file basename
    bname = os.path.basename(repaired_config_file)
    result["repaired"][bname] = {}

    # Get the assigned config options count and the change wrt to the original
    count_assigned_options = count_assigned_config_options(repaired_config_file)
    count_change = measure_change(original_config_file, repaired_config_file)

    # Record the results
    result["repaired"][bname]["assigned_config_options_count"] = count_assigned_options
    result["repaired"][bname]["change_wrt_original"] = count_change
  
  # Print the results
  logger.info("Printing the results to standard output.")
  print(json.dumps(result, sort_keys=True, indent=2))
  logger.info("All done.")

if __name__ == "__main__":
  main()
