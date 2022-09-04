# After running compute_from_all_results.sh, run this to get paper table data.
# Run per builtin config.

## COMMANDS
## ALLNOCONFIG
# find /data2/repair_size/measurements/ | grep "allnoconfig-repair_size.json$" > files_allnoconfig_repair_sizes.txt
# python3 summarize_table_data.py --measurements-files-list files_allnoconfig_repair_sizes.txt 2> /data2/repair_size/summary_allnoconfig_repair_sizes.txt

# find /data2/repair_size/measurements/ | grep "allnoconfig-compared_to_allyesconfig.json$" > files_allnoconfig_allyesconfig_comparison.txt
# python3 summarize_table_data.py --measurements-files-list files_allnoconfig_allyesconfig_comparison.txt 2> /data2/repair_size/summary_allnoconfig_allyesconfig_comparison.txt

## DEFCONFIG
# find /data2/repair_size/measurements/ | grep "defconfig-repair_size.json$" > files_defconfig_repair_sizes.txt
# python3 summarize_table_data.py --measurements-files-list files_defconfig_repair_sizes.txt 2> /data2/repair_size/summary_defconfig_repair_sizes.txt

# find /data2/repair_size/measurements/ | grep "defconfig-compared_to_allyesconfig.json$" > files_defconfig_allyesconfig_comparison.txt
# python3 summarize_table_data.py --measurements-files-list files_defconfig_allyesconfig_comparison.txt 2> /data2/repair_size/summary_defconfig_allyesconfig_comparison.txt

## RANDCONFIG
# find /data2/repair_size/measurements/ | grep "randconfig-repair_size.json$" > files_randconfig_repair_sizes.txt
# python3 summarize_table_data.py --measurements-files-list files_randconfig_repair_sizes.txt 2> /data2/repair_size/summary_randconfig_repair_sizes.txt

# find /data2/repair_size/measurements/ | grep "randconfig-compared_to_allyesconfig.json$" > files_randconfig_allyesconfig_comparison.txt
# python3 summarize_table_data.py --measurements-files-list files_randconfig_allyesconfig_comparison.txt 2> /data2/repair_size/summary_randconfig_allyesconfig_comparison.txt

## ALLYESCONFIG
# find /data2/repair_size/measurements/ | grep "allyesconfig-repair_size.json$" > files_allyesconfig_repair_sizes.txt
# python3 summarize_table_data.py --measurements-files-list files_allyesconfig_repair_sizes.txt 2> /data2/repair_size/summary_allyesconfig_repair_sizes.txt

import argparse
import sys
import os
import json
import numpy

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

logger = BasicLogger()

def main():
  argparser = argparse.ArgumentParser()

  argparser.add_argument("--measurements-files-list",
    type=str,
    required=True,
    help="""File containing paths to .json measurement files, one per line.  """
         """For example, to get this file for allnoconfig before/after repair, """
         """run \"find | grep \".*allnoconfig-repair_size.json\" > inp.txt\" """
         """inside output directory of compute_from_all_results.sh""")

  args = argparser.parse_args()
  files_list = args.measurements_files_list

  logger.info("Results will include non-zero repairs only (no measurements if repair failed).")
  with open(files_list, 'r') as f:
    m_files = [x.strip() for x in f.readlines()]
  logger.info("%s measurement files are listed." % len(m_files))

  # validate that files exist
  for m in m_files:
    logger.info("checking %s" % m)
    assert os.path.isfile(m)
  
  repaired_counts = []
  repair_sizes = []

  for m in m_files:
    with open(m, 'r') as f:
      measurement = json.load(f)
    assert measurement['repaired'] #< input doesn't contain zero repairs

    repaired_counts.append(len(measurement['repaired']))

    for cfgfile in measurement['repaired']:
      repair_sizes.append(int(measurement['repaired'][cfgfile]["change_wrt_original"]))
  
  logger.info("Done with collecting the results, now printing the stats.")
  percentiles = [0,25,50,75,99,100]
  logger.info("repair_sizes percentiles(%s): %s" % (percentiles, list(numpy.percentile(repair_sizes, percentiles))))
  logger.info("repaired_counts percentiles(%s): %s" % (percentiles, list(numpy.percentile(repaired_counts, percentiles))))
  
if __name__ == '__main__':
  main()
