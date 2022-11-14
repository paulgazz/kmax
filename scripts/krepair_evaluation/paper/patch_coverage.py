import sys
import os
import argparse
import json
# import kmax.koverage.LineCoverage

# example: ls -d outdir_many9/*/defconfig/results/koverage_outfile | while read i; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/patch_coverage.py $i; done | sort -h -t' ' -k4 | tee krepair.coverag

# example: ls -d randconfig_total/* | while read i; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/patch_coverage.py $i; done | sort -h -t' ' -k4 | tee randconfig.coverage


argparser = argparse.ArgumentParser(description='Compute the ratio of lines in the patch that are covered.  Ouput is in the format "patch_coverage covered_lines total_lines ratio"')
argparser.add_argument('coverage_file',
                       help='A more coverage report from the koverage tool.')

args = argparser.parse_args()
covfile = args.coverage_file

total_lines = 0
covered_lines = 0
if os.path.exists(covfile):
    with open(covfile, 'r') as f:
        coverage = json.load(f)
        for filetype in coverage.keys():
            for fname in coverage[filetype].keys():
                for elem in coverage[filetype][fname]:
                    linenum = elem[0]
                    status = elem[1]
                    # TODO: connect to koverage tool
                    total_lines += 1
                    if status == 'INCLUDED':
                        covered_lines += 1

print("patch_coverage %d %d %f" % (covered_lines, total_lines, covered_lines / total_lines))
