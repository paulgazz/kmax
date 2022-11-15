import sys
import os
import argparse
import json
# import kmax.koverage.LineCoverage

argparser = argparse.ArgumentParser(description='Merge the output of koverage into a single coverage report.')
argparser.add_argument("-o", "--output",
    type=str,
    help="""Optional output path.  If not provided, output will go to stdout.""")
argparser.add_argument('coverage_files', nargs='+',
                       help='A list of one or more coverage reports from the koverage tool.')

args = argparser.parse_args()
covfiles = args.coverage_files
output = args.output


def linelist_to_linedict(linelist):
    linedict = {}
    for elem in linelist:
        linenum = elem[0]
        status = elem[1]
        assert linenum not in linedict.keys()
        linedict[linenum] = status
    return linedict

def linedict_to_linelist(linedict):
    return [ [linenum, linedict[linenum]] for linenum in linedict.keys() ]


def merge_status(a, b):
    # TODO: connect to koverage tool
    status_to_rank = { 'INCLUDED': 1,
                       'LINE_EXCLUDED_FILE_INCLUDED': 2,
                       'FILE_EXCLUDED': 3,
                       'TIMEOUT_MAKE_OLDDEFCONFIG': 4,
                       'TIMEOUT_MAKE': 5 }
    rank_to_status = dict([ (value, key) for key, value in status_to_rank.items() ])
    assert a in status_to_rank.keys()
    assert b in status_to_rank.keys()
    new_status = min(status_to_rank[a], status_to_rank[b])
    return rank_to_status[new_status]


merged = {}
for covfile in covfiles:
    if os.path.exists(covfile):
        with open(covfile, 'r') as f:
            coverage = json.load(f)
            for filetype in coverage.keys():
                if filetype not in merged.keys():
                    merged[filetype] = {}
                for fname in coverage[filetype].keys():
                    if fname not in merged[filetype].keys():
                        merged[filetype][fname] = coverage[filetype][fname]
                    else:
                        oldlinedict = linelist_to_linedict(merged[filetype][fname])
                        newlinedict = linelist_to_linedict(coverage[filetype][fname])
                        for linenum in newlinedict.keys():
                            if linenum not in oldlinedict.keys():
                                oldlinedict[linenum] = newlinedict[linenum]
                            else:
                                oldstatus = oldlinedict[linenum]
                                newstatus = newlinedict[linenum]
                                newlinedict[linenum] = merge_status(oldstatus, newstatus)
                        merged[filetype][fname] = linedict_to_linelist(newlinedict)

output_file = open(output, 'w') if output is not None else sys.stdout
json.dump(merged, output_file, sort_keys=True, indent=2)
output_file.write('\n')

