## Summarize for all:
# python3 summarize_coverage.py --validation-results validation/ --patch-tags tags/ --patch-conditions pconds/
## Summarize for a single patch/experiment:
# python3 summarize_coverage.py --validation-results validation/ --patch-tags tags/ --patch_conditions pconds/ --summarize-one-patch 2883-514ef77607b9 --summarize-one-experiment allyesconfig

# Results are drawn to coverage.pdf. Delete coverage.pickle to recompute summary.
# If summarized for a single patch/experiment, the results is written to stdout.

from enum import Enum
from enum import IntEnum
import sys
import os
import json
import numpy as np
import matplotlib.pyplot as plt
import matplotlib
from collections import defaultdict
import pickle
import argparse

class BasicLogger:
  """A simple logger."""
  def __init__(self, quiet=False, verbose=False, flush=True):
    assert (not (quiet and verbose))
    self.quiet = quiet
    self.verbose = verbose
    self.flush = flush
  
  def __flush(self):
    if self.flush: sys.stderr.flush()

  def info(self, msg):
    if not self.quiet:
      sys.stderr.write("INFO: %s\n" % msg)
      self.__flush()
    
  def warning(self, msg):
    sys.stderr.write("WARNING: %s\n" % msg)
    self.__flush()
    
  def error(self, msg):
    sys.stderr.write("ERROR: %s\n" % msg)
    self.__flush()
    
  def debug(self, msg):
    if self.verbose:
      sys.stderr.write("DEBUG: %s\n" % msg)
      self.__flush()

logger = BasicLogger()

# these are the tags we use:
# NON_KERNEL_TAGS = {NON_C, REMOVED, MOVED_ONLY, NON_KERNEL_DIR}
# NON_X86_TAGS = {NON_X86_ARCH_DIR, NON_X86_64_C}
# HEADER_TAGS = {HEADER_H, HEADER_C}
# X86_TAGS = {X86_64_C, X86_64_C_SPECIAL_BUILD_TARGET, X86_64_C_COMPILER_ERROR, X86_64_C_SYSTEM_ISSUE}

NON_KERNEL_TAGS = {'NON_C', 'REMOVED', 'MOVED_ONLY', 'NON_KERNEL_DIR'}
NON_X86_TAGS = {'NON_X86_ARCH_DIR', 'NON_X86_64_C'}
HEADER_TAGS = {'HEADER_H', 'HEADER_C'}
X86_TAGS = {'X86_64_C', 'X86_64_C_SPECIAL_BUILD_TARGET', 'X86_64_C_COMPILER_ERROR', 'X86_64_C_SYSTEM_ISSUE'}

# Cache of patch conditions and patch tags.
# The same conditions/tags are read for each of the 6 experiments, which
# slows down the summarization due to IO. Instead, cache.
m_patch_conditions = {}
m_patch_tags = {}

def get_patch_conditions(pcond_dir, patchname):
    if patchname not in m_patch_conditions:
        pcond_file_path = os.path.join(pcond_dir, "%s.cond" % patchname)
        sys.stderr.write("%s\n" % pcond_file_path)
        if not os.path.isfile(pcond_file_path):
            # This could happen when the patch does not include anything
            # that was worth repairing, e.g., all non-kernel files.
            # However, summarize_coverage will still query the patch
            # conditions, and only determine that the patch was not
            # interesting after applying the standard coverage check
            # procedure.
            # TODO: Don't attempt to get patch conditions in the first
            # place if unnecessary to avoid assuming that non-existing
            # patch conditions belong to non-interesting patches.
            sys.stderr.write("patch conditions file cannot be found at \"%s\"\n" % pcond_file_path)
            m_patch_conditions[patchname] = None
        else:
            with open(pcond_file_path, 'r') as f:
                m_patch_conditions[patchname] = json.load(f)
    return m_patch_conditions[patchname]

def get_patch_tags(tags_dir, patchname):
    if patchname not in m_patch_tags:
        tag_file_path = os.path.join(tags_dir, "%s.tags" % patchname)
        sys.stderr.write("%s\n" % tag_file_path)
        with open(tag_file_path, 'r') as f:
            m_patch_tags[patchname] = json.load(f)
    return m_patch_tags[patchname]

# patch(patchname, tags_dir, inclusion_dir) -> set of (config, filename, line)
def get_patch(tags_dir, pcond_dir, inclusion_results, experiment, patchname):
    """
    Input:
    patchname - patchname-commitid

    Output:
    list of (config, filename, line)
      config - the basename of the config file in the patch's inclusion results or NO_REPAIR if no repair was done
      filename - relative path in the linux source
      line - the integer line number or -1 if not applicable
    """

    # retrieve all of the configs' filenames
    configs = []

    inclusion_dir = os.path.join(inclusion_results, patchname, "line_inclusion_results_" + experiment, "inclusion")
    if not os.path.exists(inclusion_dir):
        configs.append("NO_REPAIR")
    else:    
        for config in os.listdir(inclusion_dir):
            if not config.endswith(".config") and not config.endswith("configtorepair"):
                sys.stderr.write("ERROR: non-config file in config directory: %s\n" % (config))
                exit(1)
            else:
                configs.append(config)

    # opens the tag file for the patch.
    # adds the files to affected_files.
    # maps the unsupported files to lines [-1]
    # maps the supported files to their lines in the validation conditions
    affected_files = {}
    tag = get_patch_tags(tags_dir, patchname)
    for filename, tag in tag.items():
        # files with unsupported tags are ignored, since they do not need to be covered
        if (tag in NON_KERNEL_TAGS) or (tag in NON_X86_TAGS):
            pass
        # # files with unsupported tags map are ignored
        # if (tag in NON_KERNEL_TAGS) or (tag in NON_X86_TAGS):
        #     affected_files[filename] = [-1]

        # files with supported tags map to their lines in the validation conditions
        elif (tag in HEADER_TAGS) or (X86_TAGS): # supported tags
            pcond = get_patch_conditions(pcond_dir, patchname)
            if pcond is None:
                affected_files[filename] = [ -1 ]
            else:
                if filename in pcond.get("headerfile_loc", []):
                    affected_files[filename] = pcond["headerfile_loc"][filename]
                elif filename in pcond.get("sourcefile_loc", []):
                    affected_files[filename] = pcond["sourcefile_loc"][filename]
                else:
                    affected_files[filename] = [ -1 ]
        else:
            sys.stderr.write("ERROR: unknown tag in patch tags: %s\n" % (tag))
            exit(1)

    # generate all combinations of (config, filename, line), and return the set
    all_combos = set()
    for config in configs:
        for filename, lines in affected_files.items():
            for line in lines:
                all_combos.add((config, filename, line))
    return all_combos


class Coverage(IntEnum):
    LINE_COVERED = 1      # file built, line is there
    LINE_NOT_COVERED = 2  # file built, line is not there
    FILE_NOT_COVERED = 3  # file not built, not target found in error log
    BUILD_ERROR = 4       # file not built
    TIMEOUT = 5           # process was timed out while measuring coverage
    NOT_AVAILABLE = 6     # data not available in the inclusion results

def best_coverage(c1, c2):
    result = min(c1, c2)
    sys.stderr.write("min(%s, %s) = %s\n" % (c1, c2, result))
    return result

# Cache the koverage results output to avoid reading the same file over
# and over again for each line.
m_koverage_results = {}
def get_inclusion_result(validation_dir, patchname, experiment, config):
    result_key = (patchname, experiment, config)
    if result_key not in m_koverage_results:
        koverage_output_path = os.path.join(validation_dir, patchname, "line_inclusion_results_%s" % experiment, "inclusion", config)
        sys.stderr.write("%s\n" % koverage_output_path)
        with open(koverage_output_path, 'r') as f:
            m_koverage_results[result_key] = json.load(f)
    return m_koverage_results[result_key]

# covered() checks make stderr files for every patch condition line again
# if the validation was FILE_EXCLUDED. Cache.
m_does_make_err_signal_file_excluded = {}
def does_make_err_signal_file_excluded(validation_dir, patchname, experiment, config, filename):
    """
    Returns True if it finds "No rule to make target" in make's stderr
    for "filename". This means file is excluded by the config.

    Otherwise, returns False. This means it is a build error that we could
    not automatically interpret.
    """
    result_key = (patchname, experiment, config, filename)
    if result_key not in m_does_make_err_signal_file_excluded:
        scratch_dir_path = os.path.join(validation_dir, patchname, "line_inclusion_results_%s" % experiment, "scratch_dir_%s" % config)
        assert os.path.exists(scratch_dir_path)
        file_scratch_dir_path = os.path.join(scratch_dir_path, "per_srcfile", filename)
        assert os.path.exists(file_scratch_dir_path)
        make_err_log_path = os.path.join(file_scratch_dir_path, "make.stderr")

        # If "No rule to make target": FILE_NOT_COVERED
        # If not: BUILD_ERROR
        with open(make_err_log_path, 'r') as make_err_log:
            for line in make_err_log:
                if "No rule to make target" in line:
                    m_does_make_err_signal_file_excluded[result_key] = True
        # Otherwise, a build error. If build error did not
        # happen, we don't know whether config would've
        # covered. This is why we distinguish like this.
        m_does_make_err_signal_file_excluded[result_key] = False
    return m_does_make_err_signal_file_excluded[result_key]

def covered(inclusion_results, experiment, patchname, config, filename, line):
    """
    Input:
    inclusion_results - a path to the output of the validation scripts
    experiment - is the name of the experiment, e.g., "allnoconfig_krepair"
    patchname - is patchnumber-commitid
    config - is the name of the config file according to the inclusion_results naming
    filename - relative path in the linux source
    line - integer line number

    Returns:
    one of
    line is covered
    line is not covered
    file is not covered
    build error
    timed out
    data not available
    """
    # config NO_REPAIR is used when the patch has no repair attempt
    # line -1 is used when the file is unsupported (non-kernel code or x86)
    if config == "NO_REPAIR" or line == -1:
        return Coverage.NOT_AVAILABLE

    # retrieves the line inclusion checking results for the (config, file, line)
    result_file_content = get_inclusion_result(inclusion_results, patchname, experiment, config)

    # Methods to retrieve results from result file content.
    def get_all_lines(result_for_file):
        return [x[0] for x in result_for_file]
    def get_result_for_line(result_for_file, line):
        for r in result_for_file:
            if r[0] == line:
                return r[1]

    #
    # Sanity checks.
    #
    # The result can't appear in both: it is either header or
    # compilation unit. The filename and line must appear.
    if filename in result_file_content["headerfile_loc"]:
        assert filename not in result_file_content["sourcefile_loc"]
        assert line in get_all_lines(result_file_content["headerfile_loc"][filename])
    elif filename in result_file_content["sourcefile_loc"]:
        assert filename not in result_file_content["headerfile_loc"]
        assert line in get_all_lines(result_file_content["sourcefile_loc"][filename])
    else:
        # The result for the file must appear in the results.
        assert False #< Result can't be found for the file.

    #
    # Retrieve the result for the line and assign "is_header" flag.
    #
    if filename in result_file_content["headerfile_loc"]:
        is_header = True
        line_result = get_result_for_line(result_file_content["headerfile_loc"][filename], line)
    else:
        is_header = False
        line_result = get_result_for_line(result_file_content["sourcefile_loc"][filename], line)

    # koverage reports in one of these.
    assert line_result in ["INCLUDED", "LINE_EXCLUDED_FILE_INCLUDED", "FILE_EXCLUDED"]

    if line_result == "INCLUDED":
        return Coverage.LINE_COVERED
    elif line_result == "LINE_EXCLUDED_FILE_INCLUDED":
        return Coverage.LINE_NOT_COVERED
    elif line_result == "TIMEOUT_MAKE_OLDDEFCONFIG":
        return Coverage.TIMEOUT
    elif line_result == "TIMEOUT_MAKE":
        return Coverage.TIMEOUT
    elif line_result == "FILE_EXCLUDED":
        if is_header:
            return Coverage.FILE_NOT_COVERED
        else:
            # If a compilation unit is not included for compilation,
            # then we check the error logs from make.
            # "No rule to make target" means file was not included by
            # the config. Otherwise, all we know was that there is a
            # build error, and config might have included the file/line
            # which could not be determined due to the build error.

            # The below function checks for this in make's stderr, while
            # also caching the results.
            if does_make_err_signal_file_excluded(inclusion_results, patchname, experiment, config, filename):
                return Coverage.FILE_NOT_COVERED
            else:
                return Coverage.BUILD_ERROR

    assert False #< Should've returned until now.

class PatchCoverage(Enum):
    COMPLETELY_COVERED = 1
    PARTIALLY_COVERED = 2
    NOT_COVERED = 3
    HEADER_ONLY = 4
    NON_X86_ONLY = 5
    NON_KERNEL = 6
    
# experiments = [ "defconfig_krepair" ]

# patchname = "10996-2405252a680e"
# patchname = "9101-cac642c12a80"
# experiment = "allnoconfig_krepair"
# patchlist = get_patch(tags_dir, inclusion_results, experiment, patchname)
# coverage_set = set()
# for config, filename, line in patchlist:
#     print(patchname, config, filename, line)
#     coverage = covered(inclusion_results, experiment, patchname, config, filename, line)
#     print(coverage)
#     coverage_set.add(coverage)

# exit(1)

    
# patch -> set of (config, file, line)

# tags(file)
#   HEADER
#   X86
#   NON_X86

# covered(config, file, line)
# outputs
#   line is covered
#   line is not covered
#   file is not covered
#   build error
#   data not available

# completely covered =
# for all files, lines, you have at least one config where it's covered
#   covered(config, file, line) -> line is covered

# partially covered =
# not completely covered and
# there exists one config, one file, and one line that is covered
#   covered(config, file, line) -> line is covered
# and not(completely covered) (this implies it isn't "not covered")

# not covered =
# not completely covered and
# not partially covered and
# for all files, lines, you have at least one config where it's covered
#   covered(config, file, line) -> line is not covered or file is not covered or build error

# repair not run (data not available)
# covered(config, file, line) -> not available for all
# - header-only
#   covered(config, file, line) -> (line is not covered, file is not covered, build error, data not available) for all and for all files, tag(file) -> HEADER
# - non-x86_64 or dead
#   there exists files, tag(file) -> NON_X86 (including headers)

class Bar(Enum):
    COVERED = 0
    PARTIALLY_COVERED = 1
    NOT_COVERED = 2
    NON_X86_ONLY = 3
    HEADER_ONLY = 4

def get_coverage_summary_one(tags_dir, pcond_dir, inclusion_results, experiment, patchname):
    sys.stderr.write("processing %s\n" % (patchname))
    patchlist = get_patch(tags_dir, pcond_dir, inclusion_results, experiment, patchname)
    logger.info("patchlist is: %s" % patchlist)
    # get line coverage set
    config_coverage_set = {}
    print(patchlist)
    for config, filename, line in patchlist:
        # print(patchname, config, filename, line)
        coverage = covered(inclusion_results, experiment, patchname, config, filename, line)
        print(coverage)
        # find the best coverage by any one config
        if (filename, line) not in config_coverage_set.keys():
            config_coverage_set[(filename, line)] = Coverage.NOT_AVAILABLE
        config_coverage_set[(filename, line)] = best_coverage(config_coverage_set[(filename, line)], coverage)
    sys.stderr.write("config_coverage_set: %s\n" % (str(config_coverage_set)))
    coverage_set = set(config_coverage_set.values())
    sys.stderr.write("coverage_set: %s %s %s\n" % (experiment, patchname, coverage_set))

    def categorize_patch_coverage(coverage_set):
        tags = get_patch_tags(tags_dir, patchname)
        sys.stderr.write("tag_set: %s %s %s\n" % (experiment, patchname, tags))

        # get unique tags to help classification
        tagset = set(tags.values())

        # remove files with non kernel tags as they will be ignored
        tagset = tagset - NON_KERNEL_TAGS

        # all files fall into non kernel
        if not tagset:
            return PatchCoverage.NON_KERNEL

        # all files fall into header only
        elif tagset <= HEADER_TAGS:
            return PatchCoverage.HEADER_ONLY

        # all files fall into non x86
        elif tagset <= (NON_X86_TAGS.union(HEADER_TAGS)):
            return PatchCoverage.NON_X86_ONLY

        # at least one file is tagged as X86
        elif not tagset.isdisjoint(X86_TAGS):

            # patch with X86_64_C_SYSTEM_ISSUE only or with headers only are considered fail
            if (tagset - HEADER_TAGS) == {'X86_64_C_SYSTEM_ISSUE'}:
                return PatchCoverage.NOT_COVERED

            # all files and lines are supported by krepair
            elif tagset <= ((X86_TAGS | HEADER_TAGS) - {'X86_64_C_SYSTEM_ISSUE'}) and len(coverage_set) == 1 and Coverage.LINE_COVERED in coverage_set:
                return PatchCoverage.COMPLETELY_COVERED
            # at least one line covered
            else:
                sys.stderr.write("partial_or_no_coverage: %s %s %s %s\n" % (experiment, patchname, tagset, coverage_set))
                if Coverage.BUILD_ERROR in coverage_set or Coverage.NOT_AVAILABLE in coverage_set:
                    sys.stderr.write("build_error_or_missing: %s %s %s\n" % (experiment, patchname, coverage_set))
                if Coverage.LINE_COVERED in coverage_set:
                    return PatchCoverage.PARTIALLY_COVERED
                else:
                    return PatchCoverage.NOT_COVERED
            # # no lines covered due to file or line not covered
            # elif Coverage.LINE_NOT_COVERED in coverage_set or Coverage.FILE_NOT_COVERED in coverage_set:
            #       return PatchCoverage.NOT_COVERED_CONFIG
            # # missing data
            # elif len(coverage_set) == 1 and Coverage.NOT_AVAILABLE in coverage_set:
            #       return PatchCoverage.NOT_COVERED_MISSING
            # # no lines covered due to build error
            # elif Coverage.BUILD_ERROR in coverage_set:
            #       return PatchCoverage.NOT_COVERED_BUILD_ERROR
            # else:
            #       sys.stderr.write("unexpected coverage set: %s\n" % (coverage_set))
            #       exit(1)
        else:
            sys.stderr.write("unexpected tagset: %s\n" % (tagset))
            exit(1)
    patch_coverage = categorize_patch_coverage(coverage_set)
    return patch_coverage

def get_coverage_summary(tags_dir, pcond_dir, inclusion_results):
    experiments = [ "allnoconfig_before",
                    "allnoconfig_after",
                    "defconfig_before",
                    "defconfig_after",
                    "randconfig_before",
                    "randconfig_after",
                    "allyesconfig_before",
                    "allyesconfig_after" ]
    results = {}
    for experiment in experiments:
        results[experiment] = defaultdict(int)
        for tag_file in os.listdir(tags_dir):
            if tag_file.endswith('.tags'):
                patchname = os.path.splitext(os.path.basename(tag_file))[0]
                patch_coverage = get_coverage_summary_one(tags_dir, pcond_dir, inclusion_results, experiment, patchname)
                sys.stderr.write("patch_coverage: %s %s %s\n" % (experiment, patchname, patch_coverage))
                if patch_coverage == PatchCoverage.COMPLETELY_COVERED:
                    results[experiment][Bar.COVERED] += 1
                elif patch_coverage == PatchCoverage.PARTIALLY_COVERED:
                    results[experiment][Bar.PARTIALLY_COVERED] += 1
                elif patch_coverage == PatchCoverage.NOT_COVERED:
                    results[experiment][Bar.NOT_COVERED] += 1
                elif patch_coverage == PatchCoverage.HEADER_ONLY:
                    results[experiment][Bar.HEADER_ONLY] += 1
                elif patch_coverage == PatchCoverage.NON_X86_ONLY:
                    results[experiment][Bar.NON_X86_ONLY] += 1
                elif patch_coverage == PatchCoverage.NON_KERNEL:
                    # no need to even plot non-kernel-only code
                    pass
                else:
                    sys.stderr.write("unknown patch coverage enum value: %s\n" % (patch_coverage))
                    exit(1)
            else:
                sys.stderr.write("ignoring non-tag file %s\n" % (tag_file))
    return results
    
# # chart formatting info
# category_names = {}
# category_names[Bar.COVERED] = "Covered"
# category_names[Bar.PARTIALLY_COVERED] = "Partially covered"
# category_names[Bar.NOT_COVERED] = "Not covered"
# category_names[Bar.NON_X86_ONLY] = "Non-x86"
# category_names[Bar.HEADER_ONLY] = "Header only"

# category_colors = {}
# category_colors[Bar.COVERED] = "honeydew"
# category_colors[Bar.PARTIALLY_COVERED] = "lightyellow"
# category_colors[Bar.NOT_COVERED] = "mistyrose"
# category_colors[Bar.NON_X86_ONLY] = "lightblue"
# category_colors[Bar.HEADER_ONLY] = "violet"

# category_patterns = {}
# category_patterns[Bar.COVERED] = ""
# category_patterns[Bar.PARTIALLY_COVERED] = "-"
# category_patterns[Bar.NOT_COVERED] = "/"
# category_patterns[Bar.NON_X86_ONLY] = "|"
# category_patterns[Bar.HEADER_ONLY] = "x"
# # "+"
# # "."


# category_names = ['Covered', 'Partially covered',  'Not covered', 'Build error', 'Non-x86', 'Header only' ]
category_names = ['Covered', 'Partially covered',  'Not covered', 'Non-x86', 'Header only' ]

# category_colors = ['honeydew', 'lightyellow', 'mistyrose', 'mistyrose', 'mistyrose', 'lightblue' ]
# category_colors = ['honeydew', 'lightyellow', 'mistyrose', 'mistyrose', 'lightgray', 'lightblue' ]
# category_colors = ['green', 'yellow', 'red', 'mistyrose', 'lightgray', 'lightblue' ]
# category_colors = ['lightgreen', 'lightyellow', 'mistyrose', 'lightpink', 'lightgray', 'lightblue' ]
# category_colors = ['#00DD00', '#DDDD00', '#DD0000', 'pink', 'lightgray', 'lightblue' ]
# category_colors = ['lightgreen', 'lightyellow', 'lightpink', 'mistyrose', 'lightgray', 'lightblue' ]
# category_colors = ['lightgreen', 'cornsilk', 'mistyrose', '#fce3e3', 'lightgray', 'lightblue' ]
# category_colors = ['#5ee35c', 'lightyellow', 'lightpink', 'mistyrose', 'lightgray', 'lightblue' ]
category_colors = ['#5ee35c', 'lightyellow', 'mistyrose', 'lightgray', 'lightblue' ]


# category_patterns = ['', '-', '/', '|', 'x', '+', '.']
category_patterns = ['', '', '', '', '', '', '']

toosmall = [ "*", "†", "‡", "§", "||", "#", "*", "*" ]

labels = ['allnoconfig', 'before', 'after'] \
    + ['defconfig', 'before', 'after'] \
    + ['randconfig', 'before', 'after']

def format_label(c):
    return "{:,}".format(c)

# draw bar chart
def coverage(results, reference_data):
    # each config type gets one subplot
    fig, axes = plt.subplots(ncols=1, nrows=4, sharex='all',
                             figsize=(12, 5))
    fig.tight_layout()

    # space between config type bars
    plt.subplots_adjust(hspace= 0)
    # pattern line width
    plt.rcParams['hatch.linewidth'] = 0.1

    # before and after bars y position within [0,1] range
    ypos = [.3, .7]
    # bar width
    bheight = 0.3

    numsmall = 0

    # each ax have one config file.
    for i, (ax, res) in enumerate(zip(axes, results)):
        # TODO: we have more axes than results, how does it affect the loop?
        labels = results[res].keys() # before, after
        data = np.array(list(results[res].values()))
        data_cum = data.cumsum(axis=1)

        ax.invert_yaxis()
        #ax.xaxis.set_visible(False)
        total_patches = np.sum(data, axis=1).max()
        total_tested = sum(data[0][0:3])
        sys.stderr.write("total_patches: %d\n" % (total_patches))
        ax.set_xlim(0, np.sum(data, axis=1).max())
        ax.set_ylim(1, 0)

        ax.set_yticks(ypos)
        ax.set_yticklabels(labels, fontsize='large')
        ax.tick_params(axis='both', which='major', labelsize='large')

        increment = 2500
        xticks = [ increment * x for x in range(0, int(total_patches / increment + 1)) ] + [ total_patches ]
        xtickslabels = [ format_label(tick) for tick in xticks ]
        ax.set_xticks(xticks, xtickslabels, minor=True)
        xticks = [ total_tested ]
        xtickslabels = [ format_label(tick) for tick in xticks ]
        ax.set_xticks(xticks, xtickslabels, minor=False)
        ax.grid(axis='x', which='major')

        # remove subplot borders
        ax.spines['bottom'].set_visible(False)
        ax.spines['top'].set_visible(False)
        ax.spines['left'].set_visible(False)
        ax.spines['right'].set_visible(False)

        for start, (colname, color, pattern) in enumerate(zip(category_names, category_colors, category_patterns)):
            # draw bars
            widths = data[:, start]
            starts = data_cum[:, start] - widths
            ax.barh(ypos, widths, left=starts, height=bheight,
                    label=colname, color=color, hatch=pattern, edgecolor='black')

            # add numbers to bars
            xcenters = starts + widths / 2
            r, g, b = matplotlib.colors.to_rgb(color)
            text_color = 'black'
            for y, (x, c) in enumerate(zip(xcenters, widths)):
                if c > 400:
                    label = format_label(int(c))
                else:
                    label = toosmall[numsmall]
                    sys.stderr.write("footnote: %s %d\n" % (label, c))
                    numsmall += 1
                textlabel = ax.text(x, ypos[y], label, ha='center', va='center',
                        bbox=dict(boxstyle='square,pad=0.2', fc=color, ec='none'),
                                    fontsize='medium', color=text_color) # color=text_color)
                # textlabel.set_alpha(.5)

        # draw axis titles
        ax.set_ylabel(res, fontsize='large')

        # draw legends
        if i == 0:
            ax.legend(ncol=len(category_names), bbox_to_anchor=(0, 1),
                      loc='lower left', fontsize='large')

    # draw reference data
    ypos = [.5]

    if reference_data:
        # res used to have before, after keys
        ax = axes[-1] # reference goes to the last axis
        res = reference_data
        assert len(reference_data) == 1
        label = list(reference_data.keys())[0]
        data = np.array(list(reference_data.values()))
        data_cum = data.cumsum(axis=1)

        ax.invert_yaxis()
        #ax.xaxis.set_visible(False)
        total_patches = np.sum(data, axis=1).max()
        total_tested = sum(data[0][0:3])
        sys.stderr.write("total_patches: %d\n" % (total_patches))
        ax.set_xlim(0, np.sum(data, axis=1).max())
        ax.set_ylim(1, 0)

        ax.set_yticks(ypos)
        ax.set_yticklabels([label], fontsize='large') # TODO: make one label only
        ax.tick_params(axis='both', which='major', labelsize='large')

        increment = 2500
        xticks = [ increment * x for x in range(0, int(total_patches / increment + 1)) ] + [ total_patches ]
        xtickslabels = [ format_label(tick) for tick in xticks ]
        ax.set_xticks(xticks, xtickslabels, minor=True)
        xticks = [ total_tested ]
        xtickslabels = [ format_label(tick) for tick in xticks ]
        ax.set_xticks(xticks, xtickslabels, minor=False)
        ax.grid(axis='x', which='major')

        # remove subplot borders
        ax.spines['bottom'].set_visible(False)
        ax.spines['top'].set_visible(False)
        ax.spines['left'].set_visible(False)
        ax.spines['right'].set_visible(False)

        for start, (colname, color, pattern) in enumerate(zip(category_names, category_colors, category_patterns)):
            # draw bars
            widths = data[:, start]
            starts = data_cum[:, start] - widths
            ax.barh(ypos, widths, left=starts, height=bheight,
                    label=colname, color=color, hatch=pattern, edgecolor='black')

            # add numbers to bars
            xcenters = starts + widths / 2
            r, g, b = matplotlib.colors.to_rgb(color)
            text_color = 'black'
            for y, (x, c) in enumerate(zip(xcenters, widths)):
                if c > 400:
                    label = format_label(int(c))
                else:
                    label = toosmall[numsmall]
                    sys.stderr.write("footnote: %s %d\n" % (label, c))
                    numsmall += 1
                textlabel = ax.text(x, ypos[y], label, ha='center', va='center',
                        bbox=dict(boxstyle='square,pad=0.2', fc=color, ec='none'),
                                    fontsize='medium', color=text_color) # color=text_color)
                # textlabel.set_alpha(.5)

        # draw axis titles
#        ax.set_ylabel(res, fontsize='large')
        ax.set_xlabel('Number of Patches', fontsize='large')

        # draw legends
        if i == 0:
            ax.legend(ncol=len(category_names), bbox_to_anchor=(0, 1),
                      loc='lower left', fontsize='large')

    axes[-1].set_xlabel('Number of Patches', fontsize='large')


    return fig, axes


def graph_coverage(results, output_coverage_graph_file):
    print(results)

    graph_data = {
        'allnoconfig':{'before': [ results["allnoconfig_before"][Bar.COVERED],
                                   results["allnoconfig_before"][Bar.PARTIALLY_COVERED],
                                   results["allnoconfig_before"][Bar.NOT_COVERED],
                                   results["allnoconfig_before"][Bar.NON_X86_ONLY],
                                   results["allnoconfig_before"][Bar.HEADER_ONLY] ],
                       'after':  [ results["allnoconfig_after"][Bar.COVERED],
                                   results["allnoconfig_after"][Bar.PARTIALLY_COVERED],
                                   results["allnoconfig_after"][Bar.NOT_COVERED],
                                   results["allnoconfig_after"][Bar.NON_X86_ONLY],
                                   results["allnoconfig_after"][Bar.HEADER_ONLY] ]},
        'defconfig':{'before':   [ results["defconfig_before"][Bar.COVERED],
                                   results["defconfig_before"][Bar.PARTIALLY_COVERED],
                                   results["defconfig_before"][Bar.NOT_COVERED],
                                   results["defconfig_before"][Bar.NON_X86_ONLY],
                                   results["defconfig_before"][Bar.HEADER_ONLY] ],
                       'after':  [ results["defconfig_after"][Bar.COVERED],
                                   results["defconfig_after"][Bar.PARTIALLY_COVERED],
                                   results["defconfig_after"][Bar.NOT_COVERED],
                                   results["defconfig_after"][Bar.NON_X86_ONLY],
                                   results["defconfig_after"][Bar.HEADER_ONLY] ]},
        'randconfig':{'before':  [ results["randconfig_before"][Bar.COVERED],
                                   results["randconfig_before"][Bar.PARTIALLY_COVERED],
                                   results["randconfig_before"][Bar.NOT_COVERED],
                                   results["randconfig_before"][Bar.NON_X86_ONLY],
                                   results["randconfig_before"][Bar.HEADER_ONLY] ],
                       'after':  [ results["randconfig_after"][Bar.COVERED],
                                   results["randconfig_after"][Bar.PARTIALLY_COVERED],
                                   results["randconfig_after"][Bar.NOT_COVERED],
                                   results["randconfig_after"][Bar.NON_X86_ONLY],
                                   results["randconfig_after"][Bar.HEADER_ONLY] ]},
    }

    reference_data = {
        'allyesconfig': [ results["allyesconfig_before"][Bar.COVERED],
                          results["allyesconfig_before"][Bar.PARTIALLY_COVERED],
                          results["allyesconfig_before"][Bar.NOT_COVERED],
                          results["allyesconfig_before"][Bar.NON_X86_ONLY],
                          results["allyesconfig_before"][Bar.HEADER_ONLY] ]
    }
    
    coverage(graph_data, reference_data)

    plt.savefig(output_coverage_graph_file, bbox_inches='tight')

def main():
    # description
    argparser = argparse.ArgumentParser(description=
    """Summarize the coverage from given validation results."""
    """ Outputs a pdf where the results are drawn.""")
    # validation results
    argparser.add_argument("--validation-results",
        type=str,
        required=True,
        help="""Path to the directory of validation results.""")
    # patch tags
    argparser.add_argument("--patch-tags",
        type=str,
        required=True,
        help="""Path to the directory of patch tags.""")
    # patch conditions
    argparser.add_argument("--patch-conditions",
        type=str,
        required=True,
        help="""Path to the directory of patch conditions.""")
    # summary pickle
    argparser.add_argument("--summary-pickle",
        type=str,
        help="""Path to the coverage summary pickle file.  If the file"""
        """ exists, the script will read the summary from the pickle file"""
        """ instead of computing it from the validation results.  Otherwise,"""
        """ it will create a summary file at the specified path, computed from"""
        """ the validation results.  Defaults to \"coverage.pickle\".""",
        default="coverage.pickle")
    # output coverage graph
    argparser.add_argument("--output-coverage-graph",
        type=str,
        help="""Path to the output coverage graph pdf."""
        """ Defaults to \"coverage.pdf\".""",
        default="coverage.pdf")
    # summarize one patch (optional)
    argparser.add_argument("--summarize-one-patch",
        type=str,
        required=False,
        help="""Name of the patch to summarize (ID-COMMITID)."""
        """ If specified, the script goes into single summarization mode,"""
        """ and prints the results for the specific patch/experiment only."""
        """ --summarize-one-experiment must also be specified.""")
    # summarize one experiment (optional)
    argparser.add_argument("--summarize-one-experiment",
        type=str,
        required=False,
        help="""Name of the experiment to use while summarizing for a"""
        """ single patch (allnoconfig/defconfig/allyesconfig/randconfig)."""
        """ If specified, the script goes into single summarization mode,"""
        """ and prints the results for the specific patch/experiment only."""
        """ --summarize-one-patch must also be specified.""")

    #
    # Parse arguments
    #
    args = argparser.parse_args()
    validation_results_dir = args.validation_results
    patch_tags_dir = args. patch_tags
    patch_conditions_dir = args.patch_conditions
    summary_pickle_file = args.summary_pickle
    output_coverage_graph_file = args.output_coverage_graph
    summarize_one_patch = args.summarize_one_patch
    summarize_one_experiment = args.summarize_one_experiment

    #
    # Check arguments
    #
    def check_dir(dirpath, dirname):
        if not os.path.isdir(dirpath):
            logger.error("Cannot find %s directory at \"%s\"." % (dirname, dirpath))
            exit(-1)
    check_dir(validation_results_dir, "validation_results")
    check_dir(patch_tags_dir, "patch_tags")
    check_dir(patch_conditions_dir, "patch_conditions")
    if os.path.isdir(summary_pickle_file):
        logger.error("--summary-pickle can't be path to a directory (%s)." % summary_pickle_file)
        exit(-1)
    
    #
    # Summarize one (if specified)
    #
    if not summarize_one_patch and not summarize_one_experiment:
        summarize_one = False
    else:
        assert summarize_one_patch or summarize_one_experiment
        if not summarize_one_patch or not summarize_one_experiment:
            logger.error("--summarize-one-patch and --summarize-one-experiment must be specified together.")
            exit(-1)
        else:
            summarize_one = True
    if summarize_one:
        logger.info("Summarizing for a single patch/experiment only.")
        patch_coverage = get_coverage_summary_one(patch_tags_dir, patch_conditions_dir, validation_results_dir, summarize_one_experiment, summarize_one_patch)
        print("patch_coverage: %s %s %s" % (summarize_one_experiment, summarize_one_patch, patch_coverage))
        return
    assert not summarize_one #< summarize_one must've returned until now

    #
    # Compute the summary, or load from the summary pickle if exists
    #
    summary = None
    if os.path.isfile(summary_pickle_file):
        logger.warning(
            "Reusing the existing summary pickle at \"%s\" instead of"
            " summarizing from scratch. Delete to recompute.")
        with open(summary_pickle_file, 'rb') as f:
            summary = pickle.load(f)
    else:
        # Compute summary from scratch
        logger.info("Computing the coverage summary.")
        summary = get_coverage_summary(patch_tags_dir, patch_conditions_dir, validation_results_dir)
        # Write the coverage summary
        logger.info("Finished computing the coverage summary.")
        logger.info("Writing the summary pickle to \"%s\"." % summary_pickle_file)
        with open(summary_pickle_file, 'wb') as f:
            pickle.dump(summary, f)
    assert summary

    #
    # Draw the graph
    #
    logger.info("Drawing the summary graph to \"%s\"." % output_coverage_graph_file)
    graph_coverage(summary, output_coverage_graph_file)
    logger.info("All done.")

if __name__ == "__main__":
    main()
