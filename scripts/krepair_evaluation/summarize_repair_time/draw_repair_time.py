from pylab import *
import json
import argparse
import os
import sys

import matplotlib.pyplot as plt
import numpy as np
import matplotlib.ticker as mtick

# Dummy dataset
np.random.seed(10)
data_1 = np.random.beta(1, 5, 12000) * 600
data_2 = np.random.beta(2, 5, 12000) * 600
data_3 = np.random.beta(3, 5, 12000) * 600
dummy_data = [data_3,data_2,data_1]


# read files describing repair time for each patch.
# timedir is expected to have one directory per patch, which is named after each patch.
# in each patch directory is a a directory named after the config that was repaired.
# in each config directory is a gen_patch_files.txt
def read_time(patches, config):
    # will store a mapping of "patch": {"gen_patch_files": time_in_sec, "loc_patch_configs": time_in_sec}
    repair_times = {}

    # iterate through each patch directory
    for patch_dir in os.listdir(patches):
        repair_times[patch_dir] = {}
        # read gen_patch_files time
        gen_patch_files = os.path.join(patches, patch_dir, config + "_configs", "timings", "gen_patch_files.out")
        loc_patch_configs = os.path.join(patches, patch_dir, config + "_configs", "timings", "loc_patch_configs.out")
        # NOTE: these time files are currently allowed to not exist, because we have missing data, and need partial results.
        # TODO: uncomment all of the exit() statements once we have complete data.

        # check if the time file exists.
        if not os.path.isfile(gen_patch_files):
            sys.stderr.write("gen_patch_files time file is missing for: " + patch_dir + '\n')
            # we currently allow missing times if krepair produced no configs
            #exit(1)
        elif not os.path.isfile(loc_patch_configs):
            sys.stderr.write("gen_patch_files has a time file, but loc_patch_configs does not for patch: " + patch_dir + '\n')
            #exit(1)

        else:
            # get the time from gen_patch_files
            with open(gen_patch_files, 'r') as f:
                time = f.readlines()
                if time == []:
                    sys.stderr.write("gen_patch_files time file exists but is empty. Check patch " + patch_dir + '\n')
                    #exit(1)
                elif "Command exited with non-zero status 1" in time[0]:
                    sys.stderr.write("patch time has an error message. Check patch " + patch_dir + '\n')
                    #exit(1)

                    # NOTE: we are currently ignoring the error message in the timing output.
                    for num, line in enumerate(time):
                        if num == 1:
                            loc_configs_time = float(line)
                            repair_times[patch_dir].update({"loc_patch_configs": loc_configs_time})
                else:
                    gen_files_time = float(time[0])
                    repair_times[patch_dir].update({"gen_patch_files": gen_files_time})

            # get the time from loc_patch_configs
            with open(loc_patch_configs, 'r') as f:
                time = f.readlines()
                if time == []:
                    sys.stderr.write("loc_patch_configs time file exists but is empty. Check patch " + patch_dir + '\n')
                    #exit(1)
                elif "Command exited with non-zero status 1" in time[0]:
                    sys.stderr.write("patch time has an error message. Check patch " + patch_dir + '\n')
                    #exit(1)

                    # NOTE: we are currently ignoring the error message in the timing output.
                    for num, line in enumerate(time):
                        if num == 1:
                            loc_configs_time = float(line)
                            repair_times[patch_dir].update({"loc_patch_configs": loc_configs_time})
                else:
                    loc_configs_time = float(time[0])
                    repair_times[patch_dir].update({"loc_patch_configs": loc_configs_time})
    return repair_times


# takes all of the data as nested dictionary for one experiment.
# example input dictionary: {"patchname": {"gen_patch_files": time_as_float, "loc_patch_configs": time_as_float}}
# simplifies the data by summing up the gen_patch_files and loc_patch_configs times for each patch.
# returns this as a list, containing each time.
def sum_times(time_dict):
    summed_times = []
    for patch, times in time_dict.items():
        # NOTE: these time files are currently allowed to not exist, because we have missing data, and need partial results.
        # TODO: uncomment all of the exit() statements once we have complete data.
        if "gen_patch_files" not in times:
            sys.stderr.write("gen_patch_files time does not exist. Check patch " + patch + '\n')
            #exit(1)
        elif "loc_patch_configs" not in times:
            sys.stderr.write("loc_patch_configs time does not exist. Check patch " + patch + '\n')
            #exit(1)
        else:
            summed_times.append(times["gen_patch_files"] + times["loc_patch_configs"])
    return summed_times


# draw box plot based on repair sizes from all 3 config types
def draw_sizes(results):
    """
    results is a dictionary
    { "configname" : [time1, time2, ..] }
    """
    # create figure
    fig, ax = plt.subplots(figsize=(5, 2.5))
    fig.tight_layout()
    ax.set_ylim([0, 1]) # manual y limit to force the boxplot position
    # NOTE: positions of plots and texts are manually set.
    #       I tried some built in methods but they were not flexible enough
    percentiles = [0,10,20,25,30,40,50,60,70,75,80,90,99,100]
    for c in results:
       print("\n%s percentile(percentile:val): %s" % (c, list(zip(percentiles, np.percentile(results[c], percentiles)))))
       print("max is: %s" % max(results[c]))
       print("min is: %s" % min(results[c]))
 

    confignames = list(results.keys())
    times = [results[c] for c in confignames]
    times.reverse()
    medians = []

    # draw box plot, with only median shown
    bp = ax.boxplot(times, sym='|', whis=0, showcaps=True, vert=False, positions=[0.17,0.47,0.77], widths=0.09)

    # draw axis labels - use text instead of set_ytick_label to save space
    # TODO: this could be done in a loop but fig was set in certain positions for some reason, so necip is not fixing this now
    fig.text(0.5, -0.05, 'Time to repair [s]', ha='center', rotation='horizontal', size='large')
    fig.text(-0.1, 0.75, confignames[0], va='center', rotation='horizontal', size='large')
    fig.text(-0.07, 0.50, confignames[1], va='center', rotation='horizontal', size='large')
    fig.text(-0.095, 0.28, confignames[2], va='center', rotation='horizontal', size='large')
    ax.yaxis.set_visible(False)

    # add a legend to label the median
    plt.legend([bp["medians"][0]], ["median"], fontsize="medium")

    # add value text to median
    for median in bp["medians"]:
        x, y = median.get_xydata()[1]
        text(x, y + 0.02, '%.1f' % x, horizontalalignment='center', size='large')

    plt.xticks(fontsize="large")

    # Add major gridlines in the y-axis
    ax.grid(color='grey', axis='x', linestyle='-', linewidth=0.25, alpha=0.5)

    # use commas for values in the thousands
    ax.xaxis.set_major_formatter(mtick.StrMethodFormatter('{x:,.0f}'))


'''
Read repair time json files and create a box plot
Usage: python3 draw_repair_time.py --allnoconf <allno> --defconf <def> --allyesconf <allyes> --out <outpdf>
Input:  directory of json files describing the repair time per patch, for each config type
Output: pdf file of the box plot

'''
def old_main():
    # parse arguments
    argparser = argparse.ArgumentParser()
    argparser.add_argument("--allnoconf",
                           type=str,
                           required=True,
                           help="Path to the directory for allnoconfig repair summary.")
    argparser.add_argument("--defconf",
                           type=str,
                           required=True,
                           help="Path to the directory for defconfig repair summary.")
    argparser.add_argument("--allyesconf",
                           type=str,
                           required=True,
                           help="Path to the directory for allyesconfig repair summary.")
    argparser.add_argument("--out",
                           type=str,
                           required=True,
                           help="Path to the file for output pdf. Should include .pdf extension")
    argparser.add_argument("--test",
                           action='store_true',
                           help="Use dummy data to play with figures")


    # all path arguments are turned into absolute paths.
    args = argparser.parse_args()
    no = os.path.abspath(args.allnoconf)
    de = os.path.abspath(args.defconf)
    ye = os.path.abspath(args.allyesconf)
    out = os.path.abspath(args.out)

    if not args.test:
        if not os.path.exists(no):
            print("ERROR: invalid allno directory")
            exit(1)
        if not os.path.exists(de):
            print("ERROR: invalid def directory")
            exit(1)
        if not os.path.exists(ye):
            print("ERROR: invalid allyes directory")
            exit(1)

        allyesconfig_data = read_time(ye, "randconfig")
        defconfig_data = read_time(de, "defconfig")
        allnoconfig_data = read_time(no, "allnoconfig")
        sum_data = [
            sum_times(allyesconfig_data),
            sum_times(defconfig_data),
            sum_times(allnoconfig_data),
            ]
        draw_sizes(sum_data)
        plt.savefig(out, bbox_inches='tight')

    else:
        draw_sizes(dummy_data)
        plt.savefig(out, bbox_inches='tight')

    sys.stdout.write("Results shown only for patches that had both a gen_patch_files time AND a loc_patch_configs time.\n")

def main():
    argparser = argparse.ArgumentParser()
    argparser.add_argument
    argparser.add_argument("--allnoc",
                           type=str,
                           required=True,
                           help="Path to file containing list of floating point time values for each allno repairs, one per line")
    argparser.add_argument("--defc",
                           type=str,
                           required=True,
                           help="Path to file containing list of floating point time values for each def repairs, one per line")
    argparser.add_argument("--randc",
                           type=str,
                           required=True,
                           help="Path to file containing list of floating point time values for each rand repairs, one per line")
    argparser.add_argument("--out",
                           type=str,
                           required=True,
                           help="Output pdf")

    args = argparser.parse_args()
    allnoc = args.allnoc
    defc = args.defc
    randc = args.randc
    out = args.out

    assert os.path.isfile(allnoc)
    assert os.path.isfile(defc)
    assert os.path.isfile(randc)

    # read the data
    def read_data(fpath):
        with open(fpath, 'r') as f:
            lines = f.readlines()
        return sorted([float(l.strip()) for l in lines])

    dat_allno = read_data(allnoc)
    dat_def = read_data(defc)
    dat_rand = read_data(randc)

    all_data = {
        "allnoconfig" : dat_allno,
        "defconfig" : dat_def,
        "randconfig" : dat_rand}
    draw_sizes(all_data)
    plt.savefig(out, bbox_inches='tight')




if __name__ == "__main__":
    main()
