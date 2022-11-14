<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [krepair evaluation scripts](#krepair-evaluation-scripts)
  - [running the evaluation](#running-the-evaluation)
  - [parallelized experiments](#parallelized-experiments)
  - [summarizing the results](#summarizing-the-results)
    - [coverage](#coverage)
    - [repair size](#repair-size)
    - [repair time](#repair-time)
- [requirements](#requirements)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# krepair evaluation scripts

## running the evaluation

```
# get a copy of the linux source
git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git linux

# extract the list of patch coverage conditions
mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
(cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist

# kick off a server providing the names of patches (designed this way to enable parallelized experiments)
java superc.util.FilenameService -server 55679 patchlist &

# run the evaluation
bash evaluation_client.sh localhost 55679 6h repair_results build_targets.json linux/ formulacache/ patchconditions/ x86_64 > evaluation_client.out 2>&1
```


## parallelized experiments

```
# clone a copy of the linux source for each experiment process
for i in {0..9}; do git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git linux$i; done

# extract the list of patch coverage conditions
mkdir patchconditions; tar -C patchconditions -xvf patchconditions.tar.gz
(cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist

# kick off a server providing the names of patches (designed this way to enable parallelized experiments)
java superc.util.FilenameService -server 55679 patchlist &

# run several evaluation processes
for i in {0..9}; do bash evaluation_client.sh localhost 55679 6h repair_results build_targets.json linux$i/ formulacache$i/ patchconditions/ x86_64 > evaluation_client$i 2>&1 & sleep 1; done
```

## summarizing the results

### coverage

```
# extract the patch tags that is used for determining the category patches and modified files in the coverage summary
mkdir patchtags; tar -C patchtags -xvf patchtags.tar.gz

# get coverage summary
python3 summarize_coverage.py --validation-results repair_results/validate/ --patch-tags patchtags/ --patch-conditions patchconditions/ |& tee coverage.log

# get repair time summary
```

### repair size

Following commands first measures repair size and creates measurement output files, then summarizes the measurements as percentiles.

Two types of measurements are collected: original configurations are compared to repaired configurations, and original configurations are compared to allyesconfig.

```
EXPERIMENTS=("allnoconfig" "defconfig" "randconfig" "allyesconfig")
mkdir -p repair_size/measurements/

# measure repair size
for exp in ${EXPERIMENTS[@]}; do
  # repair_results/validate/ is created by evaluation_client.sh
  bash summarize_repair_size/compute_from_all_results.sh repair_results/validate/ ${exp} repair_size/measurements/ |& tee repair_size/exp_repair_size.log
done


# summarize repair size measurements
for exp in ${EXPERIMENTS[@]}; do
  # original config compared to repaired configs
  find repair_size/measurements/ | grep "${exp}-repair_size.json$" > files_${exp}_repair_sizes.txt
  python3 summarize_repair_size/summarize_table_data.py --measurements-files-list files_${exp}_repair_sizes.txt |& tee repair_size/summary_${exp}_repair_sizes.txt

  # original config compared to allyesconfig
  find repair_size/measurements/ | grep "${exp}-compared_to_allyesconfig.json$" > files_${exp}_allyesconfig_comparison.txt
  python3 summarize_repair_size/summarize_table_data.py --measurements-files-list files_${exp}_allyesconfig_comparison.txt 2> repair_size/summary_${exp}_allyesconfig_comparison.txt
done

# check tail of the following files for the summaries (replace ${exp}):
#  * repair_size/summary_${exp}_repair_sizes.txt
#  * repair_size/summary_${exp}_allyesconfig_comparison.txt
```

### repair time

```
EXPERIMENTS=("allnoconfig" "defconfig" "randconfig" "allyesconfig")
mkdir -p repair_time/

# Get the data points
for exp in ${EXPERIMENTS[@]}; do
  # repair_results/repair/ is created by evaluation_client.sh
  find repair_results/repair/ | grep "timings/krepair_timing.out" | grep ${exp} | xargs cat | grep "[0-9]*\.[0-9]*" | sort -n > repair_time/${exp}.timelist
done

# Summarize in a graph
python3 summarize_repair_time/draw_repair_time.py --allnoconf repair_time/allnoconfig.timelist --defconf repair_time/defconfig.timelist --allyesconf repair_time/allyesconfig.timelist --out repairtime.pdf |& tee draw_repair_time.log
```

# requirements

* make.cross in `PATH` (cross compilation)
* libisl.so.22 in `LD_LIBRARY_PATH` (for building Linux v5.13 code)
