<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Intro](#intro)
- [Measuring the changes](#measuring-the-changes)
- [How to run for a single case](#how-to-run-for-a-single-case)
- [Output format](#output-format)
- [Measuring repair size for all patches](#measuring-repair-size-for-all-patches)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Intro
`krepair` repairs given configuration files to cover patches. The amount of change on the original configuration file is an important metric since the user wants to preserve the settings from the original configuration file as much as possible.

Followings describe how to get the configurations generated during `krepair` evaluation experiments, and how to use the measurement scripts to measure the changes between the original and repaired configurations.

# Measuring the changes
Given an original and repaired configuration, the key commands to capture the change count are as follows:
```
# Assume orig.config, repaired.config, commit_id, linux_src

# Run olddefconfig on the repaired configuration
# This must be done before measuring changes.
cd $linux_src
git checkout -f $commit_id
KCONFIG_CONFIG=repaired.config make.cross ARCH=x86_64 olddefconfig

# Count the changes
comm <(grep "^CONFIG" orig.config | sort) <(grep "^CONFIG" repaired.config | sort) -3 | wc -l
```

# How to run for a single case
A single case is: an original configuration and zero or more repaired configurations.

`measure_change.py` measures the change for a single case. Usage is as follows:
```
usage: measure_change.py [-h] --original-config ORIGINAL_CONFIG [repaired_configs [repaired_configs ...]]
```

For example:
```
python3 measure_change.py --original-config original.config repaired1.config repaired2.config
```

The output is a json file printed in stdout (in bash, capture with `>`). Note that stderr contains log messages, so don't mix stdout and stderr.

The output format is shown in [Output format](#output-format) section.

# Output format

Here is `allnoconfig_configs/13675-1f9d03c5e999/13675-1f9d03c5e999-repair_changes.json`:

```
{
  "original": {
    "assigned_config_options_count": 429
  },
  "repaired": {
    "0.x86_64.config_olddef": {
      "assigned_config_options_count": 458,
      "change_wrt_original": 37
    },
    "1.x86_64.config_olddef": {
      "assigned_config_options_count": 457,
      "change_wrt_original": 36
    },
    "2.x86_64.config_olddef": {
      "assigned_config_options_count": 458,
      "change_wrt_original": 37
    }
  }
}
```

Notice that there are multiple repaired configurations.

`assigned_config_options_count` is the count of configuration options that have some value assigned in the configuration file (`^CONFIG_.*=`). This is useful when presenting the number of configuration options with a value assigned before/after repair.

`change_wrt_original` exists for repaired configurations, and it is the number of configuration options that have their value changed. It includes the non-boolean values as well. For example, if some int option was changed from `64` to `0`, it is counted. Also, if some tristate option is changed from `m` to `y`, it is counted.

# Measuring repair size for all patches

Following commands first measures repair size and creates measurement output files, then summarizes the measurements as percentiles.

Two types of measurements are collected: original configurations are compared to repaired configurations, and original configurations are compared to allyesconfig.

```
EXPERIMENTS=("allnoconfig" "defconfig" "randconfig" "allyesconfig")
mkdir -p repair_size/measurements/

# measure repair size
for exp in ${EXPERIMENTS[@]}; do
  # repair_results/validate/ is created by evaluation_client.sh
  bash compute_from_all_results.sh repair_results/validate/ ${exp} repair_size/measurements/ |& tee repair_size/exp_repair_size.log
done


# summarize repair size measurements
for exp in ${EXPERIMENTS[@]}; do
  # original config compared to repaired configs
  find repair_size/measurements/ | grep "${exp}-repair_size.json$" > files_${exp}_repair_sizes.txt
  python3 summarize_table_data.py --measurements-files-list files_${exp}_repair_sizes.txt |& tee repair_size/summary_${exp}_repair_sizes.txt

  # original config compared to allyesconfig
  find repair_size/measurements/ | grep "${exp}-compared_to_allyesconfig.json$" > files_${exp}_allyesconfig_comparison.txt
  python3 summarize_table_data.py --measurements-files-list files_${exp}_allyesconfig_comparison.txt 2> repair_size/summary_${exp}_allyesconfig_comparison.txt
done

# check tail of the following files for the summaries (replace ${exp}):
#  * repair_size/summary_${exp}_repair_sizes.txt
#  * repair_size/summary_${exp}_allyesconfig_comparison.txt
```
