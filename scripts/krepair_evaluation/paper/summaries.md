krepair_experiment_j{8,1}.csv

- one row for each commit and each config (defconfig, krepair, and allyesconfig)
  - krepair is repairing defconfig, but only if defconfig does not cover the patch
- if the builderrcode is not 0, then the patch coverage and build times should not be used (exclude the commits, since the config did not build)
- if the builderrcode is n/a, but there are results for coverage and time, use them (this happens when there are many configs that krepair produces for coverage)

krepair_runtime_{,un}cached.csv

- there is one column for the krepair runtimes for each time krepair is run
- the times where krepair fails, there is not time and it can be omitted

randconfig_coverage.csv

- shows the patch coverage for each commit and each run of the randconfig generator.  there are ten randconfigs for each patch, so ten csv lines for each patch.

change_summary{,_allnoconfig}.csv

- for each commit and config, this shows the number of config options that are changed
- when there are multiple configs, there is one row for each config, which shows as multiple rows for the same commit
- currently this is incomplete data, as we need the total number of configs in kconfig at that commit id

config_counts.csv

- for each commit, this is the number of configs in the architectures for which there are configs found
- buildid is the klocalizer build id and can be ignored for computing the summary statistics
- 0 means that likely krepair wasn't successfully run for this commit
