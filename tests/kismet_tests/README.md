<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Test documentation](#test-documentation)
  - [Longer test](#longer-test)
    - [x86_64 on README.md version v5.16](#x86_64-on-readmemd-version-v516)
    - [Replicate kismet paper](#replicate-kismet-paper)
    - [Do v4.16](#do-v416)
  - [Shorter tests](#shorter-tests)
    - [Unavailable arch exception](#unavailable-arch-exception)
    - [Missing Kconfig file error](#missing-kconfig-file-error)
    - [False negative caused due to Kconfig output format](#false-negative-caused-due-to-kconfig-output-format)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Test documentation

## Longer test

### x86_64 on README.md version v5.16

```
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.16.tar.xz
tar -xvf linux-5.16.tar.xz
cd linux-5.16/
kismet -a x86_64
```

### Replicate kismet paper

Run and compare against the [original paper's](https://doi.org/10.1145/3468264.3468578) [experimental data](https://doi.org/10.5281/zenodo.4885001) for Linux 5.4.4:

	# running the experiment, assuming kismet is already installed.
	wget https://raw.githubusercontent.com/paulgazz/kmax/master/scripts/kismet_evaluation/kismet_experiments_replication.sh
	bash kismet_experiments_replication.sh
	# getting and comparing to the original results
	wget https://zenodo.org/records/4563310/files/kismet-raw-results-main.zip
	unzip kismet-raw-results-main.zip
	for i in kismet-raw-results-main/raw_kismet/verbose_summaries/kismet_summary_*.txt; do name=$(basename $i); echo diff $i ~/kismet-experiments/$name; done | bash | less


### Do v4.16


```
git checkout v4.16
kismet -a x86_64
```


## Shorter tests

### Unavailable arch exception

https://github.com/paulgazz/kmax/pull/165

```
cd linux
git remote add stable https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux-stable.git
git fetch stable linux-4.9.y
git checkout 95302ce6d8a08e88b7562238a8018820631325b6
kismet -a riscv
```

This should raise a UnavailableArchitectureException



### Missing Kconfig file error

https://github.com/paulgazz/kmax/issues/164

This example has an error in the Kconfig files themselves, where a missing Kconfig file is being imported.  kismet should report that error instead of just saying kextract failed to run

```
git checkout 012e3ca3cb4d7f
kismet -a x86_64
```

This should emit `ERROR: Can't open Kconfig files:` to stderr


### False negative caused due to Kconfig output format


https://github.com/paulgazz/kmax/issues/168
https://github.com/paulgazz/kmax/issues/159

This false negative is not due to the formal model, but instead to a difference in how the output of Kconfig is parsed when validating the alarm


```
git checkout v4.16
kismet -a x86_64 --selectees CONFIG_BACKLIGHT_CLASS_DEVICE --selectors CONFIG_DRM_RADEON
```

