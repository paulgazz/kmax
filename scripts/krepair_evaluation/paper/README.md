<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Evaluation](#evaluation)
  - [Sampling patches](#sampling-patches)
    - [Filtering out non-source code patches](#filtering-out-non-source-code-patches)
  - [Running experiments](#running-experiments)
    - [Get patch coverage and build times](#get-patch-coverage-and-build-times)
    - [Get krepair runtimes](#get-krepair-runtimes)
    - [Run randconfig experiments](#run-randconfig-experiments)
  - [Collecting data](#collecting-data)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Evaluation

## Sampling patches

- Clone the stable linux repo: git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
- Get commits from the last year
- Filter in only those that touch code (.c/.h)
  - git log --until=2022-09-18 --since=2021-09-19 --no-merges
  - ... | grep ^commit | wc -l was 71,896
  - https://www.calculator.net/sample-size-calculator.html?type=1&cl=99&ci=5&pp=50&ps=71896&x=84&y=21
    - sample size 660 for 99% confidence in a 5% margin of error for a population of 71,896
- Take a random sample
  - head -n660 /dev/urandom > randfile  # randfile already generated and saved
  - git log --until=2022-09-18 --since=2021-09-19 --no-merges --pretty=format:%H | shuf --random-source=randfile | head -n660 > sample


### Filtering out non-source code patches

    # run the experiment on defconfig
    linuxdir=/data1/test_experiment/inputs/linux1; cat /data1/paul/kmax/scripts/krepair_evaluation/paper/sample | while read commit; do bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_evaluate_config.sh -k ${linuxdir} ${commit} x86_64 formulacache /data1/test_experiment/outdir_manyD/${commit}; done |& tee /data1/test_experiment/manyD.out

    # get those configs that have coverable lines in them
    ls /data*/test_experiment/outdir_manyD/*/defconfig/results/koverage_outfile | while read i; do egrep "(INCLUDED|EXCLUDED)" $i >/dev/null 2>&1; if [[ $? -eq 0 ]]; then echo $i; fi; done > coverable_patches
    cat coverable_patches | wc -l
    507


- Run koverage on each commit
- Check whether any lines exist included in the coverage report
- Results in 507 patches

## Running experiments

### Get patch coverage and build times

Run the full experiment, building using `-j8` for an 8-thread parallelized build

    # start the filename server
    java superc.util.FilenameService -server 45678 /data2/test_experiment/coverable_patches

    # run the experiment for all configs
    for sdd in {1..3}; do for instance in {0..9}; do linuxdir=/data${sdd}/test_experiment/inputs/linux${instance}; outdir=/data${sdd}/test_experiment/j8_krepair_out${instance}; log=/data${sdd}/test_experiment/j8_krepair_out${instance}.log; source=localhost:45678; bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_many_evaluations.sh ${source} ${linuxdir} x86_64 formulacache ${outdir} -j8 > ${log} 2>&1 & sleep 1; done; done


Re-run the experiment to collect single-threaded build times 

    java superc.util.FilenameService -server 45678 /data2/test_experiment/coverable_patches

    for sdd in {1..3}; do for instance in {0..15}; do linuxdir=/data${sdd}/test_experiment/inputs/linux${instance}; outdir=/data${sdd}/test_experiment/j1_krepair_out${instance}; log=/data${sdd}/test_experiment/j1_krepair_out${instance}.log; source=localhost:45678; bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_many_evaluations.sh ${source} ${linuxdir} x86_64 formulacache ${outdir} -j1 > ${log} 2>&1 & sleep 1; done; done

### Get krepair runtimes

Be sure that the formula cache directory is empty so that krepair runs uncached first

    linuxdir=/data1/test_experiment/inputs/linux1; cat /data2/test_experiment/coverable_patches | while read commit; do
      bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_evaluate_config.sh -k ${linuxdir} ${commit} x86_64 ${linuxdir}/formulacache /data1/test_experiment/krepair_only_uncached/${commit}
    done |& tee /data1/test_experiment/krepair_only_uncached.out

Run the experiment again using the same formula cache directory to get the cached krepair runtimes

    linuxdir=/data1/test_experiment/inputs/linux1; cat /data2/test_experiment/coverable_patches | while read commit; do
      bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_evaluate_config.sh -k ${linuxdir} ${commit} x86_64 /data2/test_experimenta/formulacache /data1/test_experiment/krepair_only_cached/${commit}
    done |& tee /data1/test_experiment/krepair_only_cached.log


### Run randconfig experiments

    mkdir randconfig; cat /data2/test_experiment/coverable_patches | while read commit; do bash /data1/paul/kmax/scripts/krepair_evaluation/paper/randconfig.sh linux2/ $commit x86_64 3 /data2/test_experiment/randconfig/$commit; done |& tee /data2/test_experiment/out.randconfig

## Collecting data

Use the `data_summaries.sh` script to extract the data into csv files.  `summaries.md` describes the csv file data that will be produced.  The data collected includes:

- patch coverage and build times for defconfig, defconfig after repair, and allyesconfig for both 1 and 8 build threads
- runtimes for krepair, both with and without the cache
- how much change krepair incurred when repairing defconfig and allnoconfig
- coverage of randomly-generated configuration files

Build errors can be identified with help from the `broken_builds.sh` script

