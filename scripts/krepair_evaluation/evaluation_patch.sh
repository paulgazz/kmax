#!/bin/bash

# example: TODO

set -x

if [ "$#" -ne 6 ]; then
  echo "Illegal number of parameters"
  exit -1
fi

# timeouts for klocalizer
make_timeout=600
superc_timeout=600

# this is an already-cloned linux source directory that only this run
# of the script will use
# git clone ..
linuxsrclone=$1

# the commit id
commit=$2

# formula cache storage directory for klocalizer
formulacache=$3

# this is the directory where output and intermediate files go
outdir=$4

# the linux architecture to use
arch=$6

if [ -d $outdir ]; then
  echo "ERROR: output directory already exists"
  exit 1
else
  mkdir -p $outdir
fi

outdir=$(realpath $outdir)

# checkout to the patch's associated commit
(cd ${linuxsrclone}; git checkout -f $commit)
# TODO: needs a error check

(cd ${linuxsrclone}; make distclean)

do_repair () {
    builtin_config_name=$1

    mkdir ${repairout}/${builtin_config_name}/

    configtorepair=${repairout}/${builtin_config_name}/configtorepair

    (cd ${linuxsrclone}; git clean -dfx)
    
    mkdir ${repairout}/${builtin_config_name}/timings

    # get patchfile
    patchfile=$(realpath ${linuxsrclone}/${commit}.patch)
    (cd ${linuxsrclone}; git show ${commit} > ${patchfile})

    # realpaths to input directories and files
    configtorepair_realpath=$(realpath ${configtorepair})
    build_targets_realpath=$(realpath ${build_targets})
    formulacache_realpath=$(realpath ${formulacache})

    # realpaths to output directories and files
    config_output_realpath=$(realpath ${repairout}/${builtin_config_name}/configs)  # repaired configs
    timing_realpath=$(realpath ${repairout}/${builtin_config_name}/timings/krepair_timing.out)  # krepair timing
    coverage_report_realpath=$(realpath ${repairout}/${builtin_config_name}/coverage_report.json)  # krepair coverage report
    klocalizer_out_realpath=$(realpath ${repairout}/${builtin_config_name}/klocalizer.out)  # krepair log
    
    mkdir ${config_output_realpath}  # create path to save output configs

    (cd ${linuxsrclone}; KCONFIG_CONFIG=${configtorepair_realpath} make.cross ARCH=${arch} ${builtin_config_name};)
    
    # run klocalizer --repair
    (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${timing_realpath} klocalizer -v -a ${arch} --repair ${configtorepair_realpath} --include-mutex ${patchfile} --build-targets ${build_targets_realpath} --build-timeout ${make_timeout} --superc-timeout ${superc_timeout} --output ${config_output_realpath} --coverage-report ${coverage_report_realpath} --formulas ${formulacache_realpath} |& tee ${klocalizer_out_realpath})
}

do_repair allnoconfig
do_repair defconfig
do_repair randconfig
do_repair allyesconfig
