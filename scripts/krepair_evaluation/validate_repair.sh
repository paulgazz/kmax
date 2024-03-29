#!/bin/bash

# example: bash validate_repair.sh ~/tmp/test_output/14522-210f563b0979 ~/tmp/patchconditions/  ~/research/repos/plocalizer/assets/build_targets.json ~/src/linux 14522-210f563b0979 ~/tmp/test_validate/14522-210f563b0979 x86_64


set -x

if [ "$#" -ne 7 ]; then
  echo "Illegal number of parameters"
  exit -1
fi

# set path for libisl.so.22, needed to build the kernel
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$HOME/.local/lib

# this is the output of krepair
repairout=$1

# wget https://github.com/appleseedlab/plocalizer/blob/master/assets/final_patch_conditions_v512_v513.tar.gz
# mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
# folder structure: archname/patchname.cond
patchconds=$2

# mapping of compilation units to their kbuild patch
# passed to validate script for every patch
# https://github.com/appleseedlab/plocalizer/blob/master/assets/build_targets.json
build_targets=$3

# this is an already-cloned linux source directory that only this run
# of the script will use
linuxsrclone=$4

# the patchname, i.e., "PATCHNUMBER-COMMIT"
patchname=$5

# this is the directory where output and intermediate files go
# providing a name of a nonexistant directory (since it's created)
# structure: validation_wrapper.sh's output, plus patchname/config_count
outdir=$6

# # we are running on x86_64 only right now
# arch=x86_64
arch=$7

# It will create a directory ./ploc_approx_allno_results_<arch>/
# Within the directory, it contains:
# - ./(<patchname>/: stores the output generated by plocalizer for given patch
# - ./logs/: stores the stderr and stdout of running plocalizer for each patch
# - ./results/: stores the log of evaluation on plocalizer outputs for patch
# - ./gen_logs/: stores the log of gen_patch_files for each patch
# - ./cond_logs/: stores the log of loc_patch_condtitions for each patch
# - ./conf_logs/: stores the log of loc_patch_configs for each patch

# used to find other scripts called
script_dir=$(dirname $(realpath $0))

if [ -d $outdir ]; then
  echo "ERROR: output directory already exists"
  exit 1
else
  mkdir -p $outdir
fi

outdir=$(realpath $outdir)

commit="$(echo $patchname | cut -d - -f 2)"
patchconditionfile="${patchconds}/${arch}/${patchname}.cond"

if [ ! -f "${patchconditionfile}" ]; then
	echo "ERROR: expected patch condition: ${patchconditionfile}"
	exit 1
fi

# checkout to the patch's associated commit
(cd ${linuxsrclone}; git checkout -f $commit)

do_validate () {
    configs=$1
    arch=$2
    validateoutdir=$3
    configcountfile=$4

    config_count=`ls ${configsdir} | wc -l`
    echo ${config_count} > ${configcountfile}
    echo "${patchname} ${configsdir} validating configs"
    (cd ${linuxsrclone}; git clean -dfx)
    mkdir ${validateoutdir}
    mkdir ${validateoutdir}/inclusion
    # koverage takes a single config, but we may have multiple ones
    # $configs handle multiple configs dir for repaired configs

    find $configs | egrep "\.config$|configtorepair$" | while IFS= read -r config; do
	configfilename=$(basename $config)
	outfile=$validateoutdir/inclusion/$configfilename
	scratchdir=$validateoutdir/scratch_dir_$configfilename
	/usr/bin/time -f %e -o ${validateoutdir}/time.out koverage --config $config --arch ${arch} --linux-ksrc ${linuxsrclone} --check-covreq $patchconditionfile --build-targets $build_targets --scratch-dir $scratchdir -o $outfile
	# if you want to use the original patchfile to measure coverage, then do this
	# patchfile= # get from linux repo and export to a file
	# /usr/bin/time -f %e -o ${validateoutdir}/time.out koverage --config $config --arch ${arch} --linux-ksrc ${linuxsrclone} --check-patch $patchfile --build-targets $build_targets --scratch-dir $scratchdir -o $outfile
    done
}


builtin_config_names=("allnoconfig" "defconfig" "randconfig" "allyesconfig")
for builtin_config_name in ${builtin_config_names[@]}; do
  configs=${repairout}/${builtin_config_name}/configs
  validateoutdir=$outdir/line_inclusion_results_${builtin_config_name}_after
  configcountfile=$outdir/config_count_${builtin_config_name}_after

  do_validate ${configs} ${arch} ${validateoutdir} ${configcountfile}

  configs=${repairout}/${builtin_config_name}/configtorepair
  validateoutdir=$outdir/line_inclusion_results_${builtin_config_name}_before
  configcountfile=$outdir/config_count_${builtin_config_name}_before

  do_validate ${configs} ${arch} ${validateoutdir} ${configcountfile}
done
