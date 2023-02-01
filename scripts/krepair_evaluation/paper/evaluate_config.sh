#!/bin/bash

# example: TODO

set -x

# used to find other scripts called
script_dir=$(dirname $(realpath $0))

function usage {
  echo "$(basename $0) [-1] [-2]"
  echo -e "\t-1\tbuild kernel with config BEFORE repair"
  echo -e "\t-1\tbuild kernel with config AFTER repair"
}

# list of arguments expected in the input
optstring="12"

build_before=
build_after=
while getopts ${optstring} arg; do
  case ${arg} in
    1)
      build_before=true
      ;;
    2)
      build_after=true
      ;;
    ?)
      echo "Invalid option: -${OPTARG}."
      usage
      exit 2
      ;;
  esac
done
shift $((OPTIND-1))

if [ "$#" -lt 6 ]; then
  echo "Illegal number of parameters"
  exit -1
fi

# timeouts for klocalizer
make_timeout=600
superc_timeout=600

# this is an already-cloned linux source directory that only this run
linuxsrclone=$1
linuxsrclone=$(realpath ${linuxsrclone})

# path to the patchfile
patch=$2
patch=$(realpath ${patch})

# path to the config file to evaluate
config=$3
config=$(realpath ${config})

# the linux architecture to use
arch=$4

# formula cache storage directory for klocalizer
formulacache=$5
formulacache=$(realpath ${formulacache})

# this is the directory where output and intermediate files go
outdir=$6
if [ -d $outdir ]; then
  echo "ERROR: output directory already exists"
  exit 1
else
  mkdir -p $outdir
fi
outdir=$(realpath $outdir)

build_flags=$7

# 1. check the coverage of the input configuration
(cd ${linuxsrclone}; git clean -dfx)  # clean the repo
koverage_time=${outdir}/koverage_time
koverage_scratch=${outdir}/koverage_scratch
koverage_outfile=${outdir}/koverage_outfile
(cd ${linuxsrclone}; /usr/bin/time -f %e -o ${koverage_time} koverage --config ${config} --arch ${arch} --linux-ksrc ${linuxsrclone} --check-patch ${patch} --scratch-dir ${koverage_scratch} -o ${koverage_outfile})

if [[ "${build_before}" != "" ]]; then
    # 2. build
    build_time=${outdir}/build.time
    build_size=${outdir}/build.size
    build_out=${outdir}/build.out
    build_errcode=${outdir}/build.errcode
    olddefconfig=${outdir}/olddefconfig
    (cd ${linuxsrclone}; git clean -dfx)  # clean the repo
    cp ${config} ${linuxsrclone}/.config
    (cd ${linuxsrclone}; make.cross ARCH=${arch} olddefconfig)  # clean the repo
    cp ${linuxsrclone}/.config ${olddefconfig}
    (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${build_time} make.cross ${build_flags} ARCH=${arch} > ${build_out} 2>&1; echo ${?} > ${build_errcode})
    # measure size of build
    (cd ${linuxsrclone}; ls -lSrh arch/*/boot; find | grep "\.ko$" | xargs ls -lSrh) > ${build_size}
fi

# 3. repair if needed
grep EXCLUDED ${koverage_outfile}
if [[ "$?" == "0" ]]; then
    touch ${outdir}/patch_uncovered

    krepair_time=${outdir}/krepair.time
    krepair_configs=${outdir}/krepair_configs
    krepair_report=${outdir}/krepair_report
    (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${krepair_time} klocalizer -v --repair ${config} --include-mutex ${patch} --build-timeout ${make_timeout} --superc-timeout ${superc_timeout} --output ${krepair_configs} --coverage-report ${krepair_report} --formulas ${formulacache})
    if [[ "$?" == 0 ]]; then
	numconfigs=$(ls ${krepair_configs} | wc -l)
	if [[ ${numconfigs} -eq 1 ]]; then
	    discovered_arch=$(ls ${krepair_configs}/*.config | head -n1 | xargs basename | cut -f1 -d\. | cut -f2 -d-)
	    touch ${outdir}/krepair_one
	    repaired_config=$(find ${krepair_configs} -type f)
	    # 4. check the coverage of the repaired configuration
	    repaired_koverage_time=${outdir}/repaired_koverage_time
	    repaired_koverage_scratch=${outdir}/repaired_koverage_scratch
	    repaired_koverage_outfile=${outdir}/repaired_koverage_outfile
	    (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${repaired_koverage_time} koverage --config ${repaired_config} --arch ${discovered_arch} --linux-ksrc ${linuxsrclone} --check-patch ${patch} --scratch-dir ${repaired_koverage_scratch} -o ${repaired_koverage_outfile})

	    grep EXCLUDED ${repaired_koverage_outfile}
	    if [[ -f ${repaired_koverage_outfile} && "$?" != "0" ]]; then
		touch ${outdir}/repaired_patch_covered
	    else
		touch ${outdir}/repaired_patch_uncovered
	    fi

            if [[ "${build_after}" != "" ]]; then
                # 5. build
                repaired_build_time=${outdir}/repaired_build.time
                repaired_build_size=${outdir}/repaired_build.size
                repaired_build_out=${outdir}/repaired_build.out
		repaired_build_errcode=${outdir}/repaired_build.errcode
                repaired_olddefconfig=${outdir}/repaired_olddefconfig
                (cd ${linuxsrclone}; git clean -dfx)  # clean the repo
                cp ${repaired_config} ${linuxsrclone}/.config
                sed -i 's/CONFIG_PHYSICAL_START=0/CONFIG_PHYSICAL_START=0x1000000/' ${linuxsrclone}/.config
                (cd ${linuxsrclone}; make.cross ARCH=${discovered_arch} olddefconfig)  # clean the repo
                cp ${linuxsrclone}/.config ${repaired_olddefconfig}
                (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${repaired_build_time} make.cross ${build_flags} ARCH=${discovered_arch} > ${repaired_build_out} 2>&1; echo ${?} > ${repaired_build_errcode})
                # measure size of build
                (cd ${linuxsrclone}; ls -lSrh arch/*/boot; find | grep "\.ko$" | xargs ls -lSrh) > ${repaired_build_size}
	    fi
	else
	    touch ${outdir}/krepair_not_one

	    ls ${krepair_configs}/*.config | while IFS= read -r repaired_config; do
		discovered_arch=$(echo $repaired_config | xargs basename | cut -f1 -d\. | cut -f2 -d-)
		basename=$(basename $repaired_config)
		
		# 4. check the coverage of the repaired configuration
		repaired_koverage_time=${outdir}/repaired_koverage_time.${basename}
		repaired_koverage_scratch=${outdir}/repaired_koverage_scratch.${basename}
		repaired_koverage_outfile=${outdir}/repaired_koverage_outfile.${basename}
		(cd ${linuxsrclone}; /usr/bin/time -f %e -o ${repaired_koverage_time} koverage --config ${repaired_config} --arch ${discovered_arch} --linux-ksrc ${linuxsrclone} --check-patch ${patch} --scratch-dir ${repaired_koverage_scratch} -o ${repaired_koverage_outfile})
	    done

	    repaired_koverage_total=${outdir}/repaired_koverage_outfile
	    python3 ${script_dir}/total_coverage.py -o ${repaired_koverage_total} ${outdir}/repaired_koverage_outfile.*

	    grep EXCLUDED ${repaired_koverage_total}
	    if [[ -f ${repaired_koverage_total} && "$?" != "0" ]]; then
		touch ${outdir}/repaired_patch_covered
	    else
		touch ${outdir}/repaired_patch_uncovered
	    fi

	    if [[ "${build_after}" != "" ]]; then
		ls ${krepair_configs}/*.config | while IFS= read -r repaired_config; do
	    	    discovered_arch=$(echo $repaired_config | xargs basename | cut -f1 -d\. | cut -f2 -d-)
	    	    basename=$(basename $repaired_config)
	    	    # 5. build
	    	    repaired_build_time=${outdir}/repaired_build.time.${basename}
	    	    repaired_build_size=${outdir}/repaired_build.size.${basename}
	    	    repaired_build_out=${outdir}/repaired_build.out.${basename}
		    repaired_build_errcode=${outdir}/repaired_build.errcode.${basename}
	    	    repaired_olddefconfig=${outdir}/repaired_olddefconfig.${basename}
	    	    (cd ${linuxsrclone}; git clean -dfx)  # clean the repo
	    	    cp ${repaired_config} ${linuxsrclone}/.config
	    	    sed -i 's/CONFIG_PHYSICAL_START=0/CONFIG_PHYSICAL_START=0x1000000/' ${linuxsrclone}/.config
	    	    (cd ${linuxsrclone}; make.cross ARCH=${discovered_arch} olddefconfig)  # clean the repo
	    	    cp ${linuxsrclone}/.config ${repaired_olddefconfig}
	    	    (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${repaired_build_time} make.cross ${build_flags} ARCH=${discovered_arch} > ${repaired_build_out} 2>&1)
	    	    # measure size of build
	    	    (cd ${linuxsrclone}; ls -lSrh arch/*/boot; find | grep "\.ko$" | xargs ls -lSrh) > ${repaired_build_size}
		done
	    fi
	fi
    else
	touch ${outdir}/krepair_errored
    fi
else
    touch ${outdir}/patch_covered
fi

# (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${timing_realpath} klocalizer -v -a ${arch} --repair ${configtorepair_realpath} --include-mutex ${patchfile} --build-targets ${build_targets_realpath} --build-timeout ${make_timeout} --superc-timeout ${superc_timeout} --output ${config_output_realpath} --coverage-report ${coverage_report_realpath} --formulas ${formulacache_realpath} |& tee ${klocalizer_out_realpath})


# # pull out these functions into a common script to include

# repair () {
#     builtin_config_name=$1

#     mkdir ${repairout}/${builtin_config_name}/

#     configtorepair=${repairout}/${builtin_config_name}/configtorepair

#     (cd ${linuxsrclone}; make distclean)
#     (cd ${linuxsrclone}; git clean -dfx)
    
#     mkdir ${repairout}/${builtin_config_name}/timings

#     # get patchfile
#     patchfile=$(realpath ${linuxsrclone}/${commit}.patch)
#     (cd ${linuxsrclone}; git show ${commit} > ${patchfile})

#     # realpaths to input directories and files
#     configtorepair_realpath=$(realpath ${configtorepair})
#     build_targets_realpath=$(realpath ${build_targets})
#     formulacache_realpath=$(realpath ${formulacache})

#     # realpaths to output directories and files
#     config_output_realpath=$(realpath ${repairout}/${builtin_config_name}/configs)  # repaired configs
#     timing_realpath=$(realpath ${repairout}/${builtin_config_name}/timings/krepair_timing.out)  # krepair timing
#     coverage_report_realpath=$(realpath ${repairout}/${builtin_config_name}/coverage_report.json)  # krepair coverage report
#     klocalizer_out_realpath=$(realpath ${repairout}/${builtin_config_name}/klocalizer.out)  # krepair log
    
#     mkdir ${config_output_realpath}  # create path to save output configs

#     (cd ${linuxsrclone}; KCONFIG_CONFIG=${configtorepair_realpath} make.cross ARCH=${arch} ${builtin_config_name};)
    
#     # run klocalizer --repair
#     (cd ${linuxsrclone}; /usr/bin/time -f %e -o ${timing_realpath} klocalizer -v -a ${arch} --repair ${configtorepair_realpath} --include-mutex ${patchfile} --build-targets ${build_targets_realpath} --build-timeout ${make_timeout} --superc-timeout ${superc_timeout} --output ${config_output_realpath} --coverage-report ${coverage_report_realpath} --formulas ${formulacache_realpath} |& tee ${klocalizer_out_realpath})
# }

# check_coverage () {
#     configs=$1
#     arch=$2
#     validateoutdir=$3
#     configcountfile=$4

#     config_count=`ls ${configsdir} | wc -l`
#     echo ${config_count} > ${configcountfile}
#     echo "${patchname} ${configsdir} validating configs"
#     (cd ${linuxsrclone}; git clean -dfx)
#     mkdir ${validateoutdir}
#     mkdir ${validateoutdir}/inclusion
#     # koverage takes a single config, but we may have multiple ones
#     # $configs handle multiple configs dir for repaired configs

#     find $configs | egrep "\.config$|configtorepair$" | while IFS= read -r config; do
# 	configfilename=$(basename $config)
# 	outfile=$validateoutdir/inclusion/$configfilename
# 	scratchdir=$validateoutdir/scratch_dir_$configfilename
# 	/usr/bin/time -f %e -o ${validateoutdir}/time.out koverage --config $config --arch ${arch} --linux-ksrc ${linuxsrclone} --check-covreq $patchconditionfile --build-targets $build_targets --scratch-dir $scratchdir -o $outfile
# 	# if you want to use the original patchfile to measure coverage, then do this
# 	# patchfile= # get from linux repo and export to a file
# 	# /usr/bin/time -f %e -o ${validateoutdir}/time.out koverage --config $config --arch ${arch} --linux-ksrc ${linuxsrclone} --check-patch $patchfile --build-targets $build_targets --scratch-dir $scratchdir -o $outfile
#     done
# }

# build_patch () {
#     configs=$1
#     arch=$2
#     buildoutdir=$3
#     makeflags=$4

#     echo "${patchname} ${configsdir} building configs"
#     mkdir ${buildoutdir}
#     # koverage takes a single config, but we may have multiple ones
#     # $configs handle multiple configs dir for repaired configs

#     find $configs | egrep "\.config$|configtorepair$" | while IFS= read -r config; do
# 	configfilename=$(basename $config)
# 	timefile=$buildoutdir/$configfilename.time
# 	outfile=$buildoutdir/$configfilename.out
# 	(cd ${linuxsrclone}; git clean -dfx)
# 	cp $config ${linuxsrclone}/.config
# 	(cd ${linuxsrclone}; make olddefconfig |& tee ${outfile})
# 	(cd ${linuxsrclone}; /usr/bin/time -f %e -o $timefile make ARCH=${arch} |& tee ${outfile})
#     done
# }

# # generate defconfig
# get_builtin_config defconfig

# # check coverage and build the config
# check_coverage defconfig
# build_patch defconfig

# # check coverage and build the repaired config
# repair defconfig
# check_coverage defconfig_repaired
# build_patch defconfig_repaired

# # rhel config

# # ubuntu config

# # syzkaller config

# # # may need to separate out the allyesconfig experiment and do it on fewer configs
# # get_config allyesconfig
# # check_coverage allyesconfig
# # build_patch allyesconfig

# # builtin_config_names=("allnoconfig" "defconfig" "randconfig" "allyesconfig")
# # for builtin_config_name in ${builtin_config_names[@]}; do
# #   configs=${repairout}/${builtin_config_name}/configs
# #   validateoutdir=$outdir/line_inclusion_results_${builtin_config_name}_after
# #   configcountfile=$outdir/config_count_${builtin_config_name}_after

# #   check_coverage ${configs} ${arch} ${validateoutdir} ${configcountfile}

# #   configs=${repairout}/${builtin_config_name}/configtorepair
# #   validateoutdir=$outdir/line_inclusion_results_${builtin_config_name}_before
# #   configcountfile=$outdir/config_count_${builtin_config_name}_before

# #   check_coverage ${configs} ${arch} ${validateoutdir} ${configcountfile}
# # done


# # build_patch ${repairout}/defconfig/configs ${arch} $outdir/build_results_defconfig_after_makej8 "-j 8"
# # build_patch ${repairout}/allyesconfig/configtorepair ${arch} $outdir/build_results_allyesconfig_before_makej8 "-j 8"
