#!/bin/bash

# example: bash /data1/paul/kmax/scripts/krepair_evaluation/paper/run_evaluate_config.sh linux/ c07ba878ca199a6089cdb323bf526adbeeb4201f x86_64 formulacache outdir_with_build_j/c07ba878ca199a6089cdb323bf526adbeeb4201f

set -x

# used to find other scripts called
script_dir=$(dirname $(realpath $0))

# list of arguments expected in the input
optstring="dynk"

all=true
defconfig=
allyesconfig=
allnoconfig=
while getopts ${optstring} arg; do
  case ${arg} in
    d)
      defconfig=true
      all=
      ;;
    y)
      allyesconfig=true
      all=
      ;;
    n)
      allnoconfig=true
      all=
      ;;
    k)
      # only run defconfig with no build
      krepaironly=true
      all=
      ;;
    ?)
      echo "Invalid option: -${OPTARG}."
      usage
      exit 2
      ;;
  esac
done
shift $((OPTIND-1))

if [ "$#" -lt 5 ]; then
  echo "Illegal number of parameters"
  exit -1
fi

linuxsrclone=${1}
linuxsrclone=$(realpath ${linuxsrclone})
commit=${2}
arch=${3}
formulacache=${4}
outdir=${5}
if [ -d $outdir ]; then
  echo "ERROR: output directory already exists"
  exit 1
else
  mkdir -p $outdir
fi
outdir=$(realpath $outdir)

build_flags=$6

patch=${outdir}/commit.patch

(cd ${linuxsrclone}; git checkout -f $commit)
(cd ${linuxsrclone}; git clean -dfx)
(cd ${linuxsrclone}; git show > ${patch})

# allnoconfig
if [[ "${allnoconfig}" != "" ||  "${all}" != "" ]]; then
  config_outdir=${outdir}/allnoconfig
  mkdir ${config_outdir}

  config=${config_outdir}/config
  (cd ${linuxsrclone}; KCONFIG_CONFIG=${config} make.cross ARCH=${arch} allnoconfig)

  results=${config_outdir}/results
  bash ${script_dir}/evaluate_config.sh ${linuxsrclone} ${patch} ${config} ${arch} ${formulacache} ${results} ${build_flags}
fi

# defconfig
if [[ "${defconfig}" != "" ||  "${all}" != "" || "${krepaironly}" != "" ]]; then
  config_outdir=${outdir}/defconfig
  mkdir ${config_outdir}

  config=${config_outdir}/config
  (cd ${linuxsrclone}; KCONFIG_CONFIG=${config} make.cross ARCH=${arch} defconfig)

  if [[ "${krepaironly}" != "" ]]; then
    build_stages=
  else
    build_stages="-1 -2"
  fi
  
  results=${config_outdir}/results
  bash ${script_dir}/evaluate_config.sh ${build_stages} ${linuxsrclone} ${patch} ${config} ${arch} ${formulacache} ${results} ${build_flags}
fi

# allyesconfig
if [[ "${allyesconfig}" != "" ||  "${all}" != "" ]]; then
  config_outdir=${outdir}/allyesconfig
  mkdir ${config_outdir}

  config=${config_outdir}/config
  (cd ${linuxsrclone}; KCONFIG_CONFIG=${config} make.cross ARCH=${arch} allyesconfig)

  results=${config_outdir}/results
  bash ${script_dir}/evaluate_config.sh -1 ${linuxsrclone} ${patch} ${config} ${arch} ${formulacache} ${results} ${build_flags}
fi
