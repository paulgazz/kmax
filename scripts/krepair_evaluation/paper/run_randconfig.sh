#!/bin/bash

# mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
# (cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist
# # head -n3 patchlist > patchlist_3
# java superc.util.FilenameService -server 55679 patchlist &
# # java superc.util.FilenameService -server 55679 patchlist_3 &
# mkdir repair_results
# bash /data1/paul/kmax/scripts/krepair_evaluation/randconfig_client.sh localhost 45678 randconfig_test patchconditions build_targets.json inputs/linux0 x86_64

# example:  experiment@church:/data2/test_experiment$ # bash /data1/paul/kmax/scripts/krepair_evaluation/randconfig_client.sh localhost 45678 randconfig_test patchconditions build_targets.json inputs/linux0 x86_64

set -x

script_dir=$(dirname $(realpath $0))

# input to code that parallelizes the experiment
server=$1
port=$2
outdir=$3
shift 3

linuxsrclone=$1
arch=$2
build_targets=$3
numconfigs=$4

while true; do
  commit=$(java superc.util.FilenameService -client $server $port)
  exit_code=$?
  if [ "$exit_code" -ne 0 ]; then
    exit $exit_code
  fi

  testout=${outdir}/${commit}

  echo "start test_randconfig $patchname $(date)"
  bash ${script_dir}/randconfig.sh $linuxsrclone $commit $arch $build_targets $numconfigs $testout
  echo "end test_randconfig $patchname $(date)"
done
