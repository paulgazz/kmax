#!/bin/bash

# for i in {0..3}; do bash /data1/paul/kmax/scripts/krepair_evaluation/build_client.sh localhost 45678 /data2/test_experiment/aggregated build_patch inputs/linux$i x86_64 > build_patch$i 2>&1 & sleep 1; done

# bash /data1/paul/kmax/scripts/krepair_evaluation/build_client.sh localhost 45678 /data2/test_experiment/aggregated build_patch inputs/linux0 x86_64
# for i in {0..31}; do bash /data1/paul/kmax/scripts/krepair_evaluation/build_client.sh localhost 45678 /data2/test_experiment/aggregated build_patch inputs/linux$i x86_64 > build_patch$i 2>&1 & sleep 1; done

# mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
# (cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist
# # head -n3 patchlist > patchlist_3
# java superc.util.FilenameService -server 55679 patchlist &
# # java superc.util.FilenameService -server 55679 patchlist_3 &
# mkdir repair_results
# bash ~/research/repos/plocalizer/krepair/evaluation_client.sh localhost 55679 1h repair_results build_targets.json ~/src/linux0 ~/tmp/formulacache/ patchconditions/ x86_64
# bash ~/research/repos/plocalizer/krepair/evaluation_client.sh localhost 55679 1h repair_results build_targets.json ~/src/linux ~/tmp/formulacache/ patchconditions/ x86_64
# bash evaluation_client.sh localhost 55679 1h repair_results build_targets.json ~/src/linux0 ~/tmp/formulacache/ patchconditions/ x86_64 > repair_log0 2>&1
# bash ~/research/repos/plocalizer/krepair/evaluation_client.sh localhost 55679 1h repair_results build_targets.json ~/src/linux0 ~/tmp/formulacache/ patchconditions/ x86_64 > repair_log0 2>&1
# for i in {1..3}; do bash evaluation_client.sh localhost 55679 1h repair_results build_targets.json ~/src/linux$i ~/tmp/formulacache/ patchconditions/ x86_64 > repair_log$i 2>&1 & sleep 1; done

set -x

script_dir=$(dirname $(realpath $0))

# input to code that parallelizes the experiment
server=$1
port=$2
indir=$3
outdir=$4
shift 4

linuxsrclone=$1
arch=$2

while true; do
  patchname=$(java superc.util.FilenameService -client $server $port)
  exit_code=$?
  if [ "$exit_code" -ne 0 ]; then
    exit $exit_code
  fi

  repairout=${indir}/repair/${patchname}
  buildout=${outdir}/${patchname}

  echo "start build $patchname $(date)"
  bash ${script_dir}/build_patch.sh $repairout $linuxsrclone $patchname $buildout $arch
  echo "end build $patchname $(date)"
done
