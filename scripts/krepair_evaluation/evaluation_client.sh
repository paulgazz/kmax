#!/bin/bash

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
patchtimeout=$3
outdir=$4
shift 4

build_targets=$1
linuxsrclone=$2
formulacache=$3
patchconds=$4
arch=$5

while true; do
  patchname=$(java superc.util.FilenameService -client $server $port)
  exit_code=$?
  if [ "$exit_code" -ne 0 ]; then
    exit $exit_code
  fi

  repairout=${outdir}/repair/${patchname}
  validateout=${outdir}/validate/${patchname}
  
  echo "start repair $patchname $(date)"
  timeout $patchtimeout bash ${script_dir}/repair_patch.sh $build_targets $linuxsrclone $formulacache $patchname $repairout $arch
  exit_code=$?
  if [ "$exit_code" -eq 124 ]; then
	  echo "timeout repair $patchname $(date)"
  else
	  echo "end repair $patchname $(date)"
  fi

  echo "start $patchname $(date)"
  timeout $patchtimeout bash ${script_dir}/validate_repair.sh $repairout $patchconds $build_targets $linuxsrclone $patchname $validateout $arch
  exit_code=$?
  if [ "$exit_code" -eq 124 ]; then
	  echo "timeout $patchname $(date)"
  else
	  echo "end $patchname $(date)"
  fi
done
