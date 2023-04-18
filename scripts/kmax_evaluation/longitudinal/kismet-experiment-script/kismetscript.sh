#!/bin/bash
#Comment on all variables
set -x

which kismet

path="~/scripts/kmax_evaluation/longitudinal/kismet-experiment-files"
# get linux 5.4.4 source
while read line;
do
    link=$(echo "$line" | cut -d' ' -f 1)
    name=$(echo "$line" | cut -d' ' -f 2)

    mkdir -p ~/kismet-experiments-$name/
    cd ~/kismet-experiments-$name
    wget $link
    tar -xvf $name.tar.xz

    while read arch;
    do
	echo "running kismet on ${arch}"
	            /usr/bin/time -o script_time_${arch}.txt kismet --linux-ksrc="$name/" --summary-csv "$name-kismet_summary_${arch}.csv" -a=${arch} --test-cases-dir="test_cas\
es\
_${arch}/" > script_log_${arch}.txt 2>&1 &
		    echo "kismet done running on ${arch}"
    done < $path/$name.txt

done < $path/linuxsrc.txt
