#!/bin/bash

for i in $(ls -d /data{1,2,3}/test_experiment/build_patch/* 2>/dev/null); do
    # repaired="$i/build_results_defconfig_after/*.time"
    # allyes="$i/build_results_allyesconfig_before/*.time"
    repaired="$i/build_results_defconfig_after_makej8/*.time"
    allyes="$i/build_results_allyesconfig_before_makej8/*.time"

    numrepaired=$(ls $repaired 2>&1 | wc -l)
    if [[ "$numrepaired" > "0" ]]; then
	grep "Command exited with non-zero status" $repaired >/dev/null
	if [[ "$?" != 0 ]]; then
	    numallyes=$(ls $allyes 2>&1 | wc -l)
	    if [[ "$numallyes" > "0" ]]; then
		grep "Command exited with non-zero status" $allyes >/dev/null
		if [[ "$?" != 0 ]]; then
		    if [[ "$numrepaired" == "1" ]]; then
			repairedbuild=$(cat $repaired)
		    elif [[ "$numrepaired" > "1" ]]; then
			repairedbuild="multiple"
			repairedbuild=$(cat $repaired | tr '\n' ' ')
			# cat $repaired
		    else
			echo "ERROR: unexpected output"
			exit 1
		    fi
		    allyesbuild=$(cat $allyes)
		    echo "time $repairedbuild $allyesbuild"
		fi
	    fi
	fi
    fi
done


