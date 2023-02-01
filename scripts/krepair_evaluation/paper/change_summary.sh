scriptsdir=$(dirname $0)

experimentdir=${1}

coverable_patches=${scriptsdir}/coverable_patches

echo "commit,configfile,changes"
# for configfile in allnoconfig defconfig; do
for configfile in defconfig; do
    cat ${coverable_patches} | while read commit; do
	commitdir=$(ls -d ${experimentdir}/${commit})
	configdir=${commitdir}/${configfile}/results
	changepct=0
	
	if [[ -e ${configdir}/patch_uncovered ]]; then
	    for repaired_olddefconfig in ${configdir}/repaired_olddefconfig*; do
		changes=$(python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/measure_change.py --original-config ${commitdir}/${configfile}/config ${repaired_olddefconfig} 2>/dev/null | jq .repaired[].change_wrt_original | paste -sd+ | bc -lq)
		echo -n ${commit},
		echo -n ${configfile},
		echo -n ${changes}
		echo
	    done
	fi
    done
done
