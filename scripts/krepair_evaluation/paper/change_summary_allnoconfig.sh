scriptsdir=$(dirname $0)

experimentdir=${1}
linuxsrclone=${2}

coverable_patches=${scriptsdir}/coverable_patches

echo "commit,configfile,changes"
for configfile in allnoconfig; do
    cat ${coverable_patches} | while read commit; do
	commitdir=$(ls -d ${experimentdir}/${commit})
	configdir=${commitdir}/${configfile}/results
	changepct=0

	if [[ -e ${configdir}/patch_uncovered ]]; then
	    krepair_configs=${configdir}/krepair_configs
	    ls ${krepair_configs}/*.config | while IFS= read -r repaired_config; do
	    # for repaired_olddefconfig in ${configdir}/repaired_olddefconfig*; do
	    	discovered_arch=$(echo $repaired_config | xargs basename | cut -f1 -d\. | cut -f2 -d-)
	    	basename=$(basename $repaired_config)
	    	repaired_olddefconfig=${linuxsrclone}/repaired_olddefconfig.${basename}
		(cd ${linuxsrclone}; git clean -dfx) >&2  # clean the repo
		cp ${repaired_config} ${linuxsrclone}/.config >&2
	    	(cd ${linuxsrclone}; make.cross ARCH=${discovered_arch} olddefconfig) >&2  # clean the repo
	    	cp ${linuxsrclone}/.config ${repaired_olddefconfig} >&2
		changes=$(python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/measure_change.py --original-config ${commitdir}/${configfile}/config ${repaired_olddefconfig} 2>/dev/null | jq .repaired[].change_wrt_original | paste -sd+ | bc -lq)
		echo -n ${commit},
		echo -n ${configfile},
		echo -n ${changes}
		echo
	    done
	fi
    done
done
