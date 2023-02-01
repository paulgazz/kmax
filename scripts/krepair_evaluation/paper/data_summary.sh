scriptsdir=$(dirname $0)

experimentdir=${1}

coverable_patches=${scriptsdir}/coverable_patches

echo "commit,configfile,builderrcode,patchcoverage,buildtime"
cat ${coverable_patches} | while read commit; do
    commitdir=$(ls -d ${experimentdir}/${commit})
    configdir=${commitdir}/defconfig/results
    echo -n ${commit},
    echo -n defconfig,
    echo -n $(cat ${commitdir}/defconfig/results/build.errcode),
    echo -n $(python3 ${scriptsdir}/patch_coverage.py ${configdir}/koverage_outfile | cut -d' ' -f4),
    echo -n $(cat ${commitdir}/defconfig/results/build.time | head -n1)
    echo
done

cat ${coverable_patches} | while read commit; do
    commitdir=$(ls -d ${experimentdir}/${commit})
    configdir=${commitdir}/defconfig/results
    echo -n ${commit},
    echo -n krepair,
    if [[ -e ${configdir}/patch_covered ]]; then
	echo -n $(cat ${commitdir}/defconfig/results/build.errcode),
	echo -n $(python3 ${scriptsdir}/patch_coverage.py ${configdir}/koverage_outfile | cut -d' ' -f4),
	echo -n $(cat ${commitdir}/defconfig/results/build.time | head -n1)
    else
	if [[ -e ${configdir}/krepair_one ]]; then
	    builderrcode=$(cat ${commitdir}/defconfig/results/repaired_build.errcode)
	    echo -n ${builderrcode},
	    if [[ "${builderrcode}" == "0" ]]; then
		echo -n $(python3 ${scriptsdir}/patch_coverage.py ${configdir}/repaired_koverage_outfile | cut -d' ' -f4),
		echo -n $(cat ${commitdir}/defconfig/results/repaired_build.time | head -n1)
	    else
		echo -n "n/a,n/a"
	    fi
	else
	    echo -n n/a,
	    ls ${configdir}/repaired_koverage_outfile.* >/dev/null 2>/dev/null
	    if [[ "${?}" == 0 ]]; then
		echo -n $(python3 ${scriptsdir}/patch_coverage.py <(python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py ${configdir}/repaired_koverage_outfile.*) | cut -d' ' -f4),
		echo -n $(ls ${configdir}/repaired_build.time.* | xargs cat | grep -v Command | paste -sd+ | bc -lq)
	    else
		echo -n "n/a,n/a"
	    fi
	fi
    fi
    echo
done

cat ${coverable_patches} | while read commit; do
    commitdir=$(ls -d ${experimentdir}/${commit})
    configdir=${commitdir}/allyesconfig/results
    echo -n ${commit},
    echo -n allyesconfig,
    echo -n $(cat ${commitdir}/allyesconfig/results/build.errcode),
    echo -n $(python3 ${scriptsdir}/patch_coverage.py ${configdir}/koverage_outfile | cut -d' ' -f4),
    echo -n $(cat ${commitdir}/allyesconfig/results/build.time | head -n1)
    echo
done

