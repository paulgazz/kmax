scriptsdir=$(dirname $0)

experimentdir=${1}

coverable_patches=${scriptsdir}/coverable_patches

echo "krepairruntime"
cat ${coverable_patches} | while read commit; do
    commitdir=$(ls -d ${experimentdir}/${commit})
    configdir=${commitdir}/defconfig/results
    if [[ -e ${configdir}/krepair.time ]]; then
	cat ${configdir}/krepair.time
    fi
done
