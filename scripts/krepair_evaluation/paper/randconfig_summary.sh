scriptsdir=$(dirname $0)

experimentdir=${1}

coverable_patches=${scriptsdir}/coverable_patches

echo "commit,run#,patchcoverage"
cat ${coverable_patches} | while read p; do
    i=${experimentdir}/$p
    for upto in {1..10}; do
	c=$(python3 ${scriptsdir}/patch_coverage.py <(python3 ${scriptsdir}/total_coverage.py $(for s in $(seq 1 $upto); do echo $i/$s/out; done)) | cut -f4 -d' ');
	echo "$p,$upto,$c"
    done
done

# total=$(cat ${scriptsdir}/coverable_patches | wc -l)

# for upto in {1..10}; do
#     notcovered=$(cat ${scriptsdir}/coverable_patches | while read p; do i=${experimentdir}/$p; python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py $(for s in $(seq 1 $upto); do echo $i/$s/out; done) | grep EXCLUDED | head -n1; done | grep EXCLUDED | wc -l);
#     coveredpct=$(echo "($total - $notcovered)/$total" | bc -lq)
#     echo ${upto},${coveredpct}
# done
