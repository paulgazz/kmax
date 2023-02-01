echo "commit,buildid,count"
cd /data1/test_experiment/inputs/linux
cat /data2/test_experiment/coverable_patches | while read commit; do
    git checkout ${commit} >/dev/null 2>&1
    git clean -dfx >/dev/null 2>&1
    buildid=$(echo -e "import kmax.vcommon\nprint(kmax.vcommon.get_build_system_id('./'))" | python3)
    count=$(cat /data1/test_experiment/formulacache/${buildid}/kclause/*/kextract | grep "^config " | sort | uniq | wc -l)
    echo "${commit},${buildid},${count}"
done
