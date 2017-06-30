## Setup
https://i4gerrit.informatik.uni-erlangen.de/undertaker
undertaker-kconfigdump # to create models for each version

# undertaker/python/vamos/golem/kbuild.py line 585 added variant="x86"
# since it doesn't seem to use the right x86 arch name

git checkout v3.19
python ../undertaker/python/golem -v -i 2>&1 | tee run_golem_3.19x86
grep ^FILE run_golem_3.19x86 | cut -f1 -d  | cut -c6- | sort | uniq > golem_3.19x86.txt

git checkout v2.6.33.3
python ../undertaker/python/golem -v -i 2>&1 | tee run_golem_2.6.33.3x86
grep ^FILE run_golem_2.6.33.3x86 | cut -f1 -d  | cut -c6- | sort | uniq > golem_2.6.33.3x86.txt
