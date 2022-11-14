#!/bin/bash


# example: cat /data1/paul/kmax/scripts/krepair_evaluation/paper/sample | while read sample; do echo bash /data1/paul/kmax/scripts/krepair_evaluation/paper/randconfig.sh linux2/ $commit x86_64 /data1/paul/kmax/scripts/krepair_evaluation/assets_linuxv513/build_targets.json 3 randconfig/$commit; done

# quick summary: ls -d randconfig/* | wc -l; for upto in {1..10}; do for i in randconfig/*; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py $(for s in $(seq 1 $upto); do echo $i/$s/out; done) | grep EXCLUDED | head -n1; done | grep EXCLUDED | wc -l; done

# summary: for i in randconfig_test/*; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py $i/{1..3}/out | grep EXCLUDED | head -n1 ; done | tee 3; for i in randconfig_test/*; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py $i/{1..6}/out | grep EXCLUDED | head -n1 ; done | tee 6; for i in randconfig_test/*; do python3 /data1/paul/kmax/scripts/krepair_evaluation/paper/total_coverage.py $i/{1..10}/out | grep EXCLUDED | head -n1 ; done | tee 10

# this is an already-cloned linux source directory that only this run
linuxsrclone=${1}
linuxsrclone=$(realpath ${linuxsrclone})

# # path to the patchfile
# patch=$2
# patch=$(realpath ${patch})

# the commit id
commit=${2}

arch=${3}

build_targets=${4}

# number of randconfigs to test
numconfigs=${5}

# this is the directory where output and intermediate files go
outdir=${6}
if [ -d $outdir ]; then
  echo "ERROR: output directory already exists"
  exit 1
else
  mkdir -p $outdir
fi
outdir=$(realpath $outdir)

build_flags=

patch=${outdir}/commit.patch

(cd ${linuxsrclone}; git checkout -f $commit)
(cd ${linuxsrclone}; git clean -dfx)
(cd ${linuxsrclone}; git show > ${patch})

for randnum in $(seq 1 ${numconfigs}); do
    randtestoutdir=${outdir}/${randnum}
    mkdir ${randtestoutdir}
    timefile=${randtestoutdir}/time
    outfile=${randtestoutdir}/out
    config=${randtestoutdir}/config
    (cd ${linuxsrclone}; git clean -dfx)
    (cd ${linuxsrclone}; make ARCH=${arch} randconfig)
    cp ${linuxsrclone}/.config ${config}

    scratchdir=${randtestoutdir}/scratch
    /usr/bin/time -f %e -o ${timefile} koverage --config ${config} --arch ${arch} --linux-ksrc ${linuxsrclone} --check-patch ${patch} --build-targets $build_targets --scratch-dir $scratchdir -o $outfile
done
