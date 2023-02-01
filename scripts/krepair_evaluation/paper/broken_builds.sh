#!/bin/bash

# report which builds are broken.  this uses a witlist of known good
# build outputs, so that it will err on the side of false positives
# (reporting builds as broken that aren't broken)


# takes in stdin a list of build output files to check


# example:

# experiment@church:/data2/test_experiment$ ls /data*/test_experiment/outdir_manyE*/*/defconfig/results/repaired_build.out | bash /data1/paul/kmax/scripts/krepair_evaluation/paper/broken_builds.sh | wc -l
# 34


while read repaired_build_out; do
    egrep -o "Kernel: arch/(x86|arm|xtensa|sh|csky|nios2|riscv|microblaze)/boot/(|bz|z)Image(|\.bz|\.gz) is ready|Kernel arch/alpha/boot/vmlinux.gz is ready|GZIP    arch/arm64/boot/Image.gz|WRAP    arch/powerpc/boot/zImage.epapr|OBJCOPY arch/(openrisc|s390)/boot/(vmlinux.bin|bzImage)|gzip -9c vmlinux.tmp >vmlinux.gz" ${repaired_build_out} >/dev/null 2>&1
    if [[ $? -ne 0 ]]; then
	echo ${repaired_build_out}
    fi
done
