#!/bin/bash

set -x

which kismet

# get linux 5.4.4 source
mkdir -p ~/kismet-experiments/
cd ~/kismet-experiments
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.4.tar.xz
tar -xvf linux-5.4.4.tar.xz

# todo: um32 is not supported by kextract, add it once resolved
ARCHS=("x86_64" "i386" "arm" "arm64" "sparc64" "sparc" "powerpc" "mips" "alpha" "arc" "c6x" "csky" "h8300" "hexagon" "ia64" "m68k" "microblaze" "nds32" "nios2" "openrisc" "parisc" "riscv" "s390" "sh" "sh64" "um" "unicore32"  "xtensa")

for arch in ${ARCHS[@]}; do
  echo "running kismet on ${arch}"
  /usr/bin/time -o script_time_${arch}.txt kismet --linux-ksrc="linux-5.4.4/" -a=${arch} --test-cases-dir="test_cases_${arch}/" > script_log_${arch}.txt 2>&1
  echo "kismet done running on ${arch}"
done