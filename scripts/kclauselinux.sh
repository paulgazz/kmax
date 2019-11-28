#!/bin/bash

set -x

script_dir=$(dirname $0)
# for arch in x86_64 i386 alpha arc arm arm64 c6x csky h8300 hexagon ia64 m68k microblaze mips nds32 nios2 openrisc parisc powerpc riscv s390 sh sh64 sparc32 sparc64 um unicore32 xtensa; do
for arch in i386 x86_64; do
  if [[ "$arch" == "x86_64" || "$arch" == "i386" || "$arch" == "um" ]]; then
    srcarch="x86"
  elif [[ "$arch" == "sparc64" || "$arch" == "sparch32" ]]; then
    srcarch="sparc"
  elif [[ "$arch" == "sh64" || "$arch" == "sh" ]]; then
    srcarch="sh"
  else
    srcarch="$arch"
  fi
  make ARCH=$arch defconfig
  mkdir -p .kmax/kclause/$arch
  "$script_dir/../kconfig_extractor/kconfig_extractor" --extract -e ARCH=$arch -e SRCARCH=$srcarch -e KERNELVERSION=kcu -e srctree=./ -e CC=cc Kconfig > .kmax/kclause/$arch/kconfig_extract
  /usr/bin/time kclause --remove-orphaned-nonvisible < .kmax/kclause/$arch/kconfig_extract > .kmax/kclause/$arch/kclause
done
