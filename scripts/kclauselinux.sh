#!/bin/bash

set -x

script_dir=$(dirname $0)
make -C "$script_dir/../kconfig_extractor"
for arch in x86_64 i386 arm arm64 sparc sparc64 mips ia64 powerpc alpha arc c6x csky h8300 hexagon m68k microblaze nds32 nios2 openrisc parisc riscv s390 sh sh64 unicore32 xtensa; do
  if [[ "$arch" == "x86_64" || "$arch" == "i386" ]]; then
    srcarch="x86"
  elif [[ "$arch" == "sparc64" || "$arch" == "sparc" ]]; then
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
