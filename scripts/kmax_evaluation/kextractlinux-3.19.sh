#!/bin/bash

set -x

script_dir=$(dirname $0)
kclause --version
for arch in x86_64 i386 arm arm64 sparc sparc64 mips ia64 powerpc alpha arc avr32 blackfin c6x cris frv hexagon m32r m68k metag microblaze mn10300 nios2 openrisc parisc s390 score sh sparc tile um unicore32 xtensa; do
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
  kextract --module-version 3.19 $arch .kmax/kclause/$arch/kextract
done
