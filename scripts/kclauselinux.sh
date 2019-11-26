#!/bin/bash

set -x

script_dir=$(dirname $0)
for arch in $(ls arch/ | grep -v Kconfig | shuf); do
  if [[ "$arch" == "um" ]]; then
    srcarch="x86"
  else
    srcarch="$arch"
  fi
  make ARCH=$arch defconfig
  mkdir -p .kmax/kclause/$arch
  "$script_dir/../kconfig_extractor/kconfig_extractor" --extract -e ARCH=$arch -e SRCARCH=$srcarch -e KERNELVERSION=kcu -e srctree=./ -e CC=cc Kconfig > .kmax/kclause/$arch/kconfig_extract
  /usr/bin/time kclause --remove-orphaned-nonvisible < .kmax/kclause/$arch/kconfig_extract > .kmax/kclause/$arch/kclause
done
