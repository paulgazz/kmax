#!/bin/bash

set -x

kmaxall --version

# remove prereq usage in arch/arm/Makefile and arch/mips/Makefile to get top-level directories
/usr/bin/time kmaxall -a $(find arch/ -maxdepth 1 -mindepth 1 | egrep -v ".gitignore|Kconfig") block certs crypto drivers fs init ipc kernel lib mm net samples security sound usr virt > .kmax/units.pending1

# add archs that require ARCH to be set to get top-level directories
/usr/bin/time kmaxall -a -F .kmax/kmax.pending1 -DARCH=h8300 arch/h8300/Makefile > .kmax/kmax.pending2
/usr/bin/time kmaxall -a -F .kmax/kmax.pending2 -DARCH=mips arch/mips/Makefile > .kmax/kmax.pending3

# amd includes Makefiles explicitly instead of using Kbuild
/usr/bin/time kmaxall -a -F .kmax/kmax.pending3 -DFULL_AMD_DISPLAY_PATH=drivers/gpu/drm/amd/display -DFULL_AMD_PATH=drivers/gpu/drm/amd -DDISPLAY_FOLDER_NAME=display drivers/gpu/drm > .kmax/kmax.pending4

# TODO: replace shell call to define OS with Linux in arch/um/Makefile
# add um results which need OS set and a call to shell replaced to get top-level directories
/usr/bin/time kmaxall -a -F .kmax/kmax.pending4 -DOS=Linux arch/um/ > .kmax/kmax.pending5

cp .kmax/kmax.pending5 .kmax/kmax
