#!/bin/bash

set -x

kmaxall --version

# remove prereq usage in arch/arm/Makefile and arch/mips/Makefile to get top-level directories
/usr/bin/time kmaxall -a $(find arch/ -maxdepth 1 -mindepth 1 | egrep -v ".gitignore|Kconfig") block certs crypto drivers fs init ipc kernel lib mm net samples security sound usr virt > .kmax/units.pending1

# add blackfin results which need ARCH set to get top-level directories
/usr/bin/time kmaxall -F .kmax/units.pending1 -a -DARCH=blackfin arch/blackfin/Makefile > .kmax/units.pending2

# TODO: replace shell call to define OS with Linux in arch/um/Makefile
# add um results which need OS set and a call to shell replaced to get top-level directories
/usr/bin/time kmaxall -F .kmax/units.pending2 -DOS=Linux -a arch/um/ > .kmax/units.pending3

cp .kmax/units.pending3 .kmax/units
