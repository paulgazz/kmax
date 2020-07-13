#!/bin/bash

exit(0) # mainly just for reference, not for execution all a once

set -x

scripts_dir=$(dirname $0)

# get linux 3.19 source
mkdir -p ~/src/
cd ~/src
wget https://cdn.kernel.org/pub/linux/kernel/v3.x/linux-3.19.tar.xz
tar -xvf linux-3.19.tar.xz
cd linux-3.19

# get unselectable options, run kmax on each architecture, and check completeness
mkdir -p .kmax/
kmax --version >> .kmax/info.txt
date >> .kmax/info.txt
/usr/bin/time bash ${scripts_dir}/kextractlinux-3.19.sh
/usr/bin/time bash ${scripts_dir}/unselectable_options.sh
/usr/bin/time bash ${scripts_dir}/kmaxarchs.sh
/usr/bin/time bash ${scripts_dir}/kmaxlinuxunits.sh
/usr/bin/time python3 ${scripts_dir}/completeness.py linux-3.19 '.kmax/archs/units.*'

# get linux 5.7.5 source
mkdir -p ~/src/
cd ~/src
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.7.5.tar.xz
tar -xvf linux-5.7.5.tar.xz
cd linux-5.7.5

# get unselectable options, run kmax on each architecture, and check completeness
mkdir .kmax/
kmax --version >> .kmax/info.txt
date >> .kmax/info.txt
/usr/bin/time bash ${scripts_dir}/kextractlinux.sh
/usr/bin/time bash ${scripts_dir}/unselectable_options.sh
/usr/bin/time bash ${scripts_dir}/kmaxarchs.sh
/usr/bin/time bash ${scripts_dir}/kmaxlinuxunits.sh
/usr/bin/time python3 ${scripts_dir}/completeness.py linux-5.7.5 '.kmax/archs/units.*'

# get busybox 1.28.0
mkdir -p ~/src/
cd ~/src
git clone https://git.busybox.net/busybox
cd busybox
git checkout 1_28_0

# run kmax and check completeness
mkdir .kmax/
kmax --version >> .kmax/info.txt
date >> .kmax/info.txt
make allnoconfig; make clean;  # generate the Kbuild files
/usr/bin/time kmaxall -a $(find | grep "Kbuild$" | cut -c3-) > .kmax/units
/usr/bin/time python3 ${scripts_dir}/completeness.py busybox-1.25.0 .kmax/units
