#!/bin/bash

set -x

scripts_dir=$(dirname $0)


# get linux source
mkdir ~/src/
cd ~/src
wget https://cdn.kernel.org/pub/linux/kernel/v3.x/linux-3.19.tar.xz
tar -xvf linux-3.19.tar.xz
cd linux-3.19

# get unselectable options and run kmax on each architecture
mkdir .kmax/
kmax --version >> .kmax/info.txt
date >> .kmax/info.txt
/usr/bin/time bash ${scripts_dir}/kextractlinux-3.19.sh
/usr/bin/time bash ${scripts_dir}/unselectable_options.sh
/usr/bin/time bash ${scripts_dir}/kmaxarchs.sh
/usr/bin/time bash ${scripts_dir}/completeness.py 3.19 '.kmax/archs/units.*'


# wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.7.5.tar.xz
