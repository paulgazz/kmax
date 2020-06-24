#!/bin/bash

set -x

scripts_dir=$(dirname $0)

mkdir .kmax/
kmax --version >> .kmax/info.txt
date >> .kmax/info.txt
/usr/bin/time bash ${scripts_dir}/kclauselinux-3.19.sh
/usr/bin/time bash ${scripts_dir}/unselectable_options.sh
/usr/bin/time bash ${scripts_dir}/kmaxarchs-3.19.sh
/usr/bin/time bash ${scripts_dir}/completeness.py
