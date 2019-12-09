#!/bin/bash

set -x

scripts_dir=$(dirname $0)

git describe
if [[ ${?} == 0 ]]; then
  rm -rf .kmax/
  mkdir .kmax/
  klocalizer --version >> .kmax/info.txt
  echo "Linux $(git describe)" >> .kmax/info.txt
  date >> .kmax/info.txt
  /usr/bin/time bash ${scripts_dir}/kmaxlinux.sh |& tee kmaxlinux.out
  /usr/bin/time bash ${scripts_dir}/kclauselinux.sh |& tee kclauselinux.out
else
  echo "ERROR: Please run from top-level of linux repo." >&2
  exit 1
fi
