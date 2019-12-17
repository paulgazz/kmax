#!/bin/bash

set -x

scripts_dir=$(dirname $0)

if [ "${#}" -gt 0 ]; then
  version="${1}"
else
  version=$(git describe)
  if [ "${?}" -ne 0 ]; then
    echo "could not find git tag"
    exit 1
  fi
fi

rm -rf .kmax/
mkdir .kmax/
klocalizer --version >> .kmax/info.txt
echo "Linux ${version}" >> .kmax/info.txt
date >> .kmax/info.txt
/usr/bin/time bash ${scripts_dir}/kmaxlinux.sh |& tee kmaxlinux.out
/usr/bin/time bash ${scripts_dir}/kclauselinux.sh |& tee kclauselinux.out
tar -jcvf "kmax-formulas_linux-${version}.tar.bz2" .kmax/
