#!/bin/bash

set -x

git describe
if [[ ${?} == 0 ]]; then
  rm -rf .kmax/
  /usr/bin/time bash ~/research/repos/kmax/scripts/kmaxlinux.sh |& tee kmaxlinux.out
  /usr/bin/time bash ~/research/repos/kmax/scripts/kclauselinux.sh |& tee kclauselinux.out
  bash ~/research/repos/kmax/scripts/packageformulaslinux.sh
  scp kmax-formulas_linux-$(git describe).tar.bz2 linode:/var/www/kmaxtools/formulas/
  # bash /home/paul/research/repos/kmax/tests/klocalizer_tests/testmake.sh |& tee ~/research/repos/kmax/docs/experiments/testmake.$(git describe).out
else
  echo "ERROR: Please run from top-level of linux repo." >&2
  exit 1
fi
