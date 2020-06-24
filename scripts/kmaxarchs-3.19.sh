#!/bin/bash

# run kmax once for architecture, using the unselectable config options to rule out arch-specific files

set -x

for dir in .kmax/kclause/*; do
  echo "processing ${dir}"
  arch="$(basename ${dir})"
  unselectable="${dir}/unselectable"
  if [[ ! -f "${unselectable}" ]]; then
    echo "\"${unselectable}\" not found.  please run selectable.sh first on the formulas."
  else
    if [[ "$arch" == "x86_64" || "$arch" == "i386" ]]; then
      srcarch="x86"
    elif [[ "$arch" == "sparc64" || "$arch" == "sparc" ]]; then
      srcarch="sparc"
    elif [[ "$arch" == "sh64" || "$arch" == "sh" ]]; then
      srcarch="sh"
    else
      srcarch="$arch"
    fi
    extra_args=""
    if [[ "$arch" == "blackfin" ]]; then
      extra_args=" -DARCH=blackfin "
    elif [[ "$arch" == "um" ]]; then
      extra_args=" -DOS=Linux "
    fi
    outfile="${dir}/units"
    # linux 3.19
    /usr/bin/time kmaxall --output-all-unit-types --unselectable "${unselectable}" $extra_args arch/${srcarch} block crypto drivers fs init ipc kernel lib mm net samples security sound usr virt > "${outfile}.pending" 2> "${outfile}.err"
    mv "${outfile}.pending" "${outfile}"
  fi
done
