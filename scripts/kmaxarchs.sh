#!/bin/bash

# run kmax once for architecture, using the unselectable config options to rule out arch-specific files

mkdir -p .kmax/archs/

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
    outfile=".kmax/archs/units.${arch}"
    /usr/bin/time kmaxall --output-all-unit-types --unselectable "${unselectable}" arch/${srcarch} block certs crypto drivers fs init ipc kernel lib mm net security sound usr virt > "${outfile}.pending"
    mv "${outfile}.pending" "${outfile}"
  fi
done
