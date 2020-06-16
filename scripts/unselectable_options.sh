#!/bin/bash

for dir in .kmax/kclause/*; do
  echo "processing $dir"
  cat "${dir}/kextract" | kclause --unselectable > "${dir}/unselectable.pending"
  mv "${dir}/unselectable.pending" "${dir}/unselectable"
done
