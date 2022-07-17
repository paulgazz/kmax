#!/bin/bash

for dir in .kmax/kclause/*; do
  echo "processing $dir"
  kclause --unselectable < "${dir}/kextract" > "${dir}/unselectable.pending"
  mv "${dir}/unselectable.pending" "${dir}/unselectable"
done
