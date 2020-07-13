#!/bin/bash

for dir in .kmax/kclause/*; do
  echo "processing $dir"
  /usr/bin/time kclause --remove-orphaned-nonvisible < "${dir}/kextract" > ."${dir}/kclause.pending"
  mv "${dir}/kclause.pending" "${dir}/kclause"
done
