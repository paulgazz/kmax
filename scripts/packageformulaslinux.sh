#!/bin/bash

set -x

if [ "${#}" -gt 0 ]; then
  version="${1}"
else
  version=$(git describe)
  if [ "${?}" -ne 0 ]; then
    echo "could not find git tag"
    exit 1
  fi
fi

tar -jcvf "kmax-formulas_linux-${version}.tar.bz2" .kmax/
