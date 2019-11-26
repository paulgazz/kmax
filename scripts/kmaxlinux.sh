#!/bin/bash

script_dir=$(dirname $0)
makefile_override="$script_dir/makefile_override"
for arch in $(ls arch/ | grep -v Kconfig); do
  timeout 4 make ARCH=$arch -f "$makefile_override" alldirs 2>/dev/null
done | tr ' ' '\n' | sort | uniq > .kmax/topleveldirs

/usr/bin/time kmaxall -z $(cat .kmax/topleveldirs) > .kmax/kmax
