#!/bin/bash

set -x

kmax --version

/usr/bin/time kmaxall -a $(find arch/ -maxdepth 1 -mindepth 1 | egrep -v ".gitignore|Kconfig") block certs crypto drivers fs init ipc kernel lib mm net samples security sound usr virt > .kmax/units.pending
mv .kmax/units.pending .kmax/units
