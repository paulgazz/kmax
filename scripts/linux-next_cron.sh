#!/bin/bash

set -x

(
  flock -x -w 10 200 || exit 1

  # keychain
  eval $(keychain --agents ssh --eval --quiet)

  script_dir="$(dirname $0)"

  cd ~/src/linux_kmaxspecs

  git remote update
  git fetch linux-next
  git fetch linux-next --tags

  today="$(date +%Y%m%d)"

  git checkout next-$today
  errorcode=${?}
  if [[ $errorcode == 0 ]]; then
    timeout 3h bash "$script_dir/formulas.sh"
  else
    echo "No tag for today found."
  fi

) 200>/var/lock/.linux-next_cron_sync.exclusivelock
