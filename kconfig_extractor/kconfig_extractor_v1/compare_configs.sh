#!/bin/bash

if [ $# -lt 2 ]; then
    echo "USAGE: $(basename $0) config1 config2"
    exit 0
fi

config1="${1}"
config2="${2}"

tmp1="$(mktemp)"
tmp2="$(mktemp)"

trap "rm -rf $tmp1 $tmp2" EXIT

function cleanandsort {
  cat $1 | sort | egrep "^(CONFIG_|# CONFIG_.*is not set)"
}

cleanandsort "${config1}" > "${tmp1}"
cleanandsort "${config2}" > "${tmp2}"

diff "${tmp1}" "${tmp2}"
exit $? 
