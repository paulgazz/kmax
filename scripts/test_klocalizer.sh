#!/bin/bash

set -x

if [[ "${#}" < "1" ]]; then
  echo "USAGE: $(basename ${0}) compilation_unit [build_path] [kbuild_path]"
  echo "  compilation_unit  The name of the compilation unit to localize and compile."
  echo "  build_path        The .o file or subdir to pass to Make (needed because of buggy build on single unit)."
  echo "  kbuild_path       The path Kbuild follows to reach the source file."
  exit 1
fi

scripts_dir="$(dirname $0)"

filename=$1
if [[ "${#}" > "1" ]]; then
  target="${2}"
else
  target="$filename"
  # target="$(dirname $filename)/"
fi
if [[ "${#}" > "2" ]]; then
  kbuild_path="${3}"
else
  kbuild_path="$filename"
fi

echo "$filename"
/usr/bin/time klocalizer "${filename}" > archname.txt
errcodekloc=${?}
cat archname.txt
if [[ $errcodekloc -eq 4 ]]; then
  grep "${kbuild_path}" archname.txt
  if [[ "${?}" -eq 0 ]]; then
    /usr/bin/time klocalizer "${kbuild_path}" > archname.txt
    errcodekloc=${?}
  fi
fi
if [[ ${errcodekloc} -eq 0 ]]; then
  arch=$(cat archname.txt)
  if [[ "${arch}" == "um32" ]]; then
    archvar="ARCH=um SUBARCH=i386"
  else
    archvar="ARCH=$(cat archname.txt)"
  fi
  timeout 30 "${scripts_dir}/make.cross" $archvar olddefconfig > build.txt 2>&1
  # "${scripts_dir}/make.cross" $archvar clean >> build.txt 2>&1
  timeout 2m "${scripts_dir}/make.cross" $archvar "$target" >> build.txt 2>&1
  errcodemake=${?}
  tail -n1000 build.txt
  if [[ ${errcodemake} -eq 0 ]]; then
    grep "CC *$kbuild_path" build.txt
    errcodegrep=${?}
    if [[ ${errcodegrep} -eq 0 ]]; then
      echo "PASS all $filename"
    else
      echo "FAIL make.cross_missing $filename"
    fi
  else
    echo "FAIL make.cross_error $filename"
  fi
elif [[ ${errcodekloc} -eq 4 ]]; then
  echo "NONE kbuild_paths need to pass a full kbuild path"
elif [[ ${errcodekloc} -eq 10 ]]; then
  echo "NONE CONFIG_BROKEN $filename"
else
  echo "FAIL klocalizer $filename"
fi
