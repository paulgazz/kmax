#!/bin/bash

if [[ "${#}" < "1" ]]; then
  echo "USAGE: $(basename ${0}) compilation_unit [build_path] [kbuild_path]"
  echo "  compilation_unit  The name of the compilation unit to localize and compile."
  echo "  build_path        The .o file or subdir to pass to Make (needed because of buggy build on single unit)."
  echo "  kbuild_path       The path Kbuild follows to reach the source file."
  exit 1
fi

set -x

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
/usr/bin/time klocalizer "${filename}" > archname.txt 2> time.txt
errcodekloc=${?}
cat time.txt
cat archname.txt
if [[ $errcodekloc -eq 4 ]]; then
  grep "${kbuild_path}" archname.txt
  if [[ "${?}" -eq 0 ]]; then
    /usr/bin/time klocalizer "${kbuild_path}" > archname.txt 2> time.txt
    errcodekloc=${?}
    cat time.txt
    cat archname.txt
  fi
fi
timetaken="$(cat time.txt | tail -n2 | head -n1 | cut -f1 -d" " )"
if [[ ${errcodekloc} -eq 0 ]]; then
  arch=$(cat archname.txt)
  if [[ "${arch}" == "um32" ]]; then
    archvar="ARCH=um SUBARCH=i386"
  else
    archvar="ARCH=$(cat archname.txt)"
  fi
  cp .config .config.klocalizer
  timeout 30 "make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
  # "make.cross" $archvar clean >> build.txt 2>&1
  timeout 2m "make.cross" -j 4 $archvar "$target" >> build.txt 2>&1
  errcodemake=${?}
  tail -n1000 build.txt
  egrep "(CC|CC [M]) *$kbuild_path" build.txt
  errcodegrep=${?}
  if [[ ${errcodegrep} -eq 0 ]]; then
    if [[ ${errcodemake} -eq 0 ]]; then
      echo "PASS all $timetaken $filename $arch"
    else
      echo "PASS make.cross_error $timetaken $filename $arch"
    fi
  else
    # try ignoring errors while building
    cp .config.klocalizer .config  # restore klocalizer .config again
    timeout 30 "make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
    # "make.cross" $archvar clean >> build.txt 2>&1
    timeout 2m "make.cross" -i -j 4 $archvar "$target" > build.txt 2>&1
    errcodemake=${?}
    tail -n1000 build.txt
    egrep "(CC|CC [M]) *$kbuild_path" build.txt
    errcodegrep=${?}
    if [[ ${errcodegrep} -eq 0 ]]; then
      echo "PASS make.cross_ignored_errors $timetaken $filename $arch"
    else
      echo "FAIL make.cross_missing $timetaken $filename $arch"
    fi
  fi
elif [[ ${errcodekloc} -eq 4 ]]; then
  echo "NONE kbuild_paths need to pass a full kbuild path"
elif [[ ${errcodekloc} -eq 10 ]]; then
  echo "NONE CONFIG_BROKEN $timetaken $filename"
else
  echo "FAIL klocalizer(${errcodekloc}) $timetaken $filename"
fi
