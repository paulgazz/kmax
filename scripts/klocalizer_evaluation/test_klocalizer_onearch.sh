#!/bin/bash

if [[ "${#}" < "1" ]]; then
  echo "USAGE: $(basename ${0}) compilation_unit arch config [build_path] [kbuild_path]"
  echo "  compilation_unit  The name of the compilation unit to localize and compile."
  echo "  arch              The architecture to build for."
  echo "  build_path        The .o file or subdir to pass to Make (needed because of buggy build on single unit)."
  echo "  kbuild_path       The path Kbuild follows to reach the source file."
  exit 1
fi

set -x

scripts_dir="$(dirname $0)"

filename=$1
arch=$2
if [[ "${#}" > "2" ]]; then
  target="${3}"
else
  target="$filename"
  # target="$(dirname $filename)/"
fi
if [[ "${#}" > "2" ]]; then
  kbuild_path="${4}"
else
  kbuild_path="$filename"
fi

if [[ "${arch}" == "um32" ]]; then
  archvar="ARCH=um SUBARCH=i386"
else
  archvar="ARCH=${arch}"
fi

echo "$filename"
/usr/bin/time klocalizer -a $arch "${filename}" 2> time.txt
errcodekloc=${?}
cat time.txt
if [[ $errcodekloc -eq 4 ]]; then
  grep "${kbuild_path}" archname.txt
  if [[ "${?}" -eq 0 ]]; then
    /usr/bin/time klocalizer -a $arch "${kbuild_path}" 2> time.txt
    errcodekloc=${?}
    cat time.txt
  fi
fi
timetaken="$(cat time.txt | tail -n2 | head -n1 | cut -f1 -d" " )"
if [[ ${errcodekloc} -eq 0 ]]; then
  cp .config .config.klocalizer
  timeout 30 "${scripts_dir}/make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
  # "${scripts_dir}/make.cross" $archvar clean >> build.txt 2>&1
  timeout 2m "${scripts_dir}/make.cross" -j 4 $archvar "$target" >> build.txt 2>&1
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
    timeout 30 "${scripts_dir}/make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
    # "${scripts_dir}/make.cross" $archvar clean >> build.txt 2>&1
    timeout 2m "${scripts_dir}/make.cross" -i -j 4 $archvar "$target" > build.txt 2>&1
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
