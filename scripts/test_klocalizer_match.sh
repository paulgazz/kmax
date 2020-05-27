#!/bin/bash

if [[ "${#}" < "1" ]]; then
  echo "USAGE: $(basename ${0}) compilation_unit arch config [build_path] [kbuild_path]"
  echo "  compilation_unit  The name of the compilation unit to localize and compile."
  echo "  arch              The architecture to build for."
  echo "  config            The make target that generates the config to match."
  echo "  build_path        The .o file or subdir to pass to Make (needed because of buggy build on single unit)."
  echo "  kbuild_path       The path Kbuild follows to reach the source file."
  exit 1
fi

set -x

scripts_dir="$(dirname $0)"

filename=$1
arch=$2
config=$3
if [[ "${#}" > "3" ]]; then
  target="${4}"
else
  target="$filename"
  # target="$(dirname $filename)/"
fi
if [[ "${#}" > "4" ]]; then
  kbuild_path="${5}"
else
  kbuild_path="$filename"
fi

if [[ "${arch}" == "um32" ]]; then
  archvar="ARCH=um SUBARCH=i386"
else
  archvar="ARCH=${arch}"
fi
timeout 30 "${scripts_dir}/make.cross" -j 4 $archvar $config
config_to_match="$config.$arch"
cp .config $config_to_match

echo "$filename"
/usr/bin/time klocalizer -a $arch --match $config_to_match "${filename}" 2> time.txt
errcodekloc=${?}
cat time.txt
if [[ $errcodekloc -eq 4 ]]; then
  grep "${kbuild_path}" archname.txt
  if [[ "${?}" -eq 0 ]]; then
    /usr/bin/time klocalizer -a $arch --match $config_to_match "${kbuild_path}" 2> time.txt
    errcodekloc=${?}
    cat time.txt
  fi
fi
timetaken="$(cat time.txt | tail -n2 | head -n1 | cut -f1 -d" " )"
if [[ ${errcodekloc} -eq 0 ]]; then
  numremoved=$(cat time.txt | egrep "INFO: Found satisfying config by removing (.*) assumptions." | cut -f7 -d' ')
  mkdir -p matched_configs
  config_klocalizer=$(mktemp -p matched_configs/ configXXXXX)
  cp .config $config_klocalizer
  timeout 30 "${scripts_dir}/make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
  # "${scripts_dir}/make.cross" $archvar clean >> build.txt 2>&1
  timeout 2m "${scripts_dir}/make.cross" -j 4 $archvar "$target" >> build.txt 2>&1
  errcodemake=${?}
  tail -n1000 build.txt
  egrep "(CC|CC [M]) *$kbuild_path" build.txt
  errcodegrep=${?}
  if [[ ${errcodegrep} -eq 0 ]]; then
    if [[ ${errcodemake} -eq 0 ]]; then
      echo "PASS all $timetaken $filename $arch $config_klocalizer $numremoved"
    else
      echo "PASS make.cross_error $timetaken $filename $arch $config_klocalizer $numremoved"
    fi
  else
    # try ignoring errors while building
    cp  $config_klocalizer .config  # restore klocalizer .config again
    timeout 30 "${scripts_dir}/make.cross" -j 4 $archvar olddefconfig > build.txt 2>&1
    # "${scripts_dir}/make.cross" $archvar clean >> build.txt 2>&1
    timeout 2m "${scripts_dir}/make.cross" -i -j 4 $archvar "$target" > build.txt 2>&1
    errcodemake=${?}
    tail -n1000 build.txt
    egrep "(CC|CC [M]) *$kbuild_path" build.txt
    errcodegrep=${?}
    if [[ ${errcodegrep} -eq 0 ]]; then
      echo "PASS make.cross_ignored_errors $timetaken $filename $arch $config_klocalizer $numremoved"
    else
      echo "FAIL make.cross_missing $timetaken $filename $arch $config_klocalizer $numremoved"
    fi
  fi
elif [[ ${errcodekloc} -eq 4 ]]; then
  echo "NONE kbuild_paths need to pass a full kbuild path"
elif [[ ${errcodekloc} -eq 10 ]]; then
  echo "NONE CONFIG_BROKEN $timetaken $filename"
else
  echo "FAIL klocalizer(${errcodekloc}) $timetaken $filename"
fi
