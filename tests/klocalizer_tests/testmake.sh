#!/bin/bash

set -x

script_dir="$(dirname $0)/../../scripts/"

# USAGE: test_klocalizer unit_name build_path kbuild_path
test_klocalizer () {
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
  if [[ ${errcodekloc} -eq 0 ]]; then
      arch=$(cat archname.txt)
      if [[ "${arch}" == "um32" ]]; then
          archvar="ARCH=um SUBARCH=i386"
      else
          archvar="ARCH=$(cat archname.txt)"
      fi
      "${script_dir}/make.cross" $archvar olddefconfig > build.txt 2>&1
      "${script_dir}/make.cross" $archvar clean "$target" >> build.txt 2>&1
      errcodemake=${?}
      tail -n50 build.txt
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
  elif [[ ${errcodekloc} -eq 2 ]]; then
    echo "NONE CONFIG_BROKEN $filename"
  else
    echo "FAIL klocalizer $filename"
  fi
}

test_klocalizer drivers/usb/storage/alauda.o
test_klocalizer sound/soc/intel/boards/glk_rt5682_max98357a.o
test_klocalizer sound/mips/sgio2audio.o
test_klocalizer drivers/char/efirtc.o
test_klocalizer sound/soc/mediatek/common/mtk-btcvsd.o
test_klocalizer drivers/watchdog/pnx833x_wdt.o
test_klocalizer drivers/tty/n_r3964.o
test_klocalizer drivers/block/ataflop.o
test_klocalizer drivers/char/ipmi/ipmi_devintf.o drivers/char/ipmi/
# test_klocalizer virt/kvm/arm/arm.o
test_klocalizer drivers/watchdog/pcwd.o
test_klocalizer drivers/watchdog/mixcomwd.o
test_klocalizer virt/kvm/kvm_main.o arch/s390/kvm/ arch/s390/kvm/../../../virt/kvm/kvm_main.o
test_klocalizer drivers/block/amiflop.o
test_klocalizer drivers/video/fbdev/fsl-diu-fb.o
test_klocalizer drivers/watchdog/cpwd.o
test_klocalizer drivers/watchdog/riowd.o
test_klocalizer drivers/gpu/drm/i915/gem/i915_gem_context.o
test_klocalizer arch/x86/kernel/irq_64.o
test_klocalizer arch/x86/kernel/irq_32.o
test_klocalizer arch/x86/um/signal.o
test_klocalizer arch/x86/um/ptrace_64.o
test_klocalizer arch/x86/um/ptrace_32.o
