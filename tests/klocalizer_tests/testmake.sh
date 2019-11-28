#!/bin/bash

set -x

script_dir="$(dirname $0)/../../scripts/"

test_klocalizer () {
  filename=$1

  echo "$filename"
  /usr/bin/time klocalizer "${filename}" > archname.txt
  errcode=${?}
  if [[ ${errcode} -eq 0 ]]; then
      echo "CONFIGURES"
      arch=$(cat archname.txt)
      target="$filename"
      # target="$(dirname $filename)/"
      "${script_dir}/make.cross" ARCH=$(cat archname.txt) clean olddefconfig "$target" |& tee build.txt
      errcode=${?}
      if [[ ${errcode} -eq 0 ]]; then
          grep "CC *$filename" build.txt
          if [[ ${errcode} -eq 0 ]]; then
              echo "PASS configure and make"
          else
            echo "FAIL not found in make output.  be sure to run make clean first"
          fi
      else
        echo "FAIL make"
      fi
  elif [[ ${errcode} -eq 2 ]]; then
    echo "PASS found CONFIG_BROKEN"
  else
    echo "FAIL klocalizer"
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
test_klocalizer drivers/char/ipmi/ipmi_devintf.o
test_klocalizer virt/kvm/arm/arm.o
test_klocalizer drivers/watchdog/pcwd.o
test_klocalizer drivers/watchdog/mixcomwd.o
test_klocalizer virt/kvm/kvm_main.o
test_klocalizer drivers/block/amiflop.o
test_klocalizer drivers/video/fbdev/fsl-diu-fb.o
test_klocalizer drivers/watchdog/cpwd.o
test_klocalizer drivers/watchdog/riowd.o
test_klocalizer drivers/gpu/drm/i915/gem/i915_gem_context.o
test_klocalizer arch/x86/kernel/irq_64.o
test_klocalizer arch/x86/kernel/irq_32.o
test_klocalizer arch/x86/um/signal.o
test_klocalizer arch/x86/um/ptrace_32.o
