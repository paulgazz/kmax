#!/bin/bash

test_klocalizer () {
  filename=$1

  echo "$filename"
  /usr/bin/time klocalizer "${filename}"

  if [[ ${?} -eq 0 ]]; then
    echo "OKAY"
  else
    echo "FAIL"
  fi
}

test_klocalizer sound/soc/cirrus/ep93xx-ac97.o
test_klocalizer sound/soc/cirrus/ep93xx-i2s.c
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
test_klocalizer arch/x86/um/signal.o
test_klocalizer arch/x86/um/ptrace_32.o
