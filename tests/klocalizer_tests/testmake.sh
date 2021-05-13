#!/bin/bash

set -x

test_klocalizer="bash $(dirname $0)/../../scripts/test_klocalizer.sh"

klocalizer --version

${test_klocalizer} sound/soc/cirrus/ep93xx-ac97.o
${test_klocalizer} sound/soc/cirrus/ep93xx-i2s.c
${test_klocalizer} drivers/usb/storage/alauda.o
${test_klocalizer} sound/soc/intel/boards/glk_rt5682_max98357a.o
${test_klocalizer} sound/mips/sgio2audio.o
${test_klocalizer} drivers/char/efirtc.o
${test_klocalizer} sound/soc/mediatek/common/mtk-btcvsd.o
${test_klocalizer} drivers/watchdog/pnx833x_wdt.o
${test_klocalizer} drivers/tty/n_r3964.o
${test_klocalizer} drivers/block/ataflop.o
${test_klocalizer} drivers/char/ipmi/ipmi_devintf.o drivers/char/ipmi/
${test_klocalizer} virt/kvm/arm/arm.o arch/arm/kvm/ arch/arm/kvm/../../../virt/kvm/arm/arm.o
${test_klocalizer} drivers/watchdog/pcwd.o
${test_klocalizer} drivers/watchdog/mixcomwd.o
${test_klocalizer} virt/kvm/kvm_main.o arch/s390/kvm/ arch/s390/kvm/../../../virt/kvm/kvm_main.o
${test_klocalizer} virt/kvm/kvm_main.o arch/mips/kvm/ arch/mips/kvm/../../../virt/kvm/kvm_main.o
${test_klocalizer} drivers/block/amiflop.o
${test_klocalizer} drivers/video/fbdev/fsl-diu-fb.o
${test_klocalizer} drivers/watchdog/cpwd.o
${test_klocalizer} drivers/watchdog/riowd.o
${test_klocalizer} drivers/gpu/drm/i915/gem/i915_gem_context.o
${test_klocalizer} arch/x86/kernel/irq_64.o
${test_klocalizer} arch/x86/kernel/irq_32.o
${test_klocalizer} arch/x86/um/signal.o
${test_klocalizer} arch/x86/um/ptrace_64.o
${test_klocalizer} arch/x86/um/ptrace_32.o
${test_klocalizer} drivers/edac/edac_pci.o
