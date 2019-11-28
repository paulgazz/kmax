# Klocalizer Tests

## Setup

Run the `testmake.sh` script, which uses `klocalizer` to find a configuration, then `make.cross` to clean and build it.

    /path/to/tests/klocalizer_tests/testmake.sh
    egrep "^(PASS|FAIL|NONE)" testmake.out

The script checks that `klocalizer` was successful, that `make.cross` is succesful, and that `make.cross`'s output actually contains the `CC` log for the compilation unit

The output will contain

- `PASS`
- `FAIL` either because `make.cross` failed (`make.cross_error`) or it did not build the compilation unit (`make.cross_missing`)
- `NONE` which is currently used when `klocalizer` finds a dependency on `CONFIG_BROKEN`, because even a satisfying configuration won't build.

## Results

| compilation unit | klocalizer | make.cross | notes |
|---|---|---|
| drivers/usb/storage/alauda.o | yes | yes | |
| sound/soc/intel/boards/glk_rt5682_max98357a.o | yes | yes | |
| sound/mips/sgio2audio.o | yes | yes | |
| drivers/char/efirtc.o | yes | yes | |
| sound/soc/mediatek/common/mtk-btcvsd.o | yes | yes | |
| drivers/watchdog/pnx833x_wdt.o | `CONFIG_BROKEN` | | |
| drivers/tty/n_r3964.o | `CONFIG_BROKEN` | | |
| drivers/block/ataflop.o | yes | yes | |
| drivers/char/ipmi/ipmi_devintf.o | yes | yes | |
| virt/kvm/arm/arm.o | yes | __no__ | `klocalizer` needs to handle arch-specific directories, `arch/s390/kvm/../../../virt/kmax` |
| drivers/watchdog/pcwd.o | yes | yes | |
| drivers/watchdog/mixcomwd.o | yes | yes | |
| virt/kvm/kvm_main.o | yes | __no__ | `klocalizer` needs to handle arch-specific directories, `arch/s390/kvm/../../../virt/kmax` |
| drivers/block/amiflop.o | yes | yes | |
| drivers/video/fbdev/fsl-diu-fb.o | yes | yes | |
| drivers/watchdog/cpwd.o | yes | yes | |
| drivers/watchdog/riowd.o | yes | yes | |
| drivers/gpu/drm/i915/gem/i915_gem_context.o | __no__ | | `kmax` bug |
| arch/x86/kernel/irq_64.o | yes | yes | |
| arch/x86/kernel/irq_32.o | yes | yes | |
| arch/x86/um/signal.o | yes | __no__ | `klocalizer` needs to handle arch-specific directories, `um` |
| arch/x86/um/ptrace_32.o | yes | __no__ | `klocalizer` needs to handle arch-specific directories, `um` |
