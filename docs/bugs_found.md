<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Bugs Found by Kmax Tools](#bugs-found-by-kmax-tools)
  - [Linux kernel](#linux-kernel)
    - [drivers: pinctrl: qcom: fix unmet dependency for PINCTRL_MSM when !GPIOLIB](#drivers-pinctrl-qcom-fix-unmet-dependency-for-pinctrl_msm-when-gpiolib)
    - [drivers: gpu: drm: bridge: fix unmet dependency for DRM_KMS_HELPER when !DRM_KMS_HELPER](#drivers-gpu-drm-bridge-fix-unmet-dependency-for-drm_kms_helper-when-drm_kms_helper)
    - [mips: fix unmet dependency for FRAME_POINTER when !ARCH_WANT_FRAME_POINTERS](#mips-fix-unmet-dependency-for-frame_pointer-when-arch_want_frame_pointers)
    - [mips: fix unmet dependency for MTD_COMPLEX_MAPPINGS when !MTD](#mips-fix-unmet-dependency-for-mtd_complex_mappings-when-mtd)
    - [mips: fix unmet dependency for DEBUG_INFO when !DEBUG_KERNEL](#mips-fix-unmet-dependency-for-debug_info-when-debug_kernel)
    - [media: drivers: media: pci: sta2x11: fix unmet dependency for VIDEO_ADV7180 when !GPIOLIB](#media-drivers-media-pci-sta2x11-fix-unmet-dependency-for-video_adv7180-when-gpiolib)
    - [drivers: tty: serial: fix unmet dependency for SERIAL_EARLYCON when !SERIAL_CORE](#drivers-tty-serial-fix-unmet-dependency-for-serial_earlycon-when-serial_core)
    - [fs: nfsd: fix unmet dependency for CRYPTO_SHA256 and CRYPTO_MD5 when !CRYPTO](#fs-nfsd-fix-unmet-dependency-for-crypto_sha256-and-crypto_md5-when-crypto)
    - [net: marvell: build error due to unmet dependency for MVMDIO by MV643XX_ETH](#net-marvell-build-error-due-to-unmet-dependency-for-mvmdio-by-mv643xx_eth)
    - [mtd: rawnand: build error due to unmet dependency for MFD_SYSCON by MTD_NAND_MESON](#mtd-rawnand-build-error-due-to-unmet-dependency-for-mfd_syscon-by-mtd_nand_meson)
    - [irqchip: build error due to unmet dependency for MFD_SYSCON by INGENIC_TCU_IRQ](#irqchip-build-error-due-to-unmet-dependency-for-mfd_syscon-by-ingenic_tcu_irq)
    - [soc: samsung: build error due to unmet dependency for MFD_SYSCON by EXYNOS_CHIPID](#soc-samsung-build-error-due-to-unmet-dependency-for-mfd_syscon-by-exynos_chipid)
    - [staging: ralink-gdma: build error due to unmet dependency for DMA_ENGINE by DMA_RALINK](#staging-ralink-gdma-build-error-due-to-unmet-dependency-for-dma_engine-by-dma_ralink)
    - [MIPS: BMC47xx: build error due to unmet dependency for SSB_B43_PCI_BRIDGE by BCM47XX_SSB](#mips-bmc47xx-build-error-due-to-unmet-dependency-for-ssb_b43_pci_bridge-by-bcm47xx_ssb)
    - [watchdog: build error due to unmet dependency for MFD_SYSCON by ARMADA_37XX_WATCHDOG](#watchdog-build-error-due-to-unmet-dependency-for-mfd_syscon-by-armada_37xx_watchdog)
    - [arm64: build error due to unmet dependency for PINCTRL_EXYNOS by ARCH_EXYNOS](#arm64-build-error-due-to-unmet-dependency-for-pinctrl_exynos-by-arch_exynos)
    - [ARM: davinci: build error due to unmet dependency for CPU_DCACHE_WRITETHROUGH by ARCH_DAVINCI_DA830](#arm-davinci-build-error-due-to-unmet-dependency-for-cpu_dcache_writethrough-by-arch_davinci_da830)
    - [ASoC: atmel: build error due to unmet dependency for SND_ATMEL_SOC_PDC by SND_ATMEL_SOC_SSC_PDC](#asoc-atmel-build-error-due-to-unmet-dependency-for-snd_atmel_soc_pdc-by-snd_atmel_soc_ssc_pdc)
    - [iio: adc: build error due to unmet dependency for MFD_STM32_TIMERS by STM32_ADC_CORE](#iio-adc-build-error-due-to-unmet-dependency-for-mfd_stm32_timers-by-stm32_adc_core)
    - [sparc64: build error due to unmet dependency for COMPAT_BINFMT_ELF by COMPAT](#sparc64-build-error-due-to-unmet-dependency-for-compat_binfmt_elf-by-compat)
    - [iio: light: build error due to unmet dependency for IIO_TRIGGERED_BUFFER by VCNL4035](#iio-light-build-error-due-to-unmet-dependency-for-iio_triggered_buffer-by-vcnl4035)
    - [Input: build error due to unmet dependency for IIO_BUFFER_CB by TOUCHSCREEN_ADC](#input-build-error-due-to-unmet-dependency-for-iio_buffer_cb-by-touchscreen_adc)
    - [MIPS: BCM47XX: build error due to unmet dependency for BCMA_DRIVER_PCI_HOSTMODE by BCM47XX_BCMA](#mips-bcm47xx-build-error-due-to-unmet-dependency-for-bcma_driver_pci_hostmode-by-bcm47xx_bcma)
    - [arc: build error due to missing ctop constants](#arc-build-error-due-to-missing-ctop-constants)
    - [m68k: build error due to missing M680x0 dependency for MMU_MOTOROLA](#m68k-build-error-due-to-missing-m680x0-dependency-for-mmu_motorola)
    - [media: mantis: remove orphan mantis_core.c](#media-mantis-remove-orphan-mantis_corec)
    - [regmap: potential dead code due to unused symbol REGCACHE_COMPRESSED](#regmap-potential-dead-code-due-to-unused-symbol-regcache_compressed)
    - [arc: eznps: fix allmodconfig kconfig warning](#arc-eznps-fix-allmodconfig-kconfig-warning)
    - [staging: netlogic: NETLOGIC_XLR_NET overleaps kconfig dependency for NETDEVICES](#staging-netlogic-netlogic_xlr_net-overleaps-kconfig-dependency-for-netdevices)
    - [staging: mt7621-dma: MTK_HSDMA overleaps kconfig dependency of DMADEVICES](#staging-mt7621-dma-mtk_hsdma-overleaps-kconfig-dependency-of-dmadevices)
    - [ASoC: fix kconfig dependency warnings for SND_SOC_WM8731](#asoc-fix-kconfig-dependency-warnings-for-snd_soc_wm8731)
    - [drm/sun4i: DRM_SUN6I_DSI overleaps Kconfig dependencies of PHY_SUN6I_MIPI_DPHY](#drmsun4i-drm_sun6i_dsi-overleaps-kconfig-dependencies-of-phy_sun6i_mipi_dphy)
    - [PM: PM_SLEEP_SMP overleaps Kconfig dependencies of HOTPLUG_CPU](#pm-pm_sleep_smp-overleaps-kconfig-dependencies-of-hotplug_cpu)
    - [ocxl: fix kconfig dependency warning for OCXL](#ocxl-fix-kconfig-dependency-warning-for-ocxl)
    - [net: broadcom: CNIC overleaps Kconfig dependency of UIO](#net-broadcom-cnic-overleaps-kconfig-dependency-of-uio)
    - [net: ipv6: fix kconfig dependency warning for IPV6_SEG6_HMAC](#net-ipv6-fix-kconfig-dependency-warning-for-ipv6_seg6_hmac)
    - [platform/x86: fix kconfig dependency warning for FUJITSU_LAPTOP](#platformx86-fix-kconfig-dependency-warning-for-fujitsu_laptop)
    - [sh: dma: fix kconfig dependency for G2_DMA](#sh-dma-fix-kconfig-dependency-for-g2_dma)
    - [Input: MOUSE_ATARI overleaps Kconfig dependency of ATARI_KBD_CORE](#input-mouse_atari-overleaps-kconfig-dependency-of-atari_kbd_core)
    - [ASoC: cros_ec_codec: fix kconfig dependency warning for SND_SOC_CROS_EC_CODEC](#asoc-cros_ec_codec-fix-kconfig-dependency-warning-for-snd_soc_cros_ec_codec)
    - [soc/tegra: fuse: SOC_TEGRA_FUSE violates Kconfig dependency of TEGRA20_APB_DMA](#soctegra-fuse-soc_tegra_fuse-violates-kconfig-dependency-of-tegra20_apb_dma)
    - [powerpc: MPC10X_BRIDGE violates Kconfig dependency of PPC_INDIRECT_PCI on PCI](#powerpc-mpc10x_bridge-violates-kconfig-dependency-of-ppc_indirect_pci-on-pci)
    - [powerpc: obsolete driver: Marvell MV64X60 MPSC](#powerpc-obsolete-driver-marvell-mv64x60-mpsc)
    - [IB/rxe: fix kconfig dependency warning for RDMA_RXE](#ibrxe-fix-kconfig-dependency-warning-for-rdma_rxe)
    - [clk: bcm: fix kconfig dependency warning for CLK_BCM2711_DVP](#clk-bcm-fix-kconfig-dependency-warning-for-clk_bcm2711_dvp)
    - [staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_CCMP](#staging-rtl8192e-fix-kconfig-dependency-warning-for-rtllib_crypto_ccmp)
    - [staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_WEP](#staging-rtl8192e-fix-kconfig-dependency-warning-for-rtllib_crypto_wep)
    - [staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_TKIP](#staging-rtl8192e-fix-kconfig-dependency-warning-for-rtllib_crypto_tkip)
    - [platform/x86: fix kconfig dependency warning for LG_LAPTOP](#platformx86-fix-kconfig-dependency-warning-for-lg_laptop)
    - [arc: plat-hsdk: fix kconfig dependency warning when !RESET_CONTROLLER](#arc-plat-hsdk-fix-kconfig-dependency-warning-when-reset_controller)
    - [ARM: davinci: fix kconfig dependency warning when !PINCTRL](#arm-davinci-fix-kconfig-dependency-warning-when-pinctrl)
    - [ARM: davinci: fix kconfig dependency warning when !GPIOLIB](#arm-davinci-fix-kconfig-dependency-warning-when-gpiolib)
    - [pinctrl: bcm: fix kconfig dependency warning when !GPIOLIB](#pinctrl-bcm-fix-kconfig-dependency-warning-when-gpiolib)
    - [nvme: tcp: fix kconfig dependency warning when !CRYPTO](#nvme-tcp-fix-kconfig-dependency-warning-when-crypto)
    - [MIPS: remove the obsolete RM7000 extended interrupts handler](#mips-remove-the-obsolete-rm7000-extended-interrupts-handler)
    - [net: Wireless: fix unmet direct dependendices config warning when !CRYPTO](#net-wireless-fix-unmet-direct-dependendices-config-warning-when-crypto)
    - [Missing dependency for the MAX77650 MFD driver](#missing-dependency-for-the-max77650-mfd-driver)
      - [Description](#description)
      - [History](#history)
  - [axTLS](#axtls)
    - [Header compile issue when "Create Language Bindings" is used](#header-compile-issue-when-create-language-bindings-is-used)
      - [Description](#description-1)
      - [History](#history-1)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Bugs Found by Kmax Tools

## Linux kernel

### efi: fix unmet dependency on CRYPTO for CRYPTO_LIB_SHA256

2021-12-15 [Patch](https://lkml.org/lkml/2021/12/15/1300)

### ARM: fix unmet dependency on BITREVERSE for HAVE_ARCH_BITREVERSE

2021-10-29 [PATCH](https://lkml.org/lkml/2021/10/29/832)

### pinctrl: qcom: fix unmet dependencies on GPIOLIB for GPIOLIB_IRQCHIP

2021-11-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=60430d4c4eddcdf8eac2bdbec9704f84a436eedf): Committed into linux-next.

2021-10-28 [PATCH](https://lkml.org/lkml/2021/10/28/1086)

### ASoC: fix unmet dependencies on GPIOLIB for SND_SOC_RT1015P

2021-10-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/broonie/sound.git/commit/?id=2554877e4b08d258c2def27e3a0fd49d60a9a2c0): Committed into sound/for-next.

2021-10-28 [PATCH](https://lkml.org/lkml/2021/10/28/1066)

### drm/sun4i: fix unmet dependency on RESET_CONTROLLER for PHY_SUN6I_MIPI_DPHY

2021-11-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=bb162bb2b4394108c8f055d1b115735331205e28): Committed into linux-next.

2021-10-28 [Patch](https://lkml.org/lkml/2021/10/28/1003)

### scsi: ufs: fix unmet dependency for RESET_TI_SYSCON when !RESET_CONTROLLER

2021-10-28 [Patch](https://lkml.org/lkml/2021/10/28/905)

### ASoC: fix unmet dependencies on GPIOLIB for SND_SOC_DMIC

2021-10-28 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=5c7dee4407dcd3522a133acdd90d64bf41d00986): Committed into linux-next.

2021-10-28 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/broonie/sound.git/commit/?id=5c7dee4407dcd3522a133acdd90d64bf41d00986): Committed into sound/for-next.

2021-10-27 [Patch](https://lkml.org/lkml/2021/10/27/894)

### drm: bridge: fix unmet dependency for DRM_PANEL_BRIDGE when !DRM_KMS_HELPER

2021-10-25 [Patch](https://lkml.org/lkml/2021/10/25/1972)

### ASoC: fix unmet dependency when SND_SOC_INTEL_KBL_DA7219_MAX98357A_MACH && !GPIOLIB

2021-10-25 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=3e701151feefc58c5194e1d9eb5af98568574f2d): Committed into linux-next.

2021-10-24 [Patch](https://lkml.org/lkml/2021/10/10/311)

### ASoC: fix unmet dependency for SND_SOC_MAX98357A when !GPIOLIB

2021-10-22 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=6cace797f1a8d54ecb42a3d327cbc0b231114ed0): Committed into linux-next.

2021-10-10 [Patch](https://lkml.org/lkml/2021/10/27/894)

### drivers: pinctrl: qcom: fix unmet dependency for PINCTRL_MSM when !GPIOLIB

2021-04-14 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=376f9e34c10faa3e94b881088b160cfda540ae5f): Committed into linux-next.

2021-02-22 [Patch](https://lkml.org/lkml/2021/2/25/105)

### drivers: gpu: drm: bridge: fix unmet dependency for DRM_PANEL_BRIDGE when !DRM_KMS_HELPER

2021-04-01 [Commit](https://cgit.freedesktop.org/drm/drm-misc/commit/?id=62066d3164467167fc27b2383f67d097e39bf176): Committed into drm-misc-next.

2021-04-01 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=62066d3164467167fc27b2383f67d097e39bf176): Committed into linux-next.

2021-02-22 [Patch](https://lkml.org/lkml/2021/2/22/1167)

### mips: fix unmet dependency for FRAME_POINTER when !ARCH_WANT_FRAME_POINTERS

2021-04-09 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=7d37cb2c912dc5c25ffac784a4f9b98c06c6bd08): Committed into linux-next.

2021-04-09 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=7d37cb2c912dc5c25ffac784a4f9b98c06c6bd08): Committed into linux-stable.

2021-03-29 [Patch](https://lkml.org/lkml/2021/3/29/1692)

### mips: fix unmet dependency for MTD_COMPLEX_MAPPINGS when !MTD

2021-03-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=f766b28a5edfd86600e55360cc4bf29c71cca2eb): Committed into linux-next.

2021-03-26 [Patch](https://lkml.org/lkml/2021/3/26/26)

### mips: fix unmet dependency for DEBUG_INFO when !DEBUG_KERNEL

2021-03-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=e87f69a5187d9414c3c2dae9539649e3823ee32c): Committed into linux-next.

2021-03-26 [Patch](https://lkml.org/lkml/2021/3/26/21)

### media: drivers: media: pci: sta2x11: fix unmet dependency for VIDEO_ADV7180 when !GPIOLIB

2021-03-11 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=24df8b74c8b2fb42c49ffe8585562da0c96446ff): Committed into linux-next.

2021-02-25 [Patch](https://lkml.org/lkml/2021/2/25/87)

### drivers: tty: serial: fix unmet dependency for SERIAL_EARLYCON when !SERIAL_CORE

2021-03-10 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=196ebe5c000afbfe67b8561f716e365174552bd7): Committed into linux-next.

2021-02-24 [Patch](https://lkml.org/lkml/2021/2/24/1184)

### fs: nfsd: fix unmet dependency for CRYPTO_SHA256 and CRYPTO_MD5 when !CRYPTO

2021-03-06 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=7005227369079963d25fb2d5d736d0feb2c44cf6): Committed into linux-next.

2021-03-06 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=7005227369079963d25fb2d5d736d0feb2c44cf6): Committed into linux-stable.

2021-02-19 [Patch](https://lkml.org/lkml/2021/2/19/669)

### net: marvell: build error due to unmet dependency for MVMDIO by MV643XX_ETH

2020-11-05 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210063)

### mtd: rawnand: build error due to unmet dependency for MFD_SYSCON by MTD_NAND_MESON

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210061)

### irqchip: build error due to unmet dependency for MFD_SYSCON by INGENIC_TCU_IRQ

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210059)

### soc: samsung: build error due to unmet dependency for MFD_SYSCON by EXYNOS_CHIPID

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210057)

### staging: ralink-gdma: build error due to unmet dependency for DMA_ENGINE by DMA_RALINK

2020-11-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-linus&id=06ea594051707c6b8834ef5b24e9b0730edd391b): Committed into gregkh/staging/staging-linus branch.

2020-11-04 [Patch](https://lkml.org/lkml/2020/11/4/912)

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210055)

### MIPS: BMC47xx: build error due to unmet dependency for SSB_B43_PCI_BRIDGE by BCM47XX_SSB

2020-11-04 [Patch](https://lkml.org/lkml/2020/11/4/754)

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210051)

### watchdog: build error due to unmet dependency for MFD_SYSCON by ARMADA_37XX_WATCHDOG

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210049)

### arm64: build error due to unmet dependency for PINCTRL_EXYNOS by ARCH_EXYNOS

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210047)

### ARM: davinci: build error due to unmet dependency for CPU_DCACHE_WRITETHROUGH by ARCH_DAVINCI_DA830

2020-11-04 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210041)

### ASoC: atmel: build error due to unmet dependency for SND_ATMEL_SOC_PDC by SND_ATMEL_SOC_SSC_PDC

2020-11-02 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210003)

### iio: adc: build error due to unmet dependency for MFD_STM32_TIMERS by STM32_ADC_CORE

2020-10-26 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209889)

### sparc64: build error due to unmet dependency for COMPAT_BINFMT_ELF by COMPAT

2020-11-03 [Patch](https://lkml.org/lkml/2020/11/2/1230)

2020-10-26 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209885)

### iio: light: build error due to unmet dependency for IIO_TRIGGERED_BUFFER by VCNL4035

2020-11-08 [Confirmation](https://lkml.org/lkml/2020/11/8/159): Marked for stable.

2020-11-03 [Patch](https://lkml.org/lkml/2020/11/2/1219)

2020-10-26 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209883)

### Input: build error due to unmet dependency for IIO_BUFFER_CB by TOUCHSCREEN_ADC

2020-11-03 [Confirmation](https://www.spinics.net/lists/linux-input/msg69800.html)

2020-11-03 [Patch](https://lkml.org/lkml/2020/11/2/1208)

2020-10-26 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209881)

### MIPS: BCM47XX: build error due to unmet dependency for BCMA_DRIVER_PCI_HOSTMODE by BCM47XX_BCMA

2020-11-03 [Patch](https://lkml.org/lkml/2020/11/2/1186)

2020-10-26 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209879)

### arc: build error due to missing ctop constants

2020-09-24 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209377)

### m68k: build error due to missing M680x0 dependency for MMU_MOTOROLA

2020-09-24 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209371)

### media: mantis: remove orphan mantis_core.c

2020-09-22 [Patch](https://lkml.org/lkml/2020/9/22/520)

### regmap: potential dead code due to unused symbol REGCACHE_COMPRESSED

2020-09-22 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209349)

### arc: eznps: fix allmodconfig kconfig warning

2020-09-22 [Patch](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=1928b36cfa4df1aeedf5f2644d0c33f3a1fcfd7b): Found with the config generated for `arch/arc/kernel/arc_hostlink.o` on linux-5.4.4 by klocalizer. Already fixed in a later version.

### staging: netlogic: NETLOGIC_XLR_NET overleaps kconfig dependency for NETDEVICES

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209315)

2021-03-26 [Patch](https://lkml.org/lkml/2021/3/26/32)

2021-03-26 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=a5bf1a101a19dbb38be7ffebe2650449e344c892): Committed into linux-next.

### staging: mt7621-dma: MTK_HSDMA overleaps kconfig dependency of DMADEVICES

2020-11-04 [Report: build error](https://bugzilla.kernel.org/show_bug.cgi?id=209313#c1): It was later found that this issue can lead to build errors as well.

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209313)

### ASoC: fix kconfig dependency warnings for SND_SOC_WM8731

2020-09-18 [Confirmation](https://lkml.org/lkml/2020/9/18/661): The issue was confirmed but a different fix was suggested.

2020-09-18 [Patch](https://lkml.org/lkml/2020/9/18/626)

### drm/sun4i: DRM_SUN6I_DSI overleaps Kconfig dependencies of PHY_SUN6I_MIPI_DPHY

2020-11-04 [Report: build error](https://bugzilla.kernel.org/show_bug.cgi?id=209311#c1): It was later found that this issue can lead to build errors as well.

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209311)

### PM: PM_SLEEP_SMP overleaps Kconfig dependencies of HOTPLUG_CPU

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209309)

### ocxl: fix kconfig dependency warning for OCXL

2020-10-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=a9c6d4e7c94d02155c2dadf41bcfa393ee058d20): Committed into linux stable.

2020-09-18 [Patch](https://lkml.org/lkml/2020/9/18/325)

### net: broadcom: CNIC overleaps Kconfig dependency of UIO

2020-11-04 [Report: build error](https://bugzilla.kernel.org/show_bug.cgi?id=209307#c1): It was later found that this issue can lead to build errors as well.

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209307)

### net: ipv6: fix kconfig dependency warning for IPV6_SEG6_HMAC

2020-11-03 [Report: build error](bugs_found/IPV6_SEG6_HMAC-CRYPTO/report.txt): It was later found that this issue can lead to build errors as well.

2020-09-25 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=db7cd91a4be15e1485d6b58c6afc8761c59c4efb): Committed into linux-stable [v4.19](https://lkml.org/lkml/2020/9/25/670), [v5.4](https://lkml.org/lkml/2020/9/25/622), [v5.8](https://lkml.org/lkml/2020/9/25/583)

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/880)

### platform/x86: fix kconfig dependency warning for FUJITSU_LAPTOP

2020-10-24 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=afdd1ebb72051e8b6b83c4d7dc542a9be0e1352d): Committed into linux stable.

2020-09-17 [Confirmation](https://lkml.org/lkml/2020/9/17/909)

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/1140)

2020-09-17 [Report](https://www.spinics.net/lists/platform-driver-x86/msg22800.html): This issue was pointed by a reviewer as [a response](https://www.spinics.net/lists/platform-driver-x86/msg22800.html) to [an earlier patch sent by us](#platformx86-fix-kconfig-dependency-warning-for-lg_laptop). It was also found by klocalizer (building with the config generated for `drivers/media/dvb-frontends/zl10353.o` for linux-5.4.4).

### sh: dma: fix kconfig dependency for G2_DMA

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/825)

### Input: MOUSE_ATARI overleaps Kconfig dependency of ATARI_KBD_CORE

2020-09-17 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209303)

### ASoC: cros_ec_codec: fix kconfig dependency warning for SND_SOC_CROS_EC_CODEC

2020-10-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=ee306f90975bdbdd1ca6709f08516015c4246df6): Committed into linux stable.

2020-09-22 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/broonie/sound.git/commit/?id=50b18e4a2608e3897f3787eaa7dfa869b40d9923): Committed into sound/for-next.

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/723)

### soc/tegra: fuse: SOC_TEGRA_FUSE violates Kconfig dependency of TEGRA20_APB_DMA

2020-09-23 [Patch](https://www.spinics.net/lists/linux-tegra/msg53800.html)

2020-09-17 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209301)

### powerpc: MPC10X_BRIDGE violates Kconfig dependency of PPC_INDIRECT_PCI on PCI

2020-09-17 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209297)

### powerpc: obsolete driver: Marvell MV64X60 MPSC

2020-09-15 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209277)

### IB/rxe: fix kconfig dependency warning for RDMA_RXE

2020-11-03 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=210021): It was later found that this issue can lead to build errors as well.

2020-09-15 [Confirmation](https://lkml.org/lkml/2020/9/15/423): The issue was confirmed but a different fix was suggested.

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/360)

2021-02-19 [Patch](https://lkml.org/lkml/2021/2/19/708): The patch was accidentally resubmitted, but then accepted this time.

2021-03-01 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=475f23b8c66d2892ad6acbf90ed757cafab13de7): Committed into linux-next.

2021-03-01 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=475f23b8c66d2892ad6acbf90ed757cafab13de7): Committed into linux-stable.

### clk: bcm: fix kconfig dependency warning for CLK_BCM2711_DVP

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/381)

2020-09-03 [Confirmation](https://lore.kernel.org/linux-clk/20200903082636.3844629-1-maxime@cerno.tech/): A similar patch was already submitted and merged.

### staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_CCMP

2020-09-17 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-next&id=5f08dede60a6f86893c70e8a519551bed0c9a8c8): Committed into staging/staging-next

2020-09-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-testing&id=5f08dede60a6f86893c70e8a519551bed0c9a8c8): Committed into staging/staging-testing

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/328)

### staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_WEP

2020-09-17 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-next&id=02c4260713d62eff0875ca4a47019cd56371ffa7): Committed into staging/staging-next

2020-09-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-testing&id=02c4260713d62eff0875ca4a47019cd56371ffa7): Committed into staging/staging-testing

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/317)

### staging: rtl8192e: fix kconfig dependency warning for RTLLIB_CRYPTO_TKIP

2020-09-17 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-next&id=243d040a6e4ae95408e133269dd72be2ba03dd48): Committed into staging/staging-next

2020-09-16 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/gregkh/staging.git/commit/?h=staging-testing&id=243d040a6e4ae95408e133269dd72be2ba03dd48): Committed into staging/staging-testing

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/299)

### platform/x86: fix kconfig dependency warning for LG_LAPTOP

2020-10-24 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=8f0c01e666685c4d2e1a233e6f4d7ab16c9f8b2a): Committed into linux stable.

2020-09-17 Confirmation [1](https://www.spinics.net/lists/platform-driver-x86/msg22800.html) [2](https://lkml.org/lkml/2020/9/17/1276)

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/270)

### arc: plat-hsdk: fix kconfig dependency warning when !RESET_CONTROLLER

2020-11-04 [Report: build error](bugs_found/ARC_SOC_HSDK-RESET_HSDK/report.txt): It was later found that this issue can lead to build errors as well.

2020-10-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=0ee5ef9d3a5a5f2f95c92269be2473e235f8f950): Committed into linux stable.

2020-09-14 [Confirmation](https://lkml.org/lkml/2020/9/14/1145)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/400)

### ARM: davinci: fix kconfig dependency warning when !PINCTRL

2020-09-14 [Confirmation](https://lkml.org/lkml/2020/9/24/867): The issue was confirmed but a different fix was suggested.

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/432)

### ARM: davinci: fix kconfig dependency warning when !GPIOLIB

2020-09-14 [Confirmation](https://lkml.org/lkml/2020/9/28/1001): The issue was confirmed but a different fix was suggested.

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/600)

### pinctrl: bcm: fix kconfig dependency warning when !GPIOLIB

2020-11-03 [Report: build error](bugs_found/PINCTRL_BCM2835-GPIOLIB_IRQCHIP/report.txt): It was later found that this issue can lead to build errors as well.

2020-10-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git/commit/?id=7f101eccd00b242dd15f6dd1dc6cd624cce2ef2c): Committed into linux stable.

2020-09-29 [Confirmation](https://lkml.org/lkml/2020/9/29/1673)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/651)

### nvme: tcp: fix kconfig dependency warning when !CRYPTO

2020-11-03 [Report: build error](bugs_found/NVME_TCP-CRYPTO_CRC32C/report.txt): It was later found that this issue can lead to build errors as well.

2020-09-29 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=af5ad17854f96a6d3c9775e776bd01ab262672a1): Committed into [5.9-rc7](https://lwn.net/Articles/832733/), [stable 5.4](https://lkml.org/lkml/2020/9/29/888) and [stable 5.8](https://lkml.org/lkml/2020/9/29/979).

2020-09-14 Confirmation [1](https://lkml.org/lkml/2020/9/14/1123) [2](https://lkml.org/lkml/2020/9/15/65)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/702)

### MIPS: remove the obsolete RM7000 extended interrupts handler

2020-09-12 [Patch](https://lkml.org/lkml/2020/9/12/193)

### net: Wireless: fix unmet direct dependendices config warning when !CRYPTO

2020-09-18 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=b959ba9f468b1c581f40e92661ad58b093abaa03): Committed into [5.9-rc7](https://lwn.net/Articles/832733/), [stable 5.4](https://lkml.org/lkml/2020/9/29/877), [stable 5.8](https://lkml.org/lkml/2020/9/29/936).

2020-09-09 [Patch](https://lkml.org/lkml/2020/9/9/413)

### Missing dependency for the MAX77650 MFD driver

#### Description

From the patch:

    MAX77650 MFD driver uses regmap_irq API but doesn't select the required
    REGMAP_IRQ option in Kconfig. This can cause the following build error
    if regmap irq is not enabled implicitly by someone else.

#### History

2020-01-20 [Patch](https://lkml.org/lkml/2020/1/3/189)

2020-01-20 [Confirmation](https://lkml.org/lkml/2020/1/3/190)

2020-01-20 [Report](https://lkml.org/lkml/2020/1/3/12)

## axTLS

### Header compile issue when "Create Language Bindings" is used

#### Description

Conflicting types for the function `ssl_client_new` when selecting the
"Create Language Bindings" configuration option.

#### History

2019-03-15 [Fix Confirmation](https://sourceforge.net/p/axtls/mailman/message/36613862/)

2017-12-26 [Report and Patch](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found/2017-12-26_axtls_language_bindings.txt)
