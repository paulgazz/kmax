<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Bugs Found by Kmax Tools](#bugs-found-by-kmax-tools)
  - [Linux kernel](#linux-kernel)
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

### staging: mt7621-dma: MTK_HSDMA overleaps kconfig dependency of DMADEVICES

2020-09-19 [Confirmation](https://bugzilla.kernel.org/show_bug.cgi?id=209301#c1)

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209313)

### ASoC: fix kconfig dependency warnings for SND_SOC_WM8731

2020-09-18 [Confirmation](https://lkml.org/lkml/2020/9/18/661): The issue was confirmed but a different fix was suggested.

2020-09-18 [Patch](https://lkml.org/lkml/2020/9/18/626)

### drm/sun4i: DRM_SUN6I_DSI overleaps Kconfig dependencies of PHY_SUN6I_MIPI_DPHY

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209311)

### PM: PM_SLEEP_SMP overleaps Kconfig dependencies of HOTPLUG_CPU

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209309)

### ocxl: fix kconfig dependency warning for OCXL

2020-09-18 [Patch](https://lkml.org/lkml/2020/9/18/325)

### net: broadcom: CNIC overleaps Kconfig dependency of UIO

2020-09-18 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209307)

### net: ipv6: fix kconfig dependency warning for IPV6_SEG6_HMAC

2020-09-25 [Commit](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=db7cd91a4be15e1485d6b58c6afc8761c59c4efb): Committed into linux-stable [v4.19](https://lkml.org/lkml/2020/9/25/670), [v5.4](https://lkml.org/lkml/2020/9/25/622), [v5.8](https://lkml.org/lkml/2020/9/25/583)

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/880)

### platform/x86: fix kconfig dependency warning for FUJITSU_LAPTOP

2020-09-17 [Confirmation](https://lkml.org/lkml/2020/9/17/909)

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/1140)

2020-09-17 [Report](https://www.spinics.net/lists/platform-driver-x86/msg22800.html): This issue was pointed by a reviewer as [a response](https://www.spinics.net/lists/platform-driver-x86/msg22800.html) to [an earlier patch sent by us](#platformx86-fix-kconfig-dependency-warning-for-lg_laptop). It was also found by klocalizer (building with the config generated for `drivers/media/dvb-frontends/zl10353.o` for linux-5.4.4).

### sh: dma: fix kconfig dependency for G2_DMA

2020-09-17 [Patch](https://lkml.org/lkml/2020/9/17/825)

### Input: MOUSE_ATARI overleaps Kconfig dependency of ATARI_KBD_CORE

2020-09-17 [Report](https://bugzilla.kernel.org/show_bug.cgi?id=209303)

### ASoC: cros_ec_codec: fix kconfig dependency warning for SND_SOC_CROS_EC_CODEC

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

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/360)

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

2020-09-17 Confirmation [1](https://www.spinics.net/lists/platform-driver-x86/msg22800.html) [2](https://lkml.org/lkml/2020/9/17/1276)

2020-09-15 [Patch](https://lkml.org/lkml/2020/9/15/270)

### arc: plat-hsdk: fix kconfig dependency warning when !RESET_CONTROLLER

2020-09-14 [Confirmation](https://lkml.org/lkml/2020/9/14/1145)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/400)

### ARM: davinci: fix kconfig dependency warning when !PINCTRL

2020-09-14 [Confirmation](https://lkml.org/lkml/2020/9/14/1145)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/432)

### ARM: davinci: fix kconfig dependency warning when !GPIOLIB

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/600)

### pinctrl: bcm: fix kconfig dependency warning when !GPIOLIB

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/651)

### nvme: tcp: fix kconfig dependency warning when !CRYPTO

2020-09-14 Confirmation [1](https://lkml.org/lkml/2020/9/14/1123) [2](https://lkml.org/lkml/2020/9/15/65)

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/702)

### MIPS: remove the obsolete RM7000 extended interrupts handler

2020-09-12 [Patch](https://lkml.org/lkml/2020/9/12/193)

### net: Wireless: fix unmet direct dependendices config warning when !CRYPTO

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
