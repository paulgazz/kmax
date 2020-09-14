<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Bugs Found by Kmax Tools](#bugs-found-by-kmax-tools)
  - [Linux kernel](#linux-kernel)
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

### arc: plat-hsdk: fix kconfig dependency warning when !RESET_CONTROLLER

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/400)

### ARM: davinci: fix kconfig dependency warning when !PINCTRL

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/432)

### ARM: davinci: fix kconfig dependency warning when !GPIOLIB

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/600)

### pinctrl: bcm: fix kconfig dependency warning when !GPIOLIB

2020-09-14 [Patch](https://lkml.org/lkml/2020/9/14/651)

### nvme: tcp: fix kconfig dependency warning when !CRYPTO

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
