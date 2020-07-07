<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Bugs Found by Kmax Tools](#bugs-found-by-kmax-tools)
  - [Linux kernel](#linux-kernel)
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

### Missing dependency for the MAX77650 MFD driver

#### Description

From the patch:

    MAX77650 MFD driver uses regmap_irq API but doesn't select the required
    REGMAP_IRQ option in Kconfig. This can cause the following build error
    if regmap irq is not enabled implicitly by someone else.

#### History

2020-01-20 [Report](https://lkml.org/lkml/2020/1/3/12)

2020-01-20 [Confirmation](https://lkml.org/lkml/2020/1/3/190)

2020-01-20 [Patch](https://lkml.org/lkml/2020/1/3/189)

## axTLS

### Header compile issue when "Create Language Bindings" is used

#### Description

Conflicting types for the function `ssl_client_new` when selecting the
"Create Language Bindings" configuration option.

#### History

2017-12-26 [Report and Patch](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found/2017-12-26_axtls_language_bindings.txt)

2019-03-15 [Fix Confirmation](https://sourceforge.net/p/axtls/mailman/message/36613862/)
