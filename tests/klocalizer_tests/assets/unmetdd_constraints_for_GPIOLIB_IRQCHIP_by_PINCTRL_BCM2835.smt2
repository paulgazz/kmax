; benchmark generated from python API
(set-info :status unknown)
(declare-fun CONFIG_COMPILE_TEST () Bool)
(declare-fun CONFIG_OF () Bool)
(declare-fun CONFIG_PINCTRL () Bool)
(declare-fun CONFIG_GPIOLIB () Bool)
(declare-fun CONFIG_PINCTRL_BCM2835 () Bool)
(assert
 (let (($x21 (and CONFIG_PINCTRL CONFIG_OF CONFIG_COMPILE_TEST)))
 (let (($x6 (not CONFIG_GPIOLIB)))
 (and CONFIG_PINCTRL_BCM2835 $x21 $x6 $x21))))
(check-sat)
