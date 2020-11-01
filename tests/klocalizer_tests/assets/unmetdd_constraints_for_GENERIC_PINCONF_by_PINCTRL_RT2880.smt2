; benchmark generated from python API
(set-info :status unknown)
(declare-fun CONFIG_RALINK () Bool)
(declare-fun CONFIG_STAGING () Bool)
(declare-fun CONFIG_PINCTRL () Bool)
(declare-fun CONFIG_PINCTRL_RT2880 () Bool)
(assert
 (let (($x39 (and CONFIG_STAGING CONFIG_RALINK)))
 (let (($x13 (not CONFIG_PINCTRL)))
 (and CONFIG_PINCTRL_RT2880 $x39 $x13 $x39))))
(check-sat)
