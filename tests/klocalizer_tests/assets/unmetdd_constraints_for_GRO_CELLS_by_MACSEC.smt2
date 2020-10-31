; benchmark generated from python API
(set-info :status unknown)
(declare-fun CONFIG_NET_CORE () Bool)
(declare-fun CONFIG_NETDEVICES () Bool)
(declare-fun CONFIG_NET () Bool)
(declare-fun CONFIG_MACSEC () Bool)
(assert
 (let (($x57 (and CONFIG_NETDEVICES CONFIG_NET_CORE)))
 (let (($x55 (not CONFIG_NET)))
 (and CONFIG_MACSEC $x57 $x55 $x57))))
(check-sat)
