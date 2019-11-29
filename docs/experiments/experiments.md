<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Experiments](#experiments)
  - [Results](#results)
    - [Linux v5.4 2019-11-28](#linux-v54-2019-11-28)
    - [Linux next-20191121 2019-11-28](#linux-next-20191121-2019-11-28)
    - [Linux next-20191121](#linux-next-20191121)
    - [Linux 5.3.11 2019-11-19](#linux-5311-2019-11-19)
    - [BusyBox 1.28.0 2019-11-18](#busybox-1280-2019-11-18)
    - [Linux 5.4-rc6 2019-11-18](#linux-54-rc6-2019-11-18)
    - [Linux 5.3.11 2019-11-18](#linux-5311-2019-11-18)
    - [BusyBox 1.28.0 2019-11-18](#busybox-1280-2019-11-18-1)
  - [Setup](#setup)
    - [Machines](#machines)
    - [Linux 5.4-rc6](#linux-54-rc6)
    - [Linux 5.3.11](#linux-5311)
    - [BusyBox 1.28.0](#busybox-1280)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Experiments

- [Results](#results)
- [Setup](#setup)

### Results

Please find the resulting formulas here: <https://opentheblackbox.com/kmax>

#### Linux v5.4 2019-11-28

- Formulas: Please find the resulting formulas here: <https://opentheblackbox.com/kmax/kmax-formulas_linux-v5.4.tar.bz2>

- Running time for `kmaxlinux.sh`

    654.23user 61.98system 11:55.82elapsed 100%CPU (0avgtext+0avgdata 71272maxresident)k
    0inputs+12184outputs (0major+24781951minor)pagefaults 0swaps

- Running time for `kclauselinux.sh`

    3443.57user 8.88system 57:31.99elapsed 100%CPU (0avgtext+0avgdata 137524maxresident)k
    0inputs+704320outputs (0major+3467838minor)pagefault

#### Linux next-20191121 2019-11-28

Using machine 2 (kmax and kclause started simultaneously)

- Formulas: Please find the resulting formulas here: <https://opentheblackbox.com/kmax/kmax-formulas_linux-next-20191121.tar.bz2>

- Running time for `kmaxlinux.sh`

    671.85user 62.03system 12:13.47elapsed 100%CPU (0avgtext+0avgdata 71160maxresident)k
    0inputs+12312outputs (0major+24954658minor)pagefaults 0swaps

- Running time for `kclauselinux.sh`

    3579.12user 12.00system 59:50.65elapsed 100%CPU (0avgtext+0avgdata 138324maxresident)k
    0inputs+711232outputs (0major+3498420minor)pagefaults 0swaps

#### Linux next-20191121

- Symbolic constraints for compilation units: 

- Running time for `kmaxdriver.py -g`

    346.55user 45.59system 7:16.39elapsed 89%CPU (0avgtext+0avgdata 38656maxresident)k
    12232inputs+0outputs (0major+11732031minor)pagefaults 0swaps

#### Linux 5.3.11 2019-11-19

Using machine 1

- Symbolic constraints for compilation units: <https://drive.google.com/file/d/10MfPgUlInKCmlQl-gSiFjYMrWJHeluhE/view?usp=sharing>

- Running time for `kmaxdriver.py -g`

        344.17user 46.60system 6:40.23elapsed 97%CPU (0avgtext+0avgdata 38288maxresident)k
        8376inputs+304outputs (0major+11573227minor)pagefaults 0swaps

This version of Kmax the usage of BDDs is added back in for unsat checks.  This is a hybrid, where both the z3 and BDD expressions are computed.  z3 is used for output (more efficient than enumerating all solutions) and BDDs are used for checking unsat (more efficient than using z3).  The ordering of the output expressions differs from the previous version, but they appear to be the same.

#### BusyBox 1.28.0 2019-11-18

Using machine 1

- Symbolic constraints for compilation units: https://drive.google.com/open?id=1vS_I_xXBwnd6hBJUds1dicOzriKOe1SP

- Running time for `kmaxdriver.py -g`

        6.72user 0.79system 0:07.75elapsed 97%CPU (0avgtext+0avgdata 35388maxresident)k
        472inputs+8outputs (0major+196079minor)pagefaults 0swaps


- Running time for `kmaxdriver.py --aggregate`

        0.12user 0.02system 0:00.15elapsed 98%CPU (0avgtext+0avgdata 18684maxresident)k
        0inputs+64outputs (0major+3712minor)pagefaults 0swaps

#### Linux 5.4-rc6 2019-11-18

Using machine 1

- Symbolic constraints for compilation units: https://drive.google.com/file/d/1wh4z8LE6wLJIJ1rqd7MnZa0AsjuabzS3/view?usp=sharing

- Running time for `kmaxdriver.py -g`

        15548.80user 94.16system 4:21:11elapsed 99%CPU (0avgtext+0avgdata 42040maxresident)k
        18672inputs+1016outputs (0major+11417656minor)pagefaults 0swaps

- Running time for `kmaxdriver.py --aggregate`


#### Linux 5.3.11 2019-11-18

Using machine 1

- Symbolic constraints for compilation units: https://drive.google.com/file/d/1q7dDzOvEKWUi7FlZ2YixValV6xlkq1yY/view

- Running time for `kmaxdriver.py -g`

        real    273m22.829s
        user    270m59.705s
        sys     2m19.206s

(Note that this is considerably slower than original BDD version of Kmax.)

- Running time for `kmaxdriver.py --aggregate`

        real    0m1.559s
        user    0m1.542s
        sys     0m0.016s

#### BusyBox 1.28.0 2019-11-18

Using machine 1

- Symbolic constraints for compilation units: https://drive.google.com/file/d/1-nG1hROOnRJnBsnv0PUwT3N1NjMfpD-m/view

- Running time for `kmaxdriver.py -g`

        real    9m54.009s
        user    9m48.282s
        sys     0m2.925s

- Running time for `kmaxdriver.py --aggregate`

        real    0m0.121s
        user    0m0.109s
        sys     0m0.012s

### Setup

#### Machines

1. Commodity PC desktop, core i5 (circa 2013), 16GB RAM, Debian 11, running with other processes
1. Commodity PC laptop, core i7 (circa 2018), 16GB RAM, Ubuntu 18.04, running with other processes


#### Linux 5.4-rc6

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.3.11.tar.xz
    tar -xvf /linux-5.4-rc6.tar.gz
    cd linux-5.4-rc6
    make defconfig # any config will work here.  it's just to setup the build system.
    /usr/bin/time bash /path/to/kmax/scripts/kmaxlinux.sh
    /usr/bin/time bash /path/to/kmax/scripts/kclauselinux.sh


#### Linux 5.3.11

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.3.11.tar.xz
    tar -xvf linux-5.3.11.tar.xz
    cd linux-5.3.11
    make defconfig # any config will work here.  it's just to setup the build system.
    /usr/bin/time bash /path/to/kmax/scripts/kmaxlinux.sh
    /usr/bin/time bash /path/to/kmax/scripts/kclauselinux.sh

Older timing used `kmaxdriver.py` which has been superceded by `kmaxlinux.sh` and `kmaxall`

#### BusyBox 1.28.0

    git clone https://git.busybox.net/busybox
    cd busybox
    git checkout 1_28_0
    make defconfig
    /usr/bin/time kmaxdriver.py -g \
            archival/ \
            archival/libarchive/ \
            console-tools/ \
            coreutils/ \
            coreutils/libcoreutils/ \
            debianutils/ \
            klibc-utils/ \
            e2fsprogs/ \
            editors/ \
            findutils/ \
            init/ \
            libbb/ \
            libpwdgrp/ \
            loginutils/ \
            mailutils/ \
            miscutils/ \
            modutils/ \
            networking/ \
            networking/libiproute/ \
            networking/udhcp/ \
            printutils/ \
            procps/ \
            runit/ \
            selinux/ \
            shell/ \
            sysklogd/ \
            util-linux/ \
            util-linux/volume_id/ \
        2>unit_pc.err | tee unit_pc
    /usr/bin/time kmaxdriver.py --aggregate < unit_pc > full_pc 2> full_pc.err

There is no automated way (yet) to get the list of top-level
directories, so right now they are manually-entered in the call to
Kmax.
