## Linux 5.3.11

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.3.11.tar.xz
    tar -xvf linux-5.3.11.tar.xz
    cd linux-5.3.11
    make defconfig # any config will work here.  it's just to setup the build system.
    time kmaxdriver.py -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) 2>unit_pc.time | tee unit_pc
    time kmaxdriver.py --aggregate < unit_pc > full_pc 2> full_pc.time

The `makefile_override` Makefile will extract the list of top-level directories from the top-leverl Linux Makefile.  This top-level Makefile is not a Kbuild Makefile, so Kmax is not used.

### Results 2019-11-18

Commodity PC desktop, core i5 (circa 2013), 16GB RAM, Debian 11, running with other processes

- Symbolic constraints for compilation units: https://drive.google.com/file/d/1q7dDzOvEKWUi7FlZ2YixValV6xlkq1yY/view

- Running time for `kmaxdriver.py -g`


- Running time for `kmaxdriver.py --aggregate`


## BusyBox 1.28.0

    git clone https://git.busybox.net/busybox
    cd busybox
    git checkout 1_28_0
    make defconfig
    time kmaxdriver.py -g \
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
        2>unit_pc.time | tee unit_pc
    time kmaxdriver.py --aggregate < unit_pc > full_pc 2> full_pc.time

There is no automated way (yet) to get the list of top-level
directories, so right now they are manually-entered in the call to
Kmax.

### Results 2019-11-18

Commodity PC desktop, core i5 (circa 2013), 16GB RAM, Debian 11, running with other processes

- Symbolic constraints for compilation units: https://drive.google.com/file/d/1-nG1hROOnRJnBsnv0PUwT3N1NjMfpD-m/view

- Running time for `kmaxdriver.py -g`

        real    9m54.009s
        user    9m48.282s
        sys     0m2.925s

- Running time for `kmaxdriver.py --aggregate`

        real    0m0.121s
        user    0m0.109s
        sys     0m0.012s
