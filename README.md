<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Getting Started](#getting-started)
  - [Upgrading `kmaxtools`](#upgrading-kmaxtools)
  - [Additional Documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The Kmax Tool Suite

## Getting Started

Install `pip3`, Linux's build dependencies, and `kmaxtools`:

    sudo apt install -y python3-pip flex bison bc libssl-dev
    sudo pip3 install kmaxtools

Download the Linux source:

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.tar.xz
    tar -xvf linux-5.4.tar.xz

Run `klocalizer`

    cd linux-5.4/
    klocalizer drivers/usb/storage/alauda.o

Build the `.config` file made by `klocalizer`:

    make ARCH=x86_64 olddefconfig
    make ARCH=x86_64 clean drivers/usb/storage/alauda.o

## Cross-Compiling

Get `make.cross`:

    sudo apt install -y xz-utils lftp
    wget https://raw.githubusercontent.com/fengguang/lkp-tests/master/sbin/make.cross

Run `klocalizer` with a different architecture:

    klocalizer -a powerpc drivers/block/ps3disk.o
    bash make.cross ARCH=powerpc olddefconfig; bash make.cross ARCH=powerpc clean drivers/block/ps3disk.o

## Additional Documentation

[Overview](https://github.com/paulgazz/kmax/blob/master/docs/overview.md)

[Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md)

[Bugs Found by `kmaxtools`](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found.md)
