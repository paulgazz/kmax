<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Getting Started](#getting-started)
  - [Upgrading `kmaxtools`](#upgrading-kmaxtools)
  - [Additional Documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The Kmax Tool Suite

## Getting Started

Install via `pip3` for python 3.X or `pip` for python 2.X:

    sudo pip3 install kmaxtools

Download the Linux source:

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.tar.xz
    tar -xvf linux-5.4.tar.xz

Run `klocalizer`

    cd linux-5.4/
    klocalizer drivers/usb/storage/alauda.o

Build the resulting `.config` file with [make.cross](https://github.com/fengguang/lkp-tests/blob/master/sbin/make.cross):

    make.cross ARCH=x86_64 olddefconfig; make.cross ARCH=x86_64 clean drivers/usb/storage/alauda.o

## Upgrading `kmaxtools`

Use the `-U` flag to `pip3`/`pip`:

    sudo pip install -U kmaxtools

## Additional Documentation

[Overview](docs/overview.md)

[Advanced Usage](docs/advanced.md)

[Bugs Found by `kmaxtools`](docs/bugs_found.md)
