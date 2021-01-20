<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Getting Started](#getting-started)
  - [Cross-Compiling](#cross-compiling)
  - [Additional Documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The Kmax Tool Suite

## Getting Started

Kmax currently depends on python 3.8 or later.  Install kmax in one of two ways:

1. To a python virtual environment (_recommended_):

        sudo apt install -y python3-pip python3-venv flex bison bc libssl-dev libelf-dev
        python3 -m venv kmax_env  # create the environment
        source kmax_env/bin/activate  # enter the environment
        pip3 install kmax  # install kmax in the environment
    
2. System-wide:

        sudo apt install -y python3-pip flex bison bc libssl-dev libelf-dev
        sudo pip3 install kmax

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

## Installing from Source

Install the prerequisites

    sudo apt install -y python3-setuptools python3-dev
    
Clone and install kmax

    git clone https://github.com/paulgazz/kmax.git
    cd kmax
    sudo python3 setup.py install

Alternatilvely, installing for development to obviate the need to
rereun setup.py when making changes to the code

    sudo python3 setup.py develop

## Additional Documentation

[Overview](https://github.com/paulgazz/kmax/blob/master/docs/overview.md)

[Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md)

[Bugs Found](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found.md)
