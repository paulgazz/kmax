<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Getting Started](#getting-started)
  - [Cross-Compiling](#cross-compiling)
  - [Installing from Source](#installing-from-source)
  - [Additional Documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The Kmax Tool Suite

## Getting Started

Kmax currently depends on python 3.8 or later.  Install kmax in one of two ways:

1. In a python virtual environment (_recommended_):

        sudo apt install -y python3-pip python3-venv flex bison bc libssl-dev libelf-dev
        python3 -m venv kmax_env  # create the environment
        source kmax_env/bin/activate  # enter the environment
        pip3 install kmax  # install kmax in the environment
    
2. System-wide:

        sudo apt install -y python3-pip flex bison bc libssl-dev libelf-dev
        sudo pip3 install kmax

Download and enter the Linux source:

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.tar.xz
    tar -xvf linux-5.4.tar.xz
    cd linux-5.4/

### `klocalizer`

Run `klocalizer` to generate a `.config` file that builds a given compilation unit:

    klocalizer drivers/usb/storage/alauda.o

Build the `.config` file made by `klocalizer` to confirm inclusion of the compilation unit:

    make ARCH=x86_64 olddefconfig
    make ARCH=x86_64 clean drivers/usb/storage/alauda.o
    
### `kismet`
    
Run `kismet` to find unmet dependency bugs due to Kconfig's [reverse dependencies](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html#menu-attributes):

    kismet --linux-ksrc="./" -a=x86_64

Once finished (it can take about an hour), kismet will produce three outputs:

  1. A summary of the results in `kismet_summary_x86_64.txt`
  2. A list of results for each `select` construct in `kismet_summary_x86_64.csv` (`UNMET_ALARM` denotes the buggy ones)
  3. A list of `.config` files meant to exercise each bug in `kismet-test-cases/`

Technical details can be found in the [paper](https://paulgazzillo.com/papers/esecfse21.pdf) on `kclause` and `kismet`.  The experiment [replication script](scripts/kismet_experiments_replication.sh) can be used to run kismet on all architectures' Kconfig specifications.


## Cross-Compiling Linux Compilation Units

Get `make.cross`:

    sudo apt install -y xz-utils lftp
    wget https://raw.githubusercontent.com/fengguang/lkp-tests/master/sbin/make.cross

Run `klocalizer` with a different architecture:

    klocalizer -a powerpc drivers/block/ps3disk.o
    bash make.cross ARCH=powerpc olddefconfig; bash make.cross ARCH=powerpc clean drivers/block/ps3disk.o


## Installing Kmax from Source

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
