<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The kmax tool suite](#the-kmax-tool-suite)
  - [Getting started](#getting-started)
    - [python setup](#python-setup)
    - [`krepair`/`klocalizer` dependencies](#krepairklocalizer-dependencies)
    - [Installing the kmax tool suite](#installing-the-kmax-tool-suite)
    - [Getting the Linux source code](#getting-the-linux-source-code)
    - [Finding unmet dependency bugs with `kismet`](#finding-unmet-dependency-bugs-with-kismet)
    - [Localizing and repairing configuration files with `klocalizer`](#localizing-and-repairing-configuration-files-with-klocalizer)
  - [Additional Documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The kmax tool suite

## Getting started

### python setup

The kmax tool suite currently depends on python 3.8 or later and is recommended to be installied with pip in a virtual environment:

    sudo apt install -y python3 python3-pip python3-venv

### `krepair`/`klocalizer` dependencies

`krepair` depends on [SuperC](https://github.com/appleseedlab/superc/) to get per-line constraints from source files.  (`klocalizer` will work without SuperC as long as per-line constraints aren't requested.)  SuperC depends on several libraries, including JavaBDD which needs to be installed manually.

    mkdir ~/superc/
    cd ~/superc/
    sudo apt-get install -y libz3-java libjson-java sat4j
    wget -O - --content-disposition -c https://sourceforge.net/projects/javabdd/files/javabdd-linux/1.0b2%20Linux%20binary/javabdd_1.0b2.tar.gz/download?use_mirror=master > javabdd.tar.bz
    tar -xvf javabdd.tar.bz JavaBDD/javabdd-1.0b2.jar
    wget https://github.com/appleseedlab/superc/releases/download/v2.0-rc4/xtc.jar
    wget https://github.com/appleseedlab/superc/releases/download/v2.0-rc4/superc.jar
    
Update your java `CLASSPATH` to contain all the requisite jarifles for SuperC.

    export CLASSPATH=$CLASSPATH:/usr/share/java/org.sat4j.core.jar:/usr/share/java/com.microsoft.z3.jar:/usr/share/java/json-lib.jar:$PWD/JavaBDD/javabdd-1.0b2.jar:$PWD/xtc.jar:$PWD/superc.jar

Download and install the SuperC Linux runner script.

    wget https://raw.githubusercontent.com/appleseedlab/superc/v2.0-rc4/scripts/superc_linux.sh
    chmod 755 superc_linux.sh
    export PATH=$PATH:~/superc/

The following dependencies are useful when compiling the Linux source code itself.

    sudo apt install -y flex bison bc libssl-dev libelf-dev

(Optional) If you want to be able to cross-compile Linux, the `make.cross` is a handy way to do that.

    sudo apt install -y xz-utils lftp
    mkdir -p ~/bin/
    wget -O ~/bin/make.cross https://raw.githubusercontent.com/fengguang/lkp-tests/master/sbin/make.cross
    chmod 755 ~/bin/make.cross
    export PATH=$PATH:~/bin/

### Installing the kmax tool suite

Create and enter a python virtual environment (optional, but recommended)

    python3 -m venv ~/kmax_env/
    source ~/kmax_env/bin/activate

Install the kmax tool suite via `pip`

    pip3 install kmax

(Optional) Instructions to install from source code can be found in the [advanced documentation](docs/advanced.md).


### Getting the Linux source code

    cd ~/
    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.16.tar.xz
    tar -xvf linux-5.16.tar.xz
    cd linux-5.16/


### Finding unmet dependency bugs with `kismet`

This tool will check for unmet dependency bugs in [Kconfig specifications](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html#menu-attributes) due to reverse dependencies overriding direct dependencies.  Run `kismet` from the root of the Linux source tree.

    kismet --linux-ksrc="./" -a=x86_64

Once finished (it can take about an hour), kismet will produce three outputs:

  1. A summary of the results in `kismet_summary_x86_64.txt`
  2. A list of results for each `select` construct in `kismet_summary_x86_64.csv` (`UNMET_ALARM` denotes the buggy ones)
  3. A list of `.config` files meant to exercise each bug in `kismet-test-cases/`

Technical details can be found in the [paper](https://paulgazzillo.com/papers/esecfse21.pdf) on `kclause` and `kismet`.  The experiment [replication script](scripts/kismet_experiments_replication.sh) can be used to run kismet on all architectures' Kconfig specifications.


### Localizing and repairing configuration files with `klocalizer`

These tools can generate or repair existing configuration files to include given source code directories, files, and lines from Linux kernel source code.  For instance, let's use it to repair the minimal `allnoconfig` so that it includes specific lines of `kernel/bpf/cgroup.c`.  `allnoconfig` will not even include the source file.

    make allnoconfig
    make kernel/bpf/cgroup.o
    
This build attempt will result in an error.

    make[2]: *** No rule to make target 'kernel/bpf/cgroup.o'.  Stop.

We can ensure that the relevant configuration options are modified in `allnoconfig`

    make allnoconfig  # configuration file stored in .config
    klocalizer --repair .config --include-mutex kernel/bpf/cgroup.o

This produces a new version of the `.config` file in `0-x86_64.config`.  To build with it, install it with `olddefconfig` and attempt to build the source file:

    cp 0-x86_64.config .config
    make olddefconfig
    make kernel/bpf/cgroup.o
    
This time, the source file is successfully built.

    CC      kernel/bpf/cgroup.o

We can also ensure that individual lines within source files can be included.  For instance, line 1357 in `kernel/bpf/cgroup.c` is controlled by an `#ifdef` and is excluded even by our repaired `allnoconfig`.  We can specify lines or line ranges with `klocalizer`.

    make allnoconfig  # configuration file stored in .config
    klocalizer --repair .config --include-mutex kernel/bpf/cgroup.o:[1354,1357-1359]

We can see the line included in the preprocessed version of the source file (`kernel/bpf/cgroup.i`).

    cp 0-x86_64.config .config
    make olddefconfig
    make kernel/bpf/cgroup.i

Any number of `--include-mutex` constraints may be added.  If there is mutual-exclusion among source files, `klocalizer` will as many configuration files needed to cover all constraints.  Always on or off constraints can be added with `--include` or `--exclude`.

## Additional Documentation

[Overview](https://github.com/paulgazz/kmax/blob/master/docs/overview.md)

[Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md)

[Bugs Found](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found.md)
