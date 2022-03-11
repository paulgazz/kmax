<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The kmax tool suite](#the-kmax-tool-suite)
  - [Getting started](#getting-started)
    - [Installing the kmax tool suite](#installing-the-kmax-tool-suite)
    - [Kicking the tires](#kicking-the-tires)
  - [Using `klocalizer --repair` on patches](#using-klocalizer---repair-on-patches)
  - [Using `kismet`](#using-kismet)
  - [Additional documentation](#additional-documentation)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The kmax tool suite

## Getting started

### Installing the kmax tool suite

Install the requiste python tools (the kmax tool suite currently depends on python 3.8 or later), setup a python virtual environment (recommended), and finally install the tools from pip.

    sudo apt install -y python3 python3-pip python3-venv
    python3 -m venv ~/env_kmax/
    source ~/env_kmax/bin/activate
    pip3 install kmax

Instructions to install from source can be found in the [advanced documentation](docs/advanced.md).


### Kicking the tires

Install dependencies for compiling Linux source, then download and enter the Linux source:

    sudo apt install -y flex bison bc libssl-dev libelf-dev
    cd ~/
    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.16.tar.xz
    tar -xvf linux-5.16.tar.xz
    cd ~/linux-5.16/

Run `klocalizer --repair` to modify `allnoconfig` so that builds a given compilation unit:

    make allnoconfig
    klocalizer --repair .config -o allnoconfig_repaired --include drivers/usb/storage/alauda.o
    KCONFIG_CONFIG=allnoconfig_repaired make ARCH=x86_64 olddefconfig clean drivers/usb/storage/alauda.o
    
You should see `CC      drivers/usb/storage/alauda.o` at the end of the build.


## Using `klocalizer --repair` on patches

First install [SuperC](https://github.com/appleseedlab/superc), which `klocalizer` depends on for per-line, `#ifdef` constraints:

    sudo apt-get install -y libz3-java libjson-java sat4j unzip flex bison bc libssl-dev libelf-dev xz-utils lftp
    wget -O - https://raw.githubusercontent.com/appleseedlab/superc/master/scripts/install.sh | bash
    export CLASSPATH=${CLASSPATH}:/usr/share/java/org.sat4j.core.jar:/usr/share/java/json-lib.jar:${HOME}/.local/share/superc/z3-4.8.12-x64-glibc-2.31/bin/com.microsoft.z3.jar:${HOME}/.local/share/superc/JavaBDD/javabdd-1.0b2.jar:${HOME}/.local/share/superc/xtc.jar:${HOME}/.local/share/superc/superc.jar
    export PATH=${PATH}:${HOME}/.local/bin/

Start with a clone of the linux repository and get a patch file:

    cd ~/
    git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
    cd ~/linux/
    git checkout 6fc88c354f3af
    git show > 6fc88c354f3af.diff
    
Repair allnoconfig to include lines of the patch and test the build.  When using `--include-mutex` all configuration files needed to cover the patch are exported as `NUM-ARCH.config`:

    make allnoconfig
    klocalizer --repair .config -a x86_64 --include-mutex 6fc88c354f3af.diff
    KCONFIG_CONFIG=0-x86_64.config make ARCH=x86_64 olddefconfig clean kernel/bpf/cgroup.o net/ipv4/af_inet.o net/ipv4/udp.o net/ipv6/af_inet6.o net/ipv6/udp.o
    

## Using `kismet`

This tool will check for unmet dependency bugs in [Kconfig specifications](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html#menu-attributes) due to reverse dependencies overriding direct dependencies.

Run `kismet` on the root of the Linux source tree.

    kismet --linux-ksrc="${HOME}/linux-5.16/" -a=x86_64

Once finished (it can take about an hour on a commodity desktop), kismet will produce three outputs:

  1. A summary of the results in `kismet_summary_x86_64.txt`
  2. A list of results for each `select` construct in `kismet_summary_x86_64.csv` (`UNMET_ALARM` denotes the buggy ones)
  3. A list of `.config` files meant to exercise each bug in `kismet-test-cases/`

Technical details can be found in in the [kismet documentation](docs/advanced.md#kismet) and the [publication](https://paulgazzillo.com/papers/esecfse21.pdf) on `kclause` and `kismet`.  The experiment [replication script](scripts/kismet_experiments_replication.sh) can be used to run kismet on all architectures' Kconfig specifications.


## Additional documentation

[Overview](docs/overview.md)

[Advanced Usage](docs/advanced.md)

[Bugs Found](docs/bugs_found.md)
