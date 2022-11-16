<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The kmax tool suite](#the-kmax-tool-suite)
  - [Getting started](#getting-started)
    - [Installing the kmax tool suite](#installing-the-kmax-tool-suite)
    - [Kicking the tires](#kicking-the-tires)
  - [Using `klocalizer --repair` on patches](#using-klocalizer---repair-on-patches)
  - [Using `koverage`](#using-koverage)
  - [Using `kismet`](#using-kismet)
  - [Additional documentation](#additional-documentation)
  - [Bugs found](#bugs-found)
  - [Credits](#credits)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The kmax tool suite

## Getting started

### Installing the kmax tool suite

Install the requiste python tools (the kmax tool suite currently depends on python 3.8 or later), setup a python virtual environment (recommended), and finally install the tools from pip.

    sudo apt install -y python3 python3-pip python3-venv
    python3 -m venv ~/env_kmax/
    source ~/env_kmax/bin/activate
    pip3 install kmax

Instructions to install from source can be found in the [advanced documentation](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md).


### Kicking the tires

Install dependencies for compiling Linux source, then download and enter the Linux source:

    sudo apt install -y flex bison bc libssl-dev libelf-dev
    cd ~/
    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.16.tar.xz
    tar -xvf linux-5.16.tar.xz
    cd ~/linux-5.16/

Run `klocalizer --repair` to modify `allnoconfig` so that builds a given compilation unit:

    make ARCH=x86_64 allnoconfig
    klocalizer --repair .config -o allnoconfig_repaired --include drivers/usb/storage/alauda.o
    KCONFIG_CONFIG=allnoconfig_repaired make ARCH=x86_64 olddefconfig clean drivers/usb/storage/alauda.o
    
You should see `CC      drivers/usb/storage/alauda.o` at the end of the build.


## Using `klocalizer --repair` on patches

This tool will automatically "fix" your .config file so that it builds the lines from a given patchfile (or any specific files or file:line pairs).  To use it, first install [SuperC](https://github.com/appleseedlab/superc), which `klocalizer` depends on for finding`#ifdef` constraints:

    sudo apt-get install -y libz3-java libjson-java sat4j unzip flex bison bc libssl-dev libelf-dev xz-utils lftp
    wget -O - https://raw.githubusercontent.com/appleseedlab/superc/master/scripts/install.sh | bash
    export COMPILER_INSTALL_PATH=$HOME/0day
    export CLASSPATH=/usr/share/java/org.sat4j.core.jar:/usr/share/java/json-lib.jar:${HOME}/.local/share/superc/z3-4.8.12-x64-glibc-2.31/bin/com.microsoft.z3.jar:${HOME}/.local/share/superc/JavaBDD/javabdd-1.0b2.jar:${HOME}/.local/share/superc/xtc.jar:${HOME}/.local/share/superc/superc.jar:${CLASSPATH}
    export PATH=${HOME}/.local/bin/:${PATH}

Too see it in action, start with a clone of the linux repository and create a patch file:

    cd ~/
    git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
    cd ~/linux/
    git checkout 6fc88c354f3af
    git show > 6fc88c354f3af.diff
    
Now try using repair to update allnoconfig, which doesn't build all lines from the patch.  After repair, the resulting configuration file builds the lines affected by the patch.  The last command builds the files affected by the patch, which would have failed with an unrepaired allnoconfig.

    make ARCH=x86_64 allnoconfig
    klocalizer --repair .config -a x86_64 --include-mutex 6fc88c354f3af.diff
    KCONFIG_CONFIG=0-x86_64.config make ARCH=x86_64 olddefconfig clean kernel/bpf/cgroup.o net/ipv4/af_inet.o net/ipv4/udp.o net/ipv6/af_inet6.o net/ipv6/udp.o
    koverage --config 0-x86_64.config --arch x86_64 --check-patch 6fc88c354f3af.diff -o coverage_results.json
    cat coverage_results.json
    
When using `--include-mutex`, the generated configuration files are exported as `NUM-ARCH.config`, since several configuration files may be needed when patches contain mutually-exclusive lines.

## Using `koverage`

`koverage` checks whether a Linux configuration file includes a set of source file:line pairs for compilation.  This following checks whether lines 256 and 261 of `kernel/fork.c` are included for compilation by Linux v5.16 allyesconfig.

    cd ~/linux-5.16/
    make.cross ARCH=x86_64 allyesconfig
    koverage --config .config --arch x86_64 --check kernel/fork.c:[259,261] -o coverage_results.json
    make allnoconfig; klocalizer -v --repair .config --include kernel/fork.c:[259]; rm -rf koverage_files/; koverage -v -a x86 --config .config --check kernel/fork.c:[259] -o coverage.out

The coverage results are in `coverage_results.json`, which indicate that line 259 is included while 261 is excluded by allyesconfig, because the lines are under mutually-exclusive `#ifdef` branches.

Use `--check-patch file.patch` to check coverage of all source lines affected by a given patch.

## Using `kismet`

This tool will check for unmet dependency bugs in [Kconfig specifications](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html#menu-attributes) due to reverse dependencies overriding direct dependencies.

Run `kismet` on the root of the Linux source tree.

    kismet --linux-ksrc="${HOME}/linux-5.16/" -a=x86_64

Once finished (it can take about an hour on a commodity desktop), kismet will produce three outputs:

  1. A summary of the results in `kismet_summary_x86_64.txt`
  2. A list of results for each `select` construct in `kismet_summary_x86_64.csv` (`UNMET_ALARM` denotes the buggy ones)
  3. A list of `.config` files meant to exercise each bug in `kismet-test-cases/`

Technical details can be found in in the [kismet documentation](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md#kismet) and the [publication](https://paulgazzillo.com/papers/esecfse21.pdf) on `kclause` and `kismet`.  The experiment [replication script](https://github.com/paulgazz/kmax/blob/master/scripts/kismet_evaluation/kismet_experiments_replication.sh) can be used to run kismet on all architectures' Kconfig specifications.


## Additional documentation

[Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md)


## Bugs found

[Bugs Found](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found.md) by our tools


## Credits

The main developers of this project have been [Paul Gazzillo](https://paulgazzillo.com) (`kextract`, `kclause`, `kmax`, `klocalizer`), [Necip Yildiran](http://www.necipyildiran.com/) (`kismet`, `krepair`, `koverage`), [Jeho Oh](https://www.linkedin.com/in/jeho-oh-110a2092/) (`kclause`), and [Julian Braha](https://julianbraha.com/) (`koverage`).  [Julia Lawall](https://pages.lip6.fr/Julia.Lawall/) has posed new applications and provided invaluable advice, feedback, and support.  Thanks to all the users who have contributed code and issues.  Special thanks to the [Intel 0-day](https://01.org/lkp) team for working to include `kismet` into the kernel test robot and for their valuable feedback.  This work is funded in part by the National Science Foundation under awards [CCF-1840934](https://nsf.gov/awardsearch/showAward?AWD_ID=1840934) and [CCF-1941816](https://nsf.gov/awardsearch/showAward?AWD_ID=1941816).
