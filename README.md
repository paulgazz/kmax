<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The kmax tool suite](#the-kmax-tool-suite)
  - [Installation](#installation)
    - [Dependencies](#dependencies)
    - [Installing the kmax tool suite](#installing-the-kmax-tool-suite)
    - [Quick test](#quick-test)
  - [Using `krepair` on patches](#using-krepair-on-patches)
    - [The paper example](#the-paper-example)
  - [Using `kismet`](#using-kismet)
    - [Checking a single select construct](#checking-a-single-select-construct)
    - [Checking all Kconfig files for an architecture](#checking-all-kconfig-files-for-an-architecture)
  - [Using `klocalizer --save-dimacs` and `klocalizer --save-smt`](#using-klocalizer---save-dimacs-and-klocalizer---save-smt)
  - [Additional documentation](#additional-documentation)
  - [Bugs found](#bugs-found)
  - [Credits](#credits)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The kmax tool suite

## Installation

### Dependencies

    # kmax dependencies
    sudo apt install -y pipx python3-dev gcc build-essential
    # linux dependencies
    sudo apt install -y flex bison bc libssl-dev libelf-dev git
    # superc dependencies
    sudo apt install -y wget libz3-java libjson-java sat4j unzip xz-utils lftp
    # install superc and make.cross
    wget -O - https://raw.githubusercontent.com/appleseedlab/superc/master/scripts/install.sh | bash

Add these environment variables to your shell, e.g., `.bash_profile`:

    export COMPILER_INSTALL_PATH=$HOME/0day
    export CLASSPATH=/usr/share/java/org.sat4j.core.jar:/usr/share/java/json-lib.jar:${HOME}/.local/share/superc/z3-4.8.12-x64-glibc-2.31/bin/com.microsoft.z3.jar:${HOME}/.local/share/superc/JavaBDD/javabdd-1.0b2.jar:${HOME}/.local/share/superc/xtc.jar:${HOME}/.local/share/superc/superc.jar:${CLASSPATH}
    export PATH=${HOME}/.local/bin/:${PATH}

### Installing the kmax tool suite

    pipx install kmax

### Quick test
    
Get Linux kernel source:

    cd ~/
    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.16.tar.xz
    tar -xvf linux-5.16.tar.xz
    cd ~/linux-5.16/

Test `krepair` by automatically repairing `allnoconfig` to include `drivers/usb/storage/alauda.o`, which would normally be omitted by `allnoconfig`.

    # create allnoconfig
    make ARCH=x86_64 allnoconfig
    # run klocalizer --repair allnoconfig to build alauda.c
    klocalizer --repair .config -o allnoconfig_repaired --include drivers/usb/storage/alauda.o
    # clean and build the kernel with the repair config file
    KCONFIG_CONFIG=allnoconfig_repaired make ARCH=x86_64 olddefconfig clean drivers/usb/storage/alauda.o
    
You should see `CC      drivers/usb/storage/alauda.o` at the end of the build.

## Using `krepair` on patches

`klocalizer --repair` will take a config file that fails to build lines of a patch and repairs it to build the whole patch. 
This uses [SuperC](https://github.com/appleseedlab/superc) to find `#ifdef` constraints.

Let's first get the Linux source code:

    cd ~/
    git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
	
Now let's get an example patch from the Linux kernel's mainline repository:	
	
    cd ~/linux/
    git checkout 6fc88c354f3af
    git show > 6fc88c354f3af.diff

Next, let's repair allnoconfig, which does not build all lines from the patch.

    # create allnoconfig
    make.cross ARCH=x86_64 allnoconfig
    # run klocalizer to repair allnoconfig to include the patch
    klocalizer --repair .config -a x86_64 --include-mutex 6fc88c354f3af.diff
    # clean and build the files modified by the patch (WERROR=0 for tools/lib/subcmd/subcmd-util.h which triggers a use-after-free on gcc 13)
    KCONFIG_CONFIG=0-x86_64.config make.cross WERROR=0 ARCH=x86_64 olddefconfig clean kernel/bpf/cgroup.o net/ipv4/af_inet.o net/ipv4/udp.o net/ipv6/af_inet6.o net/ipv6/udp.o

We can use `koverage` to check how much of patch is covered by a given config file:

    koverage -f --config 0-x86_64.config --arch x86_64 --check-patch 6fc88c354f3af.diff -o coverage_results.json
    cat coverage_results.json

In contrast, we can see that `allnoconfig` omits coverage of the patch:

    make.cross ARCH=x86_64 allnoconfig
    koverage -f --config .config --arch x86_64 --check-patch 6fc88c354f3af.diff -o allnoconfig_coverage_results.json
    cat allnoconfig_coverage_results.json

Notes:

- While repair usually covers all lines of a patch, some lines may still be omitted, for instance if they are dead code or in header files.
- If a patch modifies both arms of an `#ifdef`, multiple config files are needed to cover all lines.  These are exported as `NUM-ARCH.config`.

### The paper example

Here is another example from the [krepair paper](https://paulgazzillo.com/papers/fse24.pdf).  This [patch](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/commit/?id=8594c3b85171b6f68e34e07b533ec2f1bf7fb065) modifies code in both arms of an `#ifdef`, so a single `.config` file cannot cover all patched lines.  `klocalizer` emits two `.config` files, which together cover all lines.

    git checkout 8594c3b85171b
    git show > 8594c3b85171b.diff
	make.cross ARCH=arm allnoconfig
    klocalizer --repair .config -a arm --include-mutex 8594c3b85171b.diff
    koverage -f --config 0-arm.config --arch arm --check-patch 8594c3b85171b.diff -o 0-coverage_results.json
    koverage -f --config 1-arm.config --arch arm --check-patch 8594c3b85171b.diff -o 1-coverage_results.json
    cat 0-coverage_results.json
    cat 1-coverage_results.json
	diff -y 0-coverage_results.json 1-coverage_results.json | less

## Using `kismet`

This tool will check for unmet dependency bugs in [Kconfig specifications](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html#menu-attributes) due to reverse dependencies overriding direct dependencies.

### Checking a single select construct

Found by [Intel's kernel test robot running kismet](https://lore.kernel.org/lkml/cc9905dd-5b66-d01e-491c-64c18198d208@intel.com/)

    git checkout 5a7f27a624d9e33262767b328aa7a4baf7846c14
    kismet --linux-ksrc=./ --selectees CONFIG_SND_SOC_MAX98357A --selectors CONFIG_SND_SOC_INTEL_SOF_CS42L42_MACH -a=x86_64

The alarm can be found in `kismet_summary_x86_64.csv` and `.config` files that exercise the bug can be found in `kismet-test-cases/`.

### Checking all Kconfig files for an architecture

Run `kismet` on the root of the Linux source tree.

    kismet --linux-ksrc="${HOME}/linux-5.16/" -a=x86_64

Once finished (it can take about an hour on a commodity desktop), kismet will produce three outputs:

  1. A summary of the results in `kismet_summary_x86_64.txt`
  2. A list of results for each `select` construct in `kismet_summary_x86_64.csv` (`UNMET_ALARM` denotes the buggy ones)
  3. A list of `.config` files meant to exercise each bug in `kismet-test-cases/`

Technical details can be found in in the [kismet documentation](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md#kismet) and the [publication](https://paulgazzillo.com/papers/esecfse21.pdf) on `kclause` and `kismet`.  The experiment [replication script](https://github.com/paulgazz/kmax/blob/master/scripts/kismet_evaluation/kismet_experiments_replication.sh) can be used to run kismet on all architectures' Kconfig specifications.

## Using `klocalizer --save-dimacs` and `klocalizer --save-smt`

This tool extracts a DIMACS or a SMT formula.
Therefore, execute the following commands in the root directory of your Linux kernel:

    klocalizer -a x86_64 --save-dimacs <Path>
    klocalizer -a x86_64 --save-smt <Path>

Note that `<Path>` should be replaced by the absolute path to the file, the formulae should be written to.
If you intend to use a Docker container, feel free to use the Dockerfile provided in [Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md).

## Additional documentation

[Advanced Usage](https://github.com/paulgazz/kmax/blob/master/docs/advanced.md)


## Bugs found

[Bugs Found](https://github.com/paulgazz/kmax/blob/master/docs/bugs_found.md) by our tools


## Credits

The main developers of this project have been [Paul Gazzillo](https://paulgazzillo.com) (`kextract`, `kclause`, `kmax`, `klocalizer`), [Necip Yildiran](http://www.necipyildiran.com/) (`kismet`, `krepair`, `koverage`), [Jeho Oh](https://www.linkedin.com/in/jeho-oh-110a2092/) (`kclause`), and [Julian Braha](https://julianbraha.com/) (`koverage`).  [Julia Lawall](https://pages.lip6.fr/Julia.Lawall/) has posed new applications and provided invaluable advice, feedback, and support.  Thanks to all the users who have contributed code and issues.  Special thanks to the [Intel 0-day](https://01.org/lkp) team for working to [include `kismet` into the kernel test robot](https://lore.kernel.org/all/d13eec5d-ee87-2207-05a4-1c7732bca4cd@intel.com/) and for their valuable feedback.  This work is funded in part by the National Science Foundation under awards [CCF-1840934](https://nsf.gov/awardsearch/showAward?AWD_ID=1840934) and [CCF-1941816](https://nsf.gov/awardsearch/showAward?AWD_ID=1941816).
