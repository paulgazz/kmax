<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Tools](#tools)
  - [Contributors](#contributors)
  - [Setup](#setup)
  - [Quick Start](#quick-start)
  - [Use Cases](#use-cases)
    - [A Compilation Unit not Built by `allyesconfig`](#a-compilation-unit-not-built-by-allyesconfig)
    - [A Compilation Unit not Built by `defconfig` or `allnoconfig`](#a-compilation-unit-not-built-by-defconfig-or-allnoconfig)
    - [An Architecture-Specific Compilation Unit](#an-architecture-specific-compilation-unit)
  - [Advanced Usage](#advanced-usage)
  - [Troubleshooting](#troubleshooting)
  - [Generating Formulas for Linux](#generating-formulas-for-linux)
  - [Kmax](#kmax)
    - [Simple example](#simple-example)
    - [Example on Linux](#example-on-linux)
  - [Kclause](#kclause)
    - [Example](#example)
    - [Building kconfig_extract](#building-kconfig_extract)
    - [Other uses](#other-uses)
      - [Get a list of all visible configs](#get-a-list-of-all-visible-configs)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->


# The Kmax Tool Suite

## Tools

The Kmax Tool Suite (kmaxtools) contains a set of tools for performing
automated reasoning on Kconfig and Kbuild constraints.  It consists of
the following tools:

- `klocalizer` takes the name of a compilation unit and automatically
  generates a `.config` file that, when compiled, will include the
  given compilation unit.  It uses the logical models from `kclause` and `kmax`
- `kclause` "compiles"
  [Kconfig](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html)
  constraints into logical formulas.  `kconfig_extractor` uses Linux's
  own Kconfig parser to perform an extraction of the syntax of
  configuration option names, types, dependencies, etc.
- `kmax` collects configuration information from [Kbuild
  Makefiles](https://www.kernel.org/doc/html/latest/kbuild/makefiles.html).
  It determines, for each compilation unit, a symbolic Boolean
  expression that represents the conditions under which the file gets
  compiled and linked into the final program.  Its algorithm is
  described [here](https://paulgazzillo.com/papers/esecfse17.pdf) and
  the original implementation can be found
  [here](https://github.com/paulgazz/kmax/releases/tag/v1.0).

## Contributors

- [Paul Gazzillo](https://paulgazzillo.com) -- creator and developer
- [ThanhVu Nguyen](https://cse.unl.edu/~tnguyen/) -- developer and z3 integration into `kmax`
- Jeho Oh -- developer and kclause's Kconfig logical formulas
- [Julia Lawall](https://pages.lip6.fr/Julia.Lawall/) -- ideation, evaluation

## Setup

`kmaxtools` is currently written for python 2.

There are two ways to install kmaxtools.

1.  The latest release can be installed via `pip`

        pip install kmaxtools

    Upgrade with

        pip install -U kmaxtools
    
2.  Install from the source repository:

        git clone https://github.com/paulgazz/kmax.git
        cd kmax
        sudo python setup.py install

    Or use the `--prefix` argument for different installation directory without `sudo`.

    Please see [setup.py] for any dependencies if `setup.py` script does
    not work.  It may be necessary to install these manually via `pip`, e.g.,

        pip install enum34
        pip install regex
        pip install z3-solver
        pip install dd
        pip install networkx==2.2

## Quick Start

The fastest way to get started is to use formulas already extracted for your version of Linux, which you can download here: <https://kmaxtools.opentheblackbox.net/formulas>

    cd /path/to/linux/
    wget https://kmaxtools.opentheblackbox.net/formulas/kmax-formulas_linux-v5.4.tar.bz2
    tar -xvf kmax-formulas_linux-v5.4.tar.bz2

This contains a `.kmax` directory containing the Kconfig and Kbuild
formulas for each architecture.  If a version is not available
[here](https://kmaxtools.opentheblackbox.net/formulas) submit an issue to request
the formulas be generated and uplodated or see below for directions on
generating these formulas.

Run klocalizer for a given compilation unit, e.g.,

    klocalizer drivers/usb/storage/alauda.o

This will search each architecture for constraint satisfiability,
stopping once one is found (or no architecture's constraints are
satisfiable).  `klocalizer` writes this configuration to `.config` and
prints the architectures, e.g., `x86_64`, to standard out.

To build the compilation unit using the generated `.config`, use
[make.cross](https://github.com/fengguang/lkp-tests/blob/master/sbin/make.cross).
First set any defaults for the `.config` file:

    make.cross ARCH=x86_64 olddefconfig

Then build the compilation unit:

    make.cross ARCH=x86_64 drivers/usb/storage/alauda.o

If you cannot get a configuration or it is still not buildable, see the [Troubleshooting](#troubleshooting) section.

## Use Cases

### A compilation unit not built by allyesconfig

While `allyesconfig` strives to enable all options, some have conflicting dependencies or are mutually exclusive choices.  For instance, `fs/squashfs/decompressor_multi.o` is not compiled when using `allyesconfig`:

    make allyesconfig
    make fs/squashfs/decompressor_multi.o
    
`make` fails:

    make[3]: *** No rule to make target 'fs/squashfs/decompressor_multi.o'.  Stop.

Let us take a look at the unit's Kbuild dependencies:

    klocalizer --view fs/squashfs/decompressor_multi.o

The output in part is

    fs/squashfs/decompressor_multi.o
    [And(CONFIG_SQUASHFS, CONFIG_SQUASHFS_DECOMP_MULTI)]

The unit is not included in `allyesconfig` because it on both `CONFIG_SQUASHFS` and `CONFIG_SQUASHFS_DECOMP_MULTI`.  The latter is disabled by default, being mutually exclusive with `SQUASHFS_DECOMP_SINGLE` which is selected by allyesconfig:

    make allyesconfig
    egrep "(CONFIG_SQUASHFS|CONFIG_SQUASHFS_DECOMP_SINGLE|CONFIG_SQUASHFS_DECOMP_MULTI)( |=)" .config

`grep` shows us the relevant settings:

    CONFIG_SQUASHFS=y
    CONFIG_SQUASHFS_DECOMP_SINGLE=y
    # CONFIG_SQUASHFS_DECOMP_MULTI is not set

`klocalizer` can find a configuration that includes the unit:

    klocalizer fs/squashfs/decompressor_multi.o
    egrep "(CONFIG_SQUASHFS|CONFIG_SQUASHFS_DECOMP_SINGLE|CONFIG_SQUASHFS_DECOMP_MULTI)( |=)" .config

`grep` shows us what `klocalizer` set:

    CONFIG_SQUASHFS=y
    CONFIG_SQUASHFS_DECOMP_MULTI=y
    # CONFIG_SQUASHFS_DECOMP_SINGLE is not set

Finally, building the configuration 

    make olddefconfig
    make fs/squashfs/decompressor_multi.o

gives us

      CC      fs/squashfs/decompressor_multi.o


### A compilation unit not built by defconfig or allnoconfig

A kernel user or developer may want a smaller kernel that includes a specific compilation unit, rather than having to build `allyesconfig`.  For instance, `drivers/infiniband/core/cgroup.o` is not built by default:

    make defconfig
    make drivers/infiniband/core/cgroup.o
    
The output contains

    make[2]: *** No rule to make target 'drivers/infiniband/core/cgroup.o'.  Stop.

`klocalizer` can look for a configuration containing the compilation unit that closely matches a given configuration without it by successively removing conflicting constraints until the configuration is valid:

    make defconfig
    klocalizer --approximate .config drivers/infiniband/core/cgroup.o

Now when building the configuration, the compilation unit is included:

    make olddefconfig
    make drivers/infiniband/core/cgroup.o

The output contains:

      CC      drivers/infiniband/core/cgroup.o


### An architecture-specific compilation unit not built by allyesconfig

Sometimes a compilation unit is only available for certain architectures.   Compiling `drivers/block/ps3disk.o` won't compile on an `x86` machine.

    make allyesconfig
    klocalizer drivers/block/ps3disk.o

Its output contains

    make[3]: *** No rule to make target 'drivers/block/ps3disk.o'.  Stop.

`klocalizer --view drivers/block/ps3disk.o` shows us that it depends on `CONFIG_PS3_DISK`.  It turns out that this configuration option in turn depends on, among others options, the powerpc architecture.

`klocalizer` can try the constraints from each architecture:

    klocalizer drivers/block/ps3disk.o

It tells us that `powerpc` is a satisfying architecture.  We can use `make.cross` to cross-compile for `powerpc`.

    make.cross ARCH=powerpc olddefconfig
    make.cross ARCH=powerpc drivers/block/ps3disk.o
    
Its output contains

      CC      drivers/block/ps3disk.o

We can combine several `klocalizer` features to build an `allnoconfig` kernel that adds in the `ps3disk.o` compilation unit and sets all `tristate` options to modules.
    
    make.cross ARCH=powerpc allnoconfig
    klocalizer -a powerpc --match .config --modules --define CONFIG_MODULES drivers/block/ps3disk.o
    make.cross ARCH=powerpc olddefconfig
    make.cross ARCH=powerpc drivers/block/ps3disk.o

Its output contains

      CC [M]  drivers/block/ps3disk.o


### An Architecture-Specific Compilation Unit


## Advanced Usage

By default, `klocalizer` checks each architecture's Kconfig
constraints against the Kbuild constraints for the given compilation
unit.  The following are examples of how to customize this process.

- Controlling the search of architectures

    Use `-a` to only search a specific architecture.

        klocalizer -a x86_64 drivers/usb/storage/alauda.o

    Specify multiple `-a` arguments to search the given architectures in given order.

        klocalizer -a x86_64 -a sparc drivers/watchdog/cpwd.o

    Specify `-a` and `-all` to search all architectures, trying the ones given in `-a` first.

        klocalizer -a x86_64 -a arm --all drivers/watchdog/cpwd.o

- Generating an arbitrary configuration for an architecture

    Pass a single architecture name without the compilation unit to
    generate an arbitrary configuration for that architecture.  Passing
    multiple architectures is not supported.

        klocalizer -a x86_64 drivers/watchdog/cpwd.o

- Finding all architectures in which the compilation can be configured

    klocalizer --report-all 

- Setting additional configuration options

    Multiple `--define` and `--undefine` arguments can be used to force
    configurations on or off when searching for constraints.

        klocalizer --define CONFIG_USB --define CONFIG_FS --undefine CONFIG_SOUND drivers/usb/storage/alauda.o

    Note that this can prevent finding a valid configuration.

        klocalizer -a x86_64 --undefine CONFIG_USB drivers/usb/storage/alauda.o  # no configuration possible because alauda depends on USB

- Investigating unsatisfied constraints

    Use `--show-unsat-core` to see what constraints are causing the issue:

        klocalizer --show-unsat-core -a x86_64 --undefine CONFIG_USB drivers/usb/storage/alauda.o  # no configuration possible because alauda depends on USB

- Closely match a given configuration

Klocalizer will attempt to match a given configuration, while still
maintaing the configuration options necessary to build the given
compilation unit.  This works by passing it an existing configuration,
e.g., `allnoconfig`, with the `--approximate` flag.

    make allnoconfig
    mv .config allnoconfig
    klocalizer --approximate allnoconfig drivers/usb/storage/alauda.o

  klocalizer with specific file

- Viewing the Kbuild constraints

    View the Kbuild constraints for a compilation unit and each of
    its subdirectories with

        klocalizer --view-kbuild drivers/usb/storage/alauda.o

- Building as modules instead of built-in

    Use the `--modules` flag to set any tristate options to `m` instead of
    `y`.  Be sure to enable the `CONFIG_MODULES` option as well.

        klocalizer --modules --define CONFIG_MODULES drivers/usb/storage/alauda.o
        make olddefconfig
        make drivers/block/ps3disk.o

- Using new formulas

    Override the default formulas with the following:

        klocalizer --kmax-formula kmax --kclause-formulas kclause drivers/watchdog/cpwd.o

- Generating multiple configurations

        klocalizer -a x86_64 --random-seed 7849 --sample 8 --sample-prefix config

## Troubleshooting

- `klocalizer` requires the formulas from `kmax` and
  `kclause`. [Download](https://kmaxtools.opentheblackbox.net/formulas) these
  first or generate them (see below).

- Use the `CONFIG_` prefix on variables when referring to them in user constraints.

- Use the `.o` ending for compilation units (though `klocalizer` will change it automatically.)

- The extracted formulas may not be exact.  No resulting configuration is a sign that the formulas are overconstrained.  A resulting configuration that does not include the desired compilation unit mean the formulas may be underconstrained.

- Compilation unit not buildable.  There are several possible reasons:

    1. The compilation unit has already been compiled.  First clean with
       
            make clean

    2. While most compilation units can be built individually with make, some cannot.  In these cases, build the parent directory instead, e.g.,
    
            klocalizer drivers/char/ipmi/ipmi_devintf.o  # finds it buildable in x86_64
            make.cross ARCH=x86_64 olddefconfig
            make.cross ARCH=x86_64 drivers/char/ipmi/
            
    3. Composites do not correspond to source files and are not built directly via `make`.  Instead they are composed of other compilation units.  For instance, `drivers/block/zram/zram.o` is comprised of `zcomp.o` and `zram_drv.o`.  After finding a satisfying configuration, build the parent directory to see the source files that comprise it built.
    
            klocalizer --approximate .config drivers/block/zram/zram.o
            make olddefconfig
            make drivers/block/zram/
        
    4. The configuration causes the unit to be built, but it has a compile-time error.
    
            klocalizer drivers/block/amiflop.o  # finds it buildable in 
            make.cross ARCH=m68k olddefconfig
            make.cross ARCH=m68k drivers/block/amiflop.o  # Makefile sees it, but causes compiler error.
        
    5. Klocalizer's formulas were wrong in some cases

- If the unit's configuration constraints depend  on - `CONFIG_BROKEN`, then `klocalizer`, by default, which detect it and stop searching, because the compilation unit may not be (easily) compilable.
    
        klocalizer drivers/watchdog/pnx833x_wdt.o  # stops after finding a dependency on `CONFIG_BROKEN`

    To get a configuration anyway, use `--allow-config-broken`

        klocalizer --allow-config-broken drivers/watchdog/pnx833x_wdt.o  # finds dependency on mips
        make.cross ARCH=mips olddefconfig
        make.cross ARCH=mips drivers/watchdog/pnx833x_wdt.o  # won't be included in the build, due to CONFIG_BROKEN

## Generating Formulas for Linux

This requires cloning the kmax repository, since there are helper
scripts to generate the formulas for Linux.  These commands and
scripts are intended to be run from the root of your Linux source
tree.

To get the formulas for compilation units defined in the Kbuild files,
we first need a list of all the top-level source directories for each
architecture.  The script uses a hacky Makefile to do this.  Then
calls kmaxall with all of the top-level directories.  This is a memory
intensive operation.  The next script calls kclause on each of the
architectures, as named in the arch/ directory.

    cd /path/to/linux
    mkdir -p .kmax/
    /usr/bin/time bash /path/to/kmax/scripts/kmaxlinux.sh
    /usr/bin/time bash /path/to/kmax/scripts/kclauselinux.sh
    bash /path/to/kmax/scripts/packageformulaslinux.sh
    
## Kmax

### Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    kmax tests/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  By default, Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).  Pass `-T` for experimental support for tristate.

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](docs/unit_pc.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.  Use `-z` to emit the z3 formulas in smtlib2 format.

### Example on Linux

There is a script that will run Kmax on all Kbuild Makefiles from a project, e.g., the Linux kernel source code.

First get the Linux source and prepare its build system.

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.3.11.tar.xz
    tar -xvf linux-5.3.11.tar.xz
    cd linux-5.3.11
    make defconfig # any config will work here.  it's just to setup the build system.

To try Kmax on a particular Kbuild Makefile, use the `kbuildplus.py` tool:

    kmax ipc/
    
This will run Kmax on a single Kbuild Makefile, and show the symbolic configurations for each compilation unit and subdirectory.  Kmax can also recursively analyze Kbuild Makefiles by following subdirectories, use the `kmaxdriver.py` which uses `kbuildplus.py` to process each Kbuild Makefile and recursively process those in subdirectories.  `-g` means collect the symbolic constraints.

    kmaxall -g net/
    
Kmax includes a Makefile hack to get all the top-level Linux directories.  Combined with `kmaxall` this command will collect the symbolic constraints for the whole (x86) source, saving them into `unit_pc`.  Be sure to change `/path/to/kmax` to your kmax installation to get the Makefile shunt.

    kmaxall -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) | tee kmax

## Kclause

### Example

Kclause extracts a logical model from Kconfig.  It works in two stages:

1. The `kconfig_extractor` tool uses the Kconfig parser shipped with Linux to extract configuration variables dependencies to an intermediate language.

2. The `kclause` tool takes this intermediate language and generates a z3 formula.


First compile `kconfig_extractor`

    make -C kconfig_extractor

Then, from the root of a Linux source tree, run the following:

    /path/to/kmax/kconfig_extractor/kconfig_extractor --extract -e ARCH=x86_64 -e SRCARCH=x86 -e KERNELVERSION=kcu -e srctree=./ -e CC=cc Kconfig > kconfig_extract
    kclause --remove-orphaned-nonvisible < kconfig_extract > kclause

### Building kconfig_extract

    make -C /path/to/kmax/kconfig_extractor/

### Other uses

#### Get a list of all visible configs

    # all the configs that have a prompt condition
    grep "^prompt " kconfig.kclause | cut -f2 -d\  | sort | uniq | tee visible.txt

    # all the configs
    grep "^config " kconfig.kclause | cut -f2 -d\  | sort | uniq | tee configs.txt
    
    # the visibles should be a subset of the configs
    diff configs.txt visible.txt  | grep ">"
