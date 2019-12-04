<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Tools](#tools)
  - [Contributors](#contributors)
  - [Setup](#setup)
  - [Quick Start](#quick-start)
  - [Use Cases](#use-cases)
    - [Controlling the Search of Architectures](#controlling-the-search-of-architectures)
    - [Generating an Arbitrary Configuration for an Architecture](#generating-an-arbitrary-configuration-for-an-architecture)
    - [Setting Additional Configuration Options](#setting-additional-configuration-options)
    - [Investigating Unsatisfied Constraints](#investigating-unsatisfied-constraints)
    - [Optimizing the Resulting Configuration (Experimental)](#optimizing-the-resulting-configuration-experimental)
    - [View the Kbuild Constraints](#view-the-kbuild-constraints)
    - [Using New Formulas](#using-new-formulas)
  - [Troubleshooting](#troubleshooting)
  - [Generating Formulas](#generating-formulas)
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

Clone the repository and run

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

The fastest way to get started is to use formulas already extracted for your version of Linux.

    cd /path/to/linux/
    wget https://kmaxtools.opentheblackbox.net/formulas/kmax-formulas_linux-v5.4.tar.bz2
    tar -xvf kmax-formulas_linux-v5.4.tar.bz2

This contains a `.kmax` directory containing the Kconfig and Kbuild
formulas for each architecture.  If a version is not available
[here](https://kmaxtools.opentheblackbox.net/formulas) submit an issue to request
the formulas be generated and uplodated or see below for directions on
generating these formulas.

Assuming you are compiling for x86, the following will generate a
configuration that includes the `drivers/usb/storage/alauda.o` compilation unit.

    klocalizer drivers/usb/storage/alauda.o
    
The configuration is not complete, since it only accounts for Boolean/tristate configuration options.  Complete it with `olddefconfig`:

    make olddefconfig

The compilation unit should now be buildable.

    make drivers/usb/storage/alauda.o

If you cannot get a configuration or it is still not buildable, see the Troubleshooting section.

## Use Cases

By default, `klocalizer` checks each architecture's Kconfig
constraints against the Kbuild constraints for the given compilation
unit.  The following are examples of how to customize this process.

### Controlling the Search of Architectures

Use `-a` to only search a specific architecture.

    klocalizer -a x86_64 drivers/usb/storage/alauda.o

Specify multiple `-a` arguments to search the given architectures in given order.

    klocalizer -a x86_64 -a sparc drivers/watchdog/cpwd.o

Specify `-a` and `-all` to search all architectures, trying the ones given in `-a` first.

    klocalizer -a x86_64 -a arm --all drivers/watchdog/cpwd.o

### Generating an Arbitrary Configuration for an Architecture

Pass a single architecture name without the compilation unit to
generate an arbitrary configuration for that architecture.  Passing
multiple architectures is not supported.

    klocalizer -a x86_64

### Setting Additional Configuration Options

Multiple `--define` and `--undefine` arguments can be used to force
configurations on or off when searching for constraints.

    klocalizer --define CONFIG_USB --define CONFIG_FS --undefine CONFIG_SOUND drivers/usb/storage/alauda.o

Note that this can prevent finding a valid configuration.
 
    klocalizer -a x86_64 --undefine CONFIG_USB drivers/usb/storage/alauda.o  # no configuration possible because alauda depends on USB

### Investigating Unsatisfied Constraints

Use `--show-unsat-core` to see what constraints are causing the issue:

    klocalizer --show-unsat-core -a x86_64 --undefine CONFIG_USB drivers/usb/storage/alauda.o  # no configuration possible because alauda depends on USB

### Optimizing the Resulting Configuration (Experimental)

Klocalizer will attempt to match a given configuration, while still
maintaing the configuration options necessary to build the given
compilation unit.  This works by passing it an existing configuration,
e.g., `allnoconfig`, with the `--optimize` flag.

    make allnoconfig
    mv .config allnoconfig
    klocalizer --optimize allnoconfig drivers/usb/storage/alauda.o

  klocalizer with specific file

### View the Kbuild Constraints

View the Kbuild constraints for a compilation unit and each of
its subdirectories with

    klocalizer --view-kbuild drivers/usb/storage/alauda.o

### Using New Formulas

Override the default formulas with the following:

    klocalizer --kmax-formula kmax --kclause-formula kclause drivers/watchdog/cpwd.o
    
## Troubleshooting

- `klocalizer` requires the formulas from `kmax` and
  `kclause`. [Download](https://kmaxtools.opentheblackbox.net/formulas) these
  first or generate them (see below).

- Use the `CONFIG_` prefix on variables when referring to them in user constraints.

- Use the `.o` ending for compilation units (though `klocalizer` will change it automatically.)

- The extracted formulas may not be exact.  No resulting configuration is a sign that the formulas are overconstrained.  A resulting configuration that does not include the desired compilation unit mean the formulas may be underconstrained.

## Generating Formulas

These commands and scripts are intended to be run from the root of
your Linux source tree.

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
