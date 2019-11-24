<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [The Kmax Tool Suite](#the-kmax-tool-suite)
  - [Setup](#setup)
  - [Simple example](#simple-example)
  - [Example run on Linux](#example-run-on-linux)
  - [Kclause](#kclause)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# The Kmax Tool Suite

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

kmaxtool's creator and maintainer is [Paul
Gazzillo](https://paulgazzillo.com).  Contributors include [ThanhVu
Nguyen](https://cse.unl.edu/~tnguyen/) (z3 integration into `kmax`)
and Jeho Oh (development of Kconfig logical formaulas).

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
    wget https://opentheblackbox.com/kmaxspecs/kmaxspecs_linux_5_3_11.tar.bz2
    tar -xvf kmaxspecs_linux_5_3_11.tar.bz2
    
This will create a `kmaxspecs` directory for use with `klocalizer` and
will obviate the need to run `kclause` and `kmax`.  (See below for
directions on running these for a new version of Linux.)

### For one architecture

If you already know the architecture you'd like to build `.config`
file for, run `klocalizer` like this to create the configuration:

    klocalizer drivers/usb/storage/alauda.o > .config
    make olddefconfig
    
The compilation unit (should) now be included when compiling the kernel:

    make drivers/usb/storage/alauda.o

###

Some files 

## Kmax

(This guide on Kmax is out-of-date.)

### Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    kbuildplus.py tests/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  By default, Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).  Pass `-T` for experimental support for tristate.

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](docs/unit_pc.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.

### Example run on Linux

There is a script that will run Kmax on all Kbuild Makefiles from a project, e.g., the Linux kernel source code.

First get the Linux source and prepare its build system.

    wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.3.11.tar.xz
    tar -xvf linux-5.3.11.tar.xz
    cd linux-5.3.11
    make defconfig # any config will work here.  it's just to setup the build system.

To try Kmax on a particular Kbuild Makefile, use the `kbuildplus.py` tool:

    kbuildplus.py ipc/
    
This will run Kmax on a single Kbuild Makefile, and show the symbolic configurations for each compilation unit and subdirectory.  Kmax can also recursively analyze Kbuild Makefiles by following subdirectories, use the `kmaxdriver.py` which uses `kbuildplus.py` to process each Kbuild Makefile and recursively process those in subdirectories.  `-g` means collect the symbolic constraints.

    kmaxdriver.py -g net/
    
Kmax includes a Makefile hack to get all the top-level Linux directories.  Combined with `kmaxdriver.py` this command will collect the symbolic constraints for the whole (x86) source, saving them into `unit_pc`.  Be sure to change `/path/to/kmax` to your kmax installation to get the Makefile shunt.

    kmaxdriver.py -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) | tee unit.kmax

The symbolic constraints for each compilation unit, including the conjunction of all of its parent directories, can be computed with this command:

    cat unix.kmax | kmaxdriver.py --aggregate > kmax
    
These commands together:

    kmaxdriver.py -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) | tee unit.kmax | kmaxdriver.py --aggregate > kmax

This is the [format](docs/unit_pc.md) for `unit.kmax` and `kmax`.

## Kclause

    /path/to/kmax/kconfig_extractor/kconfig_extractor --extract -e ARCH=x86_64 -e SRCARCH=x86 -e KERNELVERSION=kcu -e srctree=./ -e CC=cc Kconfig > kconfig.kclause
    kclause --remove-orphaned-nonvisible < kconfig.extract > kconfig.kclause
