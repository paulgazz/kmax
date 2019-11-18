# Kmax

Kmax collects configuration information from [Kbuild Makefiles](https://www.kernel.org/doc/html/latest/kbuild/makefiles.html).  It determines, for each compilation unit, a symbolic Boolean expression that represents the conditions under which the file gets compiled and linked into the final program.

Kmax was created by [Paul Gazzillo](https://paulgazzillo.com).  Its algorithm is described in this [publication](https://paulgazzillo.com/papers/esecfse17.pdf).  The paper version of Kmax (v1.0) can be found [here](https://github.com/paulgazz/kmax/releases/tag/v1.0) along with other older [releases](https://github.com/paulgazz/kmax/releases) that have the Kconfig processing and other analysis scripts.

Special thanks to [ThanhVu Nguyen](https://cse.unl.edu/~tnguyen/) for integrating z3 into Kmax and refactoring the code.

## Related projects

Kclause extract logical models of Kconfig files, configuration specifications originally used in the Linux source code.  Kclause was originally part of the Kmax repository and is now under development here: <https://github.com/paulgazz/kclause>

Prior versions of Kmax can be found under releases, e.g., the original Kmax paper version from ESEC/FSE 2017 and the version used for the variability-aware bug-finding study in ESEC/FSE 2019: <https://github.com/paulgazz/kmax/releases>

Even older version of Kmax can be found in the SuperC codebase.  The SuperC project parses all configurations of unpreprocessed C code and and can be in the xtc codebase: <https://github.com/paulgazz/xtc>

## Setup

Clone the repository and run

    python setup.py install

This requires python setup tools (`pip install setuptools`).  Use
`--prefix` to specify a different installation directory.

## Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    kbuildplus.py tests/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  By default, Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).  Pass `-T` for experimental support for tristate.

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](docs/unit_pc.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.

## Example run on Linux

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
    
Kmax includes a Makefile hack to get all the top-level Linux directories.  Combined with `kmaxdriver.py` this command will collect the symbolic constraints for the whole (x86) source, saving them into `unit_pc`.

    kmaxdriver.py -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) | tee unit_pc

The symbolic constraints for each compilation unit, including the conjunction of all of its parent directories, can be computed with this command:

    cat unit_pc | python kmaxdriver.py --aggregate > full_pc

This is the [format](docs/unit_pc.md) for `unit_pc` and `full_pc`.
