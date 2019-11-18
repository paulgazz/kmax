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

## Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    kbuildplus.py -B tests/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  The `-B` tells Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](docs/unit_pc.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.

## Example run on Linux

There is a script that will run Kmax on all Kbuild Makefiles from a project, e.g., the Linux kernel source code.

    # from, e.g., the top-level directory of the linux-4.19.50 source code
    cd linux-source/
    make defconfig # setup the build and config system
    kmaxdriver.py -B -g $(make CC=cc ARCH=x86 -f /path/to/kmax/scripts/makefile_override alldirs) | tee unit_pc

The `-B` options means treat configuraion options as Boolean (as opposed to tristate) and `-g` means get the presence conditions in the `unit_pc` [format](docs/unit_pc.md).  The `makefile_override` file will extract all the top-level source directories, e.g., drivers, kernel, etc, from the Linux build system.  These are then each processed by Kmax, recursively entering any Kbuild subdirectories.

Finally, aggregate `unit_pc` to `full_pc`, i.e., combine the constraints for subdirectories with the constraints of the members of those subdirectories

    cat unit_pc | python /path/to/kmax/kbuildplus/aggregate.py > aggregate_pc

The aggregated file has a [format](docs/unit_pc.md) describing the constraints of on the compilation unit.
