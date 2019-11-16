# Kmax

Kmax collects configuration information from [Kbuild Makefiles](https://www.kernel.org/doc/html/latest/kbuild/makefiles.html).  It determines, for each compilation unit, a symbolic Boolean expression that represents the conditions under which the file gets compiled and linked into the final program.

Kmax was created by [Paul Gazzillo](https://paulgazzillo.com).  Its algorithm is described in this [publication](https://paulgazzillo.com/papers/esecfse17.pdf).  The paper version of Kmax (v1.0) can be found [here](https://github.com/paulgazz/kmax/releases/tag/v1.0) along with other older [releases](https://github.com/paulgazz/kmax/releases).

Special thanks to [ThanhVu Nguyen](https://cse.unl.edu/~tnguyen/) for helping to integrate z3 into Kmax.

## pycudd

*pycudd usage is superseded by z3.  this dependency will be removed in later versions.*

http://bears.ece.ucsb.edu/ftp/pub/pycudd2.0/pycudd2.0.2.tar.gz

The package contains two directories, `cudd-2.4.2/` and `pycudd/`.
First enter `cudd-2.4.2/`.

If you are running a 64-bit machine, edit the Makefile by uncommenting
the line shown here starting with `XCFLAGS`.  You may see a compiler
error about `sys/cdefs.h` if you haven't edited the Makefile to build
for 64-bit.

    # Gcc 4.2.4 or higher on x86_64 (64-bit compilation)
    XCFLAGS	= -mtune=native -DHAVE_IEEE_754 -DBSD -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8 -fPIC

Now compile cudd-2.4.2 and create shared libraries for pycudd:

    make
    make libso

`make libso` may fail on nanotrav, but as long as the `lib/` directory
contains six shared object libraries, libcudd.so, libdddmp.so, etc,
then pycudd should build.

Install swig for the python to c interface.  In apt-based
distributions `apt-get install swig`.

Finally, go up to the parent directory, enter `pycudd/`, and build:

    make FLAGS="-I /opt/python/include/python2.7/ -fPIC"

## Environment

Kmax expects several environment variables to be set:

    export PYCUDD_ROOT=/path/to/pycudd/
    export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${PYCUDD_ROOT}/cudd-2.4.2/lib

With those variables configured, modify the `PATH`, `PYTHONPATH`, and
`LD_LIBRARY_PATH` variables to point to kmax and pycudd like so:

    export PATH=$PATH:${KMAX_ROOT}/kconfig:${KMAX_ROOT}/kbuild:${KMAX_ROOT}/kbuildplus:${KMAX_ROOT}/analysis
    export PYTHONPATH=$PYTHONPATH:${KMAX_ROOT}/lib

## Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    python kmax/kbuildplus.py -B tests/kbuild/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  The `-B` tells Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](docs/unit_pc.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.

## Example run on Linux

There is a script that will run Kmax on all Kbuild Makefiles from a project, e.g., the Linux kernel source code.

    # from, e.g., the top-level directory of the linux-4.19.50 source code
    kmaxdriver.py -B -g $(make CC=cc ARCH=x86 -f /path/to/kmax/kbuild/makefile_override alldirs) | tee unit_pc

The `-B` options means treat configuraion options as Boolean (as opposed to tristate) and `-g` means get the presence conditions in the `unit_pc` [format](docs/unit_pc.md).  The `makefile_override` file will extract all the top-level source directories, e.g., drivers, kernel, etc, from the Linux build system.  These are then each processed by Kmax, recursively entering any Kbuild subdirectories.

Finally, aggregate `unit_pc` to `full_pc`, i.e., combine the constraints for subdirectories with the constraints of the members of those subdirectories

    cat unit_pc | python /path/to/kmax/kbuildplus/aggregate.py > aggregate_pc

The aggregated file has a [format](docs/unit_pc.md) describing the constraints of on the compilation unit.

### Troubleshooting

- Be sure the environment is set (see the Environment section above) so that the `KMAX_ROOT` is known, etc.
- Try running `makefile_override` by itself to see that it is correctly extracting the top-level files.  The build may need to be configured first.
