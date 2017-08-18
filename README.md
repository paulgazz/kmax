# Kmax

## Dependencies

### lockfile

https://github.com/smontanaro/pylockfile

    setup python.py install --user

### enum34

https://pypi.python.org/packages/source/e/enum34/enum34-1.0.tar.gz#md5=9d57f5454c70c11707998ea26c1b0a7c

    setup python.py install --user

### pycudd (http://bears.ece.ucsb.edu/ftp/pub/pycudd2.0/pycudd2.0.2.tar.gz)

make sure to edit the cudd-2.4.2/Makefile to build a 64-bit version

install swig (for python to c interface)

compile cudd-2.4.2:

    make
    make libso

compile pycudd:

    make FLAGS="-I /opt/python/include/python2.7/ -fPIC"

## Build Kmax

`check_dep` gathers constraints and other information from Kconfig files

    cd kconfig
    make

The Kbuild portion of Kmax is written in python, and needs no compilation.  It depends on `pymake`, so install that with

    cd kbuild
    make

## Environment

Kmax expects several environment variables to be set.

Setup the root of the Kmax tool, add it to path, provide a data
directory for kmax output, and provide a scratch directory for
downloaded linux instances:

    KMAX_ROOT=$CPPDIR/kmax
    PATH=$PATH:$KMAX_ROOT/kconfig:$KMAX_ROOT/kbuild:$KMAX_ROOT/analysis
    KMAX_SCRATCH=/home/user/kmax_scratch
    KMAX_DATA=/home/user/kmax_data
    export KMAX_ROOT KMAX_SCRATCH KMAX_DATA PATH

Put pycudd and kmax lib in the python path:

    PYTHONPATH=$PYTHONPATH:~/src/pycudd2.0.2/pycudd:$KMAX_ROOT/lib
    export PYTHONPATH

Put cudd libraries in the load path:

    LD_LIBRARY_PATH=$LD_LIBRARY_PATH:~/src/pycudd2.0.2/cudd-2.4.2/lib
    export LD_LIBRARY_PATH

## Example run

This will download and collect all compilation units and presence
conditions from v4.0 of the Linux kernel source.

    python analysis/collect_buildsystem.py 4.0 x86

## Using constraints on compilation units

Constraints for each compliation unit are in `$KMAX_DATA/unit_pc_VERARCH.txt`, e.g., `unit_pc_4.0x86.txt`.  The file containts two types of lines:

1. "`subdir_pc DIRNAME boolean_formula`" describes constraints for directories.
2. "`unit_pc OBJFILE boolean_formula`" describes constraints for
   compilation units.

These constraints are local to subdirectories, i.e., they need to be
combined to find the complete constraints.  For instance, in , the
complete constraints for `drivers/net/ethernet/ethoc.o` can be found by the
conjunction of the following constraints:

    subdir_pc drivers/net 1
    subdir_pc drivers/net/ethernet CONFIG_ETHERNET=y && defined(CONFIG_ETHERNET)
    unit_pc drivers/net/ethernet/ethoc.o defined(CONFIG_ETHOC) && CONFIG_ETHOC=y

Combining them yields the complete constraint for `ethdoc.o`:

    1 && CONFIG_ETHERNET=y && defined(CONFIG_ETHERNET) && defined(CONFIG_ETHOC) && CONFIG_ETHOC=y

Top-level directories like `drivers/` are always unconstrained, and a
constraint of `1` also means unconstrained.  Since Makefiles do not
have boolean variables, `CONFIG_ETHERNET=y` and
`defined(CONFIG_ETHERNET)` are boolean representations of these
variables that reflect both ways Makefiles can test variables, via
`ifeq` and `ifdef`.
