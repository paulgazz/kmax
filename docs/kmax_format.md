<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Constraints for compilation units in the `full_pc` format](#constraints-for-compilation-units-in-the-full_pc-format)
- [Constraints for compilation units in the `unit_pc` format](#constraints-for-compilation-units-in-the-unit_pc-format)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Constraints for compilation units in the `full_pc` format

The `full_pc` line has the following format:

    full_pc path constraint
    
This describes, for a given compilation unit `path`, the Kbuild configuration constraints `constraint`.  For example,

    full_pc drivers/input/touchscreen/cyttsp4_core.o CONFIG_TOUCHSCREEN_CYTTSP4_CORE && CONFIG_INPUT && CONFIG_INPUT_TOUCHSCREEN

says that the `drivers/input/touchscreen/cyttsp4_core.o` will only be included in the build when the subsequent Boolean expression is true.  In this case, all three configuration options need to be enalbed in Kconfig.

`full_pc` describes the combined configuration conditions for both the directory `drivers/input/touchscreen` and the compilation unit `cyttsp4_core.o`, which are specified separately in Kbuild.  See below for the format where these constraints are separated.  The `kbuildplus/aggregate.py` script creates the `full_pc` lines from `unit_pc` lines.

## Constraints for compilation units in the `unit_pc` format

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
