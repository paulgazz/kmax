<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->


- [Overview](#overview)
  - [Tools](#tools)
  - [Contributors](#contributors)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Overview

## Tools

The Kmax Tool Suite (kmax) contains a set of tools for performing
automated reasoning on Kconfig and Kbuild constraints.  It consists of
the following tools:

- `klocalizer` takes the name of a compilation unit and automatically
  generates a `.config` file that, when compiled, will include the
  given compilation unit.  It uses the logical models from `kclause` and `kmax`
- `kclause` "compiles"
  [Kconfig](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html)
  constraints into logical formulas.  `kextractor` uses Linux's
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
