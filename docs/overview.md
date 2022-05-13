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
  given compilation unit.  It uses the logical models from `kclause`
  and `kmax`.  The configuration localization problem is described in
  an [SPLC 2018 challenge
  paper](https://doi.org/10.1145/3233027.3236404)
  ([preprint](https://paulgazzillo.com/papers/splc18challenge.pdf)).
- `kclause` "compiles"
  [Kconfig](https://www.kernel.org/doc/html/latest/kbuild/kconfig-language.html)
  constraints into logical formulas.  `kextractor` uses Linux's own
  Kconfig parser to perform an extraction of the syntax of
  configuration option names, types, dependencies, etc.  It is
  described in our [ESEC/FSE 2021 research
  paper](https://doi.org/10.1145/3468264.3468578)
  ([preprint](https://paulgazzillo.com/papers/esecfse21.pdf)).
- `kmax` collects configuration information from [Kbuild
  Makefiles](https://www.kernel.org/doc/html/latest/kbuild/makefiles.html).
  It determines, for each compilation unit, a symbolic Boolean
  expression that represents the conditions under which the file gets
  compiled and linked into the final program.  Its algorithm is
  described in our [ESEC/FSE 2017 research
  paper](https://doi.org/10.1145/3106237.3106283)
  ([preprint](https://paulgazzillo.com/papers/esecfse17.pdf)) and the
  original implementation is in [version
  1.0](https://github.com/paulgazz/kmax/releases/tag/v1.0).
- `kismet` does verification-based static analysis to find unmet
  dependency bugs and generates test cases.  It is described in our
  [ESEC/FSE 2021 research
  paper](https://doi.org/10.1145/3468264.3468578)
  ([preprint](https://paulgazzillo.com/papers/esecfse21.pdf)).
- `koverage` checks whether a Linux configuration file includes a set of
   (sourcefile,line) for compilation.  It utilizes the Linux build system
   to determine coverage.

## Contributors

- [Paul Gazzillo](https://paulgazzillo.com) -- kextract, kclause, kmax, klocalizer
- [Jeho Oh](https://www.linkedin.com/in/jeho-oh-110a2092/) -- kclause
- [Necip Yildiran](http://www.necipyildiran.com/) -- kismet, krepair, koverage
- [Julian Braha](https://julianbraha.com/) -- kclause, koverage

Special thanks to [Julia Lawall](https://pages.lip6.fr/Julia.Lawall/)
for posing the problem and for invaluable advice, feedback, and
support. Thanks also to [ThanhVu
Nguyen](https://cse.unl.edu/~tnguyen/) for adding z3 support to kmax.
