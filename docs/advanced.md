<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Advanced Usage](#advanced-usage)
  - [Installing from Source](#installing-from-source)
  - [`klocalizer` and `krepair`](#klocalizer-and-krepair)
    - [Example usage](#example-usage)
    - [Coverage report](#coverage-report)
    - [`ERROR: SuperC checks failed`](#error-superc-checks-failed)
    - [Getting configuration files to build commit ranges](#getting-configuration-files-to-build-commit-ranges)
  - [`kismet`](#kismet)
    - [Analysis stages](#analysis-stages)
      - [Syntactical optimization](#syntactical-optimization)
      - [Optimized SAT check](#optimized-sat-check)
      - [Precise SAT check](#precise-sat-check)
    - [Summary format](#summary-format)
  - [`koverage`](#koverage)
      - [Checking (file:line) pairs](#checking-fileline-pairs)
      - [Checking patch coverage](#checking-patch-coverage)
      - [How to interpret coverage results](#how-to-interpret-coverage-results)
  - [Annotated Example](#annotated-example)
  - [Use Cases](#use-cases)
    - [A compilation unit not built by allyesconfig](#a-compilation-unit-not-built-by-allyesconfig)
    - [A compilation unit not built by defconfig or allnoconfig](#a-compilation-unit-not-built-by-defconfig-or-allnoconfig)
    - [An architecture-specific compilation unit not built by allyesconfig](#an-architecture-specific-compilation-unit-not-built-by-allyesconfig)
  - [Using merge_config.sh instead of olddefconfig](#using-merge_configsh-instead-of-olddefconfig)
  - [Klocalizer](#klocalizer)
    - [Troubleshooting](#troubleshooting)
  - [Formulas Cache Directory Structure](#formulas-cache-directory-structure)
  - [Generating Formulas for BusyBox](#generating-formulas-for-busybox)
    - [Test out `klocalizer` on BusyBox](#test-out-klocalizer-on-busybox)
  - [Kmax](#kmax)
    - [Simple example](#simple-example)
    - [Example on Linux](#example-on-linux)
    - [Using `kreader` to Print Kmax Results](#using-kreader-to-print-kmax-results)
  - [Kclause](#kclause)
    - [Example](#example)
    - [Other uses](#other-uses)
      - [Get a list of all visible configs](#get-a-list-of-all-visible-configs)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Advanced Usage

## Installing from Source

Install the prerequisites

    sudo apt install -y python3-setuptools python3-dev
    
Clone and install kmax

    git clone https://github.com/paulgazz/kmax.git
    cd kmax
    python3 -m venv ~/kmax_env/
    source ~/kmax_env/bin/activate
    python3 setup.py install

Alternatively, installing for development to obviate the need to
rereun setup.py when making changes to the code

    python3 setup.py develop


## `klocalizer` and `krepair`

### Example usage

`klocalizer --repair` can repair existing configuration files to include given source code directories, files, and lines from Linux kernel source code.  For instance, let's use it to repair the minimal `allnoconfig` so that it includes specific lines of `kernel/bpf/cgroup.c`.  `allnoconfig` will not even include the source file,

    cd ~/linux-5.16/
    make allnoconfig
    make kernel/bpf/cgroup.o
    
results in an error: `make[2]: *** No rule to make target 'kernel/bpf/cgroup.o'.  Stop.`  We can ensure that the relevant configuration options are modified in `allnoconfig` in order to include this file and any specified lines:

    make allnoconfig  # configuration file stored in .config
    klocalizer --repair .config --include-mutex kernel/bpf/cgroup.o:[1354,1357-1359]

This produces a new version of the `.config` file in `0-x86_64.config`.  To build with it, install it with `olddefconfig` and attempt to build the source file:

    cp 0-x86_64.config .config
    make olddefconfig
    make kernel/bpf/cgroup.o
    
This time, the source file is successfully built: `CC      kernel/bpf/cgroup.o`.  Any number of `--include-mutex` constraints may be added.  If there is mutual-exclusion among source files, `klocalizer` will as many configuration files needed to cover all constraints.  Always on or off constraints can be added with `--include` or `--exclude`.  See the documentation on [`klocalizer` and `krepair`](docs/advanced.md#klocalizer-and-krepair) for more usage information.


### Coverage report

- kmax failed, superc failed
- unconstrained
- headers not included

### `ERROR: SuperC checks failed`

Try running `java superc.SuperC -sourcelinePC /dev/null /dev/null`.  If the class is not found, double-check the SuperC installation and your CLASSPATH.

If you get a `java.lang.NoSuchMethodError: 'com.microsoft.z3.BoolExpr com.microsoft.z3.Context.mkAnd(com.microsoft.z3.BoolExpr[])'` error, then there is a mismatch between the z3 java library.  Please be sure that your `superc.jar` and `z3-4.8.12-x64-glibc-2.31/bin/com.microsoft.z3.jar` jarfiles downloaded according to the SuperC installation directions.  Or try [building SuperC](https://github.com/appleseedlab/superc) from scratch.



### Getting configuration files to build commit ranges

To repair `allnoconfig` to include changed lines from a range of commits, first get the diff file, checkout the version having the patch(es) applied, then call repair:

    cd ~/
    git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
    cd linux
    git diff commit1..commit2 > patch.diff
    git checkout commit2
    klocalizer --include{-mutex,} patchfile.diff
    
    
    `klocalizer` will also take patches ending in `.patch`, e.g., from `git format-patch` in addition to `.diff` as long as the file is in the unified diff format.  Be sure to run `klocalizer` from the already-patched source tree, since this contains the constraints of the resulting code from the patch.


<!-- - headers -->
<!-- - difference between cosntraints for a directory vs. constraints for the files in the directory -->
<!-- - doing patches -->
<!-- - doing commit ranges, git diff HEAD~, git diff commit1..commitN -->
<!-- - arch stuff, goes through one arch at a time -->


<!-- - --include-mutex -->
<!--   - generates N configs, each will have at least one of the include-mutex configs -->
<!--   - if not possible to get any config with at least one, then unsat, no configs made -->
  
<!-- - --include -->
<!--   - generates N configs, all will have all --include constraints  (all constraints are included) -->
  
<!-- - --exclude -->
<!--   - generates N configs, none will have any of the --exclude constraints (all cosntraints are excluded) -->


## `kismet`

### Analysis stages

`kismet`'s routine consists of a three step analyses pipeline, each at different precisions.

After the identification of the select constructs, each construct is seen as a potential unmet direct dependency case, thus, marked to raise unmet dependency alarm. The subsequent stages works on the alarms of the previous stage, trying to rule out alarms as unmet dependency safe, thus, increasing the precision. While any stage is at least as precise as the stages before it, the earlier stages helps to increase the performance.

#### Syntactical optimization
Given the fact that a select construct is unmet dependency safe if the selectee has no direct dependency, this stage marks such constructs as unmet safe. This is very fast, and does not involve any SAT solvers but only syntactical analysis of the constructs.

#### Optimized SAT check
For a select construct to be unmet dependency free, the kclause constraints for the architecture together with the additional unmet dependency free constraints (which we call optimized constraints) must be satisfiable. We name this whole set of constraints as precise constraints. Given the observation that the optimized constraints are much smaller than the precise constraints, SAT solvers can decide the optimized constraints much faster. In this stage, `kismet` discharges the optimized constraints to a SAT solver to rule out more constructs as unmet dependency safe.

#### Precise SAT check
In this stage, `kismet` discharges the whole set of constraints (optimized and kclause architecture constraints, i.e., precise constraints) to a SAT solver to analyse remaining alarms and rule them as safe. This is the last stage of the static analysis pipeline, where any construct could not be ruled to be unmet safe raise unmet alarms.

### Summary format
Upon completing the analysis, `kismet` writes a detailed summary in CSV format to the standard output.

This includes the following columns:  
- `selectee`: The selectee of the select construct.  
- `selector`: The selector of the select construct.  
- `visib_id`: The visibility id of the select construct. One (selectee, selector) pair might appear multiple times on different visibility constraints (e.g., within `CONFIG_SELECTOR`, there might be two entries, such as: `select SELECTEE if VISIB1`, `select SELECTEE if VISIB2`). Such constructs are distinguished with this visibility id.  
- `constraint_type`: There are possibly multiple ways to satisfy the optimized constraints. If exploring the whole unmet space is enabled (disabled by default, use `'--explore-whole-unmet-space` to enable), all expressions to satisfy the optimized constraints are explored individually, called as SAT options. On the other hand, some random solution to precise constraints is called generic option, which suffices to verify alarms. In the summary, generic option has `constraint_type` 0 while exhaustively explored SAT options have `constraint_type` ids starting from 1.  
- `analysis_result`: one of: `UNMET_ALARM`, `UNMET_SAFE_SYNTACTIC_PASS`, `UNMET_SAFE_OPTIMIZED_PASS`, `UNMET_SAFE_PRECISE_PASS`.  
- `verified`: If the analysis result is an alarm, includes whether the generated test case for the related construct verifies the alarm.  
- `forced_target_udd_only`: If the analysis result is an alarm, includes whether forcing the target unmet dependency only was successful.  
- `testcase`: The path to the generated test case, i.e., sample Kconfig config file.  

## `koverage`

`koverage` checks whether a Linux configuration file includes a set of
(source/header file, line) for compilation.  It utilizes the Linux build system
to determine code coverage.

#### Checking (file:line) pairs
```
cd ~/linux-5.16/
make.cross ARCH=x86_64 allyesconfig
koverage --config .config --arch x86_64 --check kernel/fork.c:[259,261] -o coverage_results.json
```

This will check whether lines 256 and 261 of `kernel/fork.c` are included for compilation by Linux v5.16 allyesconfig.

The coverage results, `coverage_results.json`, will have:
```
{
  "headerfile_loc": {},
  "sourcefile_loc": {
    "kernel/fork.c": [
      [259,"INCLUDED"],
      [261,"LINE_EXCLUDED_FILE_INCLUDED"]
    ]
  }
}
```

Looking at `kernel/fork.c`, lines 259 and 261 are encapsulated by two different branches of a conditional preprocessor directive (`#ifdef`).
`koverage` reports that the line from the first branch (line 259) is included for compilation while line from the other branch (line 261) is excluded, as expected since the configuration file enables the first branch.

#### Checking patch coverage

`koverage` will also take patch files in unified diff format, and check patch coverage of a `.config` file.

```
cd ~/linux-5.16/  #< assuming this is a git clone
# create the patch file for commit 7471e1afabf8 in unified diff format
git diff 7471e1afabf8~..7471e1afabf8 > patch.diff
# be sure to checkout to the patched source code
git checkout 7471e1afabf8
make.cross ARCH=x86_64 allyesconfig
koverage --config .config --arch x86_64 --check-patch patch.diff -o coverage_results.json
```

`koverage` will determine a set of coverage requirements for covering the input patch, and check whether these are satisfied.  Below is the content of output `coverage_results.json` file, showing all modified 
(file:line) pairs from the patch are included for compilation by the `.config` file.

```
{
  "headerfile_loc": {
    "include/trace/events/io_uring.h": [
      [293,"INCLUDED"],
      [297,"INCLUDED"],
      [298,"INCLUDED"],
      [299,"INCLUDED"],
      [300,"INCLUDED"],
      [306,"INCLUDED"],
      [313,"INCLUDED"],
      [315,"INCLUDED"],
      [316,"INCLUDED"],
      [317,"INCLUDED"],
      [318,"INCLUDED"]
    ]
  },
  "sourcefile_loc": {
    "fs/io_uring.c": [
      [1509,"INCLUDED"],
      [1510,"INCLUDED"]
    ]
  }
}
```

Any number of `--check` targets may be added, and mixed with `--check-patch` and `--check-covreq`.

#### How to interpret coverage results
The results may one of three values for each line for both headers and source files (compilation units), and should be interpreted as follows:

* `INCLUDED`: (file,line) is included.
* `LINE_EXCLUDED_FILE_INCLUDED`
    * If compilation unit, unit is successfully preprocessed but line is
    not included.
    * If header, header file is included by some compilation unit specified in the coverage requirements, but line is not.  However, line might be included by some unseen compilation unit.
* `FILE_EXCLUDED`
    * If compilation unit, file is not included (preprocessing failed).
      However, this might be a false alarm due to build issues (i.e.,
      a compiler error that prevents preprocessing while `.config` file has
      constraints to include (file,line)).
    * If header, file is not included in any of the compilation units
      preprocessed.  However, (file,line) might be included by some
      unseen compilation unit.


## Annotated Example

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

## Using merge_config.sh instead of olddefconfig

    ./scripts/kconfig/merge_config.sh -n partialconfigfile > mergeout


## Klocalizer

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

### Troubleshooting

- If you see a message like `ERROR:Kextract failed`, it likely means the Kconfig parser is out-of-date (or klocalizer cannot figure out what version of the Kconfig parser to use.)  Please submit an issues to have the Kconfig parser updated.

- Use the `CONFIG_` prefix on variables when referring to them in user constraints.

- Use the `.o` ending for compilation units (though `klocalizer` will change it automatically.)

- The extracted formulas may not be exact.  No resulting configuration is a sign that the formulas are overconstrained.  A resulting configuration that does not include the desired compilation unit may mean the formulas are underconstrained.

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
        
    5. Klocalizer's formulas were wrong in some cases.  Please file an issue with source version number and klocalizer command used.

- If the unit's configuration constraints depend on `CONFIG_BROKEN`, then `klocalizer`, by default, which detect it and stop searching, because the compilation unit may not be (easily) compilable.
    
        klocalizer drivers/watchdog/pnx833x_wdt.o  # stops after finding a dependency on `CONFIG_BROKEN`

    To get a configuration anyway, use `--allow-config-broken`

        klocalizer --allow-config-broken drivers/watchdog/pnx833x_wdt.o  # finds dependency on mips
        make.cross ARCH=mips olddefconfig
        make.cross ARCH=mips drivers/watchdog/pnx833x_wdt.o  # won't be included in the build, due to CONFIG_BROKEN

## Formulas Cache Directory Structure

The `.kmax` holds the formula cache to avoid having to regenerate
formulas on each run of klocalizer.  klocalizer will also look for
prebuilt formulas to download and store in this directory.  To support
caching multiple versions of the Linux source, i.e., when using a git
repo, the `.kmax` folder's subfolders are Linux versions, i.e., git
tags.  klocalizer will gather the current version of Linux (either via
`git describe --abbrev=0 --tags` or `make kernelversion`).

## Generating Formulas for BusyBox

Get the BusyBox source:

    git clone https://git.busybox.net/busybox
    cd busybox
    git checkout 1_28_0   # or whatever version you need

Prepare directories for formulas:

    mkdir .kmax/

Get the Kconfig constraint formulas:

    kextract --module-version 3.19 --extract Config.in > .kmax/kextract
    kclause --remove-orphaned-nonvisible < .kmax/kextract > .kmax/kclause

The number of dictionary entries will be fewer than the total number
of configuration options, because this map only stores configuration
options that have dependencies.  Options without dependencies will not
have a dictionary key (although they may be used in the dependencies
of other options).

Get the Kbuild file constraint formulas:

    kmaxall $(find | grep "Kbuild$" | cut -c3-) | tee .kmax/kmax

### Test out `klocalizer` on BusyBox

Unlike Linux, BusyBox will build a `.o` with `make`, even if it is not configured in, e.g., 

    make clean
    make allnoconfig
    make coreutils/fsync.o
    
This will compile `coreutils/fsync.o` even though it wouldn't have been built with `make`, e.g.,

    make clean
    make allnoconfig
    make
    
The `coreutils/fsync.o` file should not exist

    $ ls coreutils/fsync.o
    ls: cannot access 'coreutils/fsync.o': No such file or directory

Here is how to use `klocalizer` to create a config that includes `coreutils/fsync.o`

    make clean
    make allnoconfig
    mv .config allnoconfig
    klocalizer --approximate allnoconfig coreutils/fsync.o  # produces .config file that builds fsync.o
    yes "" | make oldconfig  # to accept default values for other options
    make

The `coreutils/fsync.o` file should now be there

    $ ls coreutils/fsync.o
    coreutils/fsync.o

The reason for approximating `allnoconfig` is to avoid adding
configuration options that may break the build on certain systems.
Using `yes ""` accepts any default values of options not forced by
constraints.

## Kmax

### Simple example

This will run Kmax on the example from the
[paper](https://paulgazzillo.com/papers/esecfse17.pdf) on Kmax.

    kmax tests/kbuild_tests/paper_example

This will output the list of configuration conditions for each compilation unit file in the example Kbuild file.  By default, Kmax to treat configuration options as Boolean options (as opposed to Kconfig tristate options).  Pass `-T` for experimental support for tristate.

    unit_pc tests/kbuild/fork.o 1
    unit_pc tests/kbuild/probe_32.o (CONFIG_A && CONFIG_B)
    unit_pc tests/kbuild/probe_64.o ((! CONFIG_A) && CONFIG_B)

The `unit_pc` lines have the [format](kmax_format.md) of compilation unit name followed by the Boolean expression, in C-style syntax.  The Boolean expression describes the constraints that must be satisfied for the compilation unit to be included.  Use `-z` to emit the z3 formulas in smtlib2 format.

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

### Using `kreader` to Print Kmax Results

kreader drivers/usb/storage/alauda.o kernel/trace/trace_i

kreader --kmax-formula .kmax/kclause/x86_64/kmax drivers/ | grep "\.o$" | wc -l
kreader --kmax-formula .kmax/kclause/arm/kmax drivers/ | grep "\.o$"| wc -l

## Kclause

### Example

Kclause extracts a logical model from Kconfig.  It works in two stages:

1. The `kextract` tool uses the Kconfig parser shipped with Linux to extract configuration variables dependencies to an intermediate language.

2. The `kclause` tool takes this intermediate language and generates a z3 formula.


Then, from the root of a Linux source tree, run the following:

    kextract --extract -e ARCH=x86_64 -e SRCARCH=x86 -e KERNELVERSION=kcu -e srctree=./ -e CC=cc -e LD=ld Kconfig > kextract
    kclause --remove-orphaned-nonvisible < kextract > kclause

### Other uses

#### Get a list of all visible configs

    # all the configs that have a prompt condition
    grep "^prompt " kconfig.kclause | cut -f2 -d\  | sort | uniq | tee visible.txt

    # all the configs
    grep "^config " kconfig.kclause | cut -f2 -d\  | sort | uniq | tee configs.txt
    
    # the visibles should be a subset of the configs
    diff configs.txt visible.txt  | grep ">"
