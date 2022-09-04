# Content 

This document explains why the krepair assets (patch conditions, build targets, patch tags) are needed and how to obtain them.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Assets](#assets)
  - [Patch conditions](#patch-conditions)
    - [Manual analysis](#manual-analysis)
    - [Manual analysis results for v5.13](#manual-analysis-results-for-v513)
  - [Build targets](#build-targets)
  - [Patch tags](#patch-tags)
    - [Creating patch tags](#creating-patch-tags)
- [Ready to use assets for v5.13](#ready-to-use-assets-for-v513)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Assets

There are three types of assets used in the evaluations, which are:
1) patch conditions: there is patch conditions for each patch, which determines under which conditions a patch is said to be covered.  Patch conditions for a patch conditons a list of file and lines that must be built so that the patch is covered.
2) build targets: mappings from compilation units to `make` targets that builds it (e.g., to build `virt/kvm/kvm_main.c`, target is `arch/x86/kvm/`, which means `make arch/x86/kvm/` must be run).
3) patch tags: there is a patch tags for each patch, which tags each modified file in a patch that is used to determine the category of file and type of change used for evaluations.  for example, it helps understand whether a file is modified/moved/removed, or whether is is arch specific (e.g., NON_X86_64).

First, patch conditions are created with a semi-automated process that involves manually analyzing the buildability of modified files in pathces.  Then, the data from patch conditions is used again to create build targets and patch tags.

## Patch conditions

For a patch, patch conditions are the source and header files and their
lines that we expect to be built for covering the patch. We use patch
conditions to measure the patch coverage of configuration files.

Patch conditions are obtained after several steps of processing the patches.
The input is the set of patches, and the output is the architecture specific
set of patch conditions.

The steps we take to obtain the patch conditions are as follows:
* `loc_patch_conditions.py`: Turns patch files into patch conditions. Does the following set of filterings:
   * Don't include non .c\.h files.
   * Don't include non-kernel files based on directory (e.g., `DOCUMENTATION/`)
   * Don't include files that are removed or only moved without modifications.
* Klocalizer experiments (`run_kloc_c_files.py`) and manual analysis:
   * Run klocalizer on each source file for each architecture.
   * Attempt to build the file with the output .config file.
   * If the file builds, it must be included in the experiments for that specific architecture.
   * (manual analysis) If the file does not build, manually analyze to check if it really can't be built (see manual analysis section for details).
      * If can be built, include it in the experiments for the specific architecture.
      * If cannot be built, exclude from the experiments for the specific architecture.
* After excluding files with above steps, remove any patch conditions that don't have any source files remaining (even if they have header files).

The exact steps taken were as follows:
* Run `loc_patch_conditions.py` on patches, obtain patch condition (`.cond`) files
* Run klocalizer (`run_kloc_c_files.py`) on patch conditions, obtain what architectures can build the source files.
* Export the previous step's output to google sheets (Run `change_format_kloc_exp_results.py` to change the format of the output for google sheets).
* Manually analyze the results, fill `label` and `build target` columns in the google sheet (see manual analysis sction for what they mean, see here for the manual analysis results for linux 5.13: https://docs.google.com/spreadsheets/d/1un5ZaGwc7qrFWMYWRPfq61UpalcekNdlIx8QdO7HWCc/edit?usp=sharing).
* Export the following columns from the google sheets as csv: file, arch, label, build target
* Run `amend_patch_conditions.py` to obtain architecture specific patch conditions.
* Resolve any cases that were labeled as `needs_attention`.

This results in obtaining the final set of patch conditions per architecture.

### Manual analysis

Klocalizer experiments attempts to build the units with .config files created by klocalizer.

If a .config file builds a unit, it is indeed a true positive. However, if a .config file cannot build the unit, it might be a false negative due to varying reasons (e.g., klocalizer's .config file is wrong, parent directory needs to be used as parent directory, etc.).

To obtain the ground truth patch conditions, manual analysis is performed on source files that klocalizer could not build.

Manual analysis results in categorizing the (sourcefile, arch) pairs as follows (named as `label` in google sheets):
* `builds`: The unit can be built with some config file despite klocalizer's config could not.
* `builds_dir`: The unit can be built with a different build target, e.g., parent directory. (recorded in `build target` column in google sheets)
* `compiler_error`: Build system can attempt to build the unit (`CC unit.o`) but a compiler error occurs.
* `header`: Despite the `.c` extension, the source file is used as header.
* `cant_built`: The unit cannot be built for varying reasons: unit is specific to other archs, no make rule, dependency on undefined or dead config option.
* `system_issue`: System setup does not allow building the unit, e.g., needs specific compiler or compiler features.
* `needs_attention`: The same source file falls in different categories from above for different commits. Therefore, one needs to specially handle this commit-by-commit.

While creating the final set of patch conditions, above cases are treated as follows:
* `builds`: include.
* `builds_dir`: include, also record in build targets mappings.
* `compiler_error`: include. We will need to manually check these cases in the evaluation results to check whether they pass/fail.
* `header`: include but move the source file from `sourcefile_loc` to `headerfile_loc`.
* `cant_build`: exclude.
* `system_issue`: exclude.
* `needs_attention`: above actions were taken commit-by-commit.

### Manual analysis results for v5.13

See the following sheet for manual analysis results for Linux v5.13: https://docs.google.com/spreadsheets/d/1un5ZaGwc7qrFWMYWRPfq61UpalcekNdlIx8QdO7HWCc/edit?usp=sharing

## Build targets

Usually, for any unit `source/file.c`, `source/file.o` is passed to make as 
build target. However, there are exceptions to this. For example, to build
`arch/arm/mach-omap1/pm.c`, the parent directory needs to be passed as target
to make, which is `arch/arm/mach-omap1/`. Such cases are pinpointed during
manual analysis, and a mapping from source files to their build targets is
created (see `scripts/krepair_evaluation/assets_linuxv513/build_targets.json`).

To obtain `build_targets.json`, get the mapping from `file` column to `build_target` column in manual analysis sheet for those files that are labeled as `builds_dir` in their `label` column.

If a source file cannot be found in the mapping, follow the usual case
(i.e., just replace .c with .o).  krepair scripts are already implemented
in this way.

## Patch tags

With patch tagging, we aim to categorize each file in a patch, so that we
can understand whether and how to summarize/present the evaluations
results for each file modified in the patches.

There is a patch tags file for each patch, which maps each file modified by the
patch to a patch tag.  Followings are the list of possible tags for files. The tags are assigned in the order
they appear in the following list. It means that, if a file falls in more than
one category, it is tagged with the earliest tag in the following list.

Since we only target `x86_64` in our evaluations, tags are designed around it.

1. **NON_C**: File without a `.c` or `.h` extension.
2. **REMOVED**: File that is removed by the patch.
3. **MOVED_ONLY**: File that is moved by the patch without any modifications to the content.
4. **NON_KERNEL_DIR**: File is in one of the following directories `["tools", "Documentation", "usr", "LICENSES", "scripts"]`
5. **HEADER_H**: File has `.h` extension (unknown whether `x86_64` can include, it is never analyzed for that).
6. **NON_X86_ARCH_DIR**: File is in one of `arch/` subfolders that is not `arch/x86/` or `arch/x86_64/`.
7. **HEADER_C**: File is used as a header but has `.c` extension.
8. **X86_64_C**: `.c` file compiles for `x86_64`. The build target is `file/unit.o` for source file `file/unit.c`.
9. **X86_64_C_SPECIAL_BUILD_TARGET**: `.c` file compiles for `x86_64`. The build target is special (may be the parent or some other directory).
10. **X86_64_C_COMPILER_ERROR**: `.c` file that build system can attempt to build for `x86_64` (`CC unit.o`) but a compiler error occurs due to some bug in the source code.
11. **X86_64_C_SYSTEM_ISSUE**: System setup does not allow building the unit, e.g., needs a specific compiler or compiler features.
12. **NON_X86_64_C**: `.c` file that cannot be compiled for `x86_64` for misc reasons:
    1. It can be compiled for architectures other than `x86_64`.
    2. Non-kernel file (but not inside non-kernel dirs as in `NON_KERNEL_DIR` tag). Can be hostprog, userprog, etc.
    3. Dead code since there is no make target.
    4. Dead code since the required config option is never defined.
    5. Dead code since the required config options is infeasible (depends on undefined config option, on CONFIG_BROKEN, etc.)
13. **NEEDS_FURTHER_ATTENTION** or **NEEDS_FURTHER_ATTENTION_2**: used within the scripts for files that need further attention to get the final tag. This never appears in final patch tags.

### Creating patch tags

The tags files (`ID-COMMITID.tags`) are created in two steps.
The first step tags files without using any external information other than
the patch itself. The tags `[1-6]` in the above list can be assigned with
this first step.

After the first step, a bunch of `.c` files remain with `NEEDS_FURTHER_ATTENTION`
tag. To know whether they compile for x86_64 or not, the information from patch conditions are used (remember that klocalizer experiments
were run and the results were manually analyzed).
Then, the second step takes the output of the klocalizer experiments and
the manual analysis, and tags the remaining files.

After the second step, only a few files remain with `NEEDS_FURTHER_ATTENTION_2`
tag.  The reason is that they need to be manually assigned (notes on how
to assign tags to these files are included in the manual analysis spreadsheet: https://docs.google.com/spreadsheets/d/1un5ZaGwc7qrFWMYWRPfq61UpalcekNdlIx8QdO7HWCc/edit?usp=sharing).

`get_patch_tags.sh` shows how to get `.tags` files step-by-step.

# Ready to use assets for v5.13
The paths to assets are relative to the top krepair repository directory.

* `scripts/krepair_evaluation/assets_linuxv513/patchconditions.tar.gz`: contains one directory per architecture. Each directory contains the patch condition files for that specific architecture. The patch conditions are for a subset of all patches between v5.12 and v5.13. The missing ones are for those patches that did not have any source that would build for the target architecture.
* `scripts/krepair_evaluation/assets_linuxv513/build_targets.json`: maps source files to build targets for source files in patches between v5.12 and v5.13. For example, `arch/arm/mach-omap1/pm.c` needs its parent directory to be passed to `make`, which means `arch/arm/mach-omap1/pm.c`'s build target is `arch/arm/mach-omap1/`. The usual case (replace `.c` with `.o`) can be used for missing files in this mapping.
* `scripts/krepair_evaluation/assets_linuxv513/patchtags.tar.gz`