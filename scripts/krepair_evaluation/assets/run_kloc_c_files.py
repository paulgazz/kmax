'''
This script takes the patch conditions for a set of patches, and runs klocalizer on all of the .c files in the patch conditions.
patch_conds has a directory per patch named as ID-COMMITID. In this directory, there is a patch conditions file named ID-COMMITID.cond
All configs produced by klocalizer are used to build the associated .c files.
Results are stored in the output_dir argument, as <patchname>.kloc (json format).
Each .c file maps to a list of architectures that klocalizer succeeded for.

Example Usage:
python3 run_kloc_c_files.py --linux_dir ./linux --formulas_dir ./formulas --formulas_map ./formulas/formulas_mapping.json --patch_conditions ./patch_conditions --cross_compiler ~/lkp_tests/sbin/make.cross --output_dir c_file_kloc
'''


#!/usr/bin/env python
import argparse
from kmax.vcommon import run
from eval_common import get_eval_lines
from os import listdir
from os import path
from os import mkdir
import sys
import json

from kmax.klocalizer import Klocalizer, Arch
import z3
import os

class BasicLogger:
  def __init__(self, quiet=False, verbose=False):
    assert (not (quiet and verbose))
    self.quiet = quiet
    self.verbose = verbose
  
  def info(self, msg):
    if not self.quiet: sys.stderr.write("INFO: %s\n" % msg)
    
  def warning(self, msg):
    sys.stderr.write("WARNING: %s\n" % msg)
    
  def error(self, msg):
    sys.stderr.write("ERROR: %s\n" % msg)
    
  def debug(self, msg):
    if self.verbose: sys.stderr.write("DEBUG: %s\n" % msg)

logger=BasicLogger()

# returns True if klocalizer succeeded without error. False o/w
def klocalizer_runner(linux_dir: str, cross_compiler: str, patch_commit: str, formulas: str, unit_path: str, arch_name: str, timeout: int) -> bool:
    """
    timeout: timeout for make in seconds.
    """
    logger.info("Running klocalizer for patch: \"%s\" unit: \"%s\" arch: \"%s\"" % (patch_commit, unit_path, arch_name))
    logger.info("Formulas are at: \"%s\"" % formulas)
    assert unit_path.endswith(".o")

    # Clean
    clean_cmd = [cross_compiler, "ARCH=%s" % arch_name, "clean"]
    run(clean_cmd, cwd=linux_dir)

    # Checkout
    checkout_cmd = ["git", "checkout", "-f", patch_commit]
    run(checkout_cmd, cwd=linux_dir)

    # Run klocalizer
    kloc = Klocalizer()
    kloc.set_linux_krsc(linux_dir)
    kloc.add_constraints([z3.Not(z3.Bool("CONFIG_BROKEN"))])
    kloc.include_compilation_unit(unit_path)
    arch = Arch(arch_name, arch_dir=formulas)
    full_constraints = kloc.compile_constraints(arch)
    model_sampler = Klocalizer.Z3ModelSampler(full_constraints)
    is_sat, z3_model = model_sampler.sample_model()
    if not is_sat:
        logger.info("The constraints are not satisfiable.")
        return False
    else:
        logger.info("The constraints are satisfiable.")
    
    # Create the .config file
    logger.info("Creating a .config file.")
    config_content = Klocalizer.get_config_from_model(z3_model, arch, set_tristate_m=False, allow_non_visibles=False)
    assert config_content
    config_filepath = os.path.join(linux_dir, ".config")
    with open(config_filepath, "w") as f:
        f.write(config_content)
    assert os.path.isfile(config_filepath)

    # Compile the unit
    logger.info("Attempting to build the unit with klocalizer's .config.")
    olddefconf_cmd = [cross_compiler, "ARCH=%s" % arch.name, "olddefconfig"]
    compile_cmd = [cross_compiler, "ARCH=%s" % arch.name, "clean", unit_path]
    run(olddefconf_cmd, cwd=linux_dir, timeout=timeout)
    run(compile_cmd, cwd=linux_dir, timeout=timeout)

    # Check if the unit is successfully built
    unit_path = os.path.join(linux_dir, unit_path)
    if os.path.isfile(unit_path):
        logger.info("Unit was successfully compiled.")
        return True
    else:
        logger.info("Unit could not be compiled.")
        return False

def main():
    argparser = argparse.ArgumentParser()
    argparser.add_argument("--linux_dir",
                           type=str,
                           required=True,
                           help="Path to a linux source directory.")
    argparser.add_argument("--formulas_dir",
                           type=str,
                           required=True,
                           help="Path to a directory containing kclause and kextract files for each each necessary commit and architecture.")
    argparser.add_argument("--formulas_map",
                           type=str,
                           required=True,
                           help="Path to a json file mapping the necessary kclause files.")
    argparser.add_argument("--patch_conditions",
                           type=str,
                           required=True,
                           help="A directory containing patch conditions for each of the patches (ID-COMMITID/ID-COMMITID.cond). This is the output of evaluation/create_patch_conditions.sh")
    argparser.add_argument("--cross_compiler",
                           type=str,
                           required=True,
                           help="Path to the cross compiler.")                           
    argparser.add_argument("--output_dir",
                           type=str,
                           required=True,
                           help="Path to a directory where this script should write its output.")

    # all path arguments are turned into absolute paths.
    args = argparser.parse_args()
    linux_dir = path.abspath(path.expanduser(args.linux_dir))
    formulas = path.abspath(path.expanduser(args.formulas_dir))
    formulas_map = path.abspath(path.expanduser(args.formulas_map))
    patch_conds = path.abspath(path.expanduser(args.patch_conditions))
    output_dir = path.abspath(path.expanduser(args.output_dir))
    cross_compiler = path.abspath(path.expanduser(args.cross_compiler))

    # TODO: check args (e.g., do "which" on cross_compiler)

    # creates a list where each element is the patch conditions for a single patch (as a dictionary)
    # Assumption: patch_conds has a directory per patch named as ID-COMMITID
    # Inside this directory, there is a patch conditions file named ID-COMMITID.cond
    patches_and_conds = {}
    for patch_dir in [directory for directory in listdir(patch_conds) if '-' in directory]:
        patch_name = patch_dir.split('/')[-1]
        if patch_name.endswith(".patch"):
            logger.error("FATAL ERROR: the passed-in patch conditions directory named directories with '.patch'. Exiting..")
            exit()
        patch_lines = get_eval_lines(patch_conds + "/" + patch_dir + "/" + patch_name + ".cond")
        patches_and_conds[patch_name] = patch_lines

    # Read the formulas mapping
    with open(formulas_map, 'r') as f:
        formulas_mapping = json.load(f)

    if not path.isdir(output_dir):
        mkdir(output_dir)

    for patch_name, conditions in patches_and_conds.items():
        patch_commit = patch_name.split('-')[1]

        # create a list of all .c files in the patch conditions
        c_files = []
        for affected_file in conditions:
            if affected_file.endswith(".c"):
                c_files.append(affected_file)

        # *** patches that don't affect any .c files ***
        # map to an empty list.
        if len(c_files) == 0:
            logger.info("Patch " + patch_name + " doesn't affect any .c files.")
            continue
        
        # *** patches that affect at least one .c file ***
        # iterate through each .c file affected by the patch, running klocalizer and attempting to build the compilation unit each time.
        single_patch_results = {}
        for c_file in c_files:
            assert c_file.endswith('.c')
            unit_path = c_file[:-1] + 'o'
            buildable_archs = []
            for arch_name in ['x86_64', 'arm']:
                # Get the formulas directory
                formulas_id = formulas_mapping[patch_commit]["after"][arch_name]
                formulas_dir = os.path.join(formulas, formulas_id, arch_name)
                assert os.path.isdir(formulas_dir)

                # Run klocalizer to create a .config, and attempt to build the unit
                try:
                    built = klocalizer_runner(linux_dir, cross_compiler, patch_commit, formulas_dir, unit_path, arch_name, 60)
                except Exception as e:
                    logger.info("Klocalizer threw an exception: %s" % str(e))
                    built = False

                if built:
                    buildable_archs.append(arch_name)

            single_patch_results[c_file] = buildable_archs

        single_output_file = os.path.join(output_dir, "%s.kloc" % patch_name)
        logger.info("Finished for the patch \"%s\". Writing the results to \"%s\"." % (patch_name, single_output_file))
        with open(single_output_file, "w") as out:
            json.dump(single_patch_results, out, sort_keys=True, indent=2)
    logger.info("All patches done.")

if __name__ == '__main__':
    main()
