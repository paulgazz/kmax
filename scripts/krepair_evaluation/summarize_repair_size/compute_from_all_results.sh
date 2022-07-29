# Runs on validation results directory, where there is one directory
# per patch.  Looks for configuration files as follows:
#
# test_validate/
#   10000-cf27f3b14961/
#     line_inclusion_results_allnoconfig_before/
#       configtorepairconfig_after_olddefconfig
#     line_inclusion_results_allnoconfig_after/
#       0-x86_64.configconfig_after_olddefconfig
#       1-x86_64.configconfig_after_olddefconfig
#       ...
# Also looks for line_inclusion_results_allyesconfig_before/configtorepairconfig_after_olddefconfig
# to compare the original configuration to original allyesconfig.


# OUTPUT: Creates two files per patch:
#  1. ID-COMMITID-CONFIGNAME-repair_size.json: before/after repair for CONFIGNAME.
#  2. ID-COMMITID-CONFIGNAME-compared_to_allyesconfig.json: comparing original
#     CONFIGNAME to original allyesconfig. Won't be created if CONFIGNAME
#     is allyesconfig.

# Commands:

# bash compute_from_all_results.sh /data2/test_experiment/aggregated/validate/ allnoconfig /data2/repair_size/measurements/ |& tee /data2/repair_size/allno_repair_size.log
# bash compute_from_all_results.sh /data2/test_experiment/aggregated/validate/ allyesconfig /data2/repair_size/measurements/ |& tee /data2/repair_size/allyes_repair_size.log
# bash compute_from_all_results.sh /data2/test_experiment/aggregated/validate/ randconfig /data2/repair_size/measurements/ |& tee /data2/repair_size/rand_repair_size.log
# bash compute_from_all_results.sh /data2/test_experiment/aggregated/validate/ defconfig /data2/repair_size/measurements/ |& tee /data2/repair_size/def_repair_size.log


set -x

# Assumption: this script is at plocalizer/evaluation/
script_dir=$(dirname -- "${BASH_SOURCE[0]}")
script_dir=$(realpath $script_dir)

if [ "$#" -ne 3 ]; then
  echo "Illegal number of parameters!"
  echo "Provide two arguments:"
  echo "  1) path to the directory where there is one directory per patch."
  echo "     This is outputted by validation scripts (aggregated/validate/)."
  echo "     Expected directory hiearchy for a patch directory is as follows:"
  echo " "
  echo "       ID-COMMITID/"
  echo "         line_inclusion_results_CONFIGNAME_before/"
  echo "           configtorepairconfig_after_olddefconfig"
  echo "         line_inclusion_results_CONFIGNAME_after/"
  echo "           0-x86_64.configconfig_after_olddefconfig"
  echo "           1-x86_64.configconfig_after_olddefconfig"
  echo "           ..."
  echo ""
  echo "  2) name of the configuration file repaired."
  echo "     used for determining which builtin and repaired configurations"
  echo "     to measure the changes for.  See CONFIGNAME in docs of first arg."
  echo ""
  echo "  3) output directory. Creates if doesn't exist. Overwrites previous result files."
  exit -1
fi

all_patches_dir=$1
builtin_config_name=$2
outdir=$3

if [ ! -d "$all_patches_dir" ]; then
  echo "Cannot find the patches directory at \"$all_patches_dir\""
  exit -1
fi

mkdir -p ${outdir}

find ${all_patches_dir} -mindepth 1 -maxdepth 1 -type d | while IFS= read -r patch_dir; do
  echo ""
  echo "Working on the patch directory: \"$patch_dir\""

  # Get the commit id from the directory name.
  patch_id=$(basename $patch_dir) # ID-COMMITID
  echo "Patch id: \"$patch_id\""

  # Find the original configuration file
  original_cfg_file=${patch_dir}/line_inclusion_results_${builtin_config_name}_before/configtorepairconfig_after_olddefconfig
  echo "Original configuration file: \"$original_cfg_file\""
  if [ ! -f "$original_cfg_file" ]; then
    echo "ERROR: cannot find the original configuration file at \"$original_cfg_file\""
    # exit -1
  else
    #
    # MEASURE BEFORE/AFTER REPAIR
    #
    # Count the repaired configuration files
    repaired_configs_dir=${patch_dir}/line_inclusion_results_${builtin_config_name}_after/
    suffix=".x86_64.configconfig_after_olddefconfig"
    numrepaired=$(find ${repaired_configs_dir} | grep "${suffix}$" | wc -l)
    echo "numrepaired ${numrepaired}"

    # Measure changes
    output_result_file=${outdir}/${patch_id}-${builtin_config_name}-repair_size.json
    if [[ $numrepaired > 0 ]]; then
      (find ${repaired_configs_dir} | grep "${suffix}$" | xargs python3 ${script_dir}/measure_change.py --original-config ${original_cfg_file}) > ${output_result_file}

      if [ ! -f "$output_result_file" ]; then
        echo "ERROR: could not create the result file at \"$output_result_file\""
        exit -1
      fi

      echo "Created the result for \"$patch_id\" at \"$output_result_file\""
    else
      echo "ERROR: no repaired files found"
      # exit -1
    fi

    #
    # MEASURE BETWEEN BEFORE AND ORIGINAL ALLYESCONFIG
    #
    allyes_cfg_file=${patch_dir}/line_inclusion_results_allyesconfig_before/configtorepairconfig_after_olddefconfig
    if [ ! -f "$allyes_cfg_file" ]; then
      echo "ERROR: cannot find the original allyesconfig file at \"$allyes_cfg_file\""
    else
      # Measure changes
      output_result_file=${outdir}/${patch_id}-${builtin_config_name}-compared_to_allyesconfig.json
      python3 ${script_dir}/measure_change.py --original-config ${original_cfg_file} ${allyes_cfg_file} > ${output_result_file}
      echo "Created the result for \"$patch_id\" at \"$output_result_file\""
    fi

    echo "Done for \"$patch_id\""
  fi
done

echo ""
echo "All done."
