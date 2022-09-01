# For each patch between v5.12 and v5.13, this script produces the "patch tags"
# files, which, for a patch, maps each modified file into a tag.

# ASSUME: this script is in krepair/scripts/krepair_evaluation/assets
krepair_assets_dir=$(dirname $(realpath $0))

krepair_assets_v513_dir=$(dirname $(realpath $0))/../assets_linuxv513/
krepair_assets_v513_dir=$(realpath $krepair_assets_v513_dir)

# Create and go into a workspace
ws=~/krepair_patch_tags_ws/
rm -rf ${ws}
mkdir -p ${ws}
cd ${ws}

# Clone linux-next.
echo "Cloning linux-next."
linux_src="${ws}/linux-next/"
git clone https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git ${linux_ksrc}

# Create the patch files.
echo "Creating the patch files."
patches_dir="${ws}/patches/"
bash ${krepair_assets_dir}/get_patches.sh -l $linux_src -o $patches_dir -s v5.12 -e v5.13

# Create tag patch files.
patch_tags_step1_dir="${ws}/patch_tags_step1/"
mkdir -p $patch_tags_step1_dir

patch_tags_step2_dir="${ws}/patch_tags_step2/"
mkdir -p $patch_tags_step2_dir

# The tag files are created in two steps. The first step tags files without
# using any external information, but only the information available within
# the patch itself. The second step fills the missing information by using
# the additional information from klocalizer experiments, and hand checking
# the files on whether they build for x86_64.

echo ""
echo "Running the first step of computing patch tags."
for patch_file in ${patches_dir}/*.patch; do
  echo "Working on: \"${patch_file}\""
  bname=$(basename ${patch_file} .patch)
  output_patch_tags_file=${patch_tags_step1_dir}/${bname}.tags
  echo "Output patch tags file: \"${output_patch_tags_file}\""
  python3 ${krepair_assets_dir}/tag_patch_files_step_1.py --patch ${patch_file} --output ${output_patch_tags_file}
  ls ${output_patch_tags_file}
done
echo "Done with the first step."
echo ""

# Extract the klocalizer experiment results from assets
kloc_exp_results_tar=${krepair_assets_v513_dir}/kloc_exp_results.tar.gz
kloc_exp_results_dir=${ws}/kloc_exp_results/
mkdir -p ${kloc_exp_results_dir}
echo "Extracting the klocalizer experiment results from \"${kloc_exp_results_tar}\" to \"${kloc_exp_results_dir}\""
tar -xf ${kloc_exp_results_tar} -C ${ws}

# The path to hand checking results over the klocalizer experiments.
# These come from https://docs.google.com/spreadsheets/d/1un5ZaGwc7qrFWMYWRPfq61UpalcekNdlIx8QdO7HWCc/edit?usp=sharing
hand_check_results=${krepair_assets_v513_dir}/manual_analysis_results.csv
echo "Using the manual analysis results from \"${hand_check_results}\""
ls ${hand_check_results}

echo "Running the second step of computing patch tags."
for patch_tag_file in ${patch_tags_step1_dir}/*.tags; do
  echo "Working on: \"${patch_tag_file}\""
  bname=$(basename ${patch_tag_file} .tags)
  output_patch_tags_file=${patch_tags_step2_dir}/${bname}.tags
  echo "Output patch tags file: \"${output_patch_tags_file}\""
  # We only need to run the second step if there is some file that needs
  # further attention. Otherwise, if all files are tagged, we don't need
  # any further tagging based on klocalizer experiments and manual analysis.
  grep -Fq "NEEDS_FURTHER_ATTENTION" ${patch_tag_file}
  need_further_attention=$?

  if [ "${need_further_attention}" -ne 0 ]; then
    # Does not need further attention (no futher tagging by second step)
    echo "No further tagging is needed: just copying the tags file."
    cp ${patch_tag_file} ${output_patch_tags_file}
  else
    # Needs further attention, i.e., there are files tagged as "NEEDS_FURTHER_ATTENTION".
    # Therefore, do the second step to fill this info from the klocalizer
    # experiments and the manual analysis.
    echo "There are files to further tag: running the second step."
    kloc_results_file=${kloc_exp_results_dir}/${bname}.kloc
    echo "Kloc results file: \"${kloc_results_file}\""
    ls ${kloc_results_file}

    python3 ${krepair_assets_dir}/tag_patch_files_step_2.py \
        --patch-tags ${patch_tag_file}                    \
        --kloc-results ${kloc_results_file}               \
        --hand-check-results ${hand_check_results}        \
        --output ${output_patch_tags_file}
  fi
  ls ${output_patch_tags_file}
done

# There are a handful of cases which needs manually assigning tags.
# Let's handle this as we know what these cases are from the spreadsheet
# for the patches between v5.12 and v5.13
echo "Simulating manually correcting the \"NEEDS_FURTHER_ATTENTION_2\" cases with sed command."

# How to correct these cases are coming from the spreadsheet at
# https://docs.google.com/spreadsheets/d/1un5ZaGwc7qrFWMYWRPfq61UpalcekNdlIx8QdO7HWCc/edit?usp=sharing
 
sed "s/NEEDS_FURTHER_ATTENTION_2/X86_64_C_COMPILER_ERROR/" ${patch_tags_step2_dir}/12197-56e2e5de441a.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11926-89f9d5400b53.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11927-b4cd249a8cc0.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11928-e42f10533d7c.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11929-0fe632471aeb.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11930-0fc96939a97f.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11931-af80425e05b2.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11932-10b26f078151.tags -i
sed "s/NEEDS_FURTHER_ATTENTION_2/NON_X86_64_C/" ${patch_tags_step2_dir}/11933-e4cd854ec487.tags -i

echo "All done."
