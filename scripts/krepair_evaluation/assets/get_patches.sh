# This script creates patch files for the patches between given two points.

###########################################################################
# USAGE
###########################################################################

help() {
  echo ""
  echo "USAGE: "
  echo "  `basename $0` -l linux_ksrc -o output_patches_dir -s start_id -e end_id"
  echo ""
  echo "    Create patch files inside output_patches_dir for patches in range (start_id:end_id]."
  echo "    linux_ksrc must have a Linux source git clone."
  echo "    Output patch files are in unified diff format, each named in \"ID-COMMITID.patch\" format."
  echo "    start_id and end_id can be tags (e.g., v5.12) or commit ids. end_id>start_id."
  echo ""
  echo "EXAMPLE: `basename $0` -l linux-next/ -o patches/ -s v5.12 -e v5.13"
}

###########################################################################
# PARSE ARGUMENTS
###########################################################################

while getopts l:o:s:e: opt; do
case $opt in
  l)
    linux_ksrc=$OPTARG ;;

  o)
    patches_dir=$OPTARG ;;

  s)
    start_tag=$OPTARG ;;

  e)
    end_tag=$OPTARG ;;

  \?)
    echo "(`basename $0`)" "Invalid argument: -$OPTARG"
    help
    exit -1
    ;;
  :)
    echo "(`basename $0`)" "-$OPTARG requires an argument."
    help
    exit -1
    ;;
esac
done

# Check arguments

if [[ -z "$linux_ksrc" || -z "$patches_dir" || -z "$start_tag" || -z "$end_tag" ]]; then
  echo "Missing option(s)."
  help
  exit -1
fi

if [ ! -d "$linux_ksrc" ]; then
  echo "Cannot find linux kernel source at \"${linux_ksrc}\"."
  help
  exit -1
fi

# TODO: further check values, i.e., whether there really is linux ksrc in linux_ksrc.

###########################################################################

# Fail if any commands below terminate with non-zero exit code.
# This is to avoid silent failures.
set -e 
set -o pipefail

mkdir -p ${patches_dir}

# Get the patches between the end points.
cd ${linux_ksrc}
git checkout ${end_tag}
echo "Creating the patches.."
git format-patch --numbered-files -o ${patches_dir} ${start_tag}
num_patches=$(ls ${patches_dir}/* | wc -l)
echo "${num_patches} patches were found."

# Embed commit ids in the patch file names.
echo "Renaming the patches in ID-COMMITID.patch format."
cd ${patches_dir}
for f in *
do
  # First 12 chars of the commit hash is the standard for identifying commits
  commit_id=$(head -n1 $f | awk '{print substr($2,1,12)}')
  # Rename patch file from "ID" to "ID-COMMITID.patch"
  mv "$f" "$f-${commit_id}.patch"
done
echo "Patches were renamed."

echo "Done."
