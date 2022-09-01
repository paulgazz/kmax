# Take kloc experiment as input and turn them into a format that is
# easier to work with when manually verifying the results.

# If kloc can build a file, it is indeed buildable. However, if it fails,
# it might be a false negative due to kmax/kclause.

# Output is per architecture, and in the following format:
# filename [commit_id_it_doesnt_build+ ]

# The directory that contains ID-COMMITID.kloc files
# TODO: set this to the directory of .kloc files outputted by run_kloc_c_files.py
kloc_files_dir="/home/necip/kloc_results/"

import glob, os, json
assert os.path.isdir(kloc_files_dir)
kloc_files = sorted(glob.glob("%s/*.kloc" % kloc_files_dir))
assert kloc_files
# file: architecture: cannot_build_commits
ret = {}

def definitely_cannot_compile(unit_path, arch_name):
  if unit_path.startswith("arch/"):
    spec_arch = unit_path.split('/')[1]
    l = min(len(arch_name), len(spec_arch))
    return spec_arch[:l] != arch_name[:l] # accounts for arch/x86 for x86_64
  else:
    return False

for kloc_file in kloc_files:
  bname = os.path.basename(kloc_file)
  id = bname.split('-')[0]
  commit_id = bname.split('-')[1].split('.')[0]
  with open(kloc_file, 'r') as f:
    single_f_content = json.load(f)
  for file in single_f_content:
    for arch in ['x86_64', 'arm']:
      if arch not in single_f_content[file]:
        # Dont include the apparent ones: e.g., arch/x86/file.c doesnt compile for arm
        # So that, we dont check them during manual analysis.
        if definitely_cannot_compile(file, arch):
          continue
        ret[file] = ret.get(file, {})
        ret[file][arch] = ret[file].get(arch, [])
        ret[file][arch].append(commit_id)


r = []

for file in ret:
  for arch in ret[file]:
    r.append([file, arch] + ret[file][arch])

r.sort()
p = [' '.join(x) for x in r]
for x in p:
  print(x)
