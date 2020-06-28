#!/usr/bin/env python

# Kmax
# Copyright (C) 2012-2015 Paul Gazzillo
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Find all compilation units given a list of directories.

import sys
import os
import glob
import re
import fnmatch
import argparse
import subprocess
try:
    import cPickle as pickle
except ImportError:  #Python3
    import pickle
import time

import kmax.vcommon as CM

scriptpath = os.path.dirname(os.path.realpath(__file__))

starting_time = time.time()

def chgext(filename, f, t):
  if filename.endswith(f):
    return filename[:-2] + t

def otoc(filename):
  return chgext(filename, ".o", ".c")

def hostprog_otoc(filename):
  """host programs don't have a .o extension, but their components
  might if it's a composite"""
  if not filename.endswith(".o"):
    filename = filename + ".o"
  return chgext(filename, ".o", ".c")

def otoS(filename):
  return chgext(filename, ".o", ".S")

def ctoo(filename):
  return chgext(filename, ".c", ".o")

def print_set(s, name):
  for elem in s:
    print name,elem
  print "size",name,len(s)

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Find a set of configurations that covers all configuration variables in the
given Kbuild Makefile.
    """,
    epilog="""\
    """
    )
argparser.add_argument('makefile',
                       nargs="*",
                       type=str,
                       help="""the name of a Linux Makefile or subdir""")
argparser.add_argument('-D',
                       '--define',
                       action='append',
                       help="""\
define a make variable""")
argparser.add_argument('-x',
                       '--excludes-file',
                       help="""\
provides the excludes filename for reading and writing subdirectories that run \
without error""")
argparser.add_argument('-c',
                       '--correlate-c-files',
                       action="store_true",
                       help="""\
find corresponding .c files for the compilation units""")
argparser.add_argument('-C',
                       '--config-vars',
                       type=str,
                       help="""the name of a KConfigData file containing \
configuration variable data""")
argparser.add_argument('--no-aggregation',
                       action="store_true",
                       help="""\
only perform Kbuild evaluation, no aggregation and analysis""")
# argparser.add_argument('-g',
#                        '--get-presence-conditions',
#                        action="store_true",
#                        help="""\
# get presence conditions for each compilation units""")
argparser.add_argument('-B',
                       '--boolean-configs',
                       action="store_true",
                       help="""\
Treat all configuration variables as Boolean variables""")
# argparser.add_argument('-n',
#                        '--naive-append',
#                        action="store_true",
#                        help="""\
# use naive append behavior, which has more exponential explosion""")


args = argparser.parse_args()

if len(args.makefile) == 0:
  argparser.print_help()
  sys.exit(1)

toplevel_dirs = args.makefile

excludes = set()
if args.excludes_file != None:
  if os.path.exists(args.excludes_file):
    with open(args.excludes_file, "r") as f:
      excludes = pickle.load(f)

def covering_set(kbuild_dir,        # src directory to process
                 compilation_units, # updated with units
                 library_units,     # updated with lib units
                 hostprog_units,    # updated with hostprog units
                 unconfigurable_units,    # updated with
                                          # unconfigurable units
                 extra_targets,     # updated with extra targets
                 clean_files,       # updated with clean-files units
                 c_file_targets,    # updated with c-files from targets var
                 composites,        # updated with composites
                 broken,            # updated with kbuild files that
                                    # break kmax
                 presence_conditions):
  """Call the covering set program to find the list of compilation
  units and subdirectories added by the makefile in kbuild_dir"""
  global excludes

  if kbuild_dir in excludes:
    print "skipping", kbuild_dir
    return set()

  covering_set_args = [ "python", os.path.join(scriptpath, "kmax"),
                        "--case-study", "linux",
                        "--log_level", "0",
                        # "-p",  #tvn why use this flag ? 
                        # "-Dsrc=" + kbuild_dir,      # drivers/staging/wlags49_h25/, drivers/gpu/drm/nouveau/
                        # # TODO default to empty variable
                        # # "-Dobj=" + kbuild_dir,    # drivers/scsi/aic7xxx/
                        # # "-DKERNELDIR=",           # drivers/staging/wlags49_h25/
                        # # "-Dlibservices=",         # drivers/staging/tidspbridge/
                        # # "-DPWD=",                 # drivers/staging/rts5139/
                        # # "-DGCOV=",                # drivers/scsi/lpfc/
                        # # "-DDBGDEF=",              # drivers/net/wan/lmc/
                        # # "-DACPI_FUTURE_USAGE=",   # drivers/acpi/acpica/
                        ]

  # if args.define != None:
  #   for define in args.define:
  #     covering_set_args.append("-D" + define)

  # if args.config_vars:
  #   covering_set_args.append("-C" + args.config_vars)

  # if args.get_presence_conditions:
  #   covering_set_args.append("-g")

  if args.boolean_configs:
    covering_set_args.append("-B")

  # if args.naive_append:
  #   covering_set_args.append("-n")
  covering_set_args.append(kbuild_dir)


  sys.stderr.write("running covering_set: {}\n".format(' '.join(covering_set_args)))
  #CM.pause()
  print covering_set_args
  p = subprocess.Popen(covering_set_args,
                       stdout=subprocess.PIPE,
                       # stderr=subprocess.PIPE
                       )
  out, err = p.communicate()

  if p.returncode != 0:
    broken.add(kbuild_dir)
    return set()

  excludes.add(kbuild_dir)

  (new_compilation_units,
   new_library_units,
   new_hostprog_units,
   new_unconfigurable_units,
   new_extra_targets,
   new_clean_files,
   new_c_file_targets,
   new_pending_subdirectories,
   new_composites,
   new_presence_conditions) = pickle.loads(out)

  compilation_units.update(new_compilation_units)
  library_units.update(new_library_units)
  hostprog_units.update(new_hostprog_units)
  unconfigurable_units.update(new_unconfigurable_units)
  extra_targets.update(new_extra_targets)
  clean_files.update(new_clean_files)
  c_file_targets.update(new_c_file_targets)
  composites.update(new_composites)
  presence_conditions.update(new_presence_conditions)

  # if args.get_presence_conditions:
  #   # print presence condition information
  #   for unit_name, pc in new_unit_pcs:
  #     print "unit_pc", unit_name, pc
  #   for subdir_name, pc in new_subdir_pcs:
  #     print "subdir_pc", subdir_name, pc

  return new_pending_subdirectories

compilation_units = set()
subdirectories = set()
library_units = set()
hostprog_units = set()
unconfigurable_units = set()
extra_targets = set()
clean_files = set()
c_file_targets = set()
composites = set()
pending_subdirectories = set()
broken = set()
presence_conditions = set()

# find all compilation_units.  run covering_set.py until no more
# Kbuild subdirectories are left.
sys.stderr.write("running covering_set\n")
pending_subdirectories.update(args.makefile)
while len(pending_subdirectories) > 0:
  subdirectories.update(pending_subdirectories)
  pending_subdirectories.update(covering_set(pending_subdirectories.pop(),
                                             compilation_units,
                                             library_units,
                                             hostprog_units,
                                             unconfigurable_units,
                                             extra_targets,
                                             clean_files,
                                             c_file_targets,
                                             composites,
                                             broken,
                                             presence_conditions))

# if args.get_presence_conditions:
#   # already printed presence conditions.  don't do anything, so exit
#   exit(1)

if args.no_aggregation:
  print_set(toplevel_dirs, "toplevel_dirs")  # list of directories started from
  print_set(subdirectories, "subdirectory")  # subdirectory visited by kbuild
  print_set(composites, "composites")  # compilation units that are composites
  print_set(library_units, "library_units")  # library units referenced by kbuild
  print_set(hostprog_units, "hostprog_units")
  print_set(unconfigurable_units, "unconfigurable_units")
  print_set(extra_targets, "extra_targets")
  print_set(clean_files, "clean_files")
  print_set(c_file_targets, "c_file_targets")
  print_set(broken, "broken")
  print_set(presence_conditions, "presence_conditions")
  print "running_time", time.time() - starting_time
  exit(0)

sys.stderr.write("aggregating and analyzing covering_set data")

# find all subdirectories with source in them
used_subdirectory = set()
for unit in compilation_units:
  used_subdirectory.add(os.path.dirname(unit))

# find all .c files
all_c_files = set([])
for subdir in (subdirectories | used_subdirectory):
  # all_c_files.update([os.path.normpath(x) for x in glob.glob(os.path.join(subdir, "*.c"))])
  all_c_files.update([os.path.abspath(os.path.normpath(x)) for x in glob.glob(os.path.join(subdir, "*.c"))])

# find all compilation units without a corresponding .c file
unmatched_units = set()
asm_compilation_units = set()
for unit in compilation_units:
  c_file = otoc(unit)
  S_file = otoS(unit)
  if not os.path.isfile(c_file) and not os.path.isfile(S_file):
    unmatched_units.add(c_file)
  if os.path.isfile(S_file):
    asm_compilation_units.add(S_file)

# find all asm-offsets.c files, for these are compiled by the root
# Kbuild file into offsets
re_offsets_file = re.compile(r'arch/[^/]+/kernel/asm-offsets\.c')

offsets_files = [ x for x in all_c_files if re_offsets_file.match(x) ]

# find all .c files without a corresponding compilation unit, starting
# with all c files
unidentified_c_files = set(all_c_files)

# remove kernel compilation units
unidentified_c_files.difference_update([otoc(filename)
                                     for filename in compilation_units])

# remove library compilation units
unidentified_c_files.difference_update([otoc(filename)
                                     for filename in library_units])

# remove hostprog compilation units
unidentified_c_files.difference_update([hostprog_otoc(filename)
                                     for filename in hostprog_units])

# remove unconfigurable compilation units
unidentified_c_files.difference_update([hostprog_otoc(filename)
                                     for filename in unconfigurable_units])

# remove unconfigurable compilation units
unidentified_c_files.difference_update([hostprog_otoc(filename)
                                     for filename in extra_targets])

# remove unconfigurable compilation units
unidentified_c_files.difference_update([filename
                                     for filename in clean_files])

# remove asm-offsets.c files
unidentified_c_files.difference_update([filename
                                        for filename in offsets_files])

# get source files that include c files
included_c_files = set()
p = subprocess.Popen(r'find . -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"',
                     shell=True,
                     stdout=subprocess.PIPE)
out, _ = p.communicate()
for line in out.split("\n"):
  parts = line.split(":", 1)
  if parts is not None:
    infile = parts[0]
    if len(parts) > 1:
      m = re.search(r"\".*\.c\"", parts[1])
      if m is not None:
        included = m.group(0)[1:-1]
        included = os.path.join(os.path.dirname(infile), included)
        included = os.path.relpath(os.path.realpath(included))
        included = os.path.abspath(included)  # added to do abs paths
        included_c_files.add(included)

# only need the files in the current source subtree
included_c_files.intersection_update(all_c_files)

# remove .c files that aren't compilation units, because they are
# included in other c files
unidentified_c_files.difference_update(included_c_files)

# separate out .c files from the staging directory, which can be a
# mess
unidentified_staging_c_files = [ x for x in unidentified_c_files
                              if "drivers/staging" in os.path.dirname(x) ]

unidentified_c_files.difference_update(unidentified_staging_c_files)

# separate out .c files with "skeleton" in their name.  this is a
# heuristic to find example drivers that aren't actually compiled.
unidentified_skeleton_c_files = [ x for x in unidentified_c_files
                               if "skeleton" in os.path.basename(x) ]

unidentified_c_files.difference_update(unidentified_skeleton_c_files)

# separate out generators heuristically.  look for "mk" or
# "gen[^a-zA-Z]" in their name

# perhaps we can find generators a better way, e.g., by looking for
# the c file in the makefile

# look for unexpanded variables or function calls
re_unexpanded = re.compile(r'.*\$\(.*\).*')
unexpanded_compilation_units = [ x for x in compilation_units
                                 if re_unexpanded.match(x) ]
unexpanded_library_units = [ x for x in library_units
                             if re_unexpanded.match(x) ]
unexpanded_hostprog_units = [ x for x in hostprog_units
                              if re_unexpanded.match(x) ]
unexpanded_unconfigurable_units = [ x for x in unconfigurable_units
                                    if re_unexpanded.match(x) ]
unexpanded_extra_targets = [ x for x in extra_targets
                                 if re_unexpanded.match(x) ]
unexpanded_clean_files = [ x for x in clean_files
                             if re_unexpanded.match(x) ]
unexpanded_subdirectories = [ x for x in subdirectories
                              if re_unexpanded.match(x) ]

# remove compilation units with unexpanded variable names
unmatched_units.difference_update([ otoc(x)
                                    for x in unexpanded_compilation_units ])

# remove library units with unexpanded variable names
unmatched_units.difference_update([ otoc(x)
                                    for x in unexpanded_library_units ])

# remove hostprog units with unexpanded variable names
unmatched_units.difference_update([ hostprog_otoc(x)
                                    for x in unexpanded_hostprog_units ])

# remove unconfigurable units with unexpanded variable names
unmatched_units.difference_update([ hostprog_otoc(x)
                                    for x in unexpanded_unconfigurable_units ])

# remove extra targets with unexpanded variable names
unmatched_units.difference_update([ hostprog_otoc(x)
                                    for x in unexpanded_extra_targets ])

# remove clean targets with unexpanded variable names
unmatched_units.difference_update([ hostprog_otoc(x)
                                    for x in unexpanded_clean_files ])

# remove c files specified in the clean-files and in targets, since
# these can be auto-generated c files
generated_c_files = set([])
for c in (clean_files | c_file_targets):
  pattern = re.compile(fnmatch.translate(c))
  for filename in unmatched_units:
    if pattern.match(filename):
      generated_c_files.add(filename)
unmatched_units.difference_update(generated_c_files)

# cache the list of working kbuild files
if args.excludes_file != None:
  with open(args.excludes_file, "w") as f:
    pickle.dump(excludes, f, 0)

print_set(toplevel_dirs, "toplevel_dirs")  # list of directories started from
print_set(all_c_files, "all_c_files")  # all .c files in used and visited subdirectories
print_set(asm_compilation_units, "asm_compilation_units")  # compilation units with a .S file
print_set(subdirectories, "subdirectory")  # subdirectory visited by kbuild
print_set(used_subdirectory, "used_subdirectory")  # subdirectories containing compilation units
print_set(compilation_units, "compilation_units")  # compilation units referenced by kbuild
print_set(["{} {}".format(x, y.replace('\n', '').replace(' ', '')) for x, y in presence_conditions], "presence_conditions") # presence conditions for the compilation units and subdirectories
print_set(composites, "composites")  # compilation units that are composites
print_set(library_units, "library_units")  # library units referenced by kbuild
print_set(hostprog_units, "hostprog_units")
print_set(unconfigurable_units, "unconfigurable_units")
print_set(extra_targets, "extra_targets")
print_set(clean_files, "clean_files")
print_set(c_file_targets, "c_file_targets")
print_set(generated_c_files, "generated_c_files")
print_set(unmatched_units, "unmatched_units")
print_set(included_c_files, "included_c_files")
print_set(offsets_files, "offsets_files")
print_set(unidentified_c_files, "unidentified_c_files")
print_set(unidentified_staging_c_files, "unidentified_staging_c_files")
print_set(unidentified_skeleton_c_files, "unidentified_skeleton_c_files")
print_set(unexpanded_compilation_units, "unexpanded_compilation_units")
print_set(unexpanded_library_units, "unexpanded_library_units")
print_set(unexpanded_hostprog_units, "unexpanded_hostprog_units")
print_set(unexpanded_unconfigurable_units, "unexpanded_unconfigurable_units")
print_set(unexpanded_extra_targets, "unexpanded_extra_targets")
print_set(unexpanded_subdirectories, "unexpanded_subdirectories")
print_set(broken, "broken")
print "running_time", time.time() - starting_time
