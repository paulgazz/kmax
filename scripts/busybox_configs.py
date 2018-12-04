#!/usr/bin/python

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

import os
import sys
import fnmatch
import subprocess
import cPickle as pickle
import linuxinstance
import kmaxdata
import lockfile # pip install lockfile
import tempfile
import csv
import argparse
from collections import defaultdict

# Collect stats on archs, kconfig files, kbuild files, and config vars
# and pickle the data to stdout

# USAGE: collect_buildsystem.py




argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect stats on archs, kconfig files, kbuild files, and config vars
and pickle the data to stdout.
    """,
    epilog="""\
    """
    )
argparser.add_argument('busybox_path',
                       type=str,
                       help="""the Busybox distribution directory to analyze""")
argparser.add_argument('-B',
                       '--boolean-configs',
                       action="store_true",
                       help="""\
Treat all configuration variables as Boolean variables""")

args = argparser.parse_args()

if len(args.busybox_path) == 0:
  argparser.print_help()
  sys.exit(1)

busybox_path = args.busybox_path

os.chdir(busybox_path)
command = 'make gen_build_files'
print command
popen = subprocess.Popen(command, shell=True)

# find | grep Config.in | xargs grep "config " | grep ":config" | wc -l

# alldirs = set()
# command = 'make -f ' + kmaxdata.makefile_override + ' alldirs'
# popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
# stdout_, stderr_ = popen.communicate()
# alldirs.update(set(stdout_.strip().split()))

# command = 'covering_set.py -D srctree=. -D ARCH=' + arch + ' -b arch/' + arch + '/Makefile'
# popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
# stdout_, stderr_ = popen.communicate()
# alldirs.update(set(stdout_.strip().split()))

kconfigdatafile = "./kconfig"
datafile = "./buildsystem"
everycfiledatafile = "./everycfile"

config_name = "Config.in"
config_path = config_name

# These are taken from the top-level Makefile's core-y and libs-y
# variables.  This is correct at least for Kmax ESEC/FSE '17 paper
# version 1.25.0 and branch 1_22_stable (for iGen journal).
# added klibc-utils for version 1.28.1
alldirs = set([
  "applets/",
  "archival/",
  "archival/libarchive/",
  "console-tools/",
  "coreutils/",
  "coreutils/libcoreutils/",
  "debianutils/",
  "klibc-utils/",
  "e2fsprogs/",
  "editors/",
  "findutils/",
  "init/",
  "libbb/",
  "libpwdgrp/",
  "loginutils/",
  "mailutils/",
  "miscutils/",
  "modutils/",
  "networking/",
  "networking/libiproute/",
  "networking/udhcp/",
  "printutils/",
  "procps/",
  "runit/",
  "selinux/",
  "shell/",
  "sysklogd/",
  "util-linux/",
  "util-linux/volume_id/"
]) 

buildsystemdata = kmaxdata.BuildSystemData("", "")
buildsystemdata = kmaxdata.BuildSystemData("", "")

buildsystemdata.alldirs = list(alldirs)

buildsystemdata.kconfig_files = []
for dir in buildsystemdata.alldirs:
  if os.path.exists(dir):
    for path, subdirs, filenames in os.walk(dir):
      buildsystemdata.kconfig_files += \
        [ os.path.join(path, fn)
          for fn in filenames
          if fn.startswith(config_name) ]
kconfigdata = kmaxdata.KConfigData()

check_dep_command = "check_dep"

command = check_dep_command + ' --kconfigs ' + config_path
print command
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
kconfigdata.config_vars = stdout_.strip().split()

command = check_dep_command + ' --bools ' + config_path
print command
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
kconfigdata.bool_vars = stdout_.strip().split()

command = check_dep_command + ' --tristate ' + config_path
print command
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
kconfigdata.bool_vars += stdout_.strip().split()

command = check_dep_command + ' --nonbools ' + config_path
print command
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
kconfigdata.nonbool_vars = stdout_.strip().split()

with lockfile.LockFile(kconfigdatafile):
  # if os.path.exists(kconfigdatafile):
  #   with tempfile.NamedTemporaryFile(dir=os.path.dirname(kconfigdatafile),
  #                                    prefix=os.path.basename(kconfigdatafile) + ".back",
  #                                    delete=False) as tmp:
  #     os.rename(kconfigdatafile, tmp.name)
  with open(kconfigdatafile, "wb") as f:
    pickle.dump(kconfigdata, f)

buildsystemdata.config_vars = kconfigdata.config_vars
buildsystemdata.bool_vars = kconfigdata.bool_vars
buildsystemdata.nonbool_vars = kconfigdata.nonbool_vars

compunit_command = 'compilation_units.py'
# if get_running_time:
#   compunit_command += ' --no-aggregation'
# remaining_arguments = ' -C ' + kconfigdatafile + ' ' + " ".join([os.path.join(x, build_name) for x in buildsystemdata.alldirs])
remaining_arguments = ' -C ' + kconfigdatafile + ' ' + " ".join(buildsystemdata.alldirs)
if args.boolean_configs:
  remaining_arguments += ' -B'

command = compunit_command + remaining_arguments
print command
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
print stdout_
for line in stdout_.strip().split("\n"):
  splitline = line.split(" ", 1)
  if len(splitline) >= 2:
    buildsystemdata.compilation_units[splitline[0]].append(splitline[1])
  else:
    print "no usable data from compilation_units.py: " + line

with lockfile.LockFile(datafile):
  # if os.path.exists(datafile):
  #   with tempfile.NamedTemporaryFile(dir=os.path.dirname(datafile),
  #                                    prefix=os.path.basename(datafile) + ".back",
  #                                    delete=False) as tmp:
  #     os.rename(datafile, tmp.name)
  with open(datafile, "wb") as f:
    pickle.dump(buildsystemdata, f)

# get presence conditions
unit_pc_datafile = './unit_pc'
kmaxdata.backup_existing_file(unit_pc_datafile)
with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as tmp:
  pc_command = compunit_command + ' --get-presence-conditions' + remaining_arguments
  print pc_command
  popen = subprocess.call(pc_command, shell=True, stdout=tmp)
  tmp.seek(0, os.SEEK_SET)
  with lockfile.LockFile(unit_pc_datafile):
    with open(unit_pc_datafile, 'ab') as dataf:
      for line in tmp:
        dataf.write(line)

def chgext(filename, f, t):
  if filename.endswith(f):
    return filename[:-2] + t

def mkc(filename):
    return filename[:-2] + ".c"

def otoc(filename):
  return chgext(filename, ".o", ".c")

def otoS(filename):
  return chgext(filename, ".o", ".S")

def ctoo(filename):
  return chgext(filename, ".c", ".o")

# get every c file
# with open(everycfiledatafile, "wb") as f:  # TODO: use this to write to file
command = 'find -type f | grep "\.c$" | sort | uniq | cut -c3-'
popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
stdout_, stderr_ = popen.communicate()
everycfile = set([os.path.normpath(x.strip('\n')) for x in stdout_.split()])

compilation_units = defaultdict(set)

for k in buildsystemdata.compilation_units.keys():
  compilation_units[k].update(buildsystemdata.compilation_units[k])

print "all c files", len(everycfile)
  
recon_compunits = set([mkc(x) for x in (compilation_units['compilation_units'] - compilation_units['library_units'])])
print "compilation units", len(recon_compunits)

recon_libunits = [mkc(x) for x in compilation_units['library_units']]
print "library units", len(recon_libunits)

recon_allunits = set(recon_compunits)
recon_allunits.update(recon_libunits)
print "recon_allunits", len(recon_allunits)

everycfile.difference_update(recon_compunits)
everycfile.difference_update(recon_libunits)
print len(everycfile)

additional_included = [
  "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
  "archival/libarchive/unxz/xz_dec_lzma2.c",
  "archival/libarchive/unxz/xz_dec_stream.c",
  
  "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
  "archival/libarchive/bz/bzlib.c",
  "archival/libarchive/bz/compress.c",
  "archival/libarchive/bz/huffman.c",

  "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
  "archival/libarchive/unxz/xz_dec_lzma2.c",
  "archival/libarchive/unxz/xz_dec_stream.c",
  
  "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
  "archival/libarchive/bz/bzlib.c",
  "archival/libarchive/bz/compress.c",
  "archival/libarchive/bz/huffman.c",

  "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
  "archival/libarchive/unxz/xz_dec_lzma2.c",
  "archival/libarchive/unxz/xz_dec_stream.c",
  
  "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
  "archival/libarchive/bz/bzlib.c",
  "archival/libarchive/bz/compress.c",
  "archival/libarchive/bz/huffman.c",
]

recon_included = set(compilation_units['included_c_files'])
recon_included.update(additional_included)
print "included c files", len(recon_included)
everycfile.difference_update(recon_included)
print len(everycfile)

recon_scripts = set([c for c in everycfile if c.startswith("scripts/")])
print "scripts", len(recon_scripts)
everycfile.difference_update(recon_scripts)
print len(everycfile)

recon_hostprogs = set([x + ".c" for x in compilation_units['hostprog_units']])
recon_hostprogs.update(["networking/ssl_helper/ssl_helper.c", # built by networking/ssl_helper/ssl_helper.sh

  "networking/ssl_helper-wolfssl/ssl_helper.c", # built by networking/ssl_helper-wolfssl/ssl_helper.sh
                        ])
print "hostprogs", len(recon_hostprogs)
everycfile.difference_update(recon_hostprogs)
print len(everycfile)

# explanations for busybox 1.25.0
explanations = {
  "examples": [
    "networking/httpd_ssi.c", # example program
    "networking/httpd_indexcgi.c",

    "shell/ash_test/printenv.c", # test program compiled and run in shell/ash_test/run-all
    "shell/ash_test/recho.c",
    "shell/ash_test/zecho.c",
    
    "applets/individual.c", # example wrapper program

    "networking/ntpd_simple.c", # for busybox 1_22_stable
  ],
  
  "unused": [
    "util-linux/volume_id/unused_highpoint.c",  # unused source
    "util-linux/volume_id/unused_hpfs.c",
    "util-linux/volume_id/unused_isw_raid.c",
    "util-linux/volume_id/unused_lsi_raid.c",
    "util-linux/volume_id/unused_lvm.c",
    "util-linux/volume_id/unused_mac.c",
    "util-linux/volume_id/unused_minix.c",
    "util-linux/volume_id/unused_msdos.c",
    "util-linux/volume_id/unused_nvidia_raid.c",
    "util-linux/volume_id/unused_promise_raid.c",
    "util-linux/volume_id/unused_silicon_raid.c",
    "util-linux/volume_id/unused_ufs.c",
    "util-linux/volume_id/unused_via_raid.c",

    "libbb/hash_md5prime.c", # commented out in libbb/Kbuild
    "libbb/bb_strtod.c",
    
    "networking/tc.c", # CONFIG_TC commented out of networking/Config.in
  ],

  "not built commented out": [
    "editors/patch_bbox.c", # not built
    "editors/patch_toybox.c",
  ],
}

# busy 1_22_stable has an unused directory of source files
old_e2fsprogs = [x for x in everycfile if x.startswith("e2fsprogs/old_e2fsprogs")]
print "old e2fsprogs dir", len(old_e2fsprogs)
everycfile.difference_update(old_e2fsprogs)
print len(everycfile)

for explanation in explanations.keys():
  print explanation,len(explanations[explanation])
  everycfile.difference_update(explanations[explanation])
  print len(everycfile)

# This will be empty if kmax got all C files correctly.  The
# explanations needs to contain all C files guaranteed to not be part
# of the build.
print everycfile

# if get_running_time == True:
#   print "running_time", buildsystemdata.compilation_units["running_time"][0]
#   continue

# compilation_units_datafile = kmaxdata.compilation_units_datafile(version, arch)
# with lockfile.LockFile(compilation_units_datafile):
#   if os.path.exists(compilation_units_datafile):
#     with tempfile.NamedTemporaryFile(dir=os.path.dirname(compilation_units_datafile),
#                                      prefix=os.path.basename(compilation_units_datafile) + ".back",
#                                      delete=False) as tmp:
#       os.rename(compilation_units_datafile, tmp.name)
#   with open(compilation_units_datafile, "wb") as f:
#     for compilation_unit in buildsystemdata.compilation_units['compilation_units']:
#       if compilation_unit.endswith('.o'):
#         c_file = compilation_unit[:-2] + '.c'
#         S_file = compilation_unit[:-2] + '.S'
#         if os.path.isfile(S_file):
#           f.write(S_file + '\n')
#         else:
#           f.write(c_file + '\n')
#       else:
#         f.write(compilation_unit + '\n')
