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
import lockfile # pip install lockfile or install from
                # https://github.com/smontanaro/pylockfile.git
import tempfile
import csv
import argparse

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect preprocessor and parser statistics and perform dynamic analysis
    """,
    epilog="""\
    """
    )
argparser.add_argument('version',
                       type=str,
                       help="""the git tag name of the Linux version""")
argparser.add_argument('arch',
                       type=str,
                       help="""the arch subdirectory name of the architecture.  passing 'x86' will
automatically switch to i386 for pre-2.6.24 kernels.""")
argparser.add_argument('-j',
                       '--job-index',
                       type=str,
                       help="""the index of the qsub array job. \
only job 0 creates the worklist and datafile.""")
argparser.add_argument('-w',
                       '--worklist',
                       type=str,
                       help="""a list of compilation units to process instead \
of the full list""")
args = argparser.parse_args()

version = args.version
arch = args.arch

if arch == "x86":
  arch = linuxinstance.get_x86_archname(version)

job_index = args.job_index if args.job_index != None else "0"

if args.worklist != None:
  compilation_units_datafile = args.worklist
else:
  compilation_units_datafile = kmaxdata.compilation_units_datafile(version, arch)

compilation_units_worklist = os.path.join(kmaxdata.kmax_data, "dynamicanalysis_worklist_" + version + arch)
dynamicanalysis_datafile = kmaxdata.dynamicanalysis_datafile(version, arch)

if job_index == "0":
  kmaxdata.backup_existing_file(compilation_units_worklist)
  with lockfile.LockFile(compilation_units_worklist):
    with open(compilation_units_worklist, 'wb') as outf:
      with open(compilation_units_datafile, 'rb') as inf:
        for line in inf:
          outf.write(line)
  kmaxdata.backup_existing_file(dynamicanalysis_datafile)

stat_parms = { 'preprocessor': '-preprocessor -preprocessorStatistics -size -configurationVariables -headerGuards',
               'parser'      : '-parserStatistics -languageStatistics -conditionGranularity' }

superc_args = linuxinstance.get_superc_args(version)

print 'version = %s, arch = %s' % (version, arch)
print 'compilation_units_datafile = %s' % (compilation_units_datafile)
print 'compilation_units_worklist = %s' % (compilation_units_worklist)

instance = linuxinstance.LinuxInstance()
instance.enter(version)
instance.init_arch(arch)

print "started"
while True:
  compilation_unit = kmaxdata.remove_last_line(compilation_units_worklist)
  if compilation_unit == None:
    break
  with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as outf:
    for stat_name in stat_parms.keys():
      with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as tmp:
        command = 'superc_linux.sh -K 600 -S"%s" %s' % (stat_parms[stat_name] + superc_args,
                                                        compilation_unit)
        print command
        popen = subprocess.call(command, shell=True, stderr=tmp, stdout=tmp)
        tmp.seek(0, os.SEEK_SET)
        for line in tmp:
          outf.write(line)
    outf.flush()
    command = 'dynamic_analysis.sh %s' % (outf.name)
    print command
    p = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
    stdout_, stderr_ = p.communicate()
    with lockfile.LockFile(dynamicanalysis_datafile):
      with open(dynamicanalysis_datafile, 'ab') as dataf:
        dataf.write(stdout_)
print "finished"
instance.exit()

# check_dep --autoconf-free arch/x86/Kconfig > autoconf-free.h; grep -v "autoconf" include/linux/kconfig.h > kconfig.h; superc_linux.sh -S"-include autoconf-free.h -include kconfig.h

# -include $CPPDIR/kmax/checkers/defs.h -TypeChef-x CONFIG_ -keepErrors" -A -c -K 300 init/main.c 2>&1 | tee /tmp/out
