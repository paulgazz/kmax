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
import zlib

# perform function analysis for the given linux version and
# architecture, collecting global function definitions and function
# calls to undefined functions with their bdds

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect function call and definitions with their conditions.
    """,
    epilog="""\
    """
    )
argparser.add_argument('version',
                       type=str,
                       help="""the git tag name of the Linux version""")
argparser.add_argument('arch',
                       type=str,
                       help="""the arch subdirectory name of the architecture""")
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

compilation_units_worklist = os.path.join(kmaxdata.kmax_data, "functions_worklist_" + version + arch)
functions_datafile = kmaxdata.functions_datafile(version, arch)
functions_pc_datafile = kmaxdata.functions_pc_datafile(version, arch)

if job_index == "0":
  kmaxdata.backup_existing_file(compilation_units_worklist)
  with lockfile.LockFile(compilation_units_worklist):
    with open(compilation_units_worklist, 'wb') as outf:
      with open(compilation_units_datafile, 'rb') as inf:
        for line in inf:
          outf.write(line)
  kmaxdata.backup_existing_file(functions_datafile)
  kmaxdata.backup_existing_file(functions_pc_datafile)

# superc_args = '-restrictFreeToPrefix CONFIG_ -U __ASSEMBLY__ -D __KERNEL__ -D CONFIG_X86 -D CONFIG_X86_64 -D CONFIG_64BIT -U CONFIG_X86_32 -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
# superc_args = '-U __ASSEMBLY__ -D __KERNEL__ -D CONFIG_X86 -D CONFIG_X86_64 -D CONFIG_64BIT -U CONFIG_X86_32 -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
# superc_args = '-D __KERNEL__ -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
# superc_args = '-restrictConfigToPrefix CONFIG_ -D __KERNEL__ -U __ASSEMBLY__ -D __KERNEL__ -D CONFIG_X86 -D CONFIG_X86_64 -D CONFIG_64BIT -U CONFIG_X86_32 -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
# superc_args = '-restrictConfigToPrefix CONFIG_ -D __KERNEL__ -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'

superc_args = '-U __ASSEMBLY__ -D __KERNEL__ -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
# superc_args = '-restrictFreeToPrefix CONFIG_ -U __ASSEMBLY__ -D __KERNEL__ -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL -functionAnalysis -printErrorConditions'
superc_args += linuxinstance.get_superc_args(version)

print 'version = %s, arch = %s' % (version, arch)
print 'compilation_units_datafile = %s' % (compilation_units_datafile)
print 'compilation_units_worklist = %s' % (compilation_units_worklist)

instance = linuxinstance.LinuxInstance()
instance.enter(version)
instance.init_arch(arch)

devnull = open(os.devnull, 'wb')

print "started"
while True:
  compilation_unit = kmaxdata.remove_last_line(compilation_units_worklist)
  if compilation_unit == None:
    break
  with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as tmp:
    # command = 'JAVA_ARGS="-Xms2048m -Xmx8048m -Xss128m" superc_linux.sh -K 600 -S"%s" %s' % (superc_args, compilation_unit)
    command = 'superc_linux.sh -K 600 -S"%s" %s' % (superc_args, compilation_unit)
    print command
    popen = subprocess.call(command, shell=True, stderr=tmp, stdout=devnull)
    tmp.seek(0, os.SEEK_SET)
    with lockfile.LockFile(functions_datafile):
      with lockfile.LockFile(functions_pc_datafile):
        with open(functions_datafile, 'ab') as dataf:
          with open(functions_pc_datafile, 'ab') as pcf:
            dataf.write("compilation_unit %s\n" % (compilation_unit))
            for line in tmp:
              if line.startswith("global_fundef") or line.startswith("undef_funcall"):
                a = line.strip().split(' ', 2)
                field = a[0]
                funname = a[1]
                if (len(a) > 2):
                  pc = a[2]
                else:
                  pc = "1"
                pc_compressed = zlib.compress(pc)
                pcf_start = pcf.tell()
                pcf_len = len(pc_compressed)
                pcf.write(pc_compressed)
                dataf.write('%s %s %d %d\n' % (field, funname, pcf_start, pcf_len))
              elif line.startswith("extra_constraint"):
                a = line.strip().split(' ', 1)
                if len(a) > 1:
                  field = a[0]
                  pc = a[1]
                  pc_compressed = zlib.compress(pc)
                  pcf_start = pcf.tell()
                  pcf_len = len(pc_compressed)
                  pcf.write(pc_compressed)
                  dataf.write('%s %d %d\n' % (field, pcf_start, pcf_len))
              else:
                dataf.write(line)
print "finished"
instance.exit()
