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
import argparse
import tempfile
import csv

# Collect linker errors

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect linker errors
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
argparser.add_argument('-s',
                       '--server',
                       type=str,
                       help="""the FilenameService server name.""")
argparser.add_argument('-p',
                       '--port',
                       type=str,
                       help="""the FilenameService port number.""")
argparser.add_argument('-j',
                       '--job-index',
                       type=str,
                       help="""the index of the qsub array job. \
only job 0 creates the worklist and datafile.""")
args = argparser.parse_args()

version = args.version
arch = args.arch

command_template = "java -ea $JAVA_ARGS xtc.lang.cpp.FunctionChecker %s %s %s %s %s"
if args.server and args.port:
  command_template += " %s %s" % (args.server, args.port)

if arch == "x86":
  arch = linuxinstance.get_x86_archname(version)

job_index = args.job_index if args.job_index != None else "0"

functions_datafile = kmaxdata.functions_datafile(version, arch)
functions_pc_datafile = kmaxdata.functions_pc_datafile(version, arch)
unit_pc_datafile = kmaxdata.unit_pc_datafile(version, arch)
clauses_datafile = kmaxdata.clauses_datafile(version, arch)
model_assumptions_datafile = kmaxdata.model_assumptions_datafile(version, arch)
linker_errors_datafile = kmaxdata.linker_errors_datafile(version, arch)

command = command_template % (functions_datafile, functions_pc_datafile, unit_pc_datafile, clauses_datafile, model_assumptions_datafile)
  
sys.stderr.write("%s\n" % (command))

if job_index == "0":
  kmaxdata.backup_existing_file(linker_errors_datafile)

with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as tmp:
  popen = subprocess.call(command, shell=True, stdout=tmp, stderr=tmp)
  tmp.seek(0, os.SEEK_SET)
  with lockfile.LockFile(linker_errors_datafile):
    with open(linker_errors_datafile, 'ab') as dataf:
      for line in tmp:
        dataf.write(line)
