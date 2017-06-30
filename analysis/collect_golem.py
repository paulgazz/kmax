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
import shutil
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
import shutil

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect golem compilation units
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
args = argparser.parse_args()

version = args.version
arch = args.arch

if arch == "x86":
  arch = linuxinstance.get_x86_archname(version)

undertaker_source = "/work/pcg234/undertaker"
undertaker_path = os.path.join(kmaxdata.kmax_scratch, "undertaker")

if not os.path.exists(undertaker_path):
  popen = subprocess.call("git clone %s %s" % (undertaker_source, undertaker_path), shell=True)

golem_command = os.path.join(undertaker_path, "python/golem -v -i")
golem_models = "/work/pcg234/golem"
golem_datafile = kmaxdata.golem_datafile(version, arch)

instance = linuxinstance.LinuxInstance()
instance.enter(version)
instance.init_arch(arch)

if os.path.exists("./models"):
  shutil.rmtree("./models")
shutil.copytree(os.path.join(golem_models, version, "models"), "./models")

with tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch) as tmp:
  print tmp.name
  command = 'ARCH=%s python %s' % (arch, golem_command)
  print command
  popen = subprocess.call(command, shell=True, stderr=tmp, stdout=tmp)
  tmp.seek(0, os.SEEK_SET)
  units = set()
  for line in tmp:
    if line.startswith("FILE_"):
      # name is first field, trim "FILE_" from it
      units.add(line.split()[0][5:])
  kmaxdata.backup_existing_file(golem_datafile)
  with lockfile.LockFile(golem_datafile):
    with open(golem_datafile, 'ab') as dataf:
      for unit in units:
        dataf.write("%s\n" % (unit))

instance.exit()
