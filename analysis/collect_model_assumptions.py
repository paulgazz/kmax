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

import sys
import os
import operator
import re
import argparse
import pycudd
import _pycudd
import tempfile
import cPickle as pickle
import re
from collections import defaultdict
import linuxinstance
import kmaxdata

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect model assumptions.
    """,
    epilog="""\
    """
    )
argparser.add_argument('version',
                       type=str,
                       help="""the git tag name of the Linux version""")
# argparser.add_argument('arch',
#                        type=str,
#                        help="""the arch subdirectory name of the architecture""")
args = argparser.parse_args()


version = args.version
# arch = args.arch
# if arch == "x86":
#   arch = linuxinstance.get_x86_archname(version)

buildsystem_data = {}
for buildsystem_datafile in kmaxdata.buildsystem_datafiles(version):
  with open(buildsystem_datafile, 'rb') as f:
    data = pickle.load(f)
    buildsystem_data[data.arch] = data

all = set([])
for arch in buildsystem_data.keys():
  all.update([ "CONFIG_" + c for c in buildsystem_data[arch].config_vars ])

unselectable = {}
for arch in buildsystem_data.keys():
  unselectable[arch] = all.difference([ "CONFIG_" + c
                                        for c
                                        in buildsystem_data[arch].config_vars
                                      ])
roots = defaultdict(set)
# roots["x86"] = set(["CONFIG_X86", "CONFIG_64BIT", "CONFIG_X86_64", "!CONFIG_X86_32"])
roots["x86"] = set(["CONFIG_X86", "CONFIG_64BIT"])

for arch in unselectable.keys():
  with open(kmaxdata.model_assumptions_datafile(version, arch), 'wb') as f:
    for v in roots[arch]:
      f.write("%s\n" % (v))
    for v in unselectable[arch]:
      f.write("!%s\n" % (v))
