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
import kmaxdata
from collections import defaultdict
import operator
import zlib

if len(sys.argv) < 3:
  print "USAGE: %s version arch [top_n]" % (sys.argv[0])
  exit(1)

version = sys.argv[1]
arch = sys.argv[2]
top_n = int(sys.argv[3]) if len(sys.argv) > 3 else 10

presenceconds_datafile = kmaxdata.presenceconds_datafile(version,
                                                         arch)
presencecond_hashes_datafile = kmaxdata.presencecond_hashes_datafile(version,
                                                                     arch)
presencecond_usages_datafile = kmaxdata.presencecond_usages_datafile(version,
                                                                     arch)

# Count all usages of the presence conditions
presencecond_frequency = defaultdict(int)
line_hashes = set([])
with open(presencecond_usages_datafile, 'rb') as f:
  for line in f:
    pc_hash, location, usage_type = line.strip().split(',', 2)
    # line_hash = hash(line)
    line_hash = hash(location)
    # if line_hash not in line_hashes:
    #   line_hashes.add(line_hash)
    # if ".c:" in location:
    if ".c:" in location and line_hash not in line_hashes:
      line_hashes.add(line_hash)
      presencecond_frequency[pc_hash] += 1
line_hases = None

top_presenceconds = sorted(presencecond_frequency.items(),
                           key=operator.itemgetter(1),
                           reverse=True)[:top_n]

# hashmap maps the presence conditions hash code to a tuple (start,
# length)
hashmap = {}
with open(presencecond_hashes_datafile, 'rb') as f:
  for line in f:
    a = line.strip().split(',')
    hashmap[a[0]] = (a[1], a[2])

# Get the text of the presence condition for each of the top ones.
# Each presence condition's text is compressed and placed inside the
# presenceconds_datafile.  hashmap contains the position in the file
# to extract the compressed text.
presencecond_text = {}
with open(presenceconds_datafile, 'rb') as f:
  for hashcode, _ in top_presenceconds:
    start = int(hashmap[hashcode][0])
    length = int(hashmap[hashcode][1])
    f.seek(start, os.SEEK_SET)
    presencecond_text[hashcode] = zlib.decompress(f.read(length))

print r"""
\begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l l r}
\textbf{\#} & \textbf{Presence Condition} & \textbf{Frequency} \\
\hline
"""

rank = 0
for hashcode, frequency in top_presenceconds:
  rank += 1
  print r'%s & %s & %s \\' % (kmaxdata.format_number(rank), presencecond_text[hashcode], kmaxdata.format_number(frequency))

print r"""
\end{tabular*}
\caption{Top %s cross-cutting presence conditions and their frequencies.}
""" % (top_n,)
