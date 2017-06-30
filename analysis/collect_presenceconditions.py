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
import zlib
import threading
import Queue

import argparse

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Collect presence conditions
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

job_index = args.job_index if args.job_index != None else "0"

if args.worklist != None:
  compilation_units_datafile = args.worklist
else:
  compilation_units_datafile = kmaxdata.compilation_units_datafile(version, arch)

compilation_units_worklist = os.path.join(kmaxdata.kmax_data,
                                          "presenceconds_worklist_" +
                                          version + arch)
dynamicanalysis_datafile = kmaxdata.dynamicanalysis_datafile(version, arch)

# The number of files to process by the copy_data thread each time the
# locks for the data files are acquired.  Should reduce io bottleneck.
n_files_per_lock = 100

# Records zlib-compressed presence condition expression strings
presenceconds_datafile = kmaxdata.presenceconds_datafile(version,
                                                         arch)
# Records the hashcode, file start location, and length of each
# compressed presence condition in the presenceconds_datafile
presencecond_hashes_datafile = kmaxdata.presencecond_hashes_datafile(version,
                                                                     arch)
# Records the presence condition used at each conditional
presencecond_usages_datafile = kmaxdata.presencecond_usages_datafile(version,
                                                                     arch)
# # Use a separate usages file for each node to avoid the io bottleneck
# presencecond_usages_datafile += "." + job_index

if job_index == "0":
  kmaxdata.backup_existing_file(compilation_units_worklist)
  with lockfile.LockFile(compilation_units_worklist):
    with open(compilation_units_worklist, 'wb') as outf:
      with open(compilation_units_datafile, 'rb') as inf:
        for line in inf:
          outf.write(line)
    kmaxdata.backup_existing_file(presenceconds_datafile)
    kmaxdata.backup_existing_file(presencecond_hashes_datafile)
    kmaxdata.backup_existing_file(presencecond_usages_datafile)

superc_args = "-presenceConditions -preprocessor"
superc_args += linuxinstance.get_superc_args(version)

print 'version = %s, arch = %s' % (version, arch)
print 'compilation_units_datafile = %s' % (compilation_units_datafile)
print 'compilation_units_worklist = %s' % (compilation_units_worklist)

instance = linuxinstance.LinuxInstance()
instance.enter(version)
instance.init_arch(arch)

# Create a separate thread to copy the tmp file data to the datafiles
def copy_data(q):
  while True:
    # Read the temp file
    next_file = q.get()
    print "[%s] got next_file" % (job_index)              
    print "[%s] waiting for locks" % (job_index)
    with lockfile.LockFile(presenceconds_datafile):
      with lockfile.LockFile(presencecond_usages_datafile):
        with lockfile.LockFile(presencecond_hashes_datafile):
          # Open the data files
          with open(presenceconds_datafile, 'ab') as pc_f:
            with open(presencecond_usages_datafile, 'ab') as pc_usages_f:
              if os.path.exists(presencecond_hashes_datafile):
                with open(presencecond_hashes_datafile, 'rb') as pc_hash_f:
                  # get the hashcode from the first column of hashes file
                  pc_hash_set = set(line.strip().split(',', 1)[0]
                                    for line in pc_hash_f)
                  pc_hash_f.seek(0, os.SEEK_END)
              else:
                pc_hash_set = set([])
              i = n_files_per_lock
              while True:
                gzip_p = subprocess.Popen("gunzip -c " + next_file,
                                          shell=True,
                                          stderr=sys.stderr,
                                          stdout=subprocess.PIPE)
                tmp = gzip_p.stdout
                with open(presencecond_hashes_datafile, 'ab') as pc_hash_f:
                  print "[%s] writing" % (job_index)
                  for line in tmp:
                    if line.startswith("static_conditional"):
                      # remove "static_conditional" to save space and
                      # put the hash code first for easier sorting
                      a = line.strip().split(',')
                      outline = "%s,%s,%s\n" % (a[3], a[2], a[1])
                      pc_usages_f.write(outline)
                    elif line.startswith("presence_condition"):
                      a = line.strip().split(',', 2)
                      hashcode = a[1]
                      pc_string = a[2]
                      pc_compressed = zlib.compress(pc_string)
                      if hashcode not in pc_hash_set:
                        pc_start = pc_f.tell()
                        pc_len = len(pc_compressed)
                        pc_f.write(pc_compressed)
                        pc_hash_f.write('%s,%d,%d\n' % (hashcode, pc_start, pc_len))
                i -= 1
                if q.empty() or i <= 0:
                  break
                else:
                  os.remove(next_file)
                  print "[%s] removed next_file (opt)" % (job_index)
                  print "[%s] done writing (opt)" % (job_index)
                  q.task_done()
                  next_file = q.get()
                  print "[%s] got next_file (opt)" % (job_index)              
                
    os.remove(next_file)
    print "[%s] removed next_file" % (job_index)
    print "[%s] done writing" % (job_index)
    q.task_done()

data_q = Queue.Queue()
copy_data_t = threading.Thread(target=copy_data, args = (data_q,))
copy_data_t.daemon = True
copy_data_t.start()

print "[%s] started" % (job_index)
while True:
  compilation_unit = kmaxdata.remove_last_line(compilation_units_worklist)
  if compilation_unit == None:
    break
  tmp = tempfile.NamedTemporaryFile(dir=kmaxdata.kmax_scratch, delete=False)
  command = 'superc_linux.sh -K 600 -S"%s" %s' % (superc_args,
                                                  compilation_unit)
  print command
  # popen = subprocess.call(command, shell=True, stderr=tmp, stdout=tmp)
  superc_p = subprocess.Popen(command, shell=True, stdout=open(os.devnull, 'w'), stderr=subprocess.PIPE)
  gzip_p = subprocess.Popen("gzip", shell=True, stderr=sys.stderr, stdout=tmp, stdin=superc_p.stderr)
  gzip_p.communicate()
  tmp.close()
  data_q.put(tmp.name)
print "[%s] finished" % (job_index)

instance.exit()

print "[%s] waiting for copy_data thread" % (job_index)
data_q.join()
print "[%s] copy_data thread done" % (job_index)
