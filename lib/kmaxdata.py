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
import glob
import locale
import lockfile # pip install lockfile
from collections import defaultdict
import tempfile

# Kmax directories, data file names, data class, and related methods.

locale.setlocale(locale.LC_ALL, 'en_US.utf8')

def format_number(number):
  return locale.format("%d", number, grouping=True)

# check and import kmax_root and linux_dir environment variables
assert "KMAX_ROOT" in os.environ
kmax_root = os.path.expanduser(os.environ["KMAX_ROOT"])
assert os.path.isdir(kmax_root)

assert "KMAX_DATA" in os.environ
kmax_data = os.path.expanduser(os.environ["KMAX_DATA"])
assert os.path.isdir(kmax_data)

assert "KMAX_SCRATCH" in os.environ
kmax_scratch = os.environ["KMAX_SCRATCH"]
assert os.path.isdir(kmax_scratch)

versions_datafile = os.path.join(kmax_root, "analysis", "versions.txt")
makefile_override = os.path.join(kmax_root, "kbuild", "makefile_override")
busybox_makefile_override = os.path.join(kmax_root, "kbuild", "busybox_makefile_override")

def kbuildminer_datafiles(version):
  return glob.glob(os.path.join(kmax_data, "kbuildminer_" + version + "*.txt"))

def golem_datafiles(version):
  return glob.glob(os.path.join(kmax_data, "golem_" + version + "*.txt"))

def buildsystem_datafiles(version, path=kmax_data):
  return [ x for x in glob.glob(os.path.join(path, "buildsystem_" + version + "[a-z]*"))
           if ".back" not in x ]

def everycfile_datafile(version, path=kmax_data):
  return os.path.join(path, "everycfile_" + version + ".txt")

def kbuildminer_datafile(version, arch):
  return os.path.join(kmax_data, "kbuildminer_" + version + arch + ".txt")

def golem_datafile(version, arch):
  return os.path.join(kmax_data, "golem_" + version + arch + ".txt")

def buildsystem_datafile(version, arch=""):
  return os.path.join(kmax_data, "buildsystem_" + version + arch)

def unit_pc_datafile(version, arch=""):
  return os.path.join(kmax_data, "unit_pc_" + version + arch + ".txt")

def kconfig_datafile(version, arch=""):
  return os.path.join(kmax_data, "kconfig_" + version + arch)

def compilation_units_datafile(version, arch):
  return os.path.join(kmax_data, "compilation_units_" + version + arch + ".txt")

def cppstats_datafile(version, arch):
  return os.path.join(kmax_data, "cppstats_" + version + arch + ".txt")

def configs_datafile(version, arch):
  return os.path.join(kmax_data, "configs_" + version + arch + ".txt")

def functions_datafile(version, arch):
  return os.path.join(kmax_data, "functions_" + version + arch + ".txt")

def functions_pc_datafile(version, arch):
  return os.path.join(kmax_data, "functions_pc_" + version + arch)

def linker_errors_datafile(version, arch):
  return os.path.join(kmax_data, "linker_errors_" + version + arch + ".txt")

def checkers_datafile(version, arch):
  return os.path.join(kmax_data, "checkers_" + version + arch + ".txt")

def clauses_datafile(version, arch):
  return os.path.join(kmax_data, "clauses_" + version + arch + ".txt")

def model_assumptions_datafile(version, arch):
  return os.path.join(kmax_data, "model_assumptions_" + version + arch + ".txt")

def dynamicanalysis_datafile(version, arch, path=kmax_data):
  return os.path.join(path, "dynamicanalysis_" + version + arch + ".txt")

def presenceconds_datafile(version, arch):
  return os.path.join(kmax_data, "presenceconds_" + version + arch)

def presencecond_hashes_datafile(version, arch):
  return os.path.join(kmax_data, "presencecond_hashes_" + version +
                      arch + ".csv")

def presencecond_usages_datafile(version, arch):
  return os.path.join(kmax_data, "presencecond_usages_" + version +
                      arch + ".csv")

def backup_existing_file(filename):
  with lockfile.LockFile(filename):
    if os.path.exists(filename):
      with tempfile.NamedTemporaryFile(dir=os.path.dirname(filename),
                                       prefix=os.path.basename(filename)
                                       + ".back", delete=False) as tmp:
        os.rename(filename, tmp.name)

def remove_last_line(file_name):
  """Removes the last line from the given file and returns it.  Returns
None if the file is empty."""
  with lockfile.LockFile(file_name):
    with open(file_name, "r+b") as f:
      line = ""
      f.seek(0, os.SEEK_END)
      p = f.tell()
      while p > 0:
        p -= 1
        f.seek(p, os.SEEK_SET)
        c = f.read(1)
        if len(c) == 0: # file is empty
          break
        elif c == "\n" or c == "\r":
          if len(line) == 0:
            continue # skip blank lines
          else:
            break # found a complete line
        else:
          line = c + line
      f.truncate(p)
      if len(line) > 0:
        return line
      else:
        return None

def last_line_generator(file_name):
  """Creates a generator that yields and removes the last line from file_name"""
  while True:
    with lockfile.LockFile(file_name):
      with open(file_name, "r+b") as f:
        line = ""
        f.seek(0, os.SEEK_END)
        p = f.tell()
        while p > 0:
          p -= 1
          f.seek(p, os.SEEK_SET)
          c = f.read(1)
          if len(c) == 0: # file is empty
            break
          elif c == "\n" or c == "\r":
            if len(line) == 0:
              continue # skip blank lines
            else:
              break # found a complete line
          else:
            line = c + line
        f.truncate(p)
        if len(line) > 0:
          yield line
        else:
          break

class BuildSystemData:
  def __init__(self, version, arch):
    self.version = version
    self.arch = arch
    self.alldirs = []
    self.kconfig_files = []
    self.config_vars = []
    self.bool_vars = []
    self.nonbool_vars = []
    self.compilation_units = defaultdict(list)

  def __str__(self):
    return "\n".join([self.version,
                      self.arch,
                      str(self.alldirs),
                      str(self.kconfig_files),
                      str(self.config_vars),
                      str(self.compilation_units)])

class KConfigData:
  def __init__(self):
    self.config_vars = []
    self.bool_vars = []
    self.nonbool_vars = []

  def __str__(self):
    return "\n".join([str(self.config_vars),
                      str(self.bool_vars),
                      str(self.nonbool_vars)])
