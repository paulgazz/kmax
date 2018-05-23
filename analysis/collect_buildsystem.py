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

# Collect stats on archs, kconfig files, kbuild files, and config vars
# and pickle the data to stdout

# USAGE: collect_buildsystem.py

args = sys.argv
versions = None
archs = None
do_kbuild = True
presence_conditions_only = False
get_running_time = False
boolean_configs = False

if len(args) > 1 and args[1] == "-h":
  print "USAGE: " + os.path.basename(args[0]) + " [ [-q] [-t] [-g] [-B] version [arch] ]"
  print "  setting -q will only run kconfig, not kbuild"
  print "  setting -t will only time kconfig and kbuild, but no analysis"
  print "  setting -g will only get presence conditions, not the set of units"
  print "  setting -B will treat every configuration variable as Boolean"
  exit(1)

if len(args) > 1 and args[1] == "-q":
  do_kbuild = False
  args = args[1:]
if len(args) > 1 and args[1] == "-t":
  get_running_time = True
  args = args[1:]
if len(args) > 1 and args[1] == "-g":
  presence_conditions_only = True
  args = args[1:]
if len(args) > 1 and args[1] == "-B":
  boolean_configs = True
  args = args[1:]

if len(args) > 1:
  versions = [ args[1] ]
if len(args) > 2:
  arch = args[2]
  if arch == 'x86':
    arch = linuxinstance.get_x86_archname(versions[0])
  archs = [ arch ]

instance = linuxinstance.LinuxInstance()

if versions == None:
  # Read in the versions chosen for the kmax experiments
  with open(kmaxdata.versions_datafile, 'rb') as f:
    versions = { row[0] for row in list(csv.reader(f, delimiter=',')) }

devnull = open(os.devnull, 'wb')

for version in versions:
  instance.enter(version)

  archs = instance.get_archs() if archs == None else archs
  for arch in archs:
    if not instance.init_arch(arch):
      sys.stderr.write("arch " + arch + " not initialized: " + instance.get_arch_config_path() + "\n")
    else:
      print "version = " + version + ", arch = " + arch
      buildsystemdata = kmaxdata.BuildSystemData(version, arch)

      alldirs = set()
      command = 'make CC=cc ARCH=' + arch + ' -f ' + kmaxdata.makefile_override + ' alldirs'
      popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      stdout_, stderr_ = popen.communicate()
      alldirs.update(set(stdout_.strip().split()))

      # command = 'covering_set.py -D srctree=. -D ARCH=' + arch + ' -b arch/' + arch + '/Makefile'
      # popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      # stdout_, stderr_ = popen.communicate()
      # alldirs.update(set(stdout_.strip().split()))

      buildsystemdata.alldirs = list(alldirs)

      buildsystemdata.kconfig_files = []
      for dir in buildsystemdata.alldirs:
        for path, subdirs, filenames in os.walk(dir):
          buildsystemdata.kconfig_files += \
            [ os.path.join(path, fn)
              for fn in filenames
              if fn.startswith(instance.get_config_filename()) ]

      check_dep_command = "check_dep " + instance.get_check_dep_args()

      command = check_dep_command + ' --kconfigs ' + instance.get_arch_config_path()
      popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      stdout_, stderr_ = popen.communicate()
      buildsystemdata.config_vars = stdout_.strip().split()

      command = check_dep_command + ' --bools ' + instance.get_arch_config_path()
      popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      stdout_, stderr_ = popen.communicate()
      buildsystemdata.bool_vars = stdout_.strip().split()

      command = check_dep_command + ' --tristate ' + instance.get_arch_config_path()
      popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      stdout_, stderr_ = popen.communicate()
      buildsystemdata.bool_vars += stdout_.strip().split()

      command = check_dep_command + ' --nonbools ' + instance.get_arch_config_path()
      popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
      stdout_, stderr_ = popen.communicate()
      buildsystemdata.nonbool_vars = stdout_.strip().split()

      kconfigdatafile = kmaxdata.kconfig_datafile(version, arch)
      with lockfile.LockFile(kconfigdatafile):
        if os.path.exists(kconfigdatafile):
          with tempfile.NamedTemporaryFile(dir=os.path.dirname(kconfigdatafile),
                                           prefix=os.path.basename(kconfigdatafile) + ".back",
                                           delete=False) as tmp:
            os.rename(kconfigdatafile, tmp.name)
        with open(kconfigdatafile, "wb") as f:
          kconfigdata = kmaxdata.KConfigData()
          kconfigdata.config_vars = buildsystemdata.config_vars
          kconfigdata.bool_vars = buildsystemdata.bool_vars
          kconfigdata.nonbool_vars = buildsystemdata.nonbool_vars
          pickle.dump(kconfigdata, f)

      if do_kbuild:
        compunit_command = 'compilation_units.py'
        if get_running_time:
          compunit_command += ' --no-aggregation'
        if boolean_configs:
          compunit_command += ' -B'
        if arch == "um":
          compunit_command += ' -D SUBARCH=x86'
        remaining_arguments =  ' -D srctree=. -D OS=Linux -D ARCH=' + arch + ' -C ' + kconfigdatafile + ' arch/' + arch + '/Makefile ' + " ".join(buildsystemdata.alldirs)

        if (not presence_conditions_only):
          command = compunit_command + remaining_arguments
          print command
          popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
          stdout_, stderr_ = popen.communicate()
          for line in stdout_.strip().split("\n"):
            splitline = line.split(" ", 1)
            if len(splitline) >= 2:
              buildsystemdata.compilation_units[splitline[0]].append(splitline[1])
            else:
              print "no usable data from compilation_units.py: " + line

          if get_running_time == True:
            print "running_time", buildsystemdata.compilation_units["running_time"][0]
            continue

          compilation_units_datafile = kmaxdata.compilation_units_datafile(version, arch)
          with lockfile.LockFile(compilation_units_datafile):
            if os.path.exists(compilation_units_datafile):
              with tempfile.NamedTemporaryFile(dir=os.path.dirname(compilation_units_datafile),
                                               prefix=os.path.basename(compilation_units_datafile) + ".back",
                                               delete=False) as tmp:
                os.rename(compilation_units_datafile, tmp.name)
            with open(compilation_units_datafile, "wb") as f:
              for compilation_unit in buildsystemdata.compilation_units['compilation_units']:
                if compilation_unit.endswith('.o'):
                  c_file = compilation_unit[:-2] + '.c'
                  S_file = compilation_unit[:-2] + '.S'
                  if os.path.isfile(S_file):
                    f.write(S_file + '\n')
                  else:
                    f.write(c_file + '\n')
                else:
                  f.write(compilation_unit + '\n')

          datafile = kmaxdata.buildsystem_datafile(version, arch)

          with lockfile.LockFile(datafile):
            if os.path.exists(datafile):
              with tempfile.NamedTemporaryFile(dir=os.path.dirname(datafile),
                                               prefix=os.path.basename(datafile) + ".back",
                                               delete=False) as tmp:
                os.rename(datafile, tmp.name)
            with open(datafile, "wb") as f:
              pickle.dump(buildsystemdata, f)

        # get presence conditions
        unit_pc_datafile = kmaxdata.unit_pc_datafile(version, arch)
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
        
  # get every c files
  with open(kmaxdata.everycfile_datafile(version), "wb") as f:
    command = 'find -type f | grep "\.c$" | sort | uniq | cut -c3-'
    popen = subprocess.Popen(command, shell=True, stdout=f)
    
  instance.exit()
