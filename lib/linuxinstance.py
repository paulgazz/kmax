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
import signal
import atexit
import subprocess
import lockfile # pip install lockfile
import tempfile

# Linux kernel source instance management.

assert "KMAX_SCRATCH" in os.environ
scratch_directory = os.environ["KMAX_SCRATCH"]
assert os.path.isdir(scratch_directory)

default_instance_parent_directory = os.path.join(scratch_directory,
                                                 "linux_instances/")
kernel_repos = { "linux": "git://git.kernel.org/pub/scm/linux/kernel/git/stable/linux-stable.git",
                 "history": "git://git.kernel.org/pub/scm/linux/kernel/git/history/history.git" }
new_repo_version = "2.6.12"

def version_to_tag(version):
  """At 2.5.0, the tags in git prepend 'v' to the version number"""
  if compare_versions(vstoa(version), vstoa("2.5.0")) >= 0:
    return "v" + version
  elif compare_versions(vstoa(version), vstoa("2.4.0")) == 0:
    return version + "-prerelease"
  else:
    return version

def compare_versions(a, b):
  """Recursively compare two arrays of ints representing Linux versions"""
  if len(a) == 0 and len(b) == 0:
    return 0
  if len(a) == 0:
    return -1
  if len(b) == 0:
    return 1
  if a[0] > b[0]:
    return 1
  if a[0] < b[0]:
    return -1
  if a[0] == b[0]:
    return compare_versions(a[1:], b[1:])

def vstoa(version):
  return [int(s) for s in version.split(".")]
  
def which_repo(version):
  if compare_versions(vstoa(version), vstoa(new_repo_version)) >= 0:
    return "linux"
  else:
    return "history"

def get_x86_archname(version):
  """At 2.6.24, i386 and x86_64 were merged into one arch, x86"""
  if (compare_versions(vstoa(version), vstoa("2.6.24")) >= 0):
    return "x86"
  else:
    return "i386"

def get_superc_args(version):
  """At 3.7, superc needs explicit config var for kconfig.h function
macros."""
  if (compare_versions(vstoa(version), vstoa("3.7")) >= 0):
    kconfig_header = "kconfig.h"
    autoconf_free = "autoconf-free.h"
    args = ""
    if (compare_versions(vstoa(version), vstoa("4.0")) >= 0):
      args += ' -D CONFIG_KASAN_SHADOW_OFFSETUL=0xdffffc0000000000UL '
    args += ' -include %s -include %s ' % (kconfig_header, autoconf_free)
    return args
  else:
    return ""

instances = []

def free_locks():
  for instance in instances:
    if instance.is_locked():
      print "Automatically unlocking", instance.instance_directory
      instance.free_lock()

def signal_handler(signum, frame):
  print "Caught signal.  Unlocking instances."
  free_locks()
  sys.exit(1)

signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)

atexit.register(free_locks)

class LinuxInstance:
  """Function call protocol: init locks and switches to instance dir,
  exit unlocks, enter also switches and locks the dir.  Changing
  directories will interfere with the instance.

  """
  def __init__(self, instance_parent_directory=default_instance_parent_directory):
    instances.append(self)
    self.instance_parent_directory = instance_parent_directory
    with lockfile.LockFile(self.instance_parent_directory):
      if not os.path.exists(self.instance_parent_directory):
        os.makedirs(self.instance_parent_directory)
    self.lockfile = None
    self.repo = None
    self.version = None
    self.arch = None
    self.instance_directory = None

  def enter(self, version):
    oldrepo = self.repo
    self.repo = which_repo(version)
    oldversion = self.version
    self.version = version

    if (oldrepo != self.repo):
      self.free_lock()
      self.instance_directory = self.get_free_instance()
      os.chdir(self.instance_directory)

    if (subprocess.call(['git', 'checkout', version_to_tag(version)]) == 0):
      self.version = version
    else:
      # handle error
      pass

  def init_arch(self, arch):
    self.arch = arch

    if not os.path.exists(self.get_arch_config_path()):
      return False
    
    if compare_versions(vstoa(self.version), vstoa("2.5.45")) >= 0:
      if compare_versions(vstoa(self.version), vstoa("2.6.26")) <= 0:
        # allyesconfig is broken on some architectures
        command = 'make CC=cc ARCH=' + arch + ' defconfig'
        subprocess.call(command, shell=True)
        return True
      else:
        command = 'make CC=cc ARCH=' + arch + ' allyesconfig'
        subprocess.call(command, shell=True)
        if compare_versions(vstoa(self.version), vstoa("3.7")) >= 0:
          # kconfig.h and autoconf-free.h
          command = 'check_dep --autoconf-free arch/%s/Kconfig > autoconf-free.h' % (arch)
          subprocess.call(command, shell=True)
          command = 'grep -v "autoconf" include/linux/kconfig.h > kconfig.h'
          subprocess.call(command, shell=True)
        return True
    # elif compare_versions(vstoa(self.version), vstoa("2.5.22")) >= 0:
    #   command = 'make CC=cc ARCH=' + arch + ' allyesconfig'
    # elif compare_versions(vstoa(self.version), vstoa("2.5.21")) == 0:
    #   command = "yes \"\" | bash scripts/Configure -y " + self.get_arch_config_path()
    else:
      return True

  def exit(self):
    self.free_lock()
    self.repo = None
    self.version = None
    self.arch = None
    self.instance_directory = None

  def get_free_instance(self):
    for instance in [ os.path.join(self.instance_parent_directory, l)
                      for l in os.listdir(self.instance_parent_directory)
                      if os.path.isdir(os.path.join(self.instance_parent_directory, l)) and
                      l.startswith(self.repo) ]:
      instance_lockfile = lockfile.LockFile(instance)
      if not instance_lockfile.is_locked():
        instance_lockfile.acquire()
        self.lockfile = instance_lockfile
        return instance
    return self.create_new_instance()

  def create_new_instance(self):
    instance = tempfile.mkdtemp(dir=self.instance_parent_directory,
                                prefix=self.repo)
    self.lockfile = lockfile.LockFile(instance)
    self.lockfile.acquire()
    if (subprocess.call(['git', 'clone', kernel_repos[self.repo],
                         instance]) != 0):
      return None
    return instance

  def is_locked(self):
    if self.lockfile == None:
      return False
    return self.lockfile.is_locked()

  def free_lock(self):
    if self.is_locked():
      self.lockfile.release()
    self.lockfile = None

  def get_archs(self):
    archdir = os.path.join(self.instance_directory, 'arch')
    return [ arch for arch in os.listdir(archdir)
             if os.path.isdir(os.path.join(archdir, arch)) ]

  def get_arch_config_path(self):
    if compare_versions(vstoa(self.version), vstoa("2.5.45")) >= 0:
      if self.arch != "um":
        return os.path.join(self.instance_directory, "arch", self.arch,
                            "Kconfig")
      else:
        # currently only x86 supports um linux
        return os.path.join(self.instance_directory, "arch/x86", self.arch,
                            "Kconfig")
    elif compare_versions(vstoa(self.version), vstoa("0.01")) >= 0:
      return os.path.join(self.instance_directory, "arch", self.arch,
                          "config.in")
    else:
      return None

  def get_config_filename(self):
    if compare_versions(vstoa(self.version), vstoa("2.5.45")) >= 0:
      return "Kconfig"
    elif compare_versions(vstoa(self.version), vstoa("0.01")) >= 0:
      return "Config.in"
    else:
      return None

  def get_check_dep_args(self):
    if compare_versions(vstoa(self.version), vstoa("2.5.45")) >= 0:
      return ""
    elif compare_versions(vstoa(self.version), vstoa("0.01")) >= 0:
      return "-C"
    else:
      return None
