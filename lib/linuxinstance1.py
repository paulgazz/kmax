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

assert "HOME" in os.environ
default_master_instance = os.path.join(os.environ["HOME"],
                                       "Work/master_linux_instance")
default_instance_parent_directory = os.path.join(scratch_directory,
                                                 "linux_instances/")
kernel_repository = "git://git.kernel.org/pub/scm/linux/kernel/git/stable/linux-stable.git"
# history_repository = "git://git.kernel.org/pub/scm/linux/kernel/git/history/history.git"

instances = []

def exit_instances():
  for instance in instances:
    if instance.is_locked():
      print "Automatically unlocking", instance.instance_directory
      instance.exit_instance()

def signal_handler(signum, frame):
  print "Caught signal.  Unlocking instances."
  exit_instances()
  sys.exit(1)

signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)

atexit.register(exit_instances)

class LinuxInstance:
  """Function call protocol: init locks and switches to instance dir,
  exit unlocks, enter also switches and locks the dir.  Changing
  directories will interfere with the instance.

  """
  def __init__(self, version=None,
               instance_parent_directory=default_instance_parent_directory,
               master_instance=default_master_instance):
    instances.append(self)
    self.instance_parent_directory = instance_parent_directory
    with lockfile.LockFile(self.instance_parent_directory):
      if not os.path.exists(self.instance_parent_directory):
        os.makedirs(self.instance_parent_directory)
    self.master_instance = master_instance
    self.lockfile = None
    self.instance_directory = self.get_free_instance()
    if version != None: self.change_version(version)

  def get_free_instance(self):
    for instance in [ os.path.join(self.instance_parent_directory, l)
                      for l in os.listdir(self.instance_parent_directory)
                      if
                      os.path.isdir(os.path.join(self.instance_parent_directory,
                                                 l)) and
                      os.path.join(self.instance_parent_directory, l)
                      != self.master_instance ]:
      instance_lockfile = lockfile.LockFile(instance)
      if not instance_lockfile.is_locked():
        self.instance_directory = instance
        self.enter_instance()
        return self.instance_directory
    return self.create_new_instance()
  

  def create_new_instance(self):
    self.instance_directory = tempfile.mkdtemp(dir=self.instance_parent_directory,
                                               prefix="tmp")
    self.lockfile = lockfile.LockFile(self.instance_directory)
    self.enter_instance()
    self.check_master()
    if (subprocess.call(['git', 'clone', self.master_instance,
                         self.instance_directory]) != 0):
      return None
    return self.instance_directory

  def make_lock(self):
    if self.lockfile == None:
      self.lockfile = lockfile.LockFile(self.instance_directory)
    if not self.lockfile.is_locked():
      self.lockfile.acquire()

  def is_locked(self):
    if self.lockfile == None:
      return False
    return self.lockfile.is_locked()

  def enter_instance(self):
    if not self.is_locked():
      os.chdir(self.instance_directory)
      self.make_lock()

  def free_lock(self):
    if self.is_locked():
      self.lockfile.release()

  def exit_instance(self):
    if self.is_locked():
      self.free_lock()

  def get_archs(self):
    return [ arch for arch in os.listdir(self.get_archdir()) if
             os.path.isdir(os.path.join(self.get_archdir(), arch)) ]

  def get_archdir(self):
    return os.path.join(self.instance_directory, 'arch')

  def change_version(self, version):
    if self.is_locked():
      if (subprocess.call(['git', 'checkout', version]) == 0):
        self.version = version
      else:
        # handle error
        pass

  def check_master(self):
    with lockfile.LockFile(self.master_instance):
      if not os.path.isdir(self.master_instance):
        if (subprocess.call(['git', 'clone', kernel_repository,
                            self.master_instance]) != 0):
          # handle error
          pass

  def get_versions(self):
    """Return an array of all available Linux versions."""
    popen = subprocess.Popen(['git', 'tag'], stdout=subprocess.PIPE)
    stdout_, stderr_ = popen.communicate()
    return stdout_.strip().split("\n")

  def get_current_version(self):
    popen = subprocess.Popen(['git', 'describe'], stdout=subprocess.PIPE)
    stdout_, stderr_ = popen.communicate()
    return stdout_.strip()
    
