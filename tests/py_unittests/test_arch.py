import unittest
from kmax.arch import Arch
import os
import sys
import logging
import random
import tempfile

# LINUX_KSRC="path/to/linux/src" python -m unittest arch_tests.py

# TODO(necip): prepare assets, load formulas from assets, dump, generate from asset kextract
# TODO(necip): test load_arch (can be done by loading arch from the assets dir)
# TODO(necip): for assets, check the content of the formulas to see if they are right
# TODO(necip): test FormulaGenerationError exceptions
# TODO(necip): test kextract summary (kconfig types etc.)
# TODO(necip): test kclause composite

linux_ksrc_test = unittest.skipUnless(
  os.environ.get('LINUX_KSRC', False), 'skipping tests requiring linux kernel source since LINUX_KSRC is unset'
)

@linux_ksrc_test
class LinuxKsrcRequiredTests(unittest.TestCase):
  @staticmethod
  def get_linux_ksrc():
    return os.environ.get('LINUX_KSRC', False)

# TODO: use subtests, for each type do: 1) generate, get, dump, 2) load, get, so that, other paths will be tested
class TestFormulaGeneration(LinuxKsrcRequiredTests):
  def __get_new_arch(self):
    self.arch_tmpdir = tempfile.TemporaryDirectory()
    return Arch(random.choice(Arch.ARCHS), loggerLevel=logging.CRITICAL, linux_ksrc=LinuxKsrcRequiredTests.get_linux_ksrc(), arch_dir=self.arch_tmpdir.name)
  
  def test_generate_kextract(self):
    self.__get_new_arch().generate_kextract()

  def test_generate_kclause(self):
    self.__get_new_arch().generate_kclause()
  
  def test_generate_dir_dep(self):
    self.__get_new_arch().generate_dir_dep()
  
  def test_generate_selects(self):
    self.__get_new_arch().generate_selects()
  
  def test_generate_rev_dep(self):
    self.__get_new_arch().generate_rev_dep()
  

class TestFormulaFileNotFound(unittest.TestCase):
  def setUp(self):
    self.arch = Arch(Arch.CUSTOM_ARCH_NAME, loggerLevel=logging.CRITICAL)
    self.unknown_path = "some/file/path/that/doesnt/exist"
  
  def test_kextract(self):
    with self.assertRaises(Arch.KextractFormulaFileNotFound):
      self.arch.load_kextract(self.unknown_path)

  def test_kclause(self):
    with self.assertRaises(Arch.KclauseFormulaFileNotFound):
      self.arch.load_kclause(self.unknown_path, is_composite=True)

  def test_dir_dep(self):
    with self.assertRaises(Arch.DirDepFormulaFileNotFound):
      self.arch.load_dir_dep(self.unknown_path)
  
  def test_rev_dep(self):
    with self.assertRaises(Arch.RevDepFormulaFileNotFound):
      self.arch.load_rev_dep(self.unknown_path)

  def test_selects(self):
    with self.assertRaises(Arch.SelectsFormulaFileNotFound):
      self.arch.load_selects(self.unknown_path)

class TestMissingLinuxSource(unittest.TestCase):
  def setUp(self):
    self.arch = Arch(Arch.CUSTOM_ARCH_NAME, loggerLevel=logging.CRITICAL)
  
  def test_kextract_generate(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.generate_kextract()
  
  def test_kextract_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kextract()

  def test_kclause_generate(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.generate_kclause()
  
  def test_kclause_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kclause()
  
  def test_kclause_composite_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kclause_composite()
  
  def test_dirdep_generate(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.generate_dir_dep()
  
  def test_dirdep_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_dir_dep()

  def test_revdep_generate(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.generate_rev_dep()
  
  def test_revdep_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_rev_dep()

  def test_selects_generate(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.generate_selects()
  
  def test_selects_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_selects()

  def test_kconfig_types_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kconfig_types()
  
  def test_kconfig_visible_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kconfig_visible()
  
  def test_kconfig_has_def_nonbool_get(self):
    with self.assertRaises(Arch.MissingLinuxSource):
      self.arch.get_kconfig_has_def_nonbool()

if __name__ == '__main__':
  unittest.main()