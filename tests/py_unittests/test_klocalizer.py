import unittest
import os
import logging
import random
import tempfile
import subprocess
from shutil import which
import kmax
from kmax.klocalizer import Klocalizer
from kmax.arch import Arch

# LINUX_KSRC="path/to/linux/src" python -m unittest klocalizer_tests.py

"""If LINUX_KSRC/.kmax/ exists, will be used, otherwise, will be created and left there."""

kmax.common.quiet=True

try:
  from subprocess import DEVNULL  # Python 3.
except ImportError:
  DEVNULL = open(os.devnull, 'wb')

linuxksrc_required = unittest.skipUnless(
  os.environ.get('LINUX_KSRC', False), 'skipping tests requiring linux kernel source since LINUX_KSRC is unset'
)

makecross_required = unittest.skipUnless(
  which("make.cross") is not None, 'skipping tests requiring make.cross'
)

klocalizer_cli_required = unittest.skipUnless(
  which("klocalizer") is not None, 'skipping tests requiring klocalizer'
)

@linuxksrc_required
class LinuxKsrcRequiredTests(unittest.TestCase):
  @staticmethod
  def get_linux_ksrc():
    return os.environ.get('LINUX_KSRC', False)

@makecross_required
class TestCompilationUnits(LinuxKsrcRequiredTests):
  def setUp(self):
    self.must_succeed_units = [
      ("x86_64", "drivers/usb/storage/alauda.o"),
      ("x86_64", "sound/soc/intel/boards/glk_rt5682_max98357a.o"),
      ("mips", "sound/mips/sgio2audio.o"),
      ("ia64", "drivers/char/efirtc.o"),
      ("arm", "sound/soc/mediatek/common/mtk-btcvsd.o"),
      ("m68k", "drivers/block/ataflop.o"),
      ("i386", "drivers/watchdog/pcwd.o"),
      ("i386", "drivers/watchdog/mixcomwd.o"),
      ("powerpc", "drivers/video/fbdev/fsl-diu-fb.o"),
      ("sparc64", "drivers/watchdog/cpwd.o"),
      ("sparc64", "drivers/watchdog/riowd.o"),
      ("um", "arch/x86/um/signal.o")
    ]

  @klocalizer_cli_required
  def test_cli_must_succeed_units(self):
    """Tests that klocalizer (CLI) can generate valid configs that compile with given compilation units."""
    linux_ksrc = LinuxKsrcRequiredTests.get_linux_ksrc()
    for arch_name, unit in self.must_succeed_units:
      with self.subTest(arch_unit=(arch_name, unit)):
        # use temp config file
        tmp_cfgfile_tempfile = tempfile.NamedTemporaryFile(mode="w")
        kconfig_file = tmp_cfgfile_tempfile.name

        klocalizer_cmd = "klocalizer {unit} --linux-ksrc={linux_ksrc} -o {kconfig_file} -a {arch_name}".format(linux_ksrc=linux_ksrc, unit=unit, kconfig_file=kconfig_file, arch_name=arch_name)
        compile_cmd = "make.cross KCONFIG_CONFIG={kconfig_file} ARCH={arch_name} olddefconfig; make.cross KCONFIG_CONFIG={kconfig_file} ARCH={arch_name} clean {unit}".format(arch_name=arch_name, unit=unit, kconfig_file=kconfig_file)

        # run klocalizer
        subprocess.Popen(klocalizer_cmd, shell=True, stdout=DEVNULL, stderr=DEVNULL).communicate()

        # check kconfig file created
        self.assertTrue(os.path.exists(kconfig_file), msg="couldn't find klocalizer generated kconfig config file")

        # compile
        subprocess.Popen(compile_cmd, shell=True, stdout=DEVNULL, stderr=DEVNULL, cwd=linux_ksrc).communicate()

        # check unit is successfuly compiled
        compiled_unit_path = os.path.join(linux_ksrc, unit)
        self.assertTrue(os.path.exists(compiled_unit_path), msg="klocalizer generated kconfig config file couldn't build the target unit")

        # clean temp config file
        old_cfg = kconfig_file + ".old" # original copy is stored after olddefconfig
        if os.path.exists(old_cfg): os.remove(old_cfg)
        tmp_cfgfile_tempfile.close()

  def test_pythonapi_must_succeed_units(self):
    """Tests that klocalizer (Python API) can generate valid configs that compile with given compilation units."""
    linux_ksrc = LinuxKsrcRequiredTests.get_linux_ksrc()

    def get_arch_formulas_dir(arch_name: str) -> str:
      return os.path.join(linux_ksrc, ".kmax/kclause/", arch_name)
    
    for arch_name, unit in self.must_succeed_units:
      with self.subTest(arch_unit=(arch_name, unit)):
        # create arch instance
        arch = Arch(name=arch_name, linux_ksrc=linux_ksrc, arch_dir=get_arch_formulas_dir(arch_name), verify_linux_ksrc=False, loggerLevel=logging.ERROR)

        # create klocalizer and do settings
        klocalizer = Klocalizer()
        klocalizer.set_linux_krsc(linux_ksrc)
        klocalizer.include_compilation_unit(unit)
        z3_constraints = klocalizer.compile_constraints(arch=arch)

        # check SAT and get model
        model_sampler = Klocalizer.Z3ModelSampler(z3_constraints)
        is_sat, z3_model = model_sampler.sample_model()

        self.assertTrue(is_sat, msg="klocalizer couldn't find SAT solution for target compilation unit")

        # create config
        cfg_content = Klocalizer.get_config_from_model(z3_model, arch, set_tristate_m=False, allow_non_visibles=False)
        tmp_cfgfile_tempfile = tempfile.NamedTemporaryFile(mode="w")
        tmp_cfgfile_path = tmp_cfgfile_tempfile.name
        tmp_cfgfile_tempfile.write(cfg_content)
        tmp_cfgfile_tempfile.flush()

        # compile and check unit exists
        compile_cmd = "make.cross KCONFIG_CONFIG={kconfig_file} ARCH={arch_name} olddefconfig; make.cross KCONFIG_CONFIG={kconfig_file} ARCH={arch_name} clean {unit}".format(arch_name=arch_name, unit=unit, kconfig_file=tmp_cfgfile_path)
        subprocess.Popen(compile_cmd, shell=True, stdout=DEVNULL, stderr=DEVNULL, cwd=linux_ksrc).communicate()
        
        # must succeed
        compiled_unit_path = os.path.join(linux_ksrc, unit)
        self.assertTrue(os.path.exists(compiled_unit_path), "klocalizer generated kconfig config file couldn't build the target unit")

        old_cfg = tmp_cfgfile_path + ".old" # original copy is stored after olddefconfig
        if os.path.exists(old_cfg): os.remove(old_cfg)
        tmp_cfgfile_tempfile.close()

