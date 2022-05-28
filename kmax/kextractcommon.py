import sys
from packaging import version
import kextractor_next_20210426
import kextractor_next_20200430
import kextractor_3_19
import kextractor_4_12_8
import kextractor_4_18

module_versions = {}

latest_module = "next-20210426"
module_versions["next-20210426"] = kextractor_next_20210426
module_versions["next-20200430"] = kextractor_next_20200430
module_versions["3.19"] = kextractor_3_19
module_versions["4.12.8"] = kextractor_4_12_8
module_versions["4.18"] = kextractor_4_18

available_versions = "Available versions: %s" % (", ".join(list(module_versions.keys())))

def pick_version(kernel_version: str):
  """Given a kernel_version string, returns the kextract version string to use."""

  # TODO: make sure if this major/minor is the exact point where we start needing next-20210426
  # if version.parse(kernel_version) >= version.parse("5.17.8"):
  #   return "5.17.8"
  # el
  if version.parse(kernel_version) >= version.parse("5.12"):
    return "next-20210426"
  elif version.parse(kernel_version) >= version.parse("5.6.8"):
    return "next-20200430"
  elif version.parse(kernel_version) >= version.parse("4.18"):
    return "4.18"
  elif version.parse(kernel_version) >= version.parse("4.12.8"):
    return "4.12.8"
  elif version.parse(kernel_version) >= version.parse("3.19"):
    return "3.19"
  else:
    # TODO: warn user that v3.19 is the current oldest version of kconfig supported
    return "3.19"


def kextract(module_version, args):
  if sys.version_info.major == 3 and sys.version_info.major == 7:
    args = [ bytes(arg, 'ascii') for arg in args ]
  module_versions[module_version].kextract(args)
