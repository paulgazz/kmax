import sys
import kextractor_next_20210426
import kextractor_next_20200430
import kextractor_3_19
import kextractor_4_12_8

module_versions = {}

latest_module = "next-20210426"
module_versions["next-20210426"] = kextractor_next_20210426
module_versions["next-20200430"] = kextractor_next_20200430
module_versions["3.19"] = kextractor_3_19
module_versions["4.12.8"] = kextractor_4_12_8

available_versions = "Available versions: %s" % (", ".join(module_versions.keys()))

def kextract(module_version, args):
  if sys.version_info.major == 3 and sys.version_info.major == 7:
    args = [ bytes(arg, 'ascii') for arg in args ]
  module_versions[module_version].kextract(args)
