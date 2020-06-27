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
import glob
from collections import defaultdict
import pickle
import fnmatch
import locale
import numpy
import itertools
import re
import subprocess
from pathlib import Path

# The script looks at the output of kmaxall --output-units-by-type

# explanations for 3.19
explanations_by_version = {
  "3.19" : {
    'orphaned': [
      'arch/alpha/lib/stacktrace.c',
      'arch/cris/arch-v10/lib/dmacopy.c',
      'arch/frv/kernel/irq-mb93093.c',
      'arch/arm/mach-msm/board-sapphire.c',
      'arch/arm/mach-omap2/prcm_mpu44xx.c',
      'arch/arm/mach-omap2/prminst44xx.c',
      'arch/arm/mach-omap2/vc44xx_data.c',
      'arch/arm/mach-omap2/vp44xx_data.c',
      'arch/mips/mti-sead3/sead3-i2c-drv.c',
      'arch/mn10300/unit-asb2305/pci-iomap.c',
      'arch/powerpc/platforms/cell/spufs/spu_restore.c',
      'arch/powerpc/platforms/cell/spufs/spu_save.c',
      'arch/x86/vdso/vdso32/vdso-fakesections.c',
      'drivers/gpu/drm/exynos/exynos_drm_connector.c',
      'drivers/infiniband/hw/cxgb3/cxio_dbg.c',
      'drivers/macintosh/nvram.c',
      'drivers/media/pci/cx18/cx18-alsa-mixer.c',
      'drivers/media/pci/cx25821/cx25821-audio-upstream.c',
      'drivers/media/pci/ivtv/ivtv-alsa-mixer.c',
      'drivers/media/pci/mantis/mantis_vp3028.c',
      'drivers/net/wireless/rtlwifi/btcoexist/halbtc8192e2ant.c',
      'drivers/net/wireless/rtlwifi/btcoexist/halbtc8723b1ant.c',
      'drivers/net/wireless/rtlwifi/btcoexist/halbtc8821a1ant.c',
      'drivers/net/wireless/rtlwifi/btcoexist/halbtc8821a2ant.c',
      'drivers/virtio/config.c',
      'sound/isa/gus/gus_instr.c',
      'sound/soc/codecs/sirf-audio-codec.c',
      'arch/cris/arch-v10/lib/old_checksum.c',
      'drivers/scsi/aic7xxx/aiclib.c',
      'arch/powerpc/math-emu/udivmodti4.c',
      'drivers/parisc/ccio-rm-dma.c', # commented out
      'lib/inflate.c', # doesn't appear in lib/Makefile
    ],
    'helpers': [
      'drivers/vhost/test.c', # test program
      'arch/powerpc/kernel/systbl_chk.c', # helper program
      'net/netfilter/nft_expr_template.c', # template
      'kernel/bounds.c', # generator
      'arch/mn10300/lib/ashrdi3.c', # used to create asm file
      'arch/mn10300/lib/lshrdi3.c', # used to create asm file
      'lib/raid6/test/test.c', # test program
      'drivers/scsi/aic7xxx/aicasm/aicasm.c', # assembler for aic7xxx scsi host firmware adapter
      'drivers/scsi/aic7xxx/aicasm/aicasm_symbol.c',
      'drivers/staging/iio/Documentation/generic_buffer.c', # test code
      'drivers/staging/iio/Documentation/iio_event_monitor.c', # test code
      'drivers/staging/iio/Documentation/lsiio.c', # tools
      'arch/ia64/scripts/check-model.c', # helper
    ],
    'make_target': [
      'arch/tile/kernel/vdso/vgettimeofday.c', # make target of different name
      'arch/arm64/crypto/aes-glue.c', # make target of different name
      'arch/ia64/kernel/nr-irqs.c', # uses make target
    ],
    'unconfigurable': [
      "drivers/acpi/acpica/hwtimer.c", 
      "drivers/acpi/acpica/nsdumpdv.c", 
      "drivers/acpi/acpica/utcache.c", 
      "drivers/acpi/acpica/utfileio.c", 
      "drivers/acpi/acpica/utprint.c", 
      "drivers/acpi/acpica/uttrack.c", 
      "drivers/acpi/acpica/utuuid.c"
    ],
    # 'staging' : [
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1500.c',
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1564.c',
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci3501.c',
    # ] + list(compilation_units['unidentified_staging_c_files']),
    'offsets' : [
      'arch/x86/um/user-offsets.c',
    ]
  },
  "5.7.5" : {
    'orphaned': [
      'arch/alpha/lib/stacktrace.c',
      'arch/powerpc/platforms/cell/spufs/spu_restore.c',
      'arch/powerpc/platforms/cell/spufs/spu_save.c',
      'arch/powerpc/math-emu/udivmodti4.c',
    ],
    'helpers': [
      'drivers/vhost/test.c', # test program
      'kernel/bounds.c', # generator
      'lib/raid6/test/test.c', # test program
      'drivers/scsi/aic7xxx/aicasm/aicasm.c', # assembler for aic7xxx scsi host firmware adapter
      'drivers/scsi/aic7xxx/aicasm/aicasm_symbol.c',
      'arch/ia64/scripts/check-model.c', # helper
    ],
    'make_target': [  # done
      'arch/arm64/crypto/aes-glue.c', # make target of different name
      'arch/ia64/kernel/nr-irqs.c', # uses make target
    ],
    'unconfigurable': [ # done
      "drivers/acpi/acpica/hwtimer.c", 
      "drivers/acpi/acpica/nsdumpdv.c", 
      "drivers/acpi/acpica/utcache.c", 
      "drivers/acpi/acpica/utprint.c", 
      "drivers/acpi/acpica/uttrack.c", 
      "drivers/acpi/acpica/utuuid.c"
    ],
    # 'staging' : [
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1500.c',
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1564.c',
    #   'drivers/staging/comedi/drivers/addi-data/hwdrv_apci3501.c',
    # ] + list(compilation_units['unidentified_staging_c_files']),
  }
}

# explanations_table = [
#   ("Orphans", r"No longer referenced", len(explanations['orphaned'])),
#   ("Helpers", r"Helper programs and generators", len(explanations['helpers'])),
#   ("Make targets", r"Built from make target instead of Kbuild syntax", len(explanations['make_target'])),
#   ("Skeleton files", r"Example files", len(explanations['skeletons'])),
#   ("Included C files", r"C files \#included in other compilation units", len(explanations['included_c_files'])),
#   ("Staging drivers", r"Files orphaned in the driver staging directory", len(explanations['staging'])),
# ]

# total_explanations = sum([x for _, _, x in explanations_table])

def chgext(filename, f, t):
  if filename.endswith(f):
    return filename[:-2] + t
  else:
    return filename

def mkc(filename):
    return filename[:-2] + ".c"

def otoc(filename):
  return chgext(filename, ".o", ".c")

def hostprog_otoc(filename):
  """host programs don't have a .o extension, but their components
  might if it's a composite"""
  if not filename.endswith(".o"):
    filename = filename + ".o"
  return chgext(filename, ".o", ".c")

def otoS(filename):
  return chgext(filename, ".o", ".S")

def ctoo(filename):
  return chgext(filename, ".c", ".o")

def append_recon_data(l, v):
    sys.stderr.write("%d\n" % v)
    l.append(l[-1] - v)
    l.append(v)

def append_info(l, name, desc):
    l.append(name)
    l.append(desc)

def resolve_path(path):
  current = os.path.abspath('.')
  abspath = os.path.abspath(path)
  resolved = abspath[len(current)+1:]
  # print(path)
  # print(resolved)
  return resolved

if __name__ == '__main__':    
  disable_slow_stuff = False

  available_versions = "Available Linux versions: %s\n" % (" ".join(explanations_by_version.keys()))
  
  if len(sys.argv) < 2:
    sys.stderr.write("USAGE: python3 completeness.py linux_version [units_file]\n\n  %s" % (available_versions))
    exit(0)
  else:
    version = sys.argv[1]
    if version not in explanations_by_version.keys():
      sys.stderr.write("ERROR: invalid version.  %s" % (available_versions))
      exit(1)

  explanations = explanations_by_version[version]

  if len(sys.argv) > 2:
    units_files = sys.argv[2]
  else:
    if version == "3.19":
      # for 3.19, we run kmax one arch at-a-time to repeat the FSE17 experiment
      units_files = ".kmax/kclause/*/units"
    else:
      # other versions can just use a single kmax file that contains all archs
      units_files = ".kmax/units"

  units_files = glob.glob(units_files)

  units_by_type = {}
  for units_file in units_files:
    with open(units_file, 'rb') as fp:
      try:
        new_units_by_type = pickle.load(fp)
        for unit_type in new_units_by_type:
          if unit_type not in units_by_type:
            units_by_type[unit_type] = set(new_units_by_type[unit_type])
          else:
            units_by_type[unit_type].update(set(new_units_by_type[unit_type]))
      except:
        pass

  # print("\n".join(units_by_type['compilation_units']))

  # print("%% program: " + os.path.basename(sys.argv[0]))
  # print("%% version: " + version)

  locale.setlocale(locale.LC_ALL, 'en_US.utf8')

  compilation_units = [ resolve_path(unit) for unit in units_by_type['compilation_units'] ]

  used_subdirectory = set()
  for unit in compilation_units:
    used_subdirectory.add(os.path.dirname(unit))

  # find all compilation units without a corresponding .c file
  check_compilation_units = set()
  asm_compilation_units = set()
  subdirectories = set()
  unmatched_units = set()
  non_units = set()
  for unit in compilation_units:
    if unit is not None:
      if unit.endswith('.o'):
        c_file = otoc(unit)
        S_file = otoS(unit)
        if os.path.isfile(c_file):
          check_compilation_units.add(resolve_path(unit))
        elif os.path.isfile(S_file):
          asm_compilation_units.add(resolve_path(S_file))
        else:
          unmatched_units.add(c_file)
      else:
        if unit.endswith("/"):
          subdirectories.add(unit)
        else:
          non_units.add(unit)

  # print("\n".join(sorted(unmatched_units)))

  # print(len(check_compilation_units))
  # print(len(asm_compilation_units))
  # print(len(unmatched_units))
  # print(len(subdirectories))
  # print(len(non_units))

  # find all .c files
  command = 'find -type f | egrep "\.c$" | sort | uniq | cut -c3-'
  popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
  out, _ = popen.communicate()
  everycfile = out.decode().splitlines()

  # print(everycfile)

  # all_c_files = set([])
  # for subdir in (sorted(used_subdirectory)):
  #   all_c_files.update([os.path.normpath(x) for x in glob.glob(os.path.join(subdir, "*.c"))])

  # print("all_c_files %s" % len(all_c_files))

  # find all .c files without a corresponding compilation unit, starting
  # with all c files
  # unidentified_c_files = set(all_c_files)
  unidentified_c_files = set(everycfile)

  sys.stderr.write("%s remaining\nremoving kmax results\n" % (str(len(unidentified_c_files))))

  # remove kernel compilation units
  unidentified_c_files.difference_update([otoc(filename)
                                       for filename in compilation_units])

  sys.stderr.write("%s remaining\nremoving unconfigurable units\n" % (str(len(unidentified_c_files))))

  # remove unconfigurable compilation units
  unidentified_c_files.difference_update([hostprog_otoc(filename)
                                          for filename in units_by_type['unconfigurable_units']])

  sys.stderr.write("%s remaining\nremoving hostprogs\n" % (str(len(unidentified_c_files))))

  # remove hostprog compilation units
  unidentified_c_files.difference_update([hostprog_otoc(filename)
                                          for filename in units_by_type['hostprog_units']])

  sys.stderr.write("%s remaining\nremoving extra units\n" % (str(len(unidentified_c_files))))

  # remove extra units
  unidentified_c_files.difference_update([hostprog_otoc(filename)
                                          for filename in units_by_type['extra']])

  sys.stderr.write("%s remaining\nremoving targets\n" % (str(len(unidentified_c_files))))

  # remove target units
  unidentified_c_files.difference_update([hostprog_otoc(filename)
                                          for filename in units_by_type['targets']])

  sys.stderr.write("%s remaining\nremoving non-kernel directories\n" % (str(len(unidentified_c_files))))

  # remove non-kernel directories
  unidentified_c_files = set([ filename for filename in unidentified_c_files
                           if not (filename.startswith("Documentation/")
                                   or filename.startswith("scripts")
                                   or filename.startswith("firmware")
                                   # or filename.startswith("include")
                                   or filename.startswith("samples")
                                   or filename.startswith("tools")
                           ) ])

  sys.stderr.write("%s remaining\nremoving clean_files\n" % (str(len(unidentified_c_files))))

  # remove clean_files
  unidentified_c_files.difference_update([filename
                                          for filename in units_by_type['clean_files']])

  sys.stderr.write("%s remaining\nremoving asm-offsets.c files\n" % (str(len(unidentified_c_files))))

  # find all asm-offsets.c files, for these are compiled by the root
  # Kbuild file into offsets
  re_offsets_file = re.compile(r'arch/[^/]+/kernel/asm-offsets\.c')
  offsets_files = [ x for x in everycfile if re_offsets_file.match(x) ]
  offsets_files.extend(explanations['offsets'])

  # remove asm-offsets.c files
  unidentified_c_files.difference_update([filename
                                          for filename in offsets_files])

  if not disable_slow_stuff:
    sys.stderr.write("%s remaining\nremoving C files included in other C files\n" % (str(len(unidentified_c_files))))

    # get source files that include c files
    included_c_files = set()
    p = subprocess.Popen(r'find . -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"',
                         shell=True,
                         stdout=subprocess.PIPE)
    out, _ = p.communicate()
    for line in out.decode().splitlines():
      parts = line.split(":", 1)
      if parts is not None:
        infile = parts[0]
        if len(parts) > 1:
          m = re.search(r"\".*\.c\"", parts[1])
          if m is not None:
            included = m.group(0)[1:-1]
            included = os.path.join(os.path.dirname(infile), included)
            included = os.path.relpath(os.path.realpath(included))
            included_c_files.add(included)

    # # only need the files in the current source subtree
    # included_c_files.intersection_update(every_c_file)

    # remove .c files that aren't compilation units, because they are
    # included in other c files
    unidentified_c_files.difference_update(included_c_files)

  sys.stderr.write("%s remaining\nremoving driver staging files\n" % (str(len(unidentified_c_files))))

  # separate out .c files from the staging directory, which can be a
  # mess
  unidentified_staging_c_files = [ x for x in unidentified_c_files
                                if "drivers/staging" in os.path.dirname(x) ]

  unidentified_c_files.difference_update(unidentified_staging_c_files)

  sys.stderr.write("%s remaining\nremoving skeleton files\n" % (str(len(unidentified_c_files))))

  # separate out .c files with "skeleton" in their name.  this is a
  # heuristic to find example drivers that aren't actually compiled.
  unidentified_skeleton_c_files = [ x for x in unidentified_c_files
                                 if "skeleton" in os.path.basename(x) ]

  unidentified_c_files.difference_update(unidentified_skeleton_c_files)

  # separate out generators heuristically.  look for "mk" or
  # "gen[^a-zA-Z]" in their name

  # perhaps we can find generators a better way, e.g., by looking for
  # the c file in the makefile

  # sys.stderr.write("%s remaining\nremoving files with unexpanded contents\n" % (str(len(unidentified_c_files))))

  # # look for unexpanded variables or function calls
  # re_unexpanded = re.compile(r'.*\$\(.*\).*')
  # unexpanded_compilation_units = [ x for x in units_by_type['compilation_units']
  #                                  if re_unexpanded.match(x) ]
  # unexpanded_hostprog_units = [ x for x in units_by_type['hostprog_units']
  #                               if re_unexpanded.match(x) ]
  # unexpanded_unconfigurable_units = [ x for x in units_by_type['unconfigurable_units']
  #                                     if re_unexpanded.match(x) ]
  # unexpanded_extra = [ x for x in units_by_type['extra']
  #                                  if re_unexpanded.match(x) ]
  # unexpanded_targets = [ x for x in units_by_type['targets']
  #                                  if re_unexpanded.match(x) ]
  # unexpanded_clean_files = [ x for x in units_by_type['clean_files']
  #                              if re_unexpanded.match(x) ]
  # unexpanded_subdirectories = [ x for x in subdirectories
  #                               if re_unexpanded.match(x) ]

  # # remove compilation units with unexpanded variable names
  # unidentified_c_files.difference_update([ otoc(x)
  #                                     for x in unexpanded_compilation_units ])

  # # remove hostprog units with unexpanded variable names
  # unidentified_c_files.difference_update([ hostprog_otoc(x)
  #                                     for x in unexpanded_hostprog_units ])

  # # remove unconfigurable units with unexpanded variable names
  # unidentified_c_files.difference_update([ hostprog_otoc(x)
  #                                     for x in unexpanded_unconfigurable_units ])

  # # remove extra targets with unexpanded variable names
  # unidentified_c_files.difference_update([ hostprog_otoc(x)
  #                                     for x in unexpanded_extra ])

  # # remove extra targets with unexpanded variable names
  # unidentified_c_files.difference_update([ hostprog_otoc(x)
  #                                     for x in unexpanded_targets ])

  # # remove clean targets with unexpanded variable names
  # unidentified_c_files.difference_update([ hostprog_otoc(x)
  #                                     for x in unexpanded_clean_files ])

  if not disable_slow_stuff:
    sys.stderr.write("%s remaining\nremoving generated C files\n" % (str(len(unidentified_c_files))))

    # remove c files specified in the clean-files and in targets, since
    # these can be auto-generated c files
    generated_c_files = set([])
    for c in (units_by_type['clean_files'] | units_by_type['targets']):
      if c.endswith(".c$"):
        pattern = re.compile(fnmatch.translate(c))
        for filename in unidentified_c_files:
          if pattern.match(filename):
            generated_c_files.add(filename)
    unidentified_c_files.difference_update(generated_c_files)

  sys.stderr.write("%s remaining\nremoving boot and tools arch files\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update([c for c in unidentified_c_files if
                                    re.match("arch/.*/boot/", c) != None or
                                    re.match("arch/.*/tools/", c) != None ])

  # remove those that have manually-found explanations
  # for key in explanations.keys():
  #   unidentified_c_files.difference_update(explanations[key])
  # # sys.stderr.write(str(len(unidentified_c_files)) + "\n")

  sys.stderr.write("%s remaining\nremoving helper programs\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update(set(explanations['helpers']))

  # unidentified_c_files.difference_update(set(explanations['staging']))

  sys.stderr.write("%s remaining\nremoving orphaned source files\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update(set(explanations['orphaned']))

  sys.stderr.write("%s remaining\nremoving source built by targets\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update(set(explanations['make_target']))

  sys.stderr.write("%s remaining\nremoving unconfigurable code\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update(set(explanations['unconfigurable']))

  sys.stderr.write("%s remaining\nremoving non-Kbuild-style object files\n" % (str(len(unidentified_c_files))))

  unidentified_c_files.difference_update(set([c for c in everycfile if
                                         c.startswith("arch/xtensa/platforms") or # calls external shell
                                         c.startswith("arch/x86/realmode/rm") or # creates realmode.bin via conventional make target, included in .S file
                                         c.startswith("arch/um/sys-ppc") or # not compiled via Kbuild
                                         c.startswith("arch/um/sys-ia64") # not compiled via Kbuild
  ]))

  # # account for compilation units identified in other architectures, when checking a single architecture
  # for key in [key for key in compilation_units.keys() if key != 'unidentified_c_files']:
  #   unidentified_c_files.difference_update([x[:-2] + ".c" for x in compilation_units[key]])
  # sys.stderr.write(str(len(unidentified_c_files)) + "\n")

  print("\n".join(sorted(unidentified_c_files)))

  sys.stderr.write("%s remaining\n" % (str(len(unidentified_c_files))))

  exit(0)

  recon_info = []
  recon_data = []
  sys.stderr.write("all c file reconciliation\n")
  sys.stderr.write("%d\n" % len(everycfile))
  append_info(recon_info, r"TOTAL", r"All \verb'.c' files in the source tree")
  recon_data.append(len(everycfile))
  recon_data.append(len(everycfile))

  everycfile.difference_update(set([mkc(x) for x in (compilation_units['compilation_units'] - compilation_units['library_units'])]))
  append_info(recon_info, r"Compilation units", r"From \verb'obj-'\{\verb'y' or \verb'm'\}.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update([mkc(x) for x in compilation_units['library_units']])
  append_info(recon_info, r"Library compilation units", r"From \verb'lib-'\{\verb'y' or \verb'm'\}.")
  append_recon_data(recon_data, len(everycfile))


  everycfile.difference_update([mkc(x) for x in compilation_units['unconfigurable_units']])
  append_info(recon_info, r"Unconfigurable units", r"No configuration variables enable them.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update([x + ".c" for x in compilation_units['hostprog_units']])
  append_info(recon_info, r"Host programs", r"\verb'hostprogs-'\{\verb'y' or \verb'm'\}, \verb'host-progs', or \verb'always' define programs used during build.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update([mkc(x) for x in compilation_units['extra_targets']])
  append_info(recon_info, r"Extra targets", r"\verb'extra-y' defines objects built but not part of the kernel.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update([mkc(x) for x in compilation_units['clean_files']])
  append_info(recon_info, r"", r"")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update([mkc(x) for x in compilation_units['c_file_targets']])
  append_info(recon_info, r"", r"")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set([c for c in everycfile if
                                    c.startswith("Documentation/") or
                                    c.startswith("samples/") or
                                    c.startswith("scripts/") or
                                    c.startswith("tools/")]))
  append_info(recon_info, r"From non-kbuild directories", r"\verb'Documentation/', \verb'samples/', \verb'scripts/', \verb'tools/'")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set([c for c in everycfile if
                                    re.match("arch/.*/boot/", c) != None or
                                    re.match("arch/.*/tools/", c) != None ]))
  append_info(recon_info, r"Architecture-specific tools", r"Tools and boot code in the \verb'arch/' subdirectories.")
  append_recon_data(recon_data, len(everycfile))

  compilation_units['offsets_files'].add('arch/x86/um/user-offsets.c')
  everycfile.difference_update([mkc(x) for x in compilation_units['offsets_files']])
  append_info(recon_info, r"ASM offsets files", r"Per-architecture files used to generate asm-offsets.h.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(compilation_units['included_c_files'])
  append_info(recon_info, r"Included C files", r"\verb'.c' Included in other C files instead of compiled independently.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set(explanations['helpers']))
  append_info(recon_info, r"Helper programs", r"Test code, templates, generators.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(compilation_units['unidentified_skeleton_c_files'])
  append_info(recon_info, r"Skeleton files", r"Examples files for drivers.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(explanations['staging'])
  append_info(recon_info, r"Staging compilation units", r"Pending drivers that may not be completely integrated into Kbuild.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set(explanations['orphaned']))
  append_info(recon_info, r"Orphaned compilation units", r"Manually verified files not referenced by Kbuild.")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set([c for c in everycfile if
                                    c.startswith("arch/xtensa/platforms") or # calls external shell
                                    c.startswith("arch/x86/realmode/rm") or # creates realmode.bin via conventional make target, included in .S file
                                    c.startswith("arch/um/sys-ppc") or # not compiled via Kbuild
                                    c.startswith("arch/um/sys-ia64") # not compiled via Kbuild
                                ]))
  append_info(recon_info, r"Other non-Kbuild", r"Real-mode and user-mode Linux not defined in Kbuild")
  append_recon_data(recon_data, len(everycfile))

  everycfile.difference_update(set(explanations['make_target']))
  append_info(recon_info, r"Make targets", r"Compilation units made by make targets rather than adding to \verb'obj-'\{\verb'y' or \verb'm'\}.")
  append_recon_data(recon_data, len(everycfile))

  # for f in sorted(everycfile):
  #   print f

  print(r"""
  \begin{table}
  \begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r }
  %% \textbf{Type of C File} & \textbf{Description} & \textbf{Count} & \textbf{Remaining} \\
  %% \textbf{Type of C File} & \textbf{Description} & \textbf{Count} \\
  \textbf{Type of C File} & \textbf{Count} \\
  \hline  
  """)

  total = 0
  lines = 0
  for n, d, c, r in zip(recon_info[0::2], recon_info[1::2], recon_data[0::2], recon_data[1::2]):
      count = kmaxdata.format_number(c)
      # if n == "TOTAL":
      #     count = "--"
      # print r"%s & %s & %s & %s \\" % (n, d, count, kmaxdata.format_number(r))
      if lines == 1:
          print(r"\multicolumn{2}{l}{\emph{Found by Kmax}} \\")
      if lines == 6:
          print(r"\multicolumn{2}{l}{\emph{Found by hand or additional scripts}} \\")
      if n != "TOTAL":
          # print r"\hspace{1.5em} %s & %s & %s \\" % (n, d, count)
          print(r"\hspace{1em} %s & %s \\" % (n, count))
          total += c
      # else:
      #     total = count
      # if n == "TOTAL":
      #     print "\hline"
      lines += 1
  print("\hline")
  print(r"TOTAL C FILES & %s \\" % (kmaxdata.format_number(total)))
  print("\hline")
  print("\hline")
  print(r"All C files in source tree & %s \\" % kmaxdata.format_number(recon_data[0]))

  print(r"""
  \end{tabular*}
  \caption{Reconciling C files Linux v3.19 source tree with Kmax's
  compilation units.}
  \label{table:cfiles}
  \end{table}
  """)
