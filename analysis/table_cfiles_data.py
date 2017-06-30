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
import cPickle as pickle
import locale
import kmaxdata
import numpy
import itertools
import re

version = "3.19"
datafiles = kmaxdata.buildsystem_datafiles(version)

print "%% program:", os.path.basename(sys.argv[0])
print "%% version: ", version
print "%% data files:", " ".join(datafiles)

locale.setlocale(locale.LC_ALL, 'en_US.utf8')

# Read pickled data object
allbuildsystemdata = {}
for datafile in datafiles:
  # if "x86" in datafile:
    with open(datafile, "rb") as f:
      buildsystemdata = pickle.load(f)
      if buildsystemdata.version == version:
        allbuildsystemdata[buildsystemdata.arch] = buildsystemdata

if len(allbuildsystemdata.keys()) == 0:
  sys.stderr.write("no data for version %s found in the datafiles given\n" % (version))
  exit(1)

# Compute totals
compilation_units = defaultdict(set)

for arch in allbuildsystemdata.keys():
  for k in allbuildsystemdata[arch].compilation_units.keys():
    compilation_units[k].update(allbuildsystemdata[arch].compilation_units[k])

with open(kmaxdata.everycfile_datafile(version)) as f:
  everycfile = set([os.path.normpath(x.strip('\n')) for x in f.readlines()])

# print r"""
# \begin{table*}
# \begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l r}
# \textbf{Type of Unit} & \textbf{Count} \\
# \hline  
# Compilation units & %s \\
# Composites & %s \\
# Libraries & %s \\
# Host programs & %s \\
# Extra targets & %s \\
# Clean files & %s \\
# Targets & %s \\
# \end{tabular*}
# \caption{Types of compilation units specified by Kbuild files.}
# \label{table:cfiles}
# \end{table*}
# """ % (kmaxdata.format_number(len(compilation_units['compilation_units'])),
#        kmaxdata.format_number(len(compilation_units['composites'])),
#        kmaxdata.format_number(len(compilation_units['library_units'])),
#        kmaxdata.format_number(len(compilation_units['hostprog_units'])),
#        kmaxdata.format_number(len(compilation_units['extra_targets'])),
#        kmaxdata.format_number(len(compilation_units['clean_files'])),
#        kmaxdata.format_number(len(compilation_units['c_file_targets'])))


# explanations for 3.19
explanations = {
  'orphaned':    [ 'arch/alpha/lib/stacktrace.c',
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
                   ],
  'helpers':     [ 'drivers/vhost/test.c', # test program
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
  'make_target': [ 'arch/tile/kernel/vdso/vgettimeofday.c', # make target of different name
                   'arch/arm64/crypto/aes-glue.c', # make target of different name
                   'arch/ia64/kernel/nr-irqs.c', # uses make target
                   ],
  'skeletons'  : list(compilation_units['unidentified_skeleton_c_files']),
  'staging'  : [ 'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1500.c',
                 'drivers/staging/comedi/drivers/addi-data/hwdrv_apci1564.c',
                 'drivers/staging/comedi/drivers/addi-data/hwdrv_apci3501.c',
                 '',
             ] + list(compilation_units['unidentified_staging_c_files']),
  'included_c_files'  : list(compilation_units['included_c_files']),
  }

explanations_table = [
  ("Orphans", r"No longer referenced", len(explanations['orphaned'])),
  ("Helpers", r"Helper programs and generators", len(explanations['helpers'])),
  ("Make targets", r"Built from make target instead of Kbuild syntax", len(explanations['make_target'])),
  ("Skeleton files", r"Example files", len(explanations['skeletons'])),
  ("Included C files", r"C files \#included in other compilation units", len(explanations['included_c_files'])),
  ("Staging drivers", r"Files orphaned in the driver staging directory", len(explanations['staging'])),
]

total_explanations = sum([x for _, _, x in explanations_table])

def chgext(filename, f, t):
  if filename.endswith(f):
    return filename[:-2] + t

def mkc(filename):
    return filename[:-2] + ".c"

def otoc(filename):
  return chgext(filename, ".o", ".c")

def otoS(filename):
  return chgext(filename, ".o", ".S")

def ctoo(filename):
  return chgext(filename, ".c", ".o")

# compilation_units['compilation_units'].difference_update([x[:-2] + ".o" for x in compilation_units['asm_compilation_units']])
# compilation_units['compilation_units'].difference_update([x[:-2] + ".o" for x in compilation_units['composites']])
# compilation_units['compilation_units'].difference_update([x[:-2] + ".o" for x in compilation_units['generated_c_files']])

# subdirectory = set(compilation_units['subdirectory'])
# for unit in compilation_units['compilation_units']:
#   subdirectory.add(os.path.dirname(unit))

# # all_c_files = set()
# # for subdir in subdirectory:
# #   all_c_files.update(glob.glob(os.path.join('/state/partition1/linux_instances/tmpnvyjWE', subdir, "*.c")))
# all_c_files = compilation_units['all_c_files']
# print len(all_c_files)
# print len(compilation_units['all_c_files'])
# print compilation_units['unidentified_c_files']

# test = set(compilation_units['compilation_units'])
# test.difference_update([x[:-2] + ".o" for x in compilation_units['all_c_files']])
# test.difference_update([x[:-2] + ".o" for x in compilation_units['unmatched_units']])
# # print (test)

explanations_sum = []
for key in explanations.keys():
  explanations_sum += explanations[key]

# s = set()
# s.update([otoc(x) for x in compilation_units['compilation_units']])
# s.update([otoc(x) for x in compilation_units['library_units']])
# s.update([otoc(x) for x in compilation_units['hostprog_units']])
# s.update([otoc(x) for x in compilation_units['unconfigurable_units']])
# s.update([otoc(x) for x in compilation_units['extra_targets']])
# s.update([otoc(x) for x in compilation_units['clean_files']])
# s.update([otoc(x) for x in compilation_units['offsets_files']])
# s.update([otoc(x) for x in compilation_units['included_c_files']])
# s.update([otoc(x) for x in compilation_units['c_file_targets']])
# s.update([otoc(x) for x in compilation_units['unidentified_staging_c_files']])
# s.update([otoc(x) for x in compilation_units['unidentified_skeleton_c_files']])
# sys.stderr.write("%d\n" % (len(s)))

# s.difference_update(compilation_units['all_c_files'])
# sys.stderr.write("%s\n" % (s))
# sys.stderr.write("%s\n" % (compilation_units['c_file_targets']))
# sys.stderr.write("%s\n" % (len(compilation_units['all_c_files'])))

# sys.stderr.write("all c file reconciliation\n")
# print len(everycfile)
# everycfile.difference_update(set([c for c in everycfile if
#                                   c.startswith("Documentation/") or
#                                   c.startswith("samples/") or
#                                   c.startswith("scripts/") or
#                                   c.startswith("tools/")]))
# print len(everycfile)
# everycfile.difference_update(set([c for c in everycfile if
#                                   re.match("arch/.*/boot/", c) != None or
#                                   re.match("arch/.*/tools/", c) != None ]))
# print len(everycfile)
# everycfile.difference_update(set([mkc(x) for x in compilation_units['compilation_units']]))
# print len(everycfile)
# everycfile.difference_update([mkc(x) for x in compilation_units['library_units']])
# print len(everycfile)
# everycfile.difference_update([mkc(x) for x in compilation_units['unconfigurable_units']])
# print len(everycfile)
# everycfile.difference_update([x + ".c" for x in compilation_units['hostprog_units']])
# print len(everycfile)
# everycfile.difference_update([mkc(x) for x in compilation_units['extra_targets']])
# print len(everycfile)
# # everycfile.difference_update([mkc(x) for x in compilation_units['clean_files']])
# # print len(everycfile)
# compilation_units['offsets_files'].add('arch/x86/um/user-offsets.c')
# everycfile.difference_update([mkc(x) for x in compilation_units['offsets_files']])
# print len(everycfile)
# # everycfile.difference_update([mkc(x) for x in compilation_units['c_file_targets']])
# # print len(everycfile)
# everycfile.difference_update(compilation_units['included_c_files'])
# print len(everycfile)
# everycfile.difference_update(set(explanations['orphaned']))
# print len(everycfile)
# everycfile.difference_update(set(explanations['helpers']))
# print len(everycfile)
# everycfile.difference_update(set(explanations['make_target']))
# print len(everycfile)
# everycfile.difference_update(compilation_units['unidentified_skeleton_c_files'])
# print len(everycfile)
# everycfile.difference_update(explanations['staging'])
# print len(everycfile)
# everycfile.difference_update(set([c for c in everycfile if
#                                   c.startswith("arch/xtensa/platforms") or # calls external shell
#                                   c.startswith("arch/x86/realmode/rm") or # creates realmode.bin via conventional make target, included in .S file
#                                   c.startswith("arch/um/sys-ppc") or # not compiled via Kbuild
#                                   c.startswith("arch/um/sys-ia64") # not compiled via Kbuild
#                               ]))
# print len(everycfile)
# for f in sorted(everycfile):
#   print f



def append_recon_data(l, v):
    sys.stderr.write("%d\n" % v)
    l.append(l[-1] - v)
    l.append(v)

def append_info(l, name, desc):
    l.append(name)
    l.append(desc)

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

# everycfile.difference_update([mkc(x) for x in compilation_units['clean_files']])
# append_info(recon_info, r"", r"")
# append_recon_data(recon_data, len(everycfile))

# everycfile.difference_update([mkc(x) for x in compilation_units['c_file_targets']])
# append_info(recon_info, r"", r"")
# append_recon_data(recon_data, len(everycfile))

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

print r"""
\begin{table}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r }
%% \textbf{Type of C File} & \textbf{Description} & \textbf{Count} & \textbf{Remaining} \\
%% \textbf{Type of C File} & \textbf{Description} & \textbf{Count} \\
\textbf{Type of C File} & \textbf{Count} \\
\hline  
"""

total = 0
lines = 0
for n, d, c, r in zip(recon_info[0::2], recon_info[1::2], recon_data[0::2], recon_data[1::2]):
    count = kmaxdata.format_number(c)
    # if n == "TOTAL":
    #     count = "--"
    # print r"%s & %s & %s & %s \\" % (n, d, count, kmaxdata.format_number(r))
    if lines == 1:
        print r"\multicolumn{2}{l}{\emph{Found by Kmax}} \\"
    if lines == 6:
        print r"\multicolumn{2}{l}{\emph{Found by hand or additional scripts}} \\"
    if n != "TOTAL":
        # print r"\hspace{1.5em} %s & %s & %s \\" % (n, d, count)
        print r"\hspace{1em} %s & %s \\" % (n, count)
        total += c
    # else:
    #     total = count
    # if n == "TOTAL":
    #     print "\hline"
    lines += 1
print "\hline"
print r"TOTAL C FILES & %s \\" % (kmaxdata.format_number(total))
print "\hline"
print "\hline"
print r"All C files in source tree & %s \\" % kmaxdata.format_number(recon_data[0])

print r"""
\end{tabular*}
\caption{Reconciling C files Linux v3.19 source tree with Kmax's
compilation units.}
\label{table:cfiles}
\end{table}
"""
exit(0)
# s = set(compilation_units['all_c_files'])
# sys.stderr.write("%d\n" % (len(s)))
# s.difference_update([otoc(x) for x in compilation_units['compilation_units']])
# s.difference_update([otoc(x) for x in compilation_units['library_units']])
# s.difference_update([otoc(x) for x in compilation_units['composites']])
# s.difference_update([otoc(x) for x in compilation_units['generated_c_files']])
# s.difference_update([otoc(x) for x in compilation_units['unidentified_staging_c_files']])
# s.difference_update([otoc(x) for x in compilation_units['unidentified_skeleton_c_files']])
# s.difference_update([otoc(x) for x in compilation_units['unconfigurable_units']])
# s.difference_update([otoc(x) for x in compilation_units['hostprog_units']])
# s.difference_update([otoc(x) for x in compilation_units['extra_targets']])
# s.difference_update([otoc(x) for x in compilation_units['clean_files']])
# s.difference_update([otoc(x) for x in compilation_units['offsets_files']])
# s.difference_update([otoc(x) for x in compilation_units['c_file_targets']])
# s.difference_update([otoc(x) for x in explanations_sum])
# sys.stderr.write("%d\n" % (len(s)))
# sys.stderr.write("%d\n" % (len(compilation_units['compilation_units'])))
# sys.stderr.write("%d\n" % (len(compilation_units['asm_compilation_units'])))
# sys.stderr.write("%d\n" % (len(compilation_units['library_units'])))
# sys.stderr.write("%s\n" % (s))

table_data = [
  ("Built-ins", r"\verb'obj-'\{\verb'y' or \verb'm'\} define part of the kernel image.", len(compilation_units['compilation_units'])),
  ("Composites", r"\verb'compositename-'\{\verb'y' or \verb'objs'\} define several units linked together.", len(compilation_units['composites'])),
  ("Libraries", r"\verb'lib-'\{\verb'y' or \verb'm'\} define compile-time libraries.", len(compilation_units['library_units'])),
  ("Host programs", r"\verb'hostprogs-'\{\verb'y' or \verb'm'\}, \verb'host-progs', or \verb'always' define programs used during build.", len(compilation_units['hostprog_units'])),
  ("Extra targets", r"\verb'extra-y' defines objects built but not part of the kernel.", len(compilation_units['extra_targets'])),
  ("Clean files", r"\verb'clean-files' defines generated files to be cleaned by kbuild.", len(compilation_units['clean_files'])),
  ("Targets", r"\verb'targets' defines Kbuild's internal list of targets.", len(compilation_units['c_file_targets'])),
  ("Manually identified", r"Not automatically found from Kbuild files", total_explanations),
]

total = sum([x for _, _, x in table_data])

print r"""
\begin{table*}
\begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l l r}
\textbf{Type of Unit} & \textbf{Description} & \textbf{Count} \\
\hline  
"""

for name, desc, count in table_data:
  print r'%s & %s & %s \\' % (name, desc, kmaxdata.format_number(count))

print r"""
%% \hline
%% TOTAL         &                                   &                & %s \\
%% \# of C Files &                                   &                & %s \\

\end{tabular*}
\caption{Types of compilation units specified by Kbuild files.}
\label{table:cfiles}
\end{table*}
""" % (kmaxdata.format_number(total - len(compilation_units['asm_compilation_units'])),
       kmaxdata.format_number(len(compilation_units['all_c_files'])))

print r"""
\begin{table*}
\begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l l r}
\textbf{Type of Unit} & \textbf{Reason} & \textbf{Count} \\
\hline  
"""

for name, desc, count in explanations_table:
  print r'%s & %s & %s \\' % (name, desc, kmaxdata.format_number(count))

print r"""
\hline
TOTAL & & %s \\
\end{tabular*}
\caption{Compilation units orphaned or otherwise not referenced by
Kbuild files.}
\label{table:cfiles_orphaned}
\end{table*}
""" % (total_explanations)


unidentified_c_files = set(compilation_units['unidentified_c_files'])
sys.stderr.write(str(len(unidentified_c_files)) + "\n")

# account for compilation units identified in other architectures
for key in [key for key in compilation_units.keys() if key != 'unidentified_c_files']:
  unidentified_c_files.difference_update([x[:-2] + ".c" for x in compilation_units[key]])
sys.stderr.write(str(len(unidentified_c_files)) + "\n")

# remove those that have manually-found explanations
for key in explanations.keys():
  unidentified_c_files.difference_update(explanations[key])
sys.stderr.write(str(len(unidentified_c_files)) + "\n")

for file in unidentified_c_files:
  sys.stderr.write(file + "\n")
