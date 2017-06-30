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

import sys
import os
import glob
from collections import defaultdict
import cPickle as pickle
import locale
import kmaxdata
import numpy

versions = [ "3.19", "2.6.33.3" ]

print "%% program:", os.path.basename(sys.argv[0])

if len(sys.argv) > 1:
  do_units = sys.argv[1] == "units"
else:
  do_units = False

locale.setlocale(locale.LC_ALL, 'en_US.utf8')

def remus(s):
  # remove underscores and path separators from each element in the
  # set, because golem replaces path separators with underscores
  return set([x.translate(None, "_/-") for x in s])

compunits = {}
cunits = {}
libunits = {}
genunits = {}
asmunits = {}
noncunits = {}
nosource = {}
unconfig = {}
extra = {}
x86 = {}
kbuildminer_compunits = {}
kbuildminer_x86 = {}
kbuildminer_compunits = {}
kbuildminer_libunits = {}
kbuildminer_asmunits = {}
kbuildminer_x86_missed = {}
kbuildminer_x86_misidentified = {}
golem_compunits = {}
golem_x86 = {}
golem_compunits = {}
golem_libunits = {}
golem_asmunits = {}
golem_x86_missed = {}
golem_x86_misidentified = {}
for version in versions:
  with open(kmaxdata.everycfile_datafile(version)) as f:
    everycfile = set([os.path.normpath(x.strip('\n')) for x in f.readlines()])

  datafiles = kmaxdata.buildsystem_datafiles(version)

  # Read pickled data object
  allbuildsystemdata = {}
  for datafile in datafiles:
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

  unconfig[version] = compilation_units["unconfigurable_units"]
  extra[version] = compilation_units["extra_targets"]

  cu1a = compilation_units['compilation_units'] | compilation_units['library_units']
  compunits[version] = cu1a
  if version == "3.19":
    sys.stderr.write("%d\n" % (len(compunits[version])))
    cu1 = cu1a.difference(compilation_units['library_units'])
    sys.stderr.write("%d\n" % (len(cu1)))
    libunits[version] = cu1a.intersection(compilation_units['library_units'])
    sys.stderr.write("%d\n" % (len(libunits[version])))

    # .c compilation units with corresponding C files
    cu2 = cu1.difference(set([ x[:-2] + ".o" for x in everycfile ]))
    sys.stderr.write("%d\n" % (len(cu2)))
    cunits[version] = cu1.intersection(set([ x[:-2] + ".o" for x in everycfile ]))
    sys.stderr.write("%d\n" % (len(cunits[version])))

    # print "dfjkldsjflkds:",cu1 - compilation_units['compilation_units']
    # print "dfjkldsjflkds:",compilation_units['compilation_units'] - cu1

    # print "a", len(everycfile)
    # tmp1 = everycfile & set([x[:-2] + ".c" for x in compilation_units['compilation_units']])
    # print "b", len(tmp1)
    # tmp2 = everycfile & set([x[:-2] + ".c" for x in compilation_units['library_units']])
    # tmp3 = set([x[:-2] + ".c" for x in compilation_units['library_units']]) - tmp2
    # print "c", len(tmp2)
    # print "d", len(tmp3)
    # # print "AAA"
    # # for x in sorted(tmp2):
    # #   print x
    # # print "BBB"
    # # for x in sorted(tmp3):
    # #   print x
    # tmp_path = "/mnt/wd20earx/paul/scratch/linux_instances/linuxCN0JkW"
    # tmp4 = set([x[:-2] + ".S" for x in tmp3])
    # tmp5 = set([x[:-2] + ".o" for x in tmp4 if not os.path.exists(os.path.join(tmp_path, x))])
    # print "e", len(tmp5)
    # print "CCC"
    # for x in sorted(tmp5):
    #   print x

    # generated .c files
    cu3 = cu2.difference(set([ x[:-2] + ".o" for x in compilation_units['generated_c_files'] ]))
    sys.stderr.write("%d\n" % (len(cu3)))
    genunits[version] = cu2.intersection(set([ x[:-2] + ".o" for x in compilation_units['generated_c_files'] ]))
    sys.stderr.write("%d\n" % (len(genunits[version])))

    # .S asm compilation units
    cu4 = cu3.difference(set([ x[:-2] + ".o" for x in compilation_units['asm_compilation_units'] ]) |
                         set(['arch/arm/crypto/aesbs-core.o'])) # .S_shipped
    sys.stderr.write("%d\n" % (len(cu4)))
    asmunits[version] = cu3.intersection(set([ x[:-2] + ".o" for x in compilation_units['asm_compilation_units'] ]) |
                                         set(['arch/arm/crypto/aesbs-core.o'])) # .S_shipped
    sys.stderr.write("%d\n" % (len(asmunits[version])))

    # other non-C kbuild compilation units
    cu5 = cu4.difference(set([ x for x in cu4 if x.startswith("firmware") and x.endswith(".gen.o") ]) | # firmware
                         set([ x for x in cu4 if x.endswith(".dtb.o") ])) # device tree blobs, loaded by bootloader
    sys.stderr.write("%d\n" % (len(cu5)))
    noncunits[version] = cu4.intersection(set([ x for x in cu4 if x.startswith("firmware") and x.endswith(".gen.o") ]) | # firmware
                                          set([ x for x in cu4 if x.endswith(".dtb.o") ])) # device tree blobs, loaded by bootloader
    sys.stderr.write("%d\n" % (len(noncunits[version])))

    # no source file of the same name
    no_source_files = set(['arch/metag/kernel/coremem.o', # obj-$(CONFIG_METAG_COREMEM)   += coremem.o
                           'arch/metag/kernel/suspend.o', # obj-$(CONFIG_METAG_SUSPEND_MEM)   += suspend.o
                           'arch/xtensa/kernel/xtensa-stub.o', # obj-$(CONFIG_KGDB) += xtensa-stub.o
                           'drivers/usb/phy/phy-samsung-usb.o', # obj-$(CONFIG_SAMSUNG_USBPHY)    += phy-samsung-usb.o

                              # # Math emulation code beyond the FRND is required for 712/80i and
                              # # other very old or stripped-down PA-RISC CPUs -- not currently supported

                              # obj-$(CONFIG_MATH_EMULATION)  += unimplemented-math-emulation.o
                           'arch/parisc/math-emu/unimplemented-math-emulation.o',

                              # obj-$(CONFIG_PPC_BOOK3E)  += tlb_low_$(CONFIG_WORD_SIZE)e.o
                           'arch/powerpc/mm/tlb_low_32e.o',
                           # obj-$(CONFIG_EFI_MIXED)   += efi_thunk_$(BITS).o
                           'arch/x86/platform/efi/efi_thunk_32.o',

                              # built by make targets
                           'arch/arm64/crypto/aes-glue-ce.o',
                           'arch/arm64/crypto/aes-glue-neon.o',
                           'arch/um/drivers/pcap.o',
                           'arch/um/drivers/vde.o',
                           'arch/m68k/68360/head.o',
                         ])
    cu6 = cu5.difference(no_source_files)
    sys.stderr.write("%d\n" % (len(cu6)))
    nosource[version] = cu5.intersection(no_source_files)
    sys.stderr.write("%d\n" % (len(nosource[version])))
    sys.stderr.write("%s\n" % (nosource[version]))

    # exit(1)

    # cu = compilation_units['compilation_units']

    # # C compilation units
    # cu.difference_update(set(['arch/arm64/crypto/aes-glue-ce.o',
    #                           'arch/arm64/crypto/aes-glue-neon.o',]))
    # cu.difference_update(set([ x[:-2] + ".o" for x in everycfile ]))

    # # generated c files
    # cu.difference_update(set([ x[:-2] + ".o" for x in compilation_units['generated_c_files'] ]))

    # # asm compilation units
    # cu.difference_update(set([ x[:-2] + ".o" for x in compilation_units['asm_compilation_units'] ]))
    # cu.difference_update(set(['arch/arm/crypto/aesbs-core.o'])) # .S_shipped

    # # non-C kbuild compilation units
    # cu.difference_update(set([ x for x in cu if x.startswith("firmware") and x.endswith(".gen.o") ]))  # firmware
    # cu.difference_update(set([ x for x in cu if x.endswith(".dtb.o") ])) # device tree blobs, loaded by bootloader

    # # no source file of the same name
    # cu.difference_update(set(['arch/metag/kernel/coremem.o', # obj-$(CONFIG_METAG_COREMEM)   += coremem.o
    #                           'arch/metag/kernel/suspend.o', # obj-$(CONFIG_METAG_SUSPEND_MEM)   += suspend.o
    #                           'arch/xtensa/kernel/xtensa-stub.o', # obj-$(CONFIG_KGDB) += xtensa-stub.o
    #                           'drivers/usb/phy/phy-samsung-usb.o', # obj-$(CONFIG_SAMSUNG_USBPHY)    += phy-samsung-usb.o

    #                           # # Math emulation code beyond the FRND is required for 712/80i and
    #                           # # other very old or stripped-down PA-RISC CPUs -- not currently supported

    #                           # obj-$(CONFIG_MATH_EMULATION)  += unimplemented-math-emulation.o
    #                           'arch/parisc/math-emu/unimplemented-math-emulation.o',

    #                           # obj-$(CONFIG_PPC_BOOK3E)  += tlb_low_$(CONFIG_WORD_SIZE)e.o
    #                           'arch/powerpc/mm/tlb_low_32e.o',
    #                           # obj-$(CONFIG_EFI_MIXED)   += efi_thunk_$(BITS).o
    #                           'arch/x86/platform/efi/efi_thunk_32.o',

    #                           # build by make targets
    #                           'arch/um/drivers/pcap.o',
    #                           'arch/um/drivers/vde.o',
    #                         ]))

    # for x in sorted(compilation_units['unmatched_units']):
    #   print x

    # print len(cu)
    # for x in sorted(cu):
    #   print x

    # exit(1)

  # if version == "2.6.33.3":
  #   for x in sorted(compilation_units['compilation_units']):
  #     print x

  x86[version] = set(allbuildsystemdata['x86'].compilation_units['compilation_units'] + allbuildsystemdata['x86'].compilation_units['library_units'])

  # KBuildMiner
  kbuildminer_datafiles = kmaxdata.kbuildminer_datafiles(version)
  kbuildminer_compunits[version] = set()
  kbuildminer_x86[version] = set()
  kbuildminer_compunits[version] = set()
  kbuildminer_libunits[version] = set()
  kbuildminer_asmunits[version] = set()
  for datafile in kbuildminer_datafiles:
    with open(datafile, "rb") as f:
      data = [x.strip('\n') for x in f.readlines()]
      kbuildminer_compunits[version].update(data)
      if "x86.txt" in datafile:
        kbuildminer_x86[version] = set([x[:-2] + '.o' for x in data])
  kbuildminer_compunits[version] = set([x[:-2] + '.o' for x in kbuildminer_compunits[version]])

  # GOLEM
  golem_datafiles = kmaxdata.golem_datafiles(version)
  golem_compunits[version] = set()
  golem_x86[version] = set()
  golem_compunits[version] = set()
  golem_libunits[version] = set()
  golem_asmunits[version] = set()
  for datafile in golem_datafiles:
    with open(datafile, "rb") as f:
      data = [x.strip('\n') for x in f.readlines()]
      # only show .c and .S files
      data = remus(set([ x for x in data if x.endswith('.c') or x.endswith('.S') or x.endswith('.o') ]))
      golem_compunits[version].update(data)
      if "x86.txt" in datafile:
        golem_x86[version] = set([x[:-2] + '.o' for x in data])
  golem_compunits[version] = set([x[:-2] + '.o' for x in golem_compunits[version]])

  kbuildminer_x86_missed[version] = x86[version] - kbuildminer_x86[version]
  kbuildminer_x86_misidentified[version] = kbuildminer_x86[version] - x86[version]
  golem_x86_missed[version] = remus(x86[version]) - remus(golem_x86[version])
  golem_x86_misidentified[version] = remus(golem_x86[version]) - remus(x86[version])


# for x in sorted(kbuildminer_x86_misidentified['3.19']):
#   print x
  
# print r"""
# \begin{table*}
# \begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l l r r | r r r r r r}
#               &                   &                      &                        & \multicolumn{6}{c}{\textbf{Compilation Units Breakdown}} \\
# \textbf{Name} & \textbf{Strategy} & \textbf{Found (x86)} & \textbf{Missing (x86)} & C & Library & Generated & ASM & Non-C & No Source \\
# \hline
# Kmax         & Configuration-preserving evaluator, python   & %s (%s) &  -- & %s & %s & %s & %s & %s & %s \\
# KbuildMiner  & Heuristic Kbuild parser, java/scala    & %s (%s) & %s (%s) & %s & %s & %s \\
# GOLEM        & Subset of configurations, python   & %s (%s) & %s (%s) & %s & %s & %s \\
# \end{tabular*}
# \caption{Comparison on Linux 3.19.}
# \label{table:comparison}
# \end{table*}

if do_units:
  print r"""
\begin{table}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r}
\textbf{Type of Unit} & \textbf{Count} \\
\hline
C files & %s \\
ASM files & %s \\
Library files & %s \\
Generated & %s \\
Other non-C files & %s \\
No corresponding source & %s \\
\hline
TOTAL UNITS        & %s \\
\end{tabular*}

\caption{The total number of compilation units found in Linux v3.19 by
Kmax with a breakdown by types of unit.}

\label{table:compunits}
\end{table}
""" % ( kmaxdata.format_number(len(cunits['3.19'])),
        kmaxdata.format_number(len(asmunits['3.19'])),
        kmaxdata.format_number(len(libunits['3.19'])),
        kmaxdata.format_number(len(genunits['3.19'])),
        kmaxdata.format_number(len(noncunits['3.19'])),
        kmaxdata.format_number(len(nosource['3.19'])),
        kmaxdata.format_number(len(compunits['3.19'])),
      )
  exit(0)

# print r"""
# \begin{table*}
# \begin{tabular*}{\textwidth}{@{\extracolsep{\fill}} l r | r r r r r r | r}
# %% \multicolumn{1}{l}{\multirow{2}{*}{\textbf{Tool}}} & \multicolumn{1}{c}{\multirow{2}{*}{\textbf{All}}} & \multicolumn{1}{c}{\multirow{2}{*}{\textbf{x86 Only}}} & \multicolumn{7}{c}{\textbf{Compilation Units by Kind}} \\
# %% & & & \multicolumn{1}{c}{\textbf{C Files}} & \multicolumn{1}{c}{\textbf{Library}} & \multicolumn{1}{c}{\textbf{Generated}} & \multicolumn{1}{c}{\textbf{ASM}} & \multicolumn{1}{c}{\textbf{Other Non-C}} & \multicolumn{1}{c}{\textbf{No Source}} & \multicolumn{1}c{\textbf{Misidentified}} \\

# %% & & & \multicolumn{6}{c}{\textbf{Compilation Units by Kind}} \\

# %% \textbf{Tool} & \multicolumn{1}{c}{\textbf{C Files}} & \multicolumn{1}{c}{\textbf{Library}} & \multicolumn{1}{c}{\textbf{Generated}} & \multicolumn{1}{c}{\textbf{ASM}} & \multicolumn{1}{c}{\textbf{Other Non-C}} & \multicolumn{1}{c}{\textbf{No Source}} & \multicolumn{1}{c}{\textbf{All}} \\
#  \textbf{Tool} & \textbf{TOTAL} & \textbf{C Files} & \textbf{Library} & \textbf{Generated} & \textbf{ASM} & \textbf{Other Non-C} & \textbf{No Source} & \textbf{Architectures} \\
# \hline
# Kmax         & %s & %s & %s & %s & %s & %s & %s & %s \\
# KbuildMiner  & %s & %s & %s & %s & %s & %s & %s & %s \\
# GOLEM        & %s & %s & %s & %s & %s & %s & %s & %s \\
# \end{tabular*}

# \caption{The total number of compilation units found in Linux v3.19 by
# each tool with a breakdown of the types of compilation units.  The
# final column shows how many architectures out of 30 were successfully
# processed by each.}

# \label{table:comparison}
# \end{table*}
# """ % ( kmaxdata.format_number(len(compunits['3.19'])),
#         # kmaxdata.format_number(len(x86['3.19'])),
#         kmaxdata.format_number(len(cunits['3.19'])),
#         kmaxdata.format_number(len(libunits['3.19'])),
#         kmaxdata.format_number(len(genunits['3.19'])),
#         kmaxdata.format_number(len(asmunits['3.19'])),
#         kmaxdata.format_number(len(noncunits['3.19'])),
#         kmaxdata.format_number(len(nosource['3.19'])),
#         kmaxdata.format_number(0),

#         kmaxdata.format_number(len(kbuildminer_compunits['3.19'])),
#         # kmaxdata.format_number(len(kbuildminer_x86['3.19'])),
#         # kmaxdata.format_number(len(compunits['3.19']) - len(kbuildminer_compunits['3.19'])),
#         # kmaxdata.format_number(len(x86['3.19']) - len(kbuildminer_x86['3.19'])),
#         kmaxdata.format_number(len(cunits['3.19'] & kbuildminer_compunits['3.19'])),
#         kmaxdata.format_number(len(libunits['3.19'] & kbuildminer_compunits['3.19'])),
#         kmaxdata.format_number(len(genunits['3.19'] & kbuildminer_compunits['3.19'])),
#         kmaxdata.format_number(len(asmunits['3.19'] & kbuildminer_compunits['3.19'])),
#         kmaxdata.format_number(len(noncunits['3.19'] & kbuildminer_compunits['3.19'])),
#         kmaxdata.format_number(len(nosource['3.19'] & kbuildminer_compunits['3.19'])),
#         # kmaxdata.format_number(len((kbuildminer_compunits['3.19'] - compunits['3.19']) & unconfig['3.19'])),
#         kmaxdata.format_number(0),

#         kmaxdata.format_number(len(golem_compunits['3.19'])),
#         # kmaxdata.format_number(len(golem_x86['3.19'])),
#         # kmaxdata.format_number(len(compunits['3.19']) - len(golem_compunits['3.19'])),
#         # kmaxdata.format_number(len(x86['3.19']) - len(golem_x86['3.19'])),
#         kmaxdata.format_number(len(remus(cunits['3.19']) & remus(golem_compunits['3.19']))),
#         kmaxdata.format_number(len(remus(libunits['3.19']) & remus(golem_compunits['3.19']))),
#         kmaxdata.format_number(len(remus(genunits['3.19']) & remus(golem_compunits['3.19']))),
#         kmaxdata.format_number(len(remus(asmunits['3.19']) & remus(golem_compunits['3.19']))),
#         kmaxdata.format_number(len(remus(noncunits['3.19']) & remus(golem_compunits['3.19']))),
#         kmaxdata.format_number(len(remus(nosource['3.19']) & remus(golem_compunits['3.19']))),
#         # kmaxdata.format_number(len((remus(golem_compunits['3.19']) - remus(compunits['3.19'])) & remus(unconfig['3.19'] | set(['drivers/video/logo/clut_vga16.o'])))),
#         kmaxdata.format_number(0),
#         )


print r"""
\begin{table}
"""

print r"""
\begin{subtable}{\columnwidth}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r r r}
\textbf{Tool} & \textbf{Units} & \textbf{C File Units} & \textbf{Archs Failed} \\
\hline
Kmax         & %s & %s & 0 \\
KbuildMiner  & %s & %s & 6 \\
GOLEM        & %s & %s & 0 \\
\end{tabular*}

\caption{The total number of compilation units found in Linux v3.19 by
each tool, the number of C file units, the number architectures the
tool failed to process.}

\label{table:comparison:comparison}
\end{subtable}
""" % ( kmaxdata.format_number(len(compunits['3.19'])),
        kmaxdata.format_number(len(cunits['3.19'])),

        kmaxdata.format_number(len(kbuildminer_compunits['3.19'])),
        kmaxdata.format_number(len(cunits['3.19'] & kbuildminer_compunits['3.19'])),

        kmaxdata.format_number(len(golem_compunits['3.19'])),
        kmaxdata.format_number(len(remus(cunits['3.19']) & remus(golem_compunits['3.19']))),
        )

# t = remus(golem_compunits['3.19'])
# t.difference_update(remus(cunits['3.19']))
# t.difference_update(remus(libunits['3.19']))
# t.difference_update(remus(genunits['3.19']))
# t.difference_update(remus(asmunits['3.19']))
# t.difference_update(remus(noncunits['3.19']))
# t.difference_update(remus(nosource['3.19']))

print r"""
\vspace{1em}
"""

print r"""
\begin{subtable}{\columnwidth}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r r r}
\textbf{Tool} & \textbf{Extracted} & \textbf{Misidentified} & \textbf{Found} \\
\hline
Kmax & %s & -- & %s \\
KBuildMiner & %s & %s & %s \\
GOLEM & %s & %s & %s \\
\end{tabular*}

\caption{A summary of previous work's precision in extracting
compilation units from the x86 version of Linux v3.19, with the number
compilation units misidentified for x86.}

\label{table:comparison:x86}
\end{subtable}
""" % ( kmaxdata.format_number(len(x86['3.19'])),
        kmaxdata.format_number(len(x86['3.19'])),
        kmaxdata.format_number(len(kbuildminer_x86['3.19'])),
        # kmaxdata.format_number(len(kbuildminer_x86_missed['3.19'])),
        # kmaxdata.format_number(len(kbuildminer_x86_misidentified['3.19']) - len(kbuildminer_x86['3.19'] - compunits['3.19'])),
        # kmaxdata.format_number(len(kbuildminer_x86_misidentified['3.19'] - compunits['3.19'])),
        kmaxdata.format_number(len(kbuildminer_x86_misidentified['3.19'])),
        kmaxdata.format_number(len(kbuildminer_x86['3.19']) - len(kbuildminer_x86_misidentified['3.19'])),
        kmaxdata.format_number(len(golem_x86['3.19'])),
        # kmaxdata.format_number(len(golem_x86_missed['3.19'])),
        kmaxdata.format_number(len(golem_x86_misidentified['3.19'])),
        # kmaxdata.format_number(len(remus(golem_x86_misidentified['3.19']) - remus(compunits['3.19']))),
        # kmaxdata.format_number(len(golem_x86['3.19']) - len(golem_x86_missed['3.19'])),
        kmaxdata.format_number(len(golem_x86['3.19']) - len(golem_x86_misidentified['3.19'])),
      )


print r"""
\vspace{1em}
"""

print r"""
\begin{subtable}{\columnwidth}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r r | r r}
\textbf{Tool} & \textbf{Units} & \textbf{Archs Failed} & \textbf{x86} & \textbf{Misidentified} \\
\hline
Kmax         & %s & 0 & %s & -- \\
KbuildMiner  & %s & 0 & %s & %s \\
GOLEM        & %s & 0 & %s & %s \\
\end{tabular*}
\caption{Comparison with Linux 2.6.33.3.}
\label{table:comparison:old}
\end{subtable}
""" % ( kmaxdata.format_number(len(compunits['2.6.33.3'])),
        kmaxdata.format_number(len(x86['2.6.33.3'])),
        kmaxdata.format_number(len(kbuildminer_compunits['2.6.33.3'])),
        kmaxdata.format_number(len(kbuildminer_x86['2.6.33.3'])),
        kmaxdata.format_number(len(kbuildminer_x86_misidentified['2.6.33.3'])),
        kmaxdata.format_number(len(golem_compunits['2.6.33.3'])),
        kmaxdata.format_number(len(golem_x86['2.6.33.3'])),
        kmaxdata.format_number(len(golem_x86_misidentified['2.6.33.3'])),
        )


print r"""
\caption{A comparison of tools running on Linux v3.19.}
\label{table:comparison}
\end{table}
"""


sys.stderr.write("[golem unconfig]\n")
for x in sorted((remus(golem_compunits['3.19']) - remus(compunits['3.19'])) & remus(unconfig['3.19'] | set(['drivers/video/logo/clut_vga16.o']))):
  sys.stderr.write("%s\n" % (x))

sys.stderr.write("[golem extra]\n")
for x in sorted((remus(golem_compunits['3.19']) - remus(compunits['3.19'])) & remus(extra['3.19'])):
  sys.stderr.write("%s\n" % (x))

sys.stderr.write("[kbuildminer unconfig]\n")
for x in sorted((kbuildminer_compunits['3.19'] - compunits['3.19']) & unconfig['3.19']):
  sys.stderr.write("%s\n" % (x))

sys.stderr.write("[kbuildminer extra]\n")
for x in sorted((kbuildminer_compunits['3.19'] - compunits['3.19']) & extra['3.19']):
  sys.stderr.write("%s\n" % (x))

# sys.stderr.write("unconfig and extra\n")
# for x in sorted(unconfig['3.19'] | extra['3.19']):
#   sys.stderr.write("%s\n" % (x))

# for x in sorted(remus(compunits['3.19'])):
#   print x
