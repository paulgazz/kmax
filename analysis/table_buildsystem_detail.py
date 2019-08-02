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
from collections import defaultdict
import cPickle as pickle
import locale
import kmaxdata
import numpy

outformats = [ 'tex', 'csv', 'x86' ]

# if len(sys.argv) < 3:
#   sys.stderr.write("USAGE: %s tex|csv|x86 buildsystem_1 buildsystem_2 ...\n" % (os.path.basename(sys.argv[0])))
#   exit(1)

# outformat = sys.argv[1]
# datafiles = sys.argv[2:]

outformat = 'tex'
version = "3.19"
version = "4.13"
version = "4.17.6"
datafiles = kmaxdata.buildsystem_datafiles(version)

if outformat not in outformats:
  print "output format not supported.  supported formats: %s" % (", ".join(outformats),)
  exit(1)

if outformat == "tex" or outformat == "x86":
  format_number = lambda number: locale.format("%d", number, grouping=True)
  format_range = lambda numbers: " & ".join(numbers)
elif outformat == "csv":
  format_number = lambda number: str(number)
  format_range = lambda numbers: ",".join(numbers)

if outformat == "tex":
  print "%% program:", os.path.basename(sys.argv[0])
  print "%% data files:", " ".join(datafiles)
elif outformat == "csv":
  print "Version,Kconfig files,Kconfig files (min),Kconfig files (max),Kbuild files,Kbuild files (min),Kbuild files (max),Configuration variables,Configuration variables (min),Configuration variables (max),Compilation units,Compilation units (min),Compilation units (max),Architectures"

locale.setlocale(locale.LC_ALL, 'en_US.utf8')

# Read pickled data object
allversionsdata = defaultdict(dict)
for datafile in datafiles:
  with open(datafile, "rb") as f:
    buildsystemdata = pickle.load(f)
    allversionsdata[buildsystemdata.version][buildsystemdata.arch] = buildsystemdata

if len(allversionsdata.keys()) == 0:
  sys.stderr.write("no data found in the datafiles given\n" % (version))
  exit(1)

for version in allversionsdata.keys():
  buildsystemdata = allversionsdata[version]

  # Compute totals
  alldirs = set()
  kconfig_files = set()
  config_vars = set()
  compilation_units = defaultdict(set)

  for arch in buildsystemdata.keys():
    alldirs.update(buildsystemdata[arch].alldirs)
    kconfig_files.update(buildsystemdata[arch].kconfig_files)
    config_vars.update(buildsystemdata[arch].config_vars)
    for k in buildsystemdata[arch].compilation_units.keys():
      compilation_units[k].update(buildsystemdata[arch].compilation_units[k])

  kbuild_files = compilation_units['subdirectory']
  c_compilation_units = compilation_units['compilation_units']

  # # Print totals table in latex
  # print r"""
  # \begin{table}
  # \begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r}
  # \textbf{} & \textbf{Count} \\
  # \hline
  # Kconfig files & %s \\
  # Kbuild files & %s \\
  # Configuration variables & %s \\
  # Compilation units & %s \\
  # \end{tabular*}
  # \caption{Types of compilation units specified by Kbuild files.}
  # \label{table:buildsystem_total}
  # \end{table}
  # """ % (format_number(len(kconfig_files)),
  #        format_number(len(kbuild_files)),
  #        format_number(len(config_vars)),
  #        format_number(len(c_compilation_units)))

  # Compute per-architecture percentiles
  percentiles = [0, 100]

  size_alldirs = [len(buildsystemdata[arch].alldirs) for arch in buildsystemdata.keys()]
  p_alldirs = format_range([str(numpy.percentile(size_alldirs, p)) for p in percentiles])

  size_kconfig_files = [len(buildsystemdata[arch].kconfig_files) for arch in buildsystemdata.keys()]
  p_kconfig_files = format_range([str(format_number(numpy.percentile(size_kconfig_files, p))) for p in percentiles])

  size_config_vars = [len(buildsystemdata[arch].config_vars) for arch in buildsystemdata.keys()]
  p_config_vars = format_range([str(format_number(numpy.percentile(size_config_vars, p))) for p in percentiles])

  size_compilation_units = defaultdict(list)
  p_compilation_units = defaultdict(str)

  for arch in buildsystemdata.keys():
    for k in buildsystemdata[arch].compilation_units.keys():
      size_compilation_units[k].append(len(buildsystemdata[arch].compilation_units[k]))

  for k in size_compilation_units.keys():
    p_compilation_units[k] = format_range([format_number(numpy.percentile(size_compilation_units[k], p)) for p in percentiles])

  num_archs = len(buildsystemdata.keys())

  # count shared compilations, arch-dir units, and non-arch-dir arch-units

  # get all compilation units
  allconfigs = set()
  allunits = set()
  archunits = defaultdict(set)
  for arch in buildsystemdata.keys():
    allconfigs.update(buildsystemdata[arch].config_vars)
    allunits.update(buildsystemdata[arch].compilation_units['compilation_units'])
    allunits.update(buildsystemdata[arch].compilation_units['library_units'])
    archunits[arch].update(buildsystemdata[arch].compilation_units['compilation_units'])
    archunits[arch].update(buildsystemdata[arch].compilation_units['library_units'])

  shared_units = set(allunits)
  archdir_units = [x for x in set(allunits) if x.startswith("arch/")]
  for arch in archunits.keys():
    shared_units.intersection_update(archunits[arch])
  shared_configs = set(allconfigs)
  for arch in archunits.keys():
    shared_configs.intersection_update(buildsystemdata[arch].config_vars)

  minunits = min([len(archunits[x]) for x in archunits.keys()])
  maxunits = max([len(archunits[x]) for x in archunits.keys()])
  minconfigs = min([len(buildsystemdata[x].config_vars) for x in buildsystemdata.keys()])
  maxconfigs = max([len(buildsystemdata[x].config_vars) for x in buildsystemdata.keys()])

  print r"""
\begin{table}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r}
\textbf{Metric} & \textbf{Count} \\
\hline
"""
  print r"Total compilation units & %s\\" % (format_number(len(allunits)))
  print r"\hspace{1em}Shared compilation units & %s\\" % (format_number(len(shared_units)))
  print r"\hspace{1em}Architecture-specific units in \verb'arch/' directories & %s\\" % (format_number(len(archdir_units)))
  print r"\hspace{1em}Architecture-specific units in common directories & %s\\" % (format_number(len(allunits) - len(shared_units) - len(archdir_units)))
  print r"\hline"
  print r"Total configuration variables & %s\\" % (format_number(len(allconfigs)))
  print r"\hspace{1em}Shared & %s\\" % (format_number(len(shared_configs)))
  print r"\hspace{1em}Architecture-specific & %s\\" % (format_number(len(allconfigs) - len(shared_configs)))
  print r"\hline"
  print r"Per-architecture compilation units & \\"
  print r"\hspace{1em}Minimum & %s \\" % (format_number(minunits))
  print r"\hspace{1em}Maximum & %s \\" % (format_number(maxunits))
  print r"\hline"
  print r"Per-architecture configuration variables & \\"
  print r"\hspace{1em}Minimum & %s \\" % (format_number(minconfigs))
  print r"\hspace{1em}Maximum & %s \\" % (format_number(maxconfigs))

  print r"""
\end{tabular*}

\caption{Linux v3.19 build system metrics broken out by
architecture-sharing.}

\label{table:buildsystem}
\end{table}
    """

  # print sorted(size_alldirs)
  # print p_alldirs
  # print sorted(size_kconfig_files)
  # print p_kconfig_files
  # print sorted(size_config_vars)
  # print p_config_vars
  # print size_compilation_units
  # print p_compilation_units

  # Print per-architecture data table in latex
  print r"""
  \begin{table}
  \begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r}
  \textbf{} & \textbf{Percentiles (min, max} \\
  \hline
  Kconfig files & %s \\
  Kbuild files & %s \\
  Configuration variables & %s \\
  Compilation units & %s \\
  \end{tabular*}
  \caption{Types of compilation units specified by Kbuild files.}
  \label{table:buildsystem_perarch}
  \end{table}
  """ % (p_kconfig_files,
         p_compilation_units["subdirectory"],
         p_config_vars,
         p_compilation_units["compilation_units"])

  print r"""
# arch, config_vars
"""
  for arch in buildsystemdata.keys():
    print arch, len(buildsystemdata[arch].config_vars)

  if outformat == "x86":
    x86_kbuild_files = format_number(len(buildsystemdata['x86'].compilation_units['subdirectory']))
    x86_kconfig_files = format_number(len(buildsystemdata['x86'].kconfig_files))
    x86_config_vars = format_number(len(buildsystemdata['x86'].config_vars))
    x86_compilation_units = format_number(len(buildsystemdata['x86'].compilation_units['compilation_units']))
    # Print combined table in latex
    print "%% version: ", version
    print r"""
\begin{table}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r | r | r r}
\textbf{} & \textbf{Total} & \textbf{x86} & \textbf{Min} & \textbf{Max} \\
\hline
Kconfig files & %s & %s & %s \\
Kbuild files & %s & %s & %s \\
Configuration vars & %s & %s & %s \\
Compilation units & %s & %s & %s \\
Architectures & %s & & & \\
\end{tabular*}
\caption{The size of the build system in terms of its kconfig files,
kbuild files, configuration variables, and compilation units.  The
minimum and maximum per-architecture numbers are compared with x86.}
\label{table:buildsystem}
\end{table}
    """ % (format_number(len(kconfig_files)),
           x86_kconfig_files,
           p_kconfig_files,
           format_number(len(kbuild_files)),
           x86_kbuild_files,
           p_compilation_units["subdirectory"],
           format_number(len(config_vars)),
           x86_config_vars,
           p_config_vars,
           format_number(len(c_compilation_units)),
           x86_compilation_units,
           p_compilation_units["compilation_units"],
           format_number(num_archs))

  elif outformat == "tex":
    # Print combined table in latex
    print "%% version: ", version
    print r"""
\begin{table}
\begin{tabular*}{\columnwidth}{@{\extracolsep{\fill}} l r r r}
\textbf{} & \textbf{Total} & \multicolumn{2}{r}{\textbf{Per-Architecture}} \\
          &                & Min & Max \\
\hline
Kconfig files & %s & %s \\
Kbuild files & %s & %s \\
Compilation units & %s & %s \\
allconfigs & %s & \\
allunits & %s & \\
arch-specific units & %s & \\
arch-specific units, archdir & %s & \\
shared units & %s & \\
Configuration variables & %s & %s \\
Architectures & %s \\
\end{tabular*}
\caption{The scale of the build system and the kernel as shown by
kconfig files, kbuild files, configuration variables, and compilation
units.}
\label{table:buildsystem}
\end{table}
    """ % (format_number(len(kconfig_files)),
           p_kconfig_files,
           format_number(len(kbuild_files)),
           p_compilation_units["subdirectory"],
           format_number(len(c_compilation_units)),
           p_compilation_units["compilation_units"],
           format_number(len(allconfigs)),
           format_number(len(allunits)),
           format_number(len(allunits) - len(shared_units) - len(archdir_units)),
           format_number(len(archdir_units)),
           format_number(len(shared_units)),
           format_number(len(config_vars)),
           p_config_vars,
           format_number(num_archs))

  elif outformat == "csv":
    print "%s,%s,%s,%s,%s,%s,%s,%s,%s,%s" % (version,
      format_number(len(kconfig_files)),
      p_kconfig_files,
      format_number(len(kbuild_files)),
      p_compilation_units["subdirectory"],
      format_number(len(config_vars)),
      p_config_vars,
      format_number(len(c_compilation_units)),
      p_compilation_units["compilation_units"],
      format_number(num_archs))
    
