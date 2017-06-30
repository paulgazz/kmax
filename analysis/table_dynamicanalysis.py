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
import locale
import subprocess

if len(sys.argv) < 2:
  print "USAGE: %s cppstats_datafile" % (sys.argv[0])
  exit(0)

cppstats_datafile = sys.argv[1]

percentiles = (.5, .9, 1)

data_def = [
  ('Macro definitions', 'summary_definitions', 2),
  ("Macro definitions contained in conditionals", 'summary_definitions', 3),
  ("Macro redefinitions", 'summary_redefinitions', 2),
  ("Macro invocations", 'summary_invocations', 2),
  ("Macro invocations with trimmed definition(s)", 'summary_invocations', 3),
  ("Hoisted function-like macro invocations", 'summary_hoisted_functions', 2),
  ("Nested macro invocations", 'summary_nested_invocations', 2),
  ("Token pasting", 'summary_paste', 2),
  ("Hoisted token pasting", 'summary_paste', 3),
  ("Stringification", 'summary_stringify', 2),
  ("Hoisted stringification", 'summary_stringify', 3),
  ("Includes", 'summary_include', 2),
  ("Computed includes", 'summary_include', 3),
  ("Hoisted includes", 'summary_include', 4),
  ("Hoisted includes, valid", 'summary_include', 5),
  ("Reincludes", 'summary_reinclude', 2),
  ("Conditionals", 'summary_conditionals', 2),
  ("Hoisted conditionals", 'summary_conditionals', 5),
  ("Max conditional depth", 'summary_conditionals', 4),
  ("Conditionals with nonboolean subexpression(s)", 'summary_conditionals', 3),
  ("Error directives", 'summary_error_directives', 2),
  ("C Statements and Declarations", 'summary_c_statements_and_declarations', 2),
  ("Conditionals Inside C Statements and Declarations", 'summary_c_statements_and_declarations', 3),
  ("Typedefs", 'summary_typedefs', 2),
  ("Typedef ambiguities", 'summary_typedef_ambiguities', 2), ]

title_row = [ "Field" ] + [ str(int(percentile * 100)) + 'th percentile' for percentile in percentiles ]
out_table = []

for field_name, row_name, col_num in data_def:
  out_row = [ field_name ]
  for percentile in percentiles:
    # pctl_name = str(int(percentile * 100)) + 'th percentile'
    command = 'percentile_summary.sh -q ' + str(percentile) + ' ' + cppstats_datafile + ' ' + row_name + ' ' + str(col_num)
    sys.stderr.write('%s\n' % (command))
    popen = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
    stdout_, stderr_ = popen.communicate()
    if popen.returncode == 0:
      result = stdout_.strip()
      # print '"' + field_name.replace(',', '') + ' ' + pctl_name + '",' + result
      out_row.append(result)
    else:
      out_row.append(None)
  out_table.append(out_row)

locale.setlocale(locale.LC_ALL, 'en_US.utf8')

def format_number(number):
  return locale.format("%d", number, grouping=True)


print "\t".join(title_row)

for row in out_table:
  print "\t".join([ row[0] ] + [ format_number(int(p)) for p in row[1:] ])
