#!/usr/bin/env python

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
import operator
import re
import argparse

from pymake import parser, parserdata, data, functions
from collections import defaultdict

force_off = defaultdict(bool)
inconditional = 0
inconditionaloff = 0
reassignments = 0

var_pattern = re.compile("'CONFIG_[^']+'")
tristate = re.compile("^y$|^m$|^n$|^CONFIG_")

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Find Kbuild Makefile patterns needed for KMax to extract compilation units.
""",
    epilog="""\
ref CONFIG_VAR means a conditional contains a config var
off CONFIG_VAR
undef CONFIG_VAR
on CONFIG_VAR means a single-branch conditional testing whether the
              variable is y or m, is not n, or is defined.
def CONFIG_VAR
ass stem CONFIG_VAR means stem-CONFIG_VAR is assigned
rea stem CONFIG_VAR means stem-CONFIG_VAR is reassigned
reassigns stem CONFIG_VAR CONFIG_VAR ... lists reassignments in order
"""
    )
argparser.add_argument('makefiles', metavar="Makefile", nargs='*',
                       type=str, default=sys.stdin, help="""\
The name of a Linux Makefile or subdir.  Otherwise read from stdin.""")

args = argparser.parse_args()

# Print any configuration variables referenced in this conditional
# expression.
def getrefs(c):
    global inconditional
    global inconditionaloff
    global reassignments

    for m in var_pattern.findall(str(c)):
        var = m[1:-1]
        inconditionaloff += 1
        inconditional += 1
        force_off[var] = True
        return "ref " + var

# Look for configuration variables used in conditionals
def process_conditionalblock(s):
    global inconditional
    global inconditionaloff
    global reassignments

    emit = True
    # If there is just one branch and it tests that a
    # configuration variable is turned off or undefined, then
    # we need to run make with the variable both on and off.
    if len(s._groups) == 1:
        c, _ = s._groups[0]
        if isinstance(c, parserdata.EqCondition):
            varref, _ = c.exp1[0]
            rhs, _ = c.exp2[0]
            if isinstance(varref, functions.VariableRef) \
                    and varref.vname.s.startswith('CONFIG_'):
                var = varref.vname.s
                if rhs == 'y' and not c.expected \
                        or rhs == 'm' and not c.expected \
                        or rhs == 'n' and c.expected:
                    print "off", var
                    inconditionaloff += 1
                    inconditional += 1
                    force_off[var] = True
                    emit = False
                elif rhs == 'y' and c.expected \
                        or rhs == 'm' and c.expected \
                        or rhs == 'n' and not c.expected:
                    print "on", var
                    inconditional += 1
                    emit = False
        elif isinstance(c, parserdata.IfdefCondition):
            if isinstance(c.exp, data.StringExpansion) \
                    and c.exp.s.startswith('CONFIG_'):
                var = c.exp.s
                if not c.expected:
                    print "undef", var
                    inconditionaloff += 1
                    inconditional += 1
                    force_off[var] = True
                else:
                    print "def", var
                    inconditional += 1
                emit = False
    for b in s._groups:
        c, s = b
        if emit:
            refs = getrefs(c)
            if refs != None:
                print refs
        process_statements(s)

# Track variables with the "stem-suffix" pattern
assigned = defaultdict(int)
reassigned = defaultdict(list)

# finds variables of the prefix-suffix pattern.  returns (prefix,
# suffix).  If it's not a kbuild var, suffix will be null.  Suffix
# will either be y, n, m or a CONFIG_ var.
def get_kbuild_var(n):
    global inconditional
    global inconditionaloff
    global reassignments

    if isinstance(n, data.StringExpansion):
        prefix, sep, suffix = n.s.rpartition('-')
        if len(sep) > 0 and tristate.match(suffix):
            return prefix, suffix
        else:
            return prefix, None
    elif isinstance(n, data.Expansion):
        if len(n) == 2:
            prefixsep = n[0][0]
            if isinstance(prefixsep, str) and prefixsep[-1] == '-':
                suffix = n[1][0]
                if isinstance(suffix, functions.VariableRef):
                    return prefixsep[:-1], suffix.vname.s
    return None, None

def process_setvariable(s):
    global inconditional
    global inconditionaloff
    global reassignments

    var, suffix = get_kbuild_var(s.vnameexp)
    if suffix != None:
        if s.token == ":=":
            if assigned[var] > 0:
                print "rea", var, suffix
            else:
                print "ass", var, suffix
            reassigned[var].append(suffix)
            assigned[var] += 1

# Print any configuration variables that either need to be turned off
# or are referenced in conditionals expressions.
def process_statements(stmts):
    global inconditional
    global inconditionaloff
    global reassignments

    for s in stmts:
        if isinstance(s, parserdata.ConditionBlock):
            process_conditionalblock(s)
        elif isinstance(s, parserdata.SetVariable):
            process_setvariable(s)

makefiles = []
for f in args.makefiles:
    if os.path.isdir(f):
        subdir = f
        f = os.path.join(subdir, "Kbuild")
        if not os.path.isfile(f):
            f = os.path.join(subdir, "Makefile") 
    if not os.path.isfile(f):
        print f, "not found"
    else:
        makefiles.append(open(f, "rU"))

for f in makefiles:
    s = f.read()
    f.close()
    stmts = parser.parsestring(s, f.name)
    process_statements(stmts)

for var in reassigned.keys():
    if assigned[var] > 1:
        reassignments += 1
        for r in [ reassigned[var][:i] for i in range(1, len(reassigned[var]) + 1) ]:
            r = [ x for x in r if x != 'y' and x != 'n' and x != 'm' ]
            if len(r) > 0:
                foff = ' '.join(r)
                print 'reassigns', var, foff
                if not force_off[foff]:
                    force_off[foff] = True

for foff in [ x for x in force_off.keys() if force_off[x] ]:
    print 'force_off', foff

print "count_inconditional", inconditional
print "count_inconditionaloff", inconditionaloff
print "count_reassignments", reassignments
