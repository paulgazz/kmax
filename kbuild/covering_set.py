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

# Given a Kbuild Makefile, emit a set of configurations that cover all
# compilation units in the Makefile.

import sys
import os
import operator
import re
import argparse
import pycudd
import _pycudd
import tempfile
import cPickle as pickle
import re

from pymake import parser, parserdata, data, functions
from collections import defaultdict, namedtuple
from cStringIO import StringIO

argparser = argparse.ArgumentParser(
    formatter_class=argparse.RawDescriptionHelpFormatter,
    description="""\
Find a set of configurations that covers all configuration variables in the
given Kbuild Makefile.
    """,
    epilog="""\
    """
    )
argparser.add_argument('makefile',
                       type=str,
                       help="""the name of a Linux Makefile or subdir""")
argparser.add_argument('-t',
                       '--table',
                       action="store_true",
                       help="""show symbol table entries""")
argparser.add_argument('-v',
                       '--variable',
                       type=str,
                       help="""show symbol table entries for VARIABLE only""")
argparser.add_argument('-n',
                       '--naive-append',
                       action="store_true",
                       help="""\
use naive append behavior, which has more exponential explosion""")
argparser.add_argument('-g',
                       '--get-presence-conditions',
                       action="store_true",
                       help="""\
get presence conditions for each compilation units""")
argparser.add_argument('-r',
                       '--recursive',
                       action="store_true",
                       help="""\
recursively enter subdirectories""")
argparser.add_argument('-D',
                       '--define',
                       action='append',
                       help="""\
recursively enter subdirectories""")
argparser.add_argument('-p',
                       '--pickle',
                       action="store_true",
                       help="""\
pickle a tuple of two sets containing the compilation units and subdirectories \
respectively""")
argparser.add_argument('-C',
                       '--config-vars',
                       type=str,
                       help="""the name of a KConfigData file containing \
configuration variable data""")
argparser.add_argument('-b',
                       '--boot-strap',
                       action="store_true",
                       help="""\
Get the top-level directories from the arch-specifier Makefile""")
argparser.add_argument('-V',
                       '--verbose',
                       action="store_true",
                       help="""\
Increase the debugging output""")
args = argparser.parse_args()

debug_level = 1 # default to 1, can set to 0 for no debugging output
if (args.verbose):
    debug_level = 2
kconfigdata = None
all_config_var_names = None
boolean_config_var_names = None
nonboolean_config_var_names = None
if args.config_vars:
    with open(args.config_vars, 'rb') as f:
        kconfigdata = pickle.load(f)
        boolean_config_var_names = [ "CONFIG_" + c
                                     for c in kconfigdata.bool_vars ]
        nonboolean_config_var_names = [ "CONFIG_" + c
                                        for c in kconfigdata.nonbool_vars ]
        all_config_var_names = [ "CONFIG_" + c
                                        for c in kconfigdata.config_vars ]

class Flavor:
    RECURSIVE = 1
    SIMPLE = 2

VariableEntry = namedtuple('VariableEntry', 'value condition flavor')

class Variable(list):
    def __init__(self):
        list.__init__(self, [])
        # TODO figure out what to do with "override"

BooleanVariable = namedtuple('BooleanVariable', 'bdd index')

class Multiverse(list):
    """A list of (condition, definition) pairs."""

    def __init__(self, data=[]):
        list.__init__(self, data)

    def __repr__(self):
        return "<Multiverse>(%r)" % \
            ([(c, v) for c, v in self])

def fatal(msg, var=None):
    """Report internal error and exit."""
    sys.stderr.write("FATAL: " + str(msg) + ' ' + str(var) + '\n')
    exit(1)

def warn(msg, var=None):
    """Report warning"""
    sys.stderr.write("WARN: " + str(msg) + ' ' + str(var) + '\n')

def debug(level, *args):
    global debug_level
    if (level <= debug_level):
        sys.stderr.write(' '.join(map(lambda arg: str(arg), args)) + '\n')

# Placeholders for symbolic boolean operations
def conjunction(a, b):
    return a & b

def disjunction(a, b):
    return a | b

def negation(a):
    return ~a

def dedup_multiverse(multiverse):
    before = len(multiverse)
    value_map = {}
    for condition, value in multiverse:
        if value not in value_map:
            value_map[value] = condition
        else:
            value_map[value] = disjunction(value_map[value], condition)
    dedup = []
    for value, condition in value_map.iteritems():
        dedup.append( (condition, value) )
    after = len(dedup)
    if after < before:
        multiverse = Multiverse(dedup)
        # debug("dedup:",before,"to",after)
    return multiverse

def hasConfig():
    return all_config_var_names != None

def isBooleanConfig(name):
    if all_config_var_names != None and not isNonbooleanConfig(name):
        return name in all_config_var_names
    return False

def isNonbooleanConfig(name):
    if nonboolean_config_var_names != None:
        return name in nonboolean_config_var_names
    return False

class Kbuild:
    def __init__(self):
        # BDD engine
        self.mgr = pycudd.DdManager()
        self.mgr.SetDefault()

        # Boolean constants
        self.T = self.mgr.One()
        self.F = self.mgr.Zero()

        # Conditional symbol table for variables
        self.variables = defaultdict(
            lambda: [VariableEntry(None, self.T, Flavor.RECURSIVE)])
        # None means the variable is undefined. Variables are
        # recursively-expanded by default, e.g., when += is used on an
        # undefined variable.

        # Mapping of boolean variable names to BDD variable number.
        # Automatically increments the variable number.
        self.boolean_variables = defaultdict(
            lambda: BooleanVariable(self.mgr.IthVar(len(self.boolean_variables)),
                                    len(self.boolean_variables)))
        self.undefined_variables = set()

        # token presence conditions
        self.token_pc = {}

        # compilation unit presence conditions
        self.unit_pc = {}

        # subdir presence conditions
        self.subdir_pc = {}

        # composite presence conditions
        self.composite_pc = {}

    def print_variable(self, name, variable):
        print "VARIABLE:", name
        for value, condition, flavor in variable:
            print "  ---"
            print "  VALUE:", value
            print "  BDD:", self.bdd_to_str(condition)
            print "  FLAVOR:", flavor

    def print_variables_table(self, variables):
        for name in variables:
            self.print_variable(name, variables[name])
            print

    def add_definitions(self, defines):
        if defines == None:
            return
        for define in defines:
            name, value = define.split("=")
            self.add_variable_entry(name, self.T, '=', value)

    def get_defined(self, variable, expected):
        variable_name = "defined(" + variable + ")"
        if expected:
            return self.boolean_variables[variable_name].bdd
        else:
            return negation(self.boolean_variables[variable_name].bdd)

    def process_variableref(self, name):
        if name == 'BITS':
            # TODO get real entry from top-level makefiles
            return Multiverse([ (self.boolean_variables["BITS=32"].bdd, "32"),
                                (self.boolean_variables["BITS=64"].bdd, "64") ])
        # elif name == 'ARCH':
        #     # TODO user-defined
        #     return Multiverse([ (self.T, "x86") ])
        elif name == "CONFIG_WORD_SIZE":
            # TODO get defaults from Kconfig files
            return Multiverse([ (self.boolean_variables["CONFIG_WORD_SIZE=32"].bdd, "32"),
                                (self.boolean_variables["CONFIG_WORD_SIZE=64"].bdd, "64") ])
        elif name not in self.variables and name == "MMU":
            # TODO get globals from arch Makefiles
            is_defined = self.get_defined("CONFIG_MMU", True)
            not_defined = self.get_defined("CONFIG_MMU", False)

            return Multiverse([ (is_defined, ''),
                                (not_defined, '-nommu') ])
        elif isBooleanConfig(name) or not hasConfig() and name.startswith("CONFIG_"):
        # if (isBooleanConfig(name) or name.startswith("CONFIG_")) \
        #    and not isNonbooleanConfig(name):
            # TODO don't use 'm' for truly boolean config vars
            equals_y = self.boolean_variables[name + "=y"].bdd
            equals_m = self.boolean_variables[name + "=m"].bdd
            is_defined_y = conjunction(self.get_defined(name, True),
                                       conjunction(equals_y,
                                                   negation(equals_m)))
            is_defined_m = conjunction(self.get_defined(name, True),
                                       conjunction(equals_m,
                                                   negation(equals_y)))
            not_defined = disjunction(self.get_defined(name, False),
                                      conjunction(negation(is_defined_y),
                                                  negation(is_defined_m)))

            return Multiverse([ (is_defined_y, 'y'),
                                (is_defined_m, 'm'),
                                (not_defined, None) ])
        # elif (name.startswith("CONFIG_")) and not isNonbooleanConfig(name):
        #     return Multiverse([ (self.T, '') ])
        else:
            if name in self.undefined_variables:
                return Multiverse( [(condition, value)
                                    for value, condition, _ in self.variables[name]])
            elif name not in self.variables and not isNonbooleanConfig(name):
                # Leave undefined variables unexpanded
                self.undefined_variables.add(name)
                self.variables[name] = [VariableEntry("$(%s)" % (name),
                                                      self.T,
                                                      Flavor.RECURSIVE)]

                warn("Undefined variable expansion", name)
                return Multiverse( [(condition, value)
                                    for value, condition, _ in self.variables[name]])
            else:
                expansions = []
                for value, condition, _ in self.variables[name]:
                    if value == None:
                        expansions.append((condition, value))
                    else:
                        expansions = expansions + self.expand_and_flatten(value, condition)

                # print expansions
                # return Multiverse( [(condition, value)
                #                     for value, condition, _ in self.variables[name]])
                return Multiverse(expansions)

    def process_function(self, function):
        """Evaluate variable expansion or built-in function and return
        either a single string or a list of (condition, string) pairs."""
        if isinstance(function, functions.VariableRef):
            name = self.repack_singleton(self.process_expansion(function.vname))
            
            expanded_names = []
            for name_cond, name_value  in name:
                expanded_name = self.process_variableref(name_value)
                for (expanded_cond, expanded_value) in expanded_name:
                    expanded_names.append(( conjunction(name_cond, expanded_cond), expanded_value ))
            return Multiverse(expanded_names)
        elif isinstance(function, functions.SubstFunction):
            from_values = self.repack_singleton(self.process_expansion(function._arguments[0]))
            to_values = self.repack_singleton(self.process_expansion(function._arguments[1]))
            in_values = self.repack_singleton(self.process_expansion(function._arguments[2]))

            # Hoist conditionals around the function by getting all
            # combinations of arguments
            hoisted_arguments = tuple((s, r, d)
                                      for s in from_values
                                      for r in to_values
                                      for d in in_values)

            hoisted_results = []
            # Compute the function for each combination of arguments
            for (c1, s), (c2, r), (c3, d) in hoisted_arguments:
                instance_condition = conjunction(c1, conjunction(c2, c3))
                if instance_condition != self.F:
                    if r == None: r = ""  # Fixes bug in net/l2tp/Makefile
                    instance_result = None if d == None else d.replace(s, r)
                    hoisted_results.append((instance_condition, instance_result))

            return Multiverse(hoisted_results)
        # elif isinstance(function, functions.CallFunction):
        #     # TODO: implement and test on drivers/xen/
        #     # fatal("Unsupported function", function)
        #     warn("Skipped function call", function)
        #     return None
        # elif isinstance(function, functions.FindstringFunction):
        #     # TODO: implement and test on drivers/staging/wlags49_h25/
        #     fatal("Unsupported function", function)
        #     return None
        elif isinstance(function, functions.SubstitutionRef):
            from_values = self.repack_singleton(self.process_expansion(function.substfrom))
            to_values = self.repack_singleton(self.process_expansion(function.substto))
            name = self.repack_singleton(self.process_expansion(function.vname))

            # first expand the variable
            in_values = []
            for name_cond, name_value in name:
                expanded_name = self.process_variableref(name_value)
                for (expanded_cond, expanded_value) in expanded_name:
                    in_values.append( (conjunction(name_cond, expanded_cond), expanded_value) )

            # then do patsubst
            hoisted_arguments = tuple((s, r, d)
                                      for s in from_values
                                      for r in to_values
                                      for d in in_values)

            hoisted_results = []
            for (c1, s), (c2, r), (c3, d) in hoisted_arguments:
                instance_condition = conjunction(c1, conjunction(c2, c3))
                if instance_condition != self.F:
                    if r == None: r = ""  # Fixes bug in net/l2tp/Makefile
                    if r"%" not in s:
                        # without a %, use a % to implement replacing
                        # the end of the string
                        s = r"%" + s
                        r = r"%" + r
                    pattern = "^" + s.replace(r"%", r"(.*)", 1) + "$"
                    replacement = r.replace(r"%", r"\1", 1)
                    if d != None:
                        instance_result = " ".join([re.sub(pattern, replacement, d_token) for d_token in d.split()])
                    else:
                        instance_result = None
                    hoisted_results.append((instance_condition, instance_result))

            return Multiverse(hoisted_results)
        elif isinstance(function, functions.IfFunction):
            condition_part = self.repack_singleton(self.process_expansion(function._arguments[0]))
            then_part = self.repack_singleton(self.process_expansion(function._arguments[1]))
            then_condition = self.F
            else_condition = self.F
            for condition, value in condition_part:
                if value == None:
                    value = ""
                if (len(str(value)) > 0):
                    then_condition = disjunction(then_condition, condition)
                else:
                    else_condition = disjunction(then_condition, condition)
            expansions = []
            for condition, value in then_part:
                condition = conjunction(then_condition, condition)
                if condition != self.F:
                    expansions.append((condition, value))
            if len(function._arguments) > 2:
                else_part = self.repack_singleton(self.process_expansion(function._arguments[2]))
                for condition, value in else_part:
                    condition = conjunction(else_condition, condition)
                    if condition != self.F:
                        expansions.append((condition, value))
            return Multiverse(expansions)
        # elif isinstance(function, functions.WildcardFunction):
        #     # TODO: implement and test on usr/
        #     fatal("Unsupported function", function)
        #     return None
        elif isinstance(function, functions.FilteroutFunction):
            from_values = self.repack_singleton(self.process_expansion(function._arguments[0]))
            in_values = self.repack_singleton(self.process_expansion(function._arguments[1]))

            # Hoist conditionals around the function by getting all
            # combinations of arguments
            hoisted_arguments = tuple((s, d)
                                      for s in from_values
                                      for d in in_values)

            hoisted_results = []
            # Compute the function for each combination of arguments
            for (c1, s), (c2, d) in hoisted_arguments:
                instance_condition = conjunction(c1, c2)
                if instance_condition != self.F:
                    if d != None:
                        instance_result = " ".join([d_token for d_token in d.split() if d_token != s])
                    else:
                        instance_result = None
                    hoisted_results.append((instance_condition, instance_result))

            return Multiverse(hoisted_results)
        # elif isinstance(function, functions.ForEachFunction):
        #     # TODO: implement and test on arch/x86/vdso/
        #     fatal("Unsupported function", function)
        #     return None
        # elif isinstance(function, functions.OriginFunction):
        #     # TODO: implement and test on ./Makefile
        #     fatal("Unsupported function", function)
        #     return None
        # elif isinstance(function, functions.FilterFunction):
        #     # TODO: implement and test on ./Makefile
        #     fatal("Unsupported function", function)
        #     return None
        elif isinstance(function, functions.PatSubstFunction):
            from_values = self.repack_singleton(self.process_expansion(function._arguments[0]))
            to_values = self.repack_singleton(self.process_expansion(function._arguments[1]))
            in_values = self.repack_singleton(self.process_expansion(function._arguments[2]))

            # Hoist conditionals around the function by getting all
            # combinations of arguments
            hoisted_arguments = tuple((s, r, d)
                                      for s in from_values
                                      for r in to_values
                                      for d in in_values)

            hoisted_results = []
            # Compute the function for each combination of arguments
            for (c1, s), (c2, r), (c3, d) in hoisted_arguments:
                instance_condition = conjunction(c1, conjunction(c2, c3))
                if instance_condition != self.F:
                    if r == None: r = ""  # Fixes bug in net/l2tp/Makefile
                    pattern = "^" + s.replace(r"%", r"(.*)", 1) + "$"
                    replacement = r.replace(r"%", r"\1", 1)
                    if d != None:
                        instance_result = " ".join([re.sub(pattern, replacement, d_token) for d_token in d.split()])
                    else:
                        instance_result = None
                    hoisted_results.append((instance_condition, instance_result))

            return Multiverse(hoisted_results)
        elif isinstance(function, functions.SortFunction):
            # no sorting for now
            return Multiverse(self.repack_singleton(self.process_expansion(function._arguments[0])))
        elif isinstance(function, functions.AddPrefixFunction):
            prefixes = self.repack_singleton(self.process_expansion(function._arguments[0]))
            token_strings = self.repack_singleton(self.process_expansion(function._arguments[1]))

            hoisted_results = []
            for (prefix_cond, prefix) in prefixes:
                for (tokens_cond, token_string) in token_strings:
                    resulting_cond = conjunction(prefix_cond, tokens_cond)
                    if resulting_cond != self.F:
                        # append prefix to each token in the token_string
                        if token_string != None:
                            prefixed_tokens = " ".join([ prefix + token
                                                         for token
                                                         in token_string.split() ])
                        else:
                            prefixed_tokens = ""
                        hoisted_results.append((resulting_cond, prefixed_tokens))

            return Multiverse(hoisted_results)
        # elif isinstance(function, functions.NotDirFunction):
        #     # TODO: implement and test on ./Makefile
        #     fatal("Unsupported function", function)
        #     return None
        # elif isinstance(function, functions.DirFunction):
        #     # TODO: implement and test on ./Makefile
        #     fatal("Unsupported function", function)
        #     return None
        # elif isinstance(function, functions.ShellFunction):
        #     warn("skipping shell function")
        #     return None
        # else: fatal("Unsupported function", function)
        else:
            return self.repack_singleton(function.to_source())

    def repack_singleton(self, expansion):
        if isinstance(expansion, str):
            return Multiverse([(self.T, expansion)])
        else:
            return expansion

    def process_element(self, element, isfunc):
        if isinstance(element, str):
            return element
        elif isfunc:
            return self.process_function(element)
        else:
            return self.process_expansion(element)

    def hoist(self, expansion):
        """Hoists a list of expansions, strings, and Multiverses."""
        hoisted = Multiverse([(self.T, [])])
        for element in expansion:
            if isinstance(element, Multiverse):
                newlist = []
                for subcondition, subverse in element:
                    for condition, verse in hoisted:
                        newcondition = conjunction(condition, subcondition)
                        newverse = list(verse)
                        if isinstance(subverse, list):
                            newverse += subverse
                        else:
                            newverse.append(subverse)
                        newlist.append((newcondition, newverse))
                hoisted = Multiverse(newlist)
            else:
                for condition, verse in hoisted:
                    verse.append(element)

        multiverse = Multiverse( [ (condition, self.join_values(verse))
                                   for condition, verse in hoisted ] )
        multiverse = dedup_multiverse(multiverse)
        return multiverse

    def process_expansion(self, expansion):
        """Expand variables in expansion, hoisting multiply-defined ones

        @param expansion is a pymake Expansion object

        @return either a single string or a list of (condition, string)
        pairs."""
        if isinstance(expansion, data.StringExpansion):
            return expansion.s
        elif isinstance(expansion, data.Expansion):
            return self.hoist([ self.process_element(element, isfunc)
                           for element, isfunc in expansion ])
        else: fatal("Unsupported BaseExpansion subtype.", expansion)

    def process_conditionalblock(self, block, presence_condition):
        """Find a satisfying configuration for each branch of the
        conditional block."""
        # See if the block has an else branch.  Assumes no "else if".
        if len(block) == 1: has_else = False
        elif len(block) == 2: has_else = True
        else:
            warn("unsupported conditional block", block)
            return

        # Process first branch
        condition, statements = block[0]  # condition is a Condition object
        first_branch_condition = None
        if isinstance(condition, parserdata.IfdefCondition):  # ifdef
            # TODO only care if condition.exp.variable_references contains
            # multiply-defined macros
            expansion = self.process_expansion(condition.exp)
            if isinstance(expansion, str):
                first_branch_condition = self.get_defined(expansion, condition.expected)
            else:
                hoisted_condition = reduce(disjunction,
                                           [ c for c, v in expansion if v != None ])
                first_branch_condition = conjunction(presence_condition,
                                                    hoisted_condition)
            else_branch_condition = negation(first_branch_condition)
        elif isinstance(condition, parserdata.EqCondition):  # ifeq
            exp1 = self.repack_singleton(self.process_expansion(condition.exp1))
            exp2 = self.repack_singleton(self.process_expansion(condition.exp2))

            # Hoist multiple expansions around equality operation
            hoisted_condition = self.F
            hoisted_else = self.F
            for c1, v1 in exp1:
                for c2, v2 in exp2:
                    if v1 == None:  # None means undefined, so use empty string for comparison
                        v1 = ""
                    if v2 == None:
                        v2 = ""
                    term_condition = conjunction(c1, c2)
                    if term_condition != self.F and (v1 == v2) == condition.expected:
                        hoisted_condition = disjunction(hoisted_condition,
                                                        term_condition)
                    elif term_condition != self.F:
                        hoisted_else = disjunction(hoisted_else,
                                                   term_condition)
                    if contains_unexpanded(v1) or contains_unexpanded(v2):
                        # this preserves configurations where we
                        # didn't have values for a config option
                        new_var_name = str(v1) + "=" + str(v2)
                        new_bdd_var = self.boolean_variables[new_var_name].bdd
                        hoisted_condition = disjunction(hoisted_condition,
                                                        new_bdd_var)
                        hoisted_else = disjunction(hoisted_else,
                                                   negation(new_bdd_var))

                first_branch_condition = conjunction(presence_condition,
                                                     hoisted_condition)
                else_branch_condition = conjunction(presence_condition,
                                                    hoisted_else)
        else: fatal("unsupported conditional branch", condition)

        if first_branch_condition == None:
            fatal("Could not get if branch condition", first_branch_condition)

        self.process_statements(statements, first_branch_condition)  # Enter first branch

        if not has_else:
            return

        # Process the else branch
        condition, statements = block[1]
        self.process_statements(statements, else_branch_condition)  # Enter else branch

    def expand_and_flatten(self, value, presence_condition):
        """Parse and expand a variable definition, flattening any
        recursive expansions by hoisting

        @return a Multiverse list of (condition, value) pairs"""
        # Parse the variable's definition
        d = parser.Data.fromstring(value, None)
        e, t, o = parser.parsemakesyntax(d, 0, (), parser.iterdata)
        if t != None or o != None:
            # TODO: do something if part of the string is left over
            pass

        expanded = self.process_expansion(e)
        if isinstance(expanded, str):
            return Multiverse([(presence_condition, expanded)])
        else:
            return expanded

    def join_values(self, value_list, delim=""):
        """Joins a list of make variable values that may be None, which
        means the variable is undefined.  When joined with defined values,
        None is the empty string.  When all values are None, the resulting
        value is also None.

        @param value_list a list of strings or Nones
        @returns A string or a None"""

        filtered = filter(lambda s: s != None, value_list)
        return None if len(filtered) == 0 else delim.join(filtered)

    def append_values(self, *args):
        return self.join_values(args, " ")

    def bdd_to_cnf(self, condition):
        """Converts the expression to conjunctive normal form

        @returns a list of terms, represented as lists of factors"""
        stdout = os.dup(1)
        temp_fd, temp_filename = tempfile.mkstemp()
        sys.stdout.flush()
        os.dup2(temp_fd, 1)
        condition.PrintMinterm()
        sys.stdout.flush()
        os.dup2(stdout, 1)
        os.close(stdout)
        os.lseek(temp_fd, 0, os.SEEK_SET)
        with os.fdopen(temp_fd) as f:
            expression = []
            for line in filter(lambda l: len(l) > 0, (l.rstrip() for l in f.readlines())):
                minterm = list(line)
                term = []
                for name in self.boolean_variables:
                    value = minterm[self.boolean_variables[name].index]
                    if value == '1':
                        term.append(name)
                    elif value == '0':
                        term.append("!" + name)
                    elif value == '-':
                        pass
                    else: fatal("Unknown setting for variable in minterm", minterm)
                expression.append(term)
            return expression
        fatal("Could not open temp file containing minterms", temp_file)

    def bdd_to_str(self, condition):
        """Converts the expression to a string"""

        if condition == self.T:
            return "1"
        elif condition == self.F:
            return "0"

        expression = ""
        term_delim = ""
        for sublist in self.bdd_to_cnf(condition):
            term = ""
            factor_delim = ""
            for factor in sublist:
                term += factor_delim + factor
                factor_delim = " && "
            if len(term) > 0:
                expression += term_delim + term
                term_delim = " || "
        if len(expression) == 0:
            expression="1"
        return expression

    def combine_expansions(self, expansions):
        before = len(expansions)
        combined = expansions
        after = len(combined)
        return combined

    def add_variable_entry(self, name, presence_condition, token, value):
        """Given a presence condition, the variable's name, its assignment
        operator, and the definition, update the variable's list of
        configurations to reflect the dry-runs needed to cover all its
        definition."""
        if token == "=":
            # Recursively-expanded variable defs are expanded at use-time

            # Update all existing definitions' presence conditions
            self.variables[name] = \
                map(lambda (old_value, old_condition, old_flavor): \
                        VariableEntry(old_value, \
                                      conjunction(old_condition, \
                                                  negation(presence_condition)), \
                                          old_flavor), \
                        self.variables[name])

            # Add complete definition to variable (needed to find variable
            # expansions at use-time)
            self.variables[name].append(VariableEntry(value,
                                                 presence_condition,
                                                 Flavor.RECURSIVE))

            # TODO: handle reassignment, but does it really matter?  Use
            # reassignment example from kbuild_examples.tex as a test

            # TODO: if reassignment doesn't matter, trim any definitions
            # that have a presence condition of FALSE
        elif token == ":=":
            # Simply-expanded self.variables are expanded at define-time

            # Update all existing definitions' presence conditions
            # AFTER getting the new definition, since the new
            # definition might refer to itself as in
            # linux-3.0.0/crypto/Makefile
            old_variables = \
                map(lambda (old_value, old_condition, old_flavor): \
                        VariableEntry(old_value, \
                                     conjunction(old_condition, \
                                                 negation(presence_condition)), \
                                         old_flavor), \
                        self.variables[name])

            # Expand and flatten self.variables in the definition and add the
            # resulting definitions.
            new_definitions = self.expand_and_flatten(value, presence_condition)
            new_definitions = self.combine_expansions(new_definitions)
            new_variables = []
            for new_condition, new_value in new_definitions:
                new_variables.append(VariableEntry(new_value,
                                                     new_condition,
                                                     Flavor.SIMPLE))

            self.variables[name] = old_variables + new_variables
            # TODO: check for computed variable names, compute them, and
            # collect any configurations resulting from those self.variables

        elif token == "+=":
            if args.naive_append:
                # Negate old definitions just like assignment, except create a
                # new entry for each old entry, appending the value to each.

                old_definitions = \
                    map(lambda (old_value, old_condition, old_flavor): \
                            VariableEntry(old_value, \
                                         conjunction(old_condition, \
                                                     negation(presence_condition)), \
                                             old_flavor), \
                            self.variables[name])

                # TODO: support computed variable names used in the definition

                # Append the value to each of the old definitions.
                appended_definitions = []
                for old_value, old_condition, flavor in self.variables[name]:
                    nested_condition = conjunction(old_condition, presence_condition)
                    if flavor == Flavor.RECURSIVE:
                        # If it's recursively-expanded (=), append the definition to
                        # each existing def, and "and" the presence conditions
                        c = VariableEntry(self.append_values(old_value, value),
                                              nested_condition,
                                              flavor)
                        appended_definitions.append(c)
                    elif flavor == Flavor.SIMPLE:
                        # If it's simply-expanded (:=), need to expand and
                        # flatten the resulting appended definition
                        expanded = self.expand_and_flatten(self.append_values(old_value,
                                                                    value),
                                                      nested_condition)
                        expanded = self.combine_expansions(expanded)

                        for new_condition, new_value in expanded:
                            appended_definitions.append(VariableEntry(new_value,
                                                                      new_condition,
                                                                      Flavor.SIMPLE))
                    else: fatal("Variable flavor is not defined", flavor)
                self.variables[name] = Multiverse(old_definitions + appended_definitions)
            else:  # efficient append
                new_variables = []
                for entry in self.variables[name]:
                    old_value, old_condition, old_flavor = entry
                    new_condition = conjunction(old_condition, presence_condition)
                    if new_condition == self.F:
                        # Make two separate definitions.  One updates the
                        # existing definition's presence_condition.  The
                        # other creates a new definition
                        updated_condition = conjunction(old_condition,
                                                        negation(presence_condition))
                        new_variables.append(VariableEntry(old_value,
                                                           updated_condition,
                                                           old_flavor))
                        new_condition = conjunction(negation(old_condition),
                                                    presence_condition)
                        if old_flavor == Flavor.SIMPLE:
                            expanded = self.expand_and_flatten(value, new_condition)
                            expanded = self.combine_expansions(expanded)
                            for expanded_condition, expanded_value in expanded:
                                expanded_entry = VariableEntry(expanded_value,
                                                               expanded_condition,
                                                               old_flavor)
                                new_variables.append(expanded_entry)
                        elif old_flavor == Flavor.RECURSIVE:
                            new_variables.append(VariableEntry(value,
                                                               new_condition,
                                                               old_flavor))
                        else: fatal("Variable flavor is not defined", flavor)
                    else:
                        # Append directly to the existing definition.
                        appended_value = self.append_values(old_value, value)
                        if old_flavor == Flavor.SIMPLE:
                            expanded = self.expand_and_flatten(appended_value,
                                                          new_condition)
                            expanded = self.combine_expansions(expanded)
                            for expanded_condition, expanded_value in expanded:
                                expanded_entry = VariableEntry(expanded_value,
                                                               expanded_condition,
                                                               old_flavor)
                                new_variables.append(expanded_entry)
                        elif old_flavor == Flavor.RECURSIVE:
                            new_variables.append(VariableEntry(appended_value,
                                                               new_condition,
                                                               old_flavor))
                        else: fatal("Variable flavor is not defined", flavor)
                self.variables[name] = new_variables

                # self.variables[name] = \
                #     map(lambda (old_value, old_condition, old_flavor):
                #             VariableEntry(self.append_values(old_value, value),
                #                           conjunction(old_condition,
                #                                       presence_condition),
                #                           old_flavor),
                #         self.variables[name])
        elif token == "?=":
            # TODO: if ?= is used on an undefined variable, it's
            # initialized as a recursively-expanded variable (=)

            pass
        else: fatal("Unknown setvariable token", token)

        # Trim definitions with a presence condition of FALSE
        self.variables[name] = \
            [ entry for entry in self.variables[name] if entry.condition != self.F ]

    def process_setvariable(self, setvar, condition):
        """Find a satisfying set of configurations for variable."""
        name = self.process_expansion(setvar.vnameexp)
        token = setvar.token
        value = setvar.value

        if isinstance(name, str):
            debug(2, "setvariable under presence condition "
                  + name + " " + value + " " + self.bdd_to_str(condition))
            if (args.get_presence_conditions):
                if (name.endswith("-y") or name.endswith("-m")):
                    splitvalue = value.split()
                    for v in splitvalue:
                        if v.endswith(".o") or v.endswith("/"):
                            if not v in self.token_pc.keys():
                                self.token_pc[v] = self.T
                            # update nested_condition
                            self.token_pc[v] = conjunction(self.token_pc[v], condition)
                            if (name in ["obj-y", "obj-m"]):
                                # save final BDD for the token
                                if v.endswith(".o"):
                                    self.unit_pc[v] = self.token_pc[v]
                                    # print self.bdd_to_str(self.unit_pc[v])
                                elif v.endswith("/"):
                                    self.subdir_pc[v] = self.token_pc[v]
            self.add_variable_entry(name, condition, token, value)
        else:
            for local_condition, expanded_name in name:
                debug(2, "setvariable under presence condition "
                          + expanded_name + " "
                      + self.bdd_to_str(local_condition))
                nested_condition = conjunction(local_condition, condition)
                if (args.get_presence_conditions):
                    if (expanded_name.endswith("-y") or expanded_name.endswith("-m")):
                        splitvalue = value.split()
                        for v in splitvalue:
                            if v.endswith(".o") or v.endswith("/"):
                                if not v in self.token_pc.keys():
                                    self.token_pc[v] = self.T
                                # update nested_condition
                                self.token_pc[v] = conjunction(self.token_pc[v], nested_condition)
                                if (expanded_name in ["obj-y", "obj-m"]):
                                    # save final BDD for the token
                                    if v.endswith(".o"):
                                        self.unit_pc[v] = self.token_pc[v]
                                        # print self.bdd_to_str(self.unit_pc[v])
                                    elif v.endswith("/"):
                                        self.subdir_pc[v] = self.token_pc[v]

                self.add_variable_entry(expanded_name, nested_condition, token, value)

    def process_rule(self, rule, condition):
        pass

    def process_include(self, s, condition):
        expanded_include = self.repack_singleton(self.process_expansion(s.exp))
        for include_cond, include_files in expanded_include:
            if include_files != None:
                for include_file in include_files.split():
                    obj = os.path.dirname(include_file)
                    if os.path.exists(include_file):
                        include_makefile = open(include_file, "rU")
                        s = include_makefile.read()
                        include_makefile.close()
                        include_statements = parser.parsestring(s, include_makefile.name)
                        self.process_statements(include_statements, include_cond)

    def process_statements(self, statements, condition):
        """Find configurations in the given list of statements under the
        given presence condition."""
        for s in statements:
            if isinstance(s, parserdata.ConditionBlock):
                self.process_conditionalblock(s, condition)
            elif isinstance(s, parserdata.SetVariable):
                self.process_setvariable(s, condition)
            elif (isinstance(s, parserdata.Rule) or
                  isinstance(s, parserdata.StaticPatternRule)):
                self.process_rule(s, condition)
            elif (isinstance(s, parserdata.Include)):
                self.process_include(s, condition)

def split_definitions(kbuild, pending_variable):
    """get every whitespace-delimited token in all definitions of the
    given variable name, expanding any variable invocations first"""
    values = []
    for index, entry in enumerate(kbuild.variables[pending_variable]):
        value, presence_condition, flavor = entry
        # Expand any variables used in definitions
        if value != None:
            expanded_values = kbuild.repack_singleton(
                kbuild.expand_and_flatten(value, presence_condition))
            for expanded_condition, expanded_value in expanded_values:
                if expanded_value != None:
                    split_expanded_values = expanded_value.split()
                    values.extend(split_expanded_values)

                    if (args.get_presence_conditions):
                        composite_unit = "-".join(pending_variable.split('-')[:-1]) + ".o"
                        if composite_unit in kbuild.token_pc:
                            for v in split_expanded_values:
                                composite_condition = conjunction(expanded_condition, kbuild.token_pc[composite_unit])
                                if not v in kbuild.token_pc.keys():
                                    kbuild.token_pc[v] = kbuild.T
                                # update nested_condition
                                kbuild.token_pc[v] = conjunction(kbuild.token_pc[v], composite_condition)

    return values

def collect_units(kbuild,            # current kbuild instance
                  obj,               # current path
                  pending_variables, # variables to extract from, gets
                                     # emptied
                  compilation_units, # adds units to this set
                  subdirectories,    # adds subdir to this set
                  composites,        # adds composites to this set
                  store_pcs=False):  # save pcs from these variables
    """fixed-point algorithm that adds composites and stops when no
    more variables to look at are available"""
    processed_variables = set()
    while len(pending_variables) > 0:
        pending_variable = pending_variables.pop()
        processed_variables.add(pending_variable)

        # Collect the list of definitions
        values = split_definitions(kbuild, pending_variable)
        for elem in values:
            unit_name = os.path.normpath(os.path.join(obj, elem))
            
            if elem.endswith(".o") and unit_name not in compilation_units:
                # Expand composites
                if (elem[:-2] + "-objs") in kbuild.variables or \
                        (elem[:-2] + "-y") in kbuild.variables:
                    # scripts/Makefile.build use the -objs and -y
                    # suffix to define composites $($(subst
                    # $(obj)/,,$(@:.o=-objs))) $($(subst
                    # $(obj)/,,$(@:.o=-y)))), $^)

                    composite_variable1 = elem[:-2] + "-objs"
                    composite_variable2 = elem[:-2] + "-y"

                    if composite_variable1 not in processed_variables and \
                            composite_variable2 not in processed_variables:
                        composites.add(unit_name)
                        pending_variables.add(composite_variable1)
                        pending_variables.add(composite_variable2)
                        if store_pcs:
                            if (elem not in kbuild.token_pc): kbuild.token_pc[elem] = kbuild.T
                            kbuild.composite_pc[elem] = kbuild.token_pc[elem]
                        
                    if os.path.isfile(unit_name[:-2] + ".c") or os.path.isfile(unit_name[:-2] + ".S"): 
                        compilation_units.add(unit_name)
                        if store_pcs:
                            if (elem not in kbuild.token_pc): kbuild.token_pc[elem] = kbuild.T
                            kbuild.unit_pc[elem] = kbuild.token_pc[elem]
                else:
                    compilation_units.add(unit_name)
                    if store_pcs:
                        if (elem not in kbuild.token_pc): kbuild.token_pc[elem] = kbuild.T
                        kbuild.unit_pc[elem] = kbuild.token_pc[elem]
            elif elem.endswith("/"):
                # scripts/Makefile.lib takes anything that
                # ends in a forward slash as a subdir
                # $(patsubst %/,%,$(filter %/, $(obj-y)))
                subdirectories.add(unit_name)
                if store_pcs:
                    if (elem not in kbuild.token_pc): kbuild.token_pc[elem] = kbuild.T
                    kbuild.subdir_pc[elem] = kbuild.token_pc[elem]

def extract(makefile_path,
            compilation_units,
            library_units,
            composites,
            hostprog_units,
            hostprog_composites,
            unconfigurable_units,
            extra_targets,
            clean_files,
            c_file_targets,
            unit_pcs,
            subdir_pcs):
    debug(1, "processing makefile", makefile_path)
    if os.path.isdir(makefile_path):
        subdir = makefile_path
        makefile_path = os.path.join(subdir, "Kbuild")
        if not os.path.isfile(makefile_path):
            makefile_path = os.path.join(subdir, "Makefile") 
    if not os.path.isfile(makefile_path):
        fatal("not found", makefile_path)
        exit(1)

    obj = os.path.dirname(makefile_path)
    makefile = open(makefile_path, "rU")

    s = makefile.read()
    makefile.close()

    statements = parser.parsestring(s, makefile.name)

    kbuild = Kbuild()

    kbuild.add_definitions(args.define)

    kbuild.process_statements(statements, kbuild.T)
    # OPTIMIZE: list by combining non-exclusive configurations
    # OPTIMIZE: find maximal list and combine configurations
    # TODO: emit list of configurations for the dry-runs
    # TODO: merge equivalence between CONFIG= and !defined(CONFIG)

    subdirectories = set()

    if args.boot_strap:
        # collect_units(kbuild,
        #               obj,
        #               set(["core-y", "core-m", "drivers-y", "drivers-m", "net-y", "net-m", "libs-y", "libs-m"]),
        #               compilation_units,
        #               subdirectories,
        #               composites)
        # print " ".join(subdirectories)
        # exit(0)
        toplevel = set()
        for var in set(["core-y", "core-m", "drivers-y", "drivers-m", "net-y", "net-m", "libs-y", "libs-m"]):
            toplevel.update(split_definitions(kbuild, var))
        print " ".join([t for t in toplevel if t.endswith("/") and not t.startswith("-")])
        exit(0)

    collect_units(kbuild,
                  "",
                  set(["core-y", "core-m", "drivers-y", "drivers-m", "net-y", "net-m", "libs-y", "libs-m", "head-y", "head-m"]),
                  compilation_units,
                  subdirectories,
                  composites)

    collect_units(kbuild,
                  obj,
                  set([ "obj-y", "obj-m" ]),
                  compilation_units,
                  subdirectories,
                  composites,
                  True and args.get_presence_conditions)

    for v in set([ "subdir-y", "subdir-m" ]):
        for u in split_definitions(kbuild, v):
            subdirectories.add(os.path.join(obj, u))

    collect_units(kbuild,
                  obj,
                  set([ "lib-y", "lib-m" ]),
                  library_units,
                  subdirectories,
                  composites)

    pending_hostprog_composites = set([])
    for v in set([ "hostprogs-y", "hostprogs-m", "host-progs", "always" ]):
        for u in split_definitions(kbuild, v):
            composite_name = u + "-objs"
            unit_name = os.path.join(obj, u)
            if composite_name in kbuild.variables:
                pending_hostprog_composites.add(composite_name)
                hostprog_composites.add(unit_name)
            else:
                hostprog_units.add(unit_name)
    if (len(pending_hostprog_composites) > 0):
        collect_units(kbuild,
                      obj,
                      pending_hostprog_composites,
                      hostprog_units,
                      None,
                      hostprog_composites)

    for v in set([ "targets", "extra-y" ]):
        for u in split_definitions(kbuild, v):
            unit_name = os.path.join(obj, u)
            if unit_name.endswith(".o"):
                extra_targets.add(unit_name)

    for u in split_definitions(kbuild, "targets"):
        if u.endswith(".c"):
            c_file_targets.add(os.path.join(obj, u))

    for u in split_definitions(kbuild, "clean-files"):
        clean_files.add(os.path.join(obj, u))

    # look for variables starting with obj-, lib-, hostprogs-,
    # compositename-, or hostprog-compositename-.  doesn't account for
    # composites in the unconfigurable variables
    unconfigurable_prefixes = set([ "obj-$", "lib-$", "hostprogs-$" ])
    for cset in (composites, hostprog_composites):
        for c in cset:
            c = os.path.basename(c)
            if c.endswith(".o"):
                c = c[:-2]
            unconfigurable_prefixes.add(c + "-$")
    unconfigurable_variables = set([])
    for x in kbuild.variables:
        for p in unconfigurable_prefixes:
            if x.startswith(p) and \
                    not x.endswith("-") and \
                    not x.endswith("-y") and \
                    not x.endswith("-m") and \
                    not x.endswith("-objs") and \
                    x != "host-progs":
                unconfigurable_variables.add(x)
            elif x.startswith(p[:-1]) and x.endswith("-"):
                # also look in variables resulting from expansion of
                # undefined config var
                unconfigurable_variables.add(x)
    collect_units(kbuild,
                  obj,
                  unconfigurable_variables,
                  unconfigurable_units,
                  unconfigurable_units,
                  unconfigurable_units)
    # subtract out compilation units that are configurable
    unconfigurable_units.difference_update(compilation_units)
    unconfigurable_units.difference_update(library_units)
    unconfigurable_units.difference_update(composites)
    unconfigurable_units.difference_update(subdirectories)

    # look for variable expansions or function calls in
    # compilation_units, subdirectories, and variable names
    check_unexpanded_variables(compilation_units, "compilation unit")
    check_unexpanded_variables(subdirectories, "subdirectory")
    check_unexpanded_variables(kbuild.variables.keys(), "variable name")
    if args.variable:
        kbuild.print_variable(args.variable, kbuild.variables[args.variable])
    elif args.table:
        kbuild.print_variables_table(kbuild.variables)

    for v in kbuild.unit_pc.keys():
        path = os.path.normpath(os.path.join(obj, v))
        unit_pcs.append((path, kbuild.bdd_to_str(kbuild.unit_pc[v])))
    for v in kbuild.subdir_pc.keys():
        path = os.path.normpath(os.path.join(obj, v))
        subdir_pcs.append((path, kbuild.bdd_to_str(kbuild.subdir_pc[v])))

    _pycudd.delete_DdManager(kbuild.mgr)

    return subdirectories

def check_unexpanded_variables(l, desc):
    for x in l:
        if contains_unexpanded(x):
            warn("A " + desc + " contains an unexpanded variable or call", x)

match_unexpanded_variables = re.compile(r'.*\$\(.*\).*')
def contains_unexpanded(s):
    if s != None and match_unexpanded_variables.match(s):
        return True
    else:
        return False

def main():
    """Find a covering set of configurations for the given
    Makefile(s)."""

    compilation_units = set()
    library_units = set()
    composites = set()
    hostprog_units = set()
    hostprog_composites = set()
    unconfigurable_units = set()
    extra_targets = set()
    clean_files = set()
    c_file_targets = set()
    subdirectories = set()
    unit_pcs = []
    subdir_pcs = []
    subdirectories.add(args.makefile)
    while len(subdirectories) > 0:
        subdirectories.update(extract(subdirectories.pop(),
                                      compilation_units,
                                      library_units,
                                      composites,
                                      hostprog_units,
                                      hostprog_composites,
                                      unconfigurable_units,
                                      extra_targets,
                                      clean_files,
                                      c_file_targets,
                                      unit_pcs,
                                      subdir_pcs))
        if not args.recursive:
            break
    if args.pickle:
        pickle.dump((compilation_units,
                     library_units,
                     hostprog_units,
                     unconfigurable_units,
                     extra_targets,
                     clean_files,
                     c_file_targets,
                     subdirectories,
                     composites,
                     unit_pcs,
                     subdir_pcs), sys.stdout)
    else:
        print compilation_units
        print library_units
        print hostprog_units
        print unconfigurable_units
        print extra_targets
        print clean_files
        print c_file_targets
        print subdirectories
        for v, b in unit_pcs:
            print v, b
        for v, b in subdir_pcs:
            print v, b
    debug(1, len(compilation_units), "compilation unit(s)")
    debug(1, len(library_units), "library unit(s)")

if __name__ == '__main__':
    main()
