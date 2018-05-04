import os
import sys
import compiler
import ast
import traceback
import argparse
from collections import defaultdict

# this script takes the check_dep --dimacs output and converts it into
# a dimacs-compatible format

argparser = argparse.ArgumentParser(
    description="""\
Convert Kmax-produced Kconfig constraints from stdin into a dimacs file.
    """,
    epilog="""\
    """
    )
argparser.add_argument('-d',
                       '--debug',
                       action="store_true",
                       help="""turn on debugging output""")
argparser.add_argument('--remove-all-nonvisibles',
                       action="store_true",
                       help="""whether to leave only those config vars that can be selected by the user.  this is defined as config vars that have a kconfig prompt.""")
argparser.add_argument('--remove-independent-nonvisibles',
                       action="store_true",
                       help="""remove all nonvisibles that aren't used in dependencies""")
argparser.add_argument('--remove-bad-selects',
                       action="store_true",
                       help="""remove reverse dependencies when not used on a non-visible or not used on a visible variables without dependencies""")
argparser.add_argument('--remove-reverse-dependencies',
                       action="store_true",
                       help="""only use direct dependencies, ignoring reverse dependencies""")
argparser.add_argument('--remove-orphaned-nonvisibles',
                       action="store_true",
                       help="""remove nonvisibles that either don't have defaults or aren't enabled by a select statement""")
argparser.add_argument('--include-bool-defaults',
                       action="store_true",
                       help="""add constraints that reflect the conditions under which boolean default values are set""")
argparser.add_argument('--include-nonvisible-bool-defaults',
                       action="store_true",
                       help="""add constraints that reflect the conditions under which boolean default values for nonvisible variables are set""")
argparser.add_argument('--include-nonbool-defaults',
                       action="store_true",
                       help="""support non-boolean defaults by creating a new boolean variable for  each nonbool default value""")
argparser.add_argument('--comment-format-v2',
                       action="store_true",
                       help="""add extra formatting information to dimacs comments to distinguish them from normal comments""")
argparser.add_argument('-r',
                       '--use-root',
                       action="store_true",
                       help="""add an extra variable for the root of the feature model""")
args = argparser.parse_args()

debug = args.debug

root_var = "SPECIAL_ROOT_VARIABLE"
use_root_var = args.use_root

# mapping from configuration variable name to dimacs variable number
varnums = {}

# collect dep and rev_dep lines
dep_exprs = {}
rev_dep_exprs = {}

# collect defaults
def_bool_lines = defaultdict(set)

# the names of configuration variables that are "visible" to the user,
# i.e., that are selectable by the user
userselectable = set()

# names of variables that should be removed later. this is currently
# used to captures string constants in boolean expressions, where it
# isn't clear what the boolean value should be.
variables_to_remove = set()

# keep track of variables that have default values
has_defaults = set()

bools = set()
choice_vars = set()

nonbools = set()
nonbools_with_dep = set()
nonbools_nonvisibles = set()
nonbool_defaults = {}
nonbool_types = {}

ghost_bools = {}

# whether to always enable nonbools or not regardless of whether they
# have dependencies.  off by default.  warning: forcing nonbools that
# have dependencies can restrict the space of configurations because
# this just adds the nonbools as clauses; this is not recommended.
force_all_nonbools_on = False

def lookup_varnum(varname):
  if varname not in varnums:
    varnums[varname] = len(varnums) + 1
  return varnums[varname]

ghost_bool_count = 0
def get_ghost_bool_name(var):
  global ghost_bool_count
  ghost_bool_count += 1
  return "GHOST_BOOL_%d_%s" % (ghost_bool_count, var)

# parse tree processing
class Transformer(compiler.visitor.ASTVisitor):
  def __init__(self):
    compiler.visitor.ASTVisitor.__init__(self)
    self.tree = ()

  # def dispatch(self, node, *args):
  #   print "JFKDSJFKDSLJKFSD"
  #   self.node = node
  #   klass = node.__class__
  #   meth = self._cache.get(klass, None)
  #   if meth is None:
  #       className = klass.__name__
  #       meth = getattr(self.visitor, 'visit' + className, self.default)
  #       self._cache[klass] = meth
  #   className = klass.__name__
  #   print "dispatch", className, (meth and meth.__name__ or '')
  #   print meth
  #   return meth(node, *args)

  def default(self, node):
    # TODO: convert ast to string to be a predicate
    predicate = str(node)
    return ("name", predicate)

  def visitDiscard(self, node):
    self.tree = self.visit(node.getChildren()[0])

  def visitOr(self, node):
    children = node.getChildren()
    left = self.visit(children[0])
    for i in range(1, len(children)):
      left = ("or", left, self.visit(children[i]))
    return left

  def visitAnd(self, node):
    children = node.getChildren()
    left = self.visit(children[0])
    for i in range(1, len(children)):
      left = ("and", left, self.visit(children[i]))
    return left

  def visitNot(self, node):
    return ("not", self.visit(node.expr))

  def visitName(self, node):
    return ("name", node.name)

  def visitConst(self, node):
    # convert to int.  strings get converted to their length. this
    # will make empty strings false and non-empty strings true.
    value = node.value
    # if value == None:
    #   return 0
    try:
      num = int(value)
      return ("const", num)
    except:
      try:
        # make a new variable out of the string constant, but remove
        # it later.
        s = str(value)
        dummy_var = "UNSUPPORTED_VALUE_" + s
        sys.stderr.write("warning: use of undefined variable in dependency: %s\n" % (dummy_var))
        variables_to_remove.add(dummy_var)
        return ("name", dummy_var)
      except:
        print(traceback.format_exc())
        sys.stderr.write("error: cannot process value \"%s\"\n" % (value))
        exit(1)

def convert(node):
  """takes a tree and returns a list of clauses or a constant value"""
  nodetype = node[0]
  if nodetype == "or":
    left = node[1]
    right = node[2]
    l = convert(left)
    r = convert(right)

    # check for constants
    if isinstance(l, int):
      if l == 0:
        return r
      else:
        return 1
    if isinstance(r, int):
      if r == 0:
        return l
      else:
        return 1

    assert(isinstance(l, list) and isinstance(r, list))
    # construct new clauses by taking each pairwise combination of l and r's elements
    new_clauses = []
    for lc in l:
      for rc in r:
        assert(isinstance(lc, list) and isinstance(rc, list))
        new_clauses.append(lc + rc)
    return new_clauses

  elif nodetype == "and":
    left = node[1]
    right = node[2]
    l = convert(left)
    r = convert(right)

    # check for constants
    if isinstance(l, int):
      if l == 0:
        return 0
      else:
        return r
    if isinstance(r, int):
      if r == 0:
        return 0
      else:
        return l
      
    assert(isinstance(l, list) and isinstance(r, list))
    return l + r  # join two lists of clauses

  elif nodetype == "not":
    negated_node = node[1]
    negated_type = negated_node[0]
    if negated_type == "name":
      varnum = lookup_varnum(negated_node[1])
      return [[-varnum]]
    if negated_type == "const":
      value = negated_node[1]
      if value == 0:
        return 1
      else:
        return 0
    elif negated_type == "not":
      return convert(negated_node[1]) # double-negation
    elif negated_type == "and":
      left = negated_node[1]
      right = negated_node[2]
      return convert(("or", ("not", left), ("not", right))) # de morgan
    elif negated_type == "or":
      left = negated_node[1]
      right = negated_node[2]
      return convert(("and", ("not", left), ("not", right))) # de morgan
    else:
      assert(False)

  elif nodetype == "name":
    varnum = lookup_varnum(node[1])
    return [[varnum]]

  elif nodetype == "const":
    return node[1]

  else:
    assert(False)

def convert_to_cnf(expr):
  try:
    ast = compiler.parse(expr)
  except:
    sys.stderr.write("error: could not parse %s\n" % (line))
    sys.stderr.write(traceback.format_exc())
    sys.stderr.write("\n")
    return []
  # get Discard(ACTUAL_EXPR) from Module(None, Stmt([Discard(ACTUAL_EXPR)))
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  # print ast
  transformer = Transformer()
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  tree = transformer.tree
  # print tree
  clauses = convert(tree)
  if (isinstance(clauses, list)):
    return clauses
  else:
    # constants don't add any clauses
    return []
  
def collect_identifiers(node):
  """takes a tree and returns a list of clauses or a constant value"""
  nodetype = node[0]
  if nodetype == "or" or nodetype == "and":
    left = node[1]
    right = node[2]
    l = collect_identifiers(left)
    r = collect_identifiers(right)
    return l+r
  elif nodetype == "not":
    negated_node = node[1]
    return collect_identifiers(negated_node)
  elif nodetype == "name":
    return [node[1]]
  elif nodetype == "const":
    return []
  else:
    assert(False)

def get_identifiers(expr):
  try:
    ast = compiler.parse(expr)
  except:
    sys.stderr.write("error: could not parse %s\n" % (line))
    sys.stderr.write(traceback.format_exc())
    sys.stderr.write("\n")
    return []
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  transformer = Transformer()
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  tree = transformer.tree
  return collect_identifiers(tree)
  
def implication(antecedent, consequent):
  return "((not (%s)) or (%s))" % (antecedent, consequent)

def biimplication(antecedent, consequent):
  return "((%s) and (%s))" % (implication(antecedent, consequent), implication(consequent, antecedent))

def conjunction(a, b):
  return "((%s) and (%s))" % (a, b)

def disjunction(a, b):
  return "((%s) or (%s))" % (a, b)

def negation(a):
  return "(not (%s))" % (a)

# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f) and g or h")
# print convert_to_cnf("a or b or c or d or f")
# exit(1)

# collect clauses
clauses = []
if use_root_var:
  userselectable.add(root_var)
  clauses.append([lookup_varnum(root_var)])
for line in sys.stdin:
  if debug: sys.stderr.write("started %s\n" % (line))
  instr, data = line.strip().split(" ", 1)
  if (instr == "bool"):
    varname, selectability = data.split(" ", 1)
    selectable = True if selectability == "selectable" else False
    if selectable:
      userselectable.add(varname)
    bools.add(varname)
    lookup_varnum(varname)
  elif (instr == "def_bool"):
    var, line = data.split(" ", 1)
    def_bool_lines[var].add(line)
  elif (instr == "nonbool"):
    varname, selectability, type_name = data.split(" ", 2)
    selectable = True if selectability == "selectable" else False
    if selectable:
      userselectable.add(varname)
    lookup_varnum(varname)
    nonbools.add(varname)
    nonbool_types[varname] = type_name
  elif (instr == "def_nonbool"):
    var, val_and_expr = data.split(" ", 1)
    val, expr = val_and_expr.split("|", 1)
    if args.include_nonbool_defaults:
      has_defaults.add(var)
      # model nonbool values with ghost boolean values
      ghost_bool_name = get_ghost_bool_name(var)
      ghost_bools[ghost_bool_name] = (var, val)
      varnum = lookup_varnum(ghost_bool_name)
      # print ghost_bool_name, varnum, val
      if expr == "(1)":
        clauses.append([varnum])
      else:
        full_expr = "(not (" + expr + ")) or (" + ghost_bool_name + ")"
        # print line
        # print full_expr
        new_clauses = convert_to_cnf(full_expr)
        # print new_clauses
        clauses.extend(new_clauses)
    else:
      # just add the first nonbool default
      if var not in nonbool_defaults:
        nonbool_defaults[var] = val
  elif (instr == "clause"):
    vars = data.split(" ")
    clause = []
    for var in vars:
      if (var[0] == "-"):  # negation
        realvar = var[1:]
        clause.append(-lookup_varnum(realvar))
      else:
        clause.append(lookup_varnum(var))
    clauses.append(clause)
  elif (instr == "bool_choice"):
    var_string, dep_expr = data.split("|",1)
    config_vars = var_string.split(" ")
    # print config_vars
    # mutex choice: a -> !b, a -> !c, ..., b -> !a, b -> !c, ...
    choice_vars.update(set(config_vars))
    for i in range(0, len(config_vars)):
      for j in range(0, len(config_vars)):
        if i != j:
          var_i = lookup_varnum(config_vars[i])
          var_j = lookup_varnum(config_vars[j])
          clause = [-var_i, -var_j]
          # print clause
          clauses.append(clause)
    # add dependency, dep <-> (a | b | ... ), i.e., .  this ensures at least
    # one is selected and that if one is selected the dependency must
    # hold
    or_vars = ""
    for var in config_vars:
      or_vars = or_vars + " or " + var
    if use_root_var and dep_expr == "(1)":
      dep_expr = root_var
    choice_dep = "((not %s)%s) and ((not (0%s)) or (%s))" % (dep_expr, or_vars, or_vars, dep_expr)
    # print choice_dep
    new_clauses = convert_to_cnf(choice_dep)
    # print new_clauses
    clauses.extend(new_clauses)
  elif (instr == "dep"):
    var, expr = data.split(" ", 1)
    if var in dep_exprs:
      sys.stderr.write("found duplicate dep for %s. currently unsupported\n" % (var))
      exit(1)
    dep_exprs[var] = expr
  elif (instr == "rev_dep"):
    var, expr = data.split(" ", 1)
    if var in rev_dep_exprs:
      sys.stderr.write("found duplicate rev_dep for %s. currently unsupported\n" % (var))
      exit(1)
    rev_dep_exprs[var] = expr
  elif (instr == "bi"):
    expr1, expr2 = data.split("|", 1)
    # print expr1, expr2
    final_expr = "(((not %s) or %s) and ((%s) or (not %s)))" % (expr1, expr2, expr1, expr2)
    # print final_expr
    clauses.extend(convert_to_cnf(final_expr))
  elif (instr == "constraint"):
    expr = data
    clauses.extend(convert_to_cnf(expr))
  else:
    sys.stderr.write("unsupported instruction: %s\n" % (line))
    exit(1)
  if debug: sys.stderr.write("done %s\n" % (line))

# the names of configuration variables that have dependencies, either
# direct or reverse
has_dependencies = set()

# the names of configuration variables used in another variable's
# dependency expression
in_dependencies = set()

# keep track of variables that have reverse dependencies
has_selects = set()

def split_top_level_clauses(expr, separator):
  terms = []
  cur_term = ""
  depth = 0
  for c in expr:
    if c == "(":
      depth += 1
    elif c == ")":
      depth -= 1
      
    if depth == 0:
      cur_term += c
      if cur_term.endswith(separator):
        # save the term we just saw
        terms.append(cur_term[:-len(separator)])
        cur_term = ""
    elif depth > 0:
      cur_term += c
    else:
      sys.stderr.write("fatal: misnested parentheses in reverse dependencies: %s\n" % expr)
      exit(1)
  # save the last term
  terms.append(cur_term)
  return terms

def remove_direct_dep_from_rev_dep_term(term):
  # the first factor of the term is the SEL var the selects the
  # variable.  this is how kconfig stores the term.
  # print "FJDKSL", term, "JFDKSL"
  split_term = term.split(" and ", 1)
  if len(split_term) < 2:
    return term
  else:
    first_factor, remaining_factors = term.split(" and ", 1)
    if first_factor in dep_exprs.keys():
      # get the dep expression for the reverse dep
      dep_expr = dep_exprs[first_factor]
      # remove the parens
      if dep_expr.startswith("(") and dep_expr.endswith(")"): dep_expr = dep_expr[1:-1]
      # now we an expression that we can cut out from the reverse dependency's term
      remaining_factors = str.replace(remaining_factors, dep_expr, "1")
      # print "JFKLDSJKFLDS", remaining_factors, len(remaining_factors)
      # reconstruct the term
      if len(remaining_factors) > 0:
        term = "%s and %s" % (first_factor, remaining_factors)
      else:
        # the entire dependency was replaced, so the term is just the
        # reverse dependency variable
        term = first_factor
      # print "new_term", term
      return term
    else:  # it has no dependencies, so there is nothing to do
      return term


# generate clauses for dependencies and defaults
for var in set(dep_exprs.keys()).union(set(rev_dep_exprs.keys())).union(set(def_bool_lines.keys())):
  # get direct dependencies
  if var in dep_exprs.keys():
    dep_expr = dep_exprs[var]
    if dep_expr != "(1)":
      has_dependencies.add(var)  # track vars that have dependencies
      in_dependencies.update(get_identifiers(dep_expr))  # track vars that are in other dependencies
  else:
    dep_expr = None

  # get reverse dependencies
  if var in rev_dep_exprs.keys():
    rev_dep_expr = rev_dep_exprs[var]
    has_selects.add(var)
    if rev_dep_expr != "(1)":
      has_dependencies.add(var)  # track vars that have dependencies
      in_dependencies.update(get_identifiers(rev_dep_expr))  # track vars that are in other dependencies
  else:
    rev_dep_expr = None

  if args.remove_reverse_dependencies:
    rev_dep_expr = None

  # check for bad selects
  if rev_dep_expr != None:
    good_select = var not in userselectable or var not in has_dependencies
    if not good_select:
      if args.remove_bad_selects:
        # restrict reverse dependencies to variables that are not
        # user-visible and have no dependencies.
        sys.stderr.write("warn: removing bad select statements for %s.  this is the expression: %s\n" % (var, rev_dep_expr))
        rev_dep_expr = None
      else:
        sys.stderr.write("warn: found bad select statement(s) for %s\n" % (var))

  # filter out dependency expressions from configurations that are
  # reverse dependencies.  if a var SEL is a reverse dependency for
  # VAR, VAR's rev_dep_expr will contain "SEL and DIR_DEP", which is not
  if rev_dep_expr != None and rev_dep_expr != "(1)":
    # get all the top-level terms of this clause.  the reverse
    # dependency will be a union of "SEL and DIR_DEP" terms,
    # representing each of the reverse dependencies.
    expr = rev_dep_expr
    # print "BEGIN", rev_dep_expr
    # (1) strip surrounding parens (as added by check_dep on all dependencies)
    if expr.startswith("(") and expr.endswith(")"): expr = expr[1:-1]
    # (2) split into ORed clauses
    terms = split_top_level_clauses(expr, " or ")
    # (3) remove the direct dependencies conjoined with the SEL vars
    edited_terms = map(remove_direct_dep_from_rev_dep_term, terms)
    rev_dep_expr = "(%s)" % (" or ".join(edited_terms))
    # print "END", rev_dep_expr
    
  # handle boolean defaults
  if var in def_bool_lines.keys():
    has_defaults.add(var)
    if args.include_bool_defaults or args.include_nonvisible_bool_defaults and var not in userselectable:
      def_y_expr = "(0)"
      delim = " or "
      for def_bool_line in def_bool_lines[var]:
        val, expr = def_bool_line.split(" ", 1)
        if val == "1":
          def_y_expr = def_y_expr + delim + "(" + expr + ")"
    else:
      # don't include default values
      def_y_expr = None
  else:
    def_y_expr = None

  # create clauses for dependencies and defaults
  if var in nonbools:
    nonbools_with_dep.add(var)
    if var not in userselectable:
      # no support for nonbool nonvisibles, because we don't support
      # nonboolean constraints and there is no way for the user to
      # directly modify these.
      nonbools_nonvisibles.add(var)
      sys.stderr.write("warning: no support for nonvisible nonbools: %s\n" % (var))
    else:  # var is visible
      if rev_dep_expr != None:
        sys.stderr.write("warning: no support for reverse dependencies on nonbooleans: %s\n" % (var))
      # bi-implication var <-> dep_expr, because a nonboolean always
      # has a value as long as its dependencies are met.
      if dep_expr == None:
        # the nonbool is always on when no dependencies
        final_expr = var
      else:
        final_expr = biimplication(var, dep_expr)
      # print final_expr
      new_clauses = convert_to_cnf(final_expr)
      clauses.extend(new_clauses)
  else:  # var is a boolean
    if var not in userselectable:
      # I <-> ((E & D) | A)
      # I is the variable, A is the selects (reverse deps), E is the direct dep, D is the default y condition

      # because nonvisible variables cannot be modified by the user
      # interactively, we use a bi-implication between it's dependencies
      # and default values and selects.  this says that the default
      # value will be taken as long as the conditions are met.
      # nonvisibles default to off if these conditions are not met.

      consequent = dep_expr
      if consequent == None:
        consequent = def_y_expr
      elif def_y_expr != None:
        consequent = conjunction(consequent, def_y_expr)

      if consequent == None:
        consequent = rev_dep_expr
      elif rev_dep_expr != None:
        consequent = disjunction(consequent, rev_dep_expr)

      if consequent != None:
        expr = biimplication(var, consequent)
        # print expr
        new_clauses = convert_to_cnf(expr)
        # print new_clauses
        clauses.extend(new_clauses)
    else:  # visible variables
      # V -> (E | A) and A -> V, where E is direct dep, and A is reverse dep

      # intuitively, this makes sense.  if V is on, then either its
      # direct dependency E or reverse dependency A must have been
      # satisfied.  if the direct dependency is off, then the variable
      # must have only been set when its reverse dependency is set
      # (biimplication).

      if args.include_bool_defaults and var in def_bool_lines.keys():
        sys.stderr.write("warn: defaults currently ignored for visibles: %s\n" % (var))

      # clause1 = var -> (dep_expr or rev_dep_expr)
      # clause2 = rev_dep_expr -> var

      if rev_dep_expr != None:
        if dep_expr != None:
          clause1 = implication(var, disjunction(dep_expr, rev_dep_expr))
          clause2 = implication(rev_dep_expr, var)
          final_expr = conjunction(clause1, clause2)
        else: # no direct dependency means biimplication between rev_dep and var
          final_expr = biimplication(var, rev_dep_expr)
      else:
        if dep_expr != None:  # no reverse dependency means that only the direct dependency applies
          clause1 = implication(var, dep_expr)
          clause2 = None
          final_expr = clause1
        else: # no direct or reverse dependencies
          clause1 = None
          clause2 = None
          final_expr = None

      if use_root_var and final_expr == None:
        # if no dependencies, then depend on special root variable
        final_expr = root_var

      if final_expr != None:
        # print final_expr
        new_clauses = convert_to_cnf(final_expr)
        clauses.extend(new_clauses)

if force_all_nonbools_on:
  for nonbool in (nonbools):
    varnum = lookup_varnum(nonbool)
    clauses.append([varnum])

# filter clauses and variables
def remove_dups(l):
  seen = set()
  seen_add = seen.add
  return [x for x in l if not (x in seen or seen_add(x))]
clauses = map(lambda clause: remove_dups(clause), clauses)

def remove_condition(var):
  return \
    var in variables_to_remove or \
    var in nonbools_nonvisibles or \
    args.remove_all_nonvisibles and var not in userselectable or \
    args.remove_independent_nonvisibles and var not in userselectable and var not in in_dependencies or \
    args.remove_orphaned_nonvisibles and var not in userselectable and var in bools and var not in in_dependencies and var not in has_defaults and var not in has_selects

# print "|".join([ var for var in varnums.keys() if var not in userselectable and var not in in_dependencies and isinstance(var, str) ])
# exit(1)

keep_vars = filter(lambda var: not remove_condition(var), varnums.keys())
keep_varnums = filter(lambda (name, num): name in keep_vars, sorted(varnums.items(), key=lambda tup: tup[1]))

for var in varnums.keys():
  if var not in userselectable and var in bools and var not in has_defaults and var not in has_selects:
    if args.remove_orphaned_nonvisibles:
      sys.stderr.write("warning: remove orphaned nonvisible variables: %s\n" % (var))
    else:
      sys.stderr.write("warning: %s is an orphaned nonvisible variable\n" % (var))
    
# renumber variables
num_mapping = {}
for (name, old_num) in keep_varnums:
  num_mapping[old_num] = len(num_mapping) + 1

# update varnums
varnums = {name: num_mapping[old_num] for (name, old_num) in keep_varnums}

# remove vars from clauses
filtered_clauses = []
for clause in clauses:
  # trim undefined vars from clauses
  filtered_clause = filter(lambda x: abs(x) in num_mapping.keys(), clause)
  remapped_clause = [num_mapping[x] if x >= 0 else -num_mapping[abs(x)] for x in filtered_clause]
  if len(remapped_clause) == 1 and len(clause) > 1:
    # if all vars but one was removed, then there is no constraint
    pass
  elif len(remapped_clause) == 0:
    # nothing to print now
    pass
  else:
    filtered_clauses.append(remapped_clause)

# emit dimacs format
def print_dimacs(varnum_map, clause_list):
  if args.comment_format_v2:
    print "c format kmax_kconfig_v2"
    comment_prefix = "c kconfig_variable"
  else:
    comment_prefix = "c"
  for varname in sorted(varnum_map, key=varnum_map.get):
    if varname in nonbools:
      if varname in choice_vars:
        sys.stderr.write("choice variable is not boolean: %s\n" % (varname))
      if varname in nonbool_defaults:
        defaultval = nonbool_defaults[varname]
        if nonbool_types[varname] != "string":
          defaultval = defaultval[1:-1]  # strip off quotes for nonstrings
      else:
        defaultval = '""' if nonbool_types[varname] == "string" else "0"
      defaultval = " " + defaultval
      if args.comment_format_v2:
        typename = "string" if nonbool_types[varname] == "string" else "int"
      else:
        typename = "nonbool"
      print "%s %d %s %s%s" % (comment_prefix, varnum_map[varname], varname, typename, defaultval)
    else:
      if varname in choice_vars:
        print "%s %d %s choice_bool" % (comment_prefix, varnum_map[varname], varname)
      elif varname in userselectable:
        print "%s %d %s bool" % (comment_prefix, varnum_map[varname], varname)
      elif varname in ghost_bools.keys():
        nonbool_var, defval = ghost_bools[varname]
        print "%s %d %s ghost_bool %s %s" % (comment_prefix, varnum_map[varname], varname, nonbool_var, defval)
      else:
        print "%s %d %s hidden_bool" % (comment_prefix, varnum_map[varname], varname)
  print "p cnf %d %d" % (len(varnum_map), len(clause_list))
  for clause in clause_list:
    print "%s 0" % (" ".join([str(num) for num in clause]))

print_dimacs(varnums, filtered_clauses)
