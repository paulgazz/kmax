import os
import sys
import compiler
import ast
import traceback
import argparse
from collections import defaultdict
import time
import regex  # pip install regex
import z3

# this script takes the check_dep --dimacs output and converts it into
# a dimacs-compatible format

sys.setrecursionlimit(2000) # temporary fix until we improve parsing

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
argparser.add_argument('-e',
                       '--debug-expressions',
                       action="store_true",
                       help="""print all expressions""")
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
argparser.add_argument('--use-z3',
                       action="store_true",
                       help="""generate z3 clauses (instead of dimacs clauses)""")
args = argparser.parse_args()

debug = args.debug
debug_expressions = args.debug_expressions
remove_true_clauses = True
deduplicate_clauses = True

use_z3 = args.use_z3

root_var = "SPECIAL_ROOT_VARIABLE"

# mapping from configuration variable name to dimacs variable number
varnums = {}

# mapping from configuration variable name to z3 variable
z3vars = {}

# dimacs clauses
clauses = []
z3_clauses = []

# collect dep lines
dep_exprs = {}
rev_dep_exprs = {}

# collect select lines
selects = {}

# collect visibility conditions
prompt_lines = {}

# collect defaults
def_bool_lines = defaultdict(set)

# names of variables that should be removed later. this is currently
# used to captures string constants in boolean expressions, where it
# isn't clear what the boolean value should be.
variables_to_remove = set()

# keep track of variables that have default values
has_defaults = set()
has_prompt = set()

bools = set()
choice_vars = set()
bool_choices = []

# nonbool var attributes
nonbools = set()
nonbools_with_dep = set()
nonbools_nonvisibles = set()
nonbool_defaults = {}
nonbool_types = {}

# vars that can be set by the user via an environment variable (and thus are free variables)
envs = set()

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

def lookup_z3var(varname):
  if varname not in z3vars:
    z3vars[varname] = z3.Bool(varname)
  return z3vars[varname]

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
  except RuntimeError as e:
    sys.stderr.write("exception: %s\n" % (e))
    sys.stderr.write("could not convert expression to cnf\n%s\n" % (expr))
    exit(1)
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

def convert_z3_ast(node):
  """takes a tree and returns a list of clauses or a constant value"""
  nodetype = node[0]
  if nodetype == "or":
    left = node[1]
    right = node[2]
    l = convert_z3_ast(left)
    r = convert_z3_ast(right)

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
        # assert(isinstance(lc, list) and isinstance(rc, list))
        new_clauses.append(z3.Or(lc,rc))
    return new_clauses

  elif nodetype == "and":
    left = node[1]
    right = node[2]
    l = convert_z3_ast(left)
    r = convert_z3_ast(right)

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
    # construct new clauses by taking each pairwise combination of l and r's elements
    new_clauses = []
    for lc in l:
      for rc in r:
        # assert(isinstance(lc, list) and isinstance(rc, list))
        new_clauses.append(z3.And(lc,rc))
    return new_clauses

  elif nodetype == "not":
    negated_node = node[1]
    negated_type = negated_node[0]
    if negated_type == "name":
      z3var = lookup_z3var(negated_node[1])
      return [z3.Not(z3var)]
    if negated_type == "const":
      value = negated_node[1]
      if value == 0:
        return 1
      else:
        return 0
    elif negated_type == "not":
      return convert_z3_ast(negated_node[1]) # double-negation
    elif negated_type == "and":
      left = negated_node[1]
      right = negated_node[2]
      return convert_z3_ast(("or", ("not", left), ("not", right))) # de morgan
    elif negated_type == "or":
      left = negated_node[1]
      right = negated_node[2]
      return convert_z3_ast(("and", ("not", left), ("not", right))) # de morgan
    else:
      assert(False)

  elif nodetype == "name":
    z3var = lookup_z3var(node[1])
    return [z3var]

  elif nodetype == "const":
    return node[1]

  else:
    assert(False)

t_simplify = z3.Tactic('ctx-solver-simplify')
t_tseitin = z3.Tactic('tseitin-cnf-core')
def convert_to_z3(expr):
  try:
    ast = compiler.parse(expr)
  except RuntimeError as e:
    sys.stderr.write("exception: %s\n" % (e))
    sys.stderr.write("could not convert expression to cnf\n%s\n" % (expr))
    # exit(1)
    return []
  except:
    # handle broken expressions
    return []
  # get Discard(ACTUAL_EXPR) from Module(None, Stmt([Discard(ACTUAL_EXPR)))
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  # print ast
  transformer = Transformer()
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  tree = transformer.tree
  # print tree
  clauses = convert_z3_ast(tree)
  # print clauses
  if isinstance(clauses, list):
    # for clause in clauses:
    #   print "hello"
    #   print "really before", clause
    #   clause = z3.simplify(clause, elim_and=True)
    #   print "before", clause
    #   clause = t_tseitin(clause)
    #   print "after", clause
    #   # print clause
    #   # print "after"
    #   # g = z3.Goal()
    #   # # g.add(t_simplify(z3.simplify(clause)))
    #   # # g.add(clause)
    #   # test = z3.And(z3.Not(z3.Bool('CONFIG_CRC32')),
    #   #               z3.Bool('CONFIG_CRC32_SLICEBY8'))
    #   # # g.add(test)
    #   # test = z3.And(z3.Or(z3.Not(z3.Bool('CONFIG_CRC32')),
    #   #        z3.Bool('CONFIG_CRC32_SLICEBY8'),
    #   #        z3.Bool('CONFIG_CRC32_SLICEBY4'),
    #   #        z3.Bool('CONFIG_CRC32_SARWATE'),
    #   #        z3.Bool('CONFIG_CRC32_BIT')),
    #   #     z3.Or(z3.And(z3.Not(z3.Bool('CONFIG_CRC32_SLICEBY8')),
    #   #            z3.Not(z3.Bool('CONFIG_CRC32_SLICEBY4')),
    #   #            z3.Not(z3.Bool('CONFIG_CRC32_SARWATE')),
    #   #            z3.Not(z3.Bool('CONFIG_CRC32_BIT'))),
    #   #        z3.Bool('CONFIG_CRC32')))
    #   # # test = z3.And(z3.Not(z3.Bool('CONFIG_CRC32')),
    #   # #        z3.Bool('CONFIG_CRC32_SLICEBY8'))
    #   # test = z3.simplify(test, elim_and=True)
    #   # # test = t_simplify(test)
    #   # print test
    #   # g.add(test)
    #   # print "yo"
    #   # print t_tseitin(g)
    #   # print "next"
    #   exit(1)
    clauses = [ t_tseitin(z3.simplify(clause, elim_and=True)) if z3.is_expr(clause) else clause for clause in clauses ]
    print clauses
  if (isinstance(clauses, list)):
    return clauses
  else:
    # constants don't add any clauses
    return []

def add_clauses(expr):
  """Either convert to dimacs or to z3"""
  if use_z3:
    new_clauses = convert_to_z3(expr)
    z3_clauses.extend(new_clauses)
  else:
    new_clauses = convert_to_cnf(expr)
    # print new_clauses
    clauses.extend(new_clauses)

def pretty_printer(expr, stream=sys.stdout):
  depth = 0
  for i in range(0, len(expr)):
    if expr[i] == "(":
      if (i < len(expr) - 1 and expr[i + 1] == "("):
        stream.write("\n")
        stream.write("%s" % (". " * depth))
        stream.write("%s" % (expr[i]))
        depth += 1
      else:
        stream.write("\n")
        stream.write("%s" % (". " * depth))
        stream.write("%s" % (expr[i]))
        stream.write("\n")
        depth += 1
        stream.write("%s" % (". " * depth))
    elif expr[i] == ")":
      if (i < len(expr) - 1 and expr[i + 1] == ")"):
        stream.write("\n")
        depth -= 1
        stream.write("%s" % (". " * depth))
        stream.write("%s" % (expr[i]))
      else:
        stream.write("\n")
        depth -= 1
        stream.write("%s" % (". " * depth))
        stream.write("%s" % (expr[i]))
        stream.write("\n")
        stream.write("%s" % (". " * depth))
    elif expr[i] == " ":
      pass
    else:
      stream.write("%s" % (expr[i]))

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

# def disjunction(a, b):
#   return "((%s) or (%s))" % (a, b)

def disjunction(*args):
  return "(%s)" % (" or ".join(map(lambda x: "(%s)" % (x), args)))

def existential_disjunction(*args):
  """Create a string expression disjoining all non-null elements of args."""
  filtered_args = [ x for x in args if x is not None ]
  if len(filtered_args) == 0:
    return None
  else:
    return disjunction(*filtered_args)

def negation(a):
  if a is None:
    return a
  else:
    return "(not (%s))" % (a)

# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f) and g or h")
# print convert_to_cnf("a or b or c or d or f")
# exit(1)

# collect clauses
for line in sys.stdin:
  if debug: sys.stderr.write("started %s\n" % (line))
  instr, data = line.strip().split(" ", 1)
  if instr.startswith("#"):
    # skip a comment
    pass
  elif (instr == "config"):
    varname, typename = data.split(" ", 1)
    lookup_varnum(varname)
    if typename == "bool":
      bools.add(varname)
    else:
      nonbools.add(varname)
      nonbool_types[varname] = typename
  elif (instr == "prompt"):
    varname, condition = data.split(" ", 1)
    if varname in prompt_lines:
      sys.stderr.write("found duplicate prompt for %s. currently unsupported\n" % (varname))
    has_prompt.add(varname)
    prompt_lines[varname] = condition
  elif (instr == "env"):
    varname = data
    envs.add(varname)
    # treat variables that can be passed in as environment variables as
    # always selectable.
    has_prompt.add(varname)
    prompt_lines[varname] = "(1)"  # note: this depends on env lines being after prompt lines
  elif (instr == "def_bool"):
    var, line = data.split(" ", 1)
    def_bool_lines[var].add(line)
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
        add_clauses(full_expr)
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
    bool_choices.append((config_vars, dep_expr))
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
  elif (instr == "select"):
    selected_var, selecting_var, expr = data.split(" ", 2)
    if selected_var not in selects.keys():
      selects[selected_var] = {}
    if selecting_var not in selects[selected_var].keys():
      selects[selected_var][selecting_var] = set()
    selects[selected_var][selecting_var].add(expr)
  elif (instr == "bi"):
    expr1, expr2 = data.split("|", 1)
    # print expr1, expr2
    final_expr = "(((not %s) or %s) and ((%s) or (not %s)))" % (expr1, expr2, expr1, expr2)
    # print final_expr
    add_clauses(final_expr_expr)
  elif (instr == "constraint"):
    expr = data
    add_clauses(expr)
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

token_pattern = regex.compile("(\(|\)|[^() ]+| +)+")

def tokenize(expr):
  return token_pattern.match(expr).captures(1)

def replace_tokens(expr, match_expr, rep_expr):
  # sys.stderr.write("replace_tokens('%s', '%s', '%s')\n" % (expr, match_expr, rep_expr))
  expr_tokens = tokenize(expr)
  match_tokens = tokenize(match_expr)
  # 1 2 3 4 5
  # a a
  #   a a
  #     a a
  #       a a
  return_expr = ""
  if len(match_tokens) > len(expr_tokens):
    return_expr = expr
  elif len(match_tokens) == 0:
    return_expr = expr
  else:
    new_expr = ""
    i = 0
    while i < len(expr_tokens):
      matches = True
      for j in range(len(match_tokens)):
        if i + j < len(expr_tokens) and expr_tokens[i + j] == match_tokens[j]:
          # still matches
          pass
        else:
          matches = False
          break
      if matches:
        new_expr += rep_expr
        i += len(match_tokens)
      else:
        new_expr += expr_tokens[i]
        i += 1
    return_expr = new_expr
  # sys.stderr.write("return_expr:  %s\n" % (return_expr))
  return return_expr

def remove_direct_dep_from_rev_dep_term(term):
  # the first factor of the term is the SEL var the selects the
  # variable.  this is how kconfig stores the term.
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
      remaining_factors_replaced = replace_tokens(remaining_factors, dep_expr, "1")
      # remaining_factors_replaced_str = str.replace(remaining_factors, dep_expr, "1")
      # if remaining_factors_replaced != remaining_factors_replaced_str:
      #   sys.stderr.write("DIFF\n%s\n%s\n" % (remaining_factors_replaced, remaining_factors_replaced_str))
      # reconstruct the term
      if len(remaining_factors_replaced) > 0:
        term = "%s and %s" % (first_factor, remaining_factors_replaced)
      else:
        # the entire dependency was replaced, so the term is just the
        # reverse dependency variable
        term = first_factor
      # print "new_term", term
      return term
    else:  # it has no dependencies, so there is nothing to do
      return term

# generate clauses for boolean choices
for (config_vars, dep_expr) in bool_choices:
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
  assert len(config_vars) > 0

  # adding the following clauses:

  # dep_expr and individual_conditions -> possible_choices
  # possible_choices -> dep_expr

  # this says that, if the dependencies are met for any choice and
  # for the choice block itself, one of the options must be
  # selected.  otherwise no option needs to be selected.
  # conversely, if a choice is selected, that implies the choice
  # blocks conditions have been met.  the individual dependencies of
  # the choice options are met by the "dep" lines.

  possible_choices = ""
  individual_conditions = ""
  delim = ""
  for var in config_vars:
    possible_choices = possible_choices + delim + var
    if var in dep_exprs and dep_exprs[var] != None:
      individual_dep_expr = "(%s)" % (dep_exprs[var])
    else:
      individual_dep_expr = "(1)"
    individual_conditions = individual_conditions + delim + individual_dep_expr
    delim = " or "

  clause1 = implication(conjunction(dep_expr, individual_conditions), possible_choices)
  clause2 = implication(possible_choices, dep_expr)
  final_expression = conjunction(clause1, clause2)
  if debug_expressions:
    sys.stderr.write("bool choice")
    pretty_printer(final_expression, stream=sys.stderr)
  add_clauses(final_expression)

# generate clauses for dependencies and defaults
for var in set(dep_exprs.keys()).union(set(rev_dep_exprs.keys())).union(set(selects.keys())).union(set(def_bool_lines.keys())).union(set(prompt_lines.keys())):
  if debug: sys.stderr.write("processing %s\n" % (var))
  # get direct dependencies
  if var in dep_exprs.keys():
    dep_expr = dep_exprs[var]
    if dep_expr != "(1)":
      has_dependencies.add(var)  # track vars that have dependencies
      in_dependencies.update(get_identifiers(dep_expr))  # track vars that are in other dependencies
  else:
    dep_expr = None

  # get reverse dependencies
  if True:  # use rev_dep lines always
    if var in rev_dep_exprs.keys():
      rev_dep_expr = rev_dep_exprs[var]
      has_selects.add(var)
      if rev_dep_expr != "(1)":
        has_dependencies.add(var)  # track vars that have dependencies
        in_dependencies.update(get_identifiers(rev_dep_expr))  # track vars that are in other dependencies
    else:
      rev_dep_expr = None

    # filter out dependency expressions from configurations that are
    # reverse dependencies.  if a var SEL is a reverse dependency for
    # VAR, VAR's rev_dep_expr will contain "SEL and DIR_DEP".  we can
    # remove the DIR_DEP for SEL, since it will be covered when
    # processing SEL.  this reduces clause size.
    if rev_dep_expr != None and rev_dep_expr != "(1)":
      # get all the top-level terms of this clause.  the reverse
      # dependency will be a union of "SEL and DIR_DEP" terms,
      # representing each of the reverse dependencies.
      expr = rev_dep_expr
      if debug: sys.stderr.write("rev_dep_expr %s\n" % (rev_dep_expr))
      # (1) strip surrounding parens (as added by check_dep on all dependencies)
      if expr.startswith("(") and expr.endswith(")"): expr = expr[1:-1]
      # (2) split into ORed clauses
      terms = split_top_level_clauses(expr, " or ")
      # (3) remove the direct dependencies conjoined with the SEL vars
      # if debug: sys.stderr.write("after split: %s %s\n" % (var, terms))
      terms = map(remove_direct_dep_from_rev_dep_term, terms)
      # if debug: sys.stderr.write("after rem:   %s %s\n" % (var, terms))

      if False:  # don't ever use the unoptimized version
        rev_dep_expr = "(%s)" % (" or ".join(terms))
      else:
        # optimization to reduce cnf blowup: combine factors by
        # disjunction for top-level terms, i.e., A & D1 or A & D2 => A &
        # (D1 or D2).

        # assume the first factor is the reverse dependency and the rest
        # of the term is the reverse dependency's dependency (heuristic
        # based on how kconfig emits expressions)
        split_factors = [ term.split(" and ", 1) for term in terms ]
        # split_factors is now a list containing lists of either 1 or 2
        # elements, the former having now dependency factor.

        # aggregate split factors
        # if debug: sys.stderr.write("split_factors %s\n" % (split_factors))
        combined_terms = defaultdict(set)
        for split_factor in split_factors:
          assert len(split_factor) == 1 or len(split_factor) == 2
          if len(split_factor) == 1:
            combined_terms[split_factor[0]].add("(1)")
          elif len(split_factor) == 2:
            combined_terms[split_factor[0]].add(split_factor[1])
        # if debug: sys.stderr.write("combined_terms %s\n" % (combined_terms))

        stringified_terms = ["%s and (%s)" % (select_var, " or ".join(combined_terms[select_var]))
                             for select_var in combined_terms.keys()]
        # rev_dep_expr = "(%s)" % (" or ".join(stringified_terms))
        rev_dep_expr = "(%s)" % (" or ".join(stringified_terms))
        if debug: # sys.stderr.write("stringified %s\n" % (rev_dep_expr))
          sys.stderr.write("stringified\n")
          pretty_printer(rev_dep_expr, stream=sys.stderr)

      
  else:  # use select lines (deprecated)
    if var in selects.keys():
      has_selects.add(var)
      has_dependencies.add(var)  # track vars that have dependencies
      selecting_vars = selects[var]
      rev_dep_expr = None
      for selecting_var in selecting_vars.keys():
        deps = selecting_vars[selecting_var]

        # compute the select dependency (select_dep) for the var that
        # does the selecting.  this is complicated by the fact that one
        # var can be used many times to select the same var under
        # different conditions.
        if len(deps) == 0:
          select_dep = None
        else:
          # optimization: if any are (1), then the whole thing is (1).
          # we set it to None since it is as if there is no dependency.
          if len(filter(lambda x: x == "(1)", deps)) > 0:
            select_dep = None
          else:
            # generate the union of all dependencies for this selecting
            # var
            if len(deps) == 1:
              select_dep = list(deps)[0]
            else:
              select_dep = "(%s)" % (" or ".join(deps))
        if select_dep == None:
          selecting_term = selecting_var
        else:
          selecting_term = conjunction(selecting_var, select_dep)

        # update reverse dependency
        if rev_dep_expr == None:
          rev_dep_expr = selecting_term
        else:
          rev_dep_expr = disjunction(rev_dep_expr, selecting_term)
      in_dependencies.update(get_identifiers(rev_dep_expr))
      if debug_expressions: sys.stderr.write("rev_dep_expr: %s\n" % (rev_dep_expr))
    else:
      rev_dep_expr = None

  if args.remove_reverse_dependencies:
    rev_dep_expr = None

  # collect prompt condition
  if var in has_prompt:
    prompt_expr = prompt_lines[var]
  else:
    prompt_expr = None

  # check for bad selects
  if rev_dep_expr != None:
    good_select = var not in has_prompt or var not in has_dependencies
    if not good_select:
      if args.remove_bad_selects:
        # restrict reverse dependencies to variables that are not
        # user-visible and have no dependencies.
        sys.stderr.write("warning: removing bad select statements for %s.  this is the expression: %s\n" % (var, rev_dep_expr))
        rev_dep_expr = None
      else:
        sys.stderr.write("warning: found bad select statement(s) for %s\n" % (var))

  # collect boolean default expression
  if var in def_bool_lines.keys():
    has_defaults.add(var)
    def_y_expr = "(0)"
    delim = " or "
    for def_bool_line in def_bool_lines[var]:
      val, expr = def_bool_line.split(" ", 1)
      if val == "1":
        def_y_expr = def_y_expr + delim + "(" + expr + ")"
  else:
    def_y_expr = None

  # create clauses for dependencies and defaults
  if var in bools:
    # compute the expression for the visible condition
    super_simplified_expression = False
    if super_simplified_expression:
      # V prompt P
      # R selects V
      # V depends on D
      # V default y if F
      # V is the variable
      # D is the direct dependency
      # R is the reverse dependency
      # P is the prompt condition
      # F is the default true condition for nonvisibles

      # this is a currently broken attempt
      clauses = [
      # (P or R or D or !V) and
        [ prompt_expr, rev_dep_expr, dep_expr, negation(var) ],
      # (P or R or !D or V or !F) and
        [ prompt_expr, rev_dep_expr, negation(dep_expr), var, negation(def_y_expr) ],
      # (P or !R or V) and
        [ prompt_expr, negation(rev_dep_expr), var ],
      # (P or !V or !F) and
        [ prompt_expr, negation(var), def_y_expr ],
      # (!P or R or D or !V) and
        [ negation(prompt_expr), rev_dep_expr, dep_expr, negation(var) ],
      # (R or D or !V) and
        [ rev_dep_expr, dep_expr, negation(var) ],
      # (R or D or !V or !F) and
        [ rev_dep_expr, dep_expr, negation(var), negation(def_y_expr) ],
      # (!P or !R or V) and
        [ negation(prompt_expr), negation(rev_dep_expr), var ],
      # (R! or V)
        [ negation(rev_dep_expr), var ]
      ]
      for clause in clauses:
        if clause is not None:
          expression = existential_disjunction(*clause)
          add_clauses(expression)
        
    else:
      if var not in has_prompt:
        # don't bother computing the visible expression if there is no
        # prompt, because it couldn't be user-selectable
        visible_expr = None
      else:
        if dep_expr != None and rev_dep_expr == None:
          # only direct dependency
          visible_expr = implication(var, dep_expr)
        elif dep_expr == None and rev_dep_expr != None:
          # only reverse dependency
          visible_expr = implication(rev_dep_expr, var)
          pass
        elif dep_expr != None and rev_dep_expr != None:
          # both kinds
          clause1 = disjunction(rev_dep_expr, disjunction(dep_expr, negation(var)))
          clause2 = disjunction(negation(rev_dep_expr), var)
          visible_expr = conjunction(clause1, clause2)

          # # unsimplified form
          # clause1 = conjunction(rev_dep_expr, var)
          # clause2 = conjunction(negation(rev_dep_expr), implication(var, dep_expr))
          # visible_expr = disjunction(clause1, clause2)
          pass
        else:
          # neither kind means it's a free variable
          visible_expr = None

        if args.include_bool_defaults and var in def_bool_lines.keys():
          sys.stderr.write("warning: defaults are ignored for visibles, because they are user-selectable: %s\n" % (var))

        # # V -> (E | A) and A -> V, where E is direct dep, and A is reverse dep

        # # intuitively, this makes sense.  if V is on, then either its
        # # direct dependency E or reverse dependency A must have been
        # # satisfied.  if the direct dependency is off, then the variable
        # # must have only been set when its reverse dependency is set
        # # (biimplication).


        # # clause1 = var -> (dep_expr or rev_dep_expr)
        # # clause2 = rev_dep_expr -> var

        # if rev_dep_expr != None:
        #   if dep_expr != None:
        #     clause1 = implication(var, disjunction(dep_expr, rev_dep_expr))
        #     clause2 = implication(rev_dep_expr, var)
        #     visible_expr = conjunction(clause1, clause2)
        #   else: # no direct dependency means biimplication between rev_dep and var
        #     visible_expr = biimplication(var, rev_dep_expr)
        # else:
        #   if dep_expr != None:  # no reverse dependency means that only the direct dependency applies
        #     clause1 = implication(var, dep_expr)
        #     clause2 = None
        #     visible_expr = clause1
        #   else: # no direct or reverse dependencies
        #     clause1 = None
        #     clause2 = None
        #     visible_expr = None

      # compute the expression for the nonvisible condition
      # if prompt_expr == "(1)" or prompt_expr == dep_expr:
      #   sys.stderr.write("no prompt\n")
      if prompt_expr == "(1)":
        # there is no possibility of the variable being nonvisible, so
        # don't bother computing the expression
        nonvisible_expr = None
      else:
        # nonvisibles that have no default, default to off
        if def_y_expr == None:
          def_y_expr = "(0)"
        simplified_nonvisibles = False
        if simplified_nonvisibles:
          # visible
          # elif dep_expr != None and rev_dep_expr != None:
            # clause1 = disjunction(rev_dep_expr, disjunction(dep_expr, negation(var)))
            # clause2 = disjunction(negation(rev_dep_expr), var)
            # visible_expr = conjunction(clause1, clause2)


          # A rev_dep_expr
          # B dep_expr
          # Idef def_y_expr
          # I var

          # unsimplified:
          # (rev_dep_expr and var) or (not rev_dep_expr and (var biimp (dep_expr and def_y_expr)))

          # simplified
          # (    A or     B or not I            ) and
          # (    A or not B or     I or not Idef) and
          # (not A          or     I            ) and
          # (         not B or     I or not Idef)


          if dep_expr != None and rev_dep_expr == None:
            clause1 = disjunction(dep_expr, negation(var))
            clause2 = disjunction(negation(dep_expr), disjunction(var, negation(def_y_expr)))
            clause3 = var
            clause4 = disjunction(negation(dep_expr), disjunction(var, negation(def_y_expr)))
            nonvisible_expr = conjunction(clause1, conjunction(clause2, conjunction(clause3, clause4)))
          elif dep_expr == None and rev_dep_expr != None:
            clause1 = "(1)"
            clause2 = disjunction(rev_dep_expr, disjunction(var, negation(def_y_expr)))
            clause3 = disjunction(negation(rev_dep_expr), var)
            clause4 = disjunction(var, negation(def_y_expr))
            nonvisible_expr = conjunction(clause1, conjunction(clause2, conjunction(clause3, clause4)))
          elif dep_expr != None and rev_dep_expr != None:
            clause1 = disjunction(rev_dep_expr, disjunction(dep_expr, negation(var)))
            clause2 = disjunction(rev_dep_expr, disjunction(negation(dep_expr), disjunction(var, negation(def_y_expr))))
            clause3 = disjunction(negation(rev_dep_expr), var)
            clause4 = disjunction(negation(dep_expr), disjunction(var, negation(def_y_expr)))
            nonvisible_expr = conjunction(clause1, conjunction(clause2, conjunction(clause3, clause4)))
          else:
            clause1 = "(1)"
            clause2 = disjunction(rev_dep_expr, disjunction(var, negation(def_y_expr)))
            clause3 = disjunction(negation(rev_dep_expr), var)
            clause4 = disjunction(var, negation(def_y_expr))
            nonvisible_expr = conjunction(clause1, conjunction(clause2, conjunction(clause3, clause4)))

        else:
          # old
          
          # I <-> ((E & D) | A)
          # I is the variable, A is the selects (reverse deps), E is the direct dep, D is the default y condition

          # because nonvisible variables cannot be modified by the user
          # interactively, we use a bi-implication between it's dependencies
          # and default values and selects.  this says that the default
          # value will be taken as long as the conditions are met.
          # nonvisibles default to off if these conditions are not met.

          # var biimp (dep_expr and def_y_expr or rev_dep_expr)
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
            nonvisible_expr = biimplication(var, consequent)
            # print nonvisible_expr
          else:
            nonvisible_expr = None

      # compute the complete expression for the variable
      # prompt_expr and visible_expr or not prompt_expr and nonvisible_expr
      if visible_expr != None:
        if prompt_expr != None:
          cond_visible_expr = conjunction(prompt_expr, visible_expr)
        else:
          # if there is no prompt expression, it means there is no possibility of visibility
          cond_visible_expr = None
      else:
        cond_visible_expr = None

      if nonvisible_expr != None:
        if prompt_expr != None:
          cond_nonvisible_expr = conjunction(negation(prompt_expr), nonvisible_expr)
        else:
          # if there is no prompt_expr, it means the variable is unconditionally nonvisible
          cond_nonvisible_expr = nonvisible_expr
      else:
        cond_nonvisible_expr = None

      if debug_expressions: sys.stderr.write("var %s\n" % (var))
      if debug_expressions: sys.stderr.write("unconditional visible %s\n" % (visible_expr))
      if debug_expressions: sys.stderr.write("visible %s\n" % (cond_visible_expr))
      if debug_expressions: sys.stderr.write("unconditional nonvisible %s\n" % (cond_nonvisible_expr))
      if debug_expressions: sys.stderr.write("nonvisible %s\n" % (cond_nonvisible_expr))

      if cond_visible_expr != None and cond_nonvisible_expr != None:
        final_expr = disjunction(cond_visible_expr, cond_nonvisible_expr)
      elif cond_visible_expr != None and cond_nonvisible_expr == None:
        final_expr = cond_visible_expr
      elif cond_visible_expr == None and cond_nonvisible_expr != None:
        final_expr = cond_nonvisible_expr
      else: # cond_visible_expr == None and cond_nonvisible_expr == None:
        final_expr = None

      if final_expr != None:
        if debug_expressions: sys.stderr.write("%s final expression is %s\n" % (var, final_expr))
        add_clauses(final_expr)
        
  elif var in nonbools:
    nonbools_with_dep.add(var)
    if var not in has_prompt:
      # no support for nonbool nonvisibles, because we don't support
      # nonboolean constraints and there is no way for the user to
      # directly modify these.
      nonbools_nonvisibles.add(var)
      sys.stderr.write("warning: no support for nonvisible nonbools: %s\n" % (var))
    else:  # var is visible
      if rev_dep_expr != None:
        sys.stderr.write("warning: no support for reverse dependencies on nonbooleans: %s\n" % (var))
      # include the prompt condition as part of the dependency
      if prompt_expr != None and dep_expr != None:
        dep_expr = conjunction(prompt_expr, dep_expr)
      elif prompt_expr != None and dep_expr == None:
        dep_expr = prompt_expr
      # bi-implication var <-> dep_expr, because a nonboolean always
      # has a value as long as its dependencies are met.
      if dep_expr == None:
        # the nonbool is always on when no dependencies
        final_expr = var
      else:
        final_expr = biimplication(var, dep_expr)
      # print final_expr
      add_clauses(final_expr)
  else:
    assert True

if use_z3:
  # print clauses for now
  # for clause in z3_clauses:
  #   print clause
  final_z3 = z3.And([ x for x in z3_clauses if z3.is_expr(x) ])
  print final_z3

  s = z3.Solver()
  # s.add(z3.Not(final_z3))
  s.add(final_z3)
  print s.check()

  # s = z3.Solver()
  # s.add(z3.Not(final_z3))
  # print s.check()

  # quit and don't do dimacs clause processing
  exit(1)

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
    args.remove_all_nonvisibles and var not in has_prompt or \
    args.remove_independent_nonvisibles and var not in has_prompt and var not in in_dependencies or \
    args.remove_orphaned_nonvisibles and var not in has_prompt and var in bools and var not in in_dependencies and var not in has_defaults and var not in has_selects

if debug: sys.stderr.write("filtering vars\n")
keep_vars = filter(lambda var: not remove_condition(var), varnums.keys())
keep_varnums = filter(lambda (name, num): name in keep_vars, sorted(varnums.items(), key=lambda tup: tup[1]))

for var in varnums.keys():
  if var not in has_prompt and var in bools and var not in has_defaults and var not in has_selects:
    if args.remove_orphaned_nonvisibles:
      sys.stderr.write("warning: remove orphaned nonvisible variables: %s\n" % (var))
    else:
      sys.stderr.write("warning: %s is an orphaned nonvisible variable\n" % (var))
    
if debug: sys.stderr.write("renumbering\n")
# renumber variables
num_mapping = {}
for (name, old_num) in keep_varnums:
  num_mapping[old_num] = len(num_mapping) + 1

# update varnums
varnums = {name: num_mapping[old_num] for (name, old_num) in keep_varnums}

if debug: sys.stderr.write("trimming clauses\n")
# remove vars from clauses
filtered_clauses = []
original_num_clauses = len(clauses)
num_processed = 0
start_time = time.time()
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
  num_processed += 1
  if debug:
    if time.time() - start_time > 2:
      sys.stderr.write("trimmed %s/%s clauses\n" % (num_processed, original_num_clauses))
      start_time = time.time()
if debug: sys.stderr.write("finished trimming %s/%s clauses\n" % (num_processed, original_num_clauses))

def is_true(clause):
  neg = set()
  pos = set()
  for elem in clause:
    if elem > 0:
      if abs(elem) in neg:
        return True
      pos.add(abs(elem))
      pass
    elif elem < 0:
      if abs(elem) in pos:
        return True
      neg.add(abs(elem))
      pass
    else:
      # should never have a varnum of 0
      assert True
  return False
    
if debug: sys.stderr.write("trimming true clauses\n")
# remove true clauses
if remove_true_clauses:
  filtered_clauses = filter(lambda x: not is_true(x), filtered_clauses)

if debug: sys.stderr.write("stringifying clauses\n")
# convert clauses to strings
string_clauses = ["%s 0" % (" ".join([str(num) for num in sorted(clause, key=abs)])) for clause in filtered_clauses]

if debug: sys.stderr.write("deduplicating clauses\n")
# deduplicate clauses
if deduplicate_clauses:
  string_clauses = list(set(string_clauses))

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
        if nonbool_types[varname] == "string":
          defaultval = defaultval.replace("\\", "\\\\") # escape
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
      elif varname in has_prompt:
        print "%s %d %s bool" % (comment_prefix, varnum_map[varname], varname)
      elif varname in ghost_bools.keys():
        nonbool_var, defval = ghost_bools[varname]
        print "%s %d %s ghost_bool %s %s" % (comment_prefix, varnum_map[varname], varname, nonbool_var, defval)
      else:
        print "%s %d %s hidden_bool" % (comment_prefix, varnum_map[varname], varname)
  print "p cnf %d %d" % (len(varnum_map), len(clause_list))
  for clause in clause_list:
    print clause

if debug: sys.stderr.write("printing dimacs file\n")
print_dimacs(varnums, string_clauses)
sys.stderr.write("done\n")
