import os
import sys
import compiler
import ast

# this script takes the check_dep --dimacs output and converts it into
# a dimacs-compatible format

root_var = "SPECIAL_ROOT_VARIABLE"
use_root_var = False

varnums = {}
userselectable = set()

nonbools = set()
nonbools_with_dep = set()
nonbool_defaults = {}
nonbool_types = {}

ghost_bools = {}

# whether to leave only those config vars that can be selected by the
# user.  this is defined as config vars that have a kconfig prompt.
remove_nonselectable_variables = True

# add constraints that reflect the conditions under which boolean
# default values are set.  off by default.
support_bool_defaults = False

# support non-boolean defaults by creating a new boolean variable for
# each nonbool default value.  off by default.
support_nonbool_defaults = False

# whether to always enable nonbools or not regardless of whether they
# have dependencies.  off by default.  warning: forcing nonbools that
# have dependencies can restrict the space of configurations because
# this just adds the nonbools as clauses; this is not recommended.
force_all_nonbools_on = False

def lookup_varnum(varname):
  if remove_nonselectable_variables and varname not in userselectable:
    return 0
  else:
    if varname not in varnums:
      varnums[varname] = len(varnums) + 1
    return varnums[varname]

ghost_bool_count = 0
def get_ghost_bool_name(var):
  global ghost_bool_count
  ghost_bool_count += 1
  return "GHOST_BOOL_%d_%s" % (ghost_bool_count, var)

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
    return ("name", "PREDICATE")

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
    return ("const", int(node.value))

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
  ast = compiler.parse(expr)
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

# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f)")
# print convert_to_cnf("not a or (b and (c or d)) and not (e and f) and g or h")
# print convert_to_cnf("a or b or c or d or f")
# exit(1)

clauses = []
if use_root_var:
  userselectable.add(root_var)
  clauses.append([lookup_varnum(root_var)])
for line in sys.stdin:
  sys.stderr.write("started %s\n" % (line))
  instr, data = line.strip().split(" ", 1)
  if (instr == "bool"):
    varname, selectability = data.split(" ", 1)
    selectable = True if selectability == "selectable" else False
    if selectable:
      userselectable.add(varname)
    lookup_varnum(varname)
  elif (instr == "def_bool"):
    var, val, expr = data.split(" ", 2)
    if support_bool_defaults:
      if val == "1":
        defsetting = True
      elif val == "0":
        defsetting = False
      else:
        defsetting = None
        sys.stderr.write("invalid default value for bool: %s\n" % (line))
        exit(1)
      if expr == "(1)":
        # default value is always set
        varnum = lookup_varnum(var)
        if defsetting:
          clauses.append([varnum])
        else:
          clauses.append([-varnum])
      else:
        # default is set if dependency holds
        # expr -> defexpr, i.e., not expr or defexpr
        if defsetting:
          defexpr = var
        else:
          defexpr = "not " + var
        full_expr = "(not (" + expr + ")) or (" + defexpr + ")"
        # print line
        # print full_expr
        new_clauses = convert_to_cnf(full_expr)
        # print new_clauses
        clauses.extend(new_clauses)
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
    if support_nonbool_defaults:
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
  elif (instr == "dep"):  # assumes only one dep line per unique variable
    # print instr,data
    var, expr = data.split(" ", 1)
    # if no dependencies, then depend on special root variable
    if use_root_var and expr == "(1)":
      expr = root_var
    # if no dependencies, don't add any clause
    if expr != "(1)":
      # var -> expr, i.e., not var or expr
      full_expr = "(not (" + var + ")) or (" + expr + ")"
      # print full_expr
      new_clauses = convert_to_cnf(full_expr)
      # print new_clauses
      clauses.extend(new_clauses)
    if var in nonbools:
      # nonbools are mandatory unless disabled by dependency, so we
      # also ensure that nonbool var is selected whenever its
      # dependencies holds.
      full_expr = "(not (" + expr + ")) or (" + var + ")"
      # print full_expr
      new_clauses = convert_to_cnf(full_expr)
      # print new_clauses
      clauses.extend(new_clauses)
      nonbools_with_dep.add(var)
  else:
    sys.stderr.write("unsupported instruction: %s\n" % (line))
    exit(1)
  sys.stderr.write("done %s\n" % (line))

# if force_independent_nonbools_on:
#   # this should be covered by "nonbools are mandatory unless disabled
#   # by dependency" above"
#   for nonbool in (nonbools - nonbools_with_dep):
#     varnum = lookup_varnum(nonbool)
#     clauses.append([varnum])

if force_all_nonbools_on:
  for nonbool in (nonbools):
    varnum = lookup_varnum(nonbool)
    clauses.append([varnum])

for varname in sorted(varnums, key=varnums.get):
  if varname in nonbools:
    if varname in nonbool_defaults:
      defaultval = nonbool_defaults[varname]
    else:
      defaultval = '""' if nonbool_types[varname] == "string" else "0"
    defaultval = " " + defaultval
    print "c %d %s nonbool%s" % (varnums[varname], varname, defaultval)
  else:
    if varname in userselectable:
      print "c %d %s bool" % (varnums[varname], varname)
    elif varname in ghost_bools.keys():
      nonbool_var, defval = ghost_bools[varname]
      print "c %d %s ghost_bool %s %s" % (varnums[varname], varname, nonbool_var, defval)
    else:
      print "c %d %s hidden_bool" % (varnums[varname], varname)

def remove_dups(l):
  # clause = list(set(clause)) # doesn't preserve order
  seen = set()
  seen_add = seen.add
  return [x for x in l if not (x in seen or seen_add(x))]

filtered_clauses = []
for clause in clauses:
  clause = remove_dups(clause)
  if remove_nonselectable_variables:
    # trim undefined vars from clauses
    modified_clause = filter(lambda x: x != 0, clause)
    if len(modified_clause) == 1 and len(clause) > 1:
      # if all vars but one was removed, then there is no constraint
      pass
    elif len(modified_clause) == 0:
      # nothing to print now
      pass
    else:
      filtered_clauses.append(modified_clause)
  else:
    filtered_clauses.append(clause)

print "p cnf %d %d" % (len(varnums), len(filtered_clauses))
for clause in filtered_clauses:
  print "%s 0" % (" ".join([str(num) for num in clause]))
