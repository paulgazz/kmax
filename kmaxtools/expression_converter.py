import traceback
import sys
import compiler
import z3

# names of variables that should be removed later. this is currently
# used to captures string constants in boolean expressions, where it
# isn't clear what the boolean value should be.
variables_to_remove = set()

flatten = False

t_simplify = z3.Tactic('ctx-solver-simplify')
t_tseitin = z3.Tactic('tseitin-cnf-core')

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

def walk_ast_flatten(node):
  """takes a tree and returns a list of clauses or a constant value"""
  nodetype = node[0]
  if nodetype == "or":
    left = node[1]
    right = node[2]
    l = walk_ast_flatten(left)
    r = walk_ast_flatten(right)

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
    l = walk_ast_flatten(left)
    r = walk_ast_flatten(right)

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
      z3var = z3.Bool(negated_node[1])
      return [z3.Not(z3var)]
    if negated_type == "const":
      value = negated_node[1]
      if value == 0:
        return 1
      else:
        return 0
    elif negated_type == "not":
      return walk_ast_flatten(negated_node[1]) # double-negation
    elif negated_type == "and":
      left = negated_node[1]
      right = negated_node[2]
      return walk_ast_flatten(("or", ("not", left), ("not", right))) # de morgan
    elif negated_type == "or":
      left = negated_node[1]
      right = negated_node[2]
      return walk_ast_flatten(("and", ("not", left), ("not", right))) # de morgan
    else:
      assert(False)

  elif nodetype == "name":
    z3var = z3.Bool(node[1])
    return [z3var]

  elif nodetype == "const":
    return node[1]

  else:
    assert(False)

def walk_ast_normal(node):
  """takes a tree and returns a list of clauses or a constant value"""
  nodetype = node[0]
  if nodetype == "or":
    left = node[1]
    right = node[2]
    l = walk_ast_normal(left)
    r = walk_ast_normal(right)

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

    return z3.Or(l, r)

  elif nodetype == "and":
    left = node[1]
    right = node[2]
    l = walk_ast_normal(left)
    r = walk_ast_normal(right)

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

    return z3.And(l, r)

  elif nodetype == "not":
    negated_node = node[1]
    negated_type = negated_node[0]
    if negated_type == "name":
      z3var = z3.Bool(negated_node[1])
      return z3.Not(z3var)
    if negated_type == "const":
      value = negated_node[1]
      if value == 0:
        return 1
      else:
        return 0
    elif negated_type == "not" or negated_type == "and" or negated_type == "or":
      # print(negated_node)
      z3_node = walk_ast_normal(negated_node)
      if isinstance(z3_node, int):
        return z3_node
      else:
        return z3.Not(z3_node)
    else:
      assert(False)

  elif nodetype == "name":
    z3var = z3.Bool(node[1])
    # print("FJKDLS", z3var)
    return z3var

  elif nodetype == "const":
    return node[1]

  else:
    assert(False)

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
    sys.stderr.write("warning: couldn't parse %s\n" % (expr))
    return []
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  transformer = Transformer()
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  tree = transformer.tree

  # flatten or not to flatten
  if not flatten:
    clause = walk_ast_normal(tree)
    if z3.is_expr(clause):
      # clause = t_simplify(clause)
      clause = clause
    else: # constants don't add clauses
      clause = None
    return clause
  else:
    clauses = walk_ast_flatten(tree)
    clauses = [ t_simplify(clause) if z3.is_expr(clause) else clause for clause in clauses ]
    if (isinstance(clauses, list)) and len(clauses) > 0:
      return z3.And(clauses)
    else:
      # constants don't add any clauses
      return None
