import traceback
import sys
import compiler
import z3

t_simplify = z3.Tactic('ctx-solver-simplify')
t_tseitin = z3.Tactic('tseitin-cnf-core')

# parse tree processing
class Transformer(compiler.visitor.ASTVisitor):
  def __init__(self):
    compiler.visitor.ASTVisitor.__init__(self)
    self.tree = None

  def default(self, node):
    # sys.stderr.write("default %s\n" % (str(node)))
    if isinstance(node, int):
      if node == 0:
        return z3.BoolVal(False)
      else:
        return z3.BoolVal(True)
    elif isinstance(node, str):
      return z3.Bool(node)
    else:
      # sys.stderr.write("predicate %d %s\n" % (len(node.getChildren()), str(node)))
      predicate = str(node)
      return z3.Bool("PREDICATE_%s" % (predicate))

  def visitDiscard(self, node):
    self.tree = self.visit(node.getChildren()[0])

  def visitOr(self, node):
    # sys.stderr.write("or %s\n" % (str(node)))
    children = node.getChildren()
    return z3.Or([self.visit(child) for child in children])

  def visitAnd(self, node):
    # sys.stderr.write("and %s\n" % (str(node)))
    children = node.getChildren()
    return z3.And([self.visit(child) for child in children])

  def visitNot(self, node):
    # sys.stderr.write("not %s\n" % (str(node)))
    return z3.Not(self.visit(node.expr))

  def visitName(self, node):
    # sys.stderr.write("name %s\n" % (str(node)))
    return z3.Bool(node.name)

  def visitConst(self, node):
    # sys.stderr.write("const %s %s\n" % (str(node), str(type(node.value))))
    value = node.value
    if isinstance(value, int):
      if value == 0:
        return z3.BoolVal(False)
      else:
        return z3.BoolVal(True)
    try:
      num = int(value)
      if num == 0:
        return z3.BoolVal(False)
      else:
        return z3.BoolVal(True)
    except:
      try:
        s = str(value)
        if s is "0":
          return z3.BoolVal(False)
        elif s is "1":
          return z3.BoolVal(True)
        dummy_var = "VALUE_%s" % (s)
        # sys.stderr.write("warning: use of undefined variable in dependency: %s\n" % (dummy_var))
        return z3.Bool(dummy_var)
      except:
        print(traceback.format_exc())
        sys.stderr.write("error: cannot process value \"%s\"\n" % (value))
        exit(1)

# parse tree processing
class IdentifierCollector(compiler.visitor.ASTVisitor):
  def __init__(self):
    compiler.visitor.ASTVisitor.__init__(self)
    self.tree = ()

  def default(self, node):
    predicate = str(node)
    return ["PREDICATE_%s" % (predicate)]

  def visitDiscard(self, node):
    self.tree = self.visit(node.getChildren()[0])

  def visitOr(self, node):
    children = node.getChildren()
    left = []
    for i in range(0, len(children)):
      left.extend(self.visit(children[i]))
    return left

  def visitAnd(self, node):
    children = node.getChildren()
    left = []
    for i in range(0, len(children)):
      left.extend(self.visit(children[i]))
    return left

  def visitNot(self, node):
    return self.visit(node.expr)

  def visitName(self, node):
    return [node.name]

  def visitConst(self, node):
    return []

def get_identifiers(expr):
  try:
    ast = compiler.parse(expr)
  except:
    sys.stderr.write("error: could not parse %s\n" % (line))
    sys.stderr.write(traceback.format_exc())
    sys.stderr.write("\n")
    return []
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  transformer = IdentifierCollector()
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  return transformer.tree

def convert_to_z3(expr):
  try:
    ast = compiler.parse(expr)
  except RuntimeError as e:
    sys.stderr.write("exception: %s\n" % (e))
    sys.stderr.write("could not convert expression to cnf\n%s\n" % (expr))
    exit(1)
    return []
  except:
    # handle broken expressions
    sys.stderr.write("warning: couldn't parse %s\n" % (expr))
    exit(1)
    return []
  actual_expr = ast.getChildNodes()[0].getChildNodes()[0]
  transformer = Transformer()
  # sys.stderr.write("actual_expr %s\n" % (str(actual_expr)))
  compiler.walk(actual_expr, transformer, walker=transformer, verbose=True)
  z3_clause = transformer.tree
  # sys.stderr.write("z3_clause %s\n" % (str(z3_clause)))
  return z3.simplify(z3_clause)
