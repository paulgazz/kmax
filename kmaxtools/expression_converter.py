import traceback
import sys
import compiler
import z3
import regex

t_simplify = z3.Tactic('ctx-solver-simplify')
t_tseitin = z3.Tactic('tseitin-cnf-core')
identifier_pattern = regex.compile("^[A-Za-z0-9_]+$") # config var names can start with numbers, see kconfig/lexer.l
int_pattern = regex.compile("^[0-9]+$")
hex_pattern = regex.compile("^0x[0-9ABCDEFabcdef]+$")

def glean_unknown_symbol(sym):
  sym = str(sym)
  # sys.stderr.write("trying to glean unknown symbol: \"%s\"\n" % (sym))
  if int_pattern.match(sym):
    num = int(sym)
    if num == 0:
      return z3.BoolVal(False)
    else:
      return z3.BoolVal(True)
  elif hex_pattern.match(sym):
    return z3.Bool("\"%s\"" % (sym))
  # elif identifier_pattern.match(sym):
  #   return z3.Bool("CONFIG_%s" % (sym))
  else:
    return z3.StringVal(sym)

# parse tree processing
class Transformer(compiler.visitor.ASTVisitor):
  def __init__(self):
    compiler.visitor.ASTVisitor.__init__(self)
    self.tree = None

  def default(self, node):
    # sys.stderr.write("trying to process default: \"%s\"\n" % (node))
    result = glean_unknown_symbol(node)
    # sys.stderr.write("result: %s\n" % (result))
    if result is not None:
      return result
    else:
      predicate = str(node)
      return z3.Bool("PREDICATE_%s" % (predicate))

  def visitCompare(self, node):
    children = node.getChildren()
    if len(children) == 3:
      left = node.getChildren()[0]
      op = str(node.getChildren()[1])
      if op == "==" or op == "!=":
        right = node.getChildren()[2]
        left_z3 = self.visit(left)
        right_z3 = self.visit(right)
        if z3.is_string(left_z3) and z3.is_string(right_z3) or z3.is_bool(left_z3) and z3.is_bool(right_z3):
          if op == "==":
            result = z3.simplify(z3.Not(z3.Distinct(left_z3, right_z3)))
            return result
          elif op == "!=":
            # sys.stderr.write("%s != %s\n" % (left_z3, right_z3))
            result = z3.simplify(z3.Distinct(left_z3, right_z3))
            return result
        # elif z3.is_string(left_z3) and z3.is_bool(right_z3):
        #   if op == "==":
        #     pass
        #   elif op == "!=":
        #     pass
        # elif z3.is_bool(left_z3) and z3.is_string(right_z3):
        #   if op == "==":
        #     pass
        #   elif op == "!=":
        #     pass
          
    # this expression is not supported, so make a predicate variable for it
    predicate = str(node)
    return z3.Bool("PREDICATE_%s" % (predicate))

  def visitDiscard(self, node):
    # sys.stderr.write("%s\n" % (node.getChildren()[0]))
    self.tree = self.visit(node.getChildren()[0])
    # sys.stderr.write("%s\n" % (self.tree))

  def visitOr(self, node):
    # sys.stderr.write("or %s\n" % (str(node)))
    children = node.getChildren()
    # sys.stderr.write("%s\n" % str(children))
    operands = [self.visit(child) for child in children]
    # sys.stderr.write("%s\n" % str(operands))
    # for child in operands:
    #   sys.stderr.write("%s\n" % str(child))
    #   sys.stderr.write("%s\n" % str(z3.is_bool(child)))
    operands = [(child if z3.is_bool(child) else z3.BoolVal(False)) for child in operands]
    return z3.Or(operands)

  def visitAnd(self, node):
    # sys.stderr.write("and %s\n" % (str(node)))
    children = node.getChildren()
    # sys.stderr.write("%s\n" % str(children))
    operands = [self.visit(child) for child in children]
    # sys.stderr.write("%s\n" % str(operands))
    # for child in operands:
    #   sys.stderr.write("%s\n" % str(child))
    #   sys.stderr.write("%s\n" % str(z3.is_bool(child)))
    operands = [(child if z3.is_bool(child) else z3.BoolVal(False)) for child in operands]
    return z3.And(operands)

  def visitNot(self, node):
    # sys.stderr.write("not %s\n" % (str(node)))
    operand = self.visit(node.expr)
    if z3.is_bool(operand):
      return z3.Not(operand)
    else:
      return z3.BoolVal(True)

  def visitName(self, node):
    # sys.stderr.write("name %s\n" % (str(node)))
    result = z3.Bool(node.name)
    # sys.stderr.write("name z3 %s\n" % (str(result)))
    # sys.stderr.write("name is_bool %s\n" % (str(z3.is_bool(result))))
    return result

  def visitConst(self, node):
    # sys.stderr.write("const %s %s\n" % (str(node), str(type(node.value))))
    value = node.value
    result = glean_unknown_symbol(value)
    # sys.stderr.write("result const: %s\n" % (result))
    if result is not None:
      return result
    else:
      print(traceback.format_exc())
      sys.stderr.write("error: cannot process value \"%s\"\n" % (value))
      exit(1)
      return None

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
