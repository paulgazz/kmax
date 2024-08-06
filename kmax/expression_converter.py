import traceback
import sys
import ast
import z3
import regex
from kmax.kclause import tristate_config_gen

# Documentation of ast and the visitors: https://greentreesnakes.readthedocs.io/en/latest/nodes.html

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
class Converter(ast.NodeVisitor):
  def __init__(self, allow_tristate=True):
    ast.NodeVisitor.__init__(self)
    self.z3 = None
    self.allow_tristate = allow_tristate

  def result(self):
    return self.z3

  def visit_Expr(self, node):
    self.generic_visit(node)
    node.z3 = node.value.z3
    self.z3 = node.z3

  def visit_BoolOp(self, node):
    self.generic_visit(node)
    operands = []
    for value in node.values:
      operands.append(value.z3)
    # string values should not normally appear in boolean expressions,
    # but this can happen when there are undefined configuration
    # options used in expressions.  instead of throwing an error,
    # kconfig treats the usage of undefined configuration options
    # (identifiers) as strings.  such strings are assumed to be false,
    # since they aren't options that can ever be true.  (see visit_UnaryOp)
    operands = [(operand if z3.is_bool(operand) else z3.BoolVal(False)) for operand in operands]
    if node.op.name == "and":
      node.z3 = z3.And(operands)
    elif node.op.name == "or":
      node.z3 = z3.Or(operands)
    else:
      assert(False)

  def visit_And(self, node):
    node.name = "and"

  def visit_Or(self, node):
    node.name = "or"

  def visit_Not(self, node):
    node.name = "not"

  def visit_BinOp(self, node):
    self.generic_visit(node)
    # string values should not normally appear in expressions,
    # but this can happen when there are undefined configuration
    # options used in expressions.  instead of throwing an error,
    # kconfig treats the usage of undefined configuration options
    # (identifiers) as strings.  such strings are assumed to be false,
    # since they aren't options that can ever be true.  (see visit_UnaryOp)
    leftoperand = node.left.z3 if z3.is_bool(node.left.z3) else z3.BoolVal(False)
    rightoperand = node.right.z3 if z3.is_bool(node.right.z3) else z3.BoolVal(False)

    if node.op.name == "xor":
      node.z3 = z3.Xor(leftoperand, rightoperand)
    else:
      print(node.op)
      assert(False)

  def visit_BitXor(self, node):
    node.name = "xor"

  def visit_UnaryOp(self, node):
    self.generic_visit(node)
    operand = node.operand.z3
    # print("lalalal")
    # print(operand)
    if node.op.name == "not":
      if z3.is_bool(operand):
        node.z3 = z3.Not(operand)
      else:
        # the expression could be a stringval in the case of the usage
        # of an undefined configuration option, which kconfig allows.
        # we treat such variables are always off, so negating that
        # variable makes it always true.  we can't assume all strings
        # are undefined variables, because string constants are also
        # permitted in kconfig.  such string constants have a false
        # value anyway.  (see visit_BoolOp)
        node.z3 = z3.BoolVal(True)
    else:
      assert(False)

  def visit_Constant(self, node):
    # sys.stderr.write("const %s %s\n" % (str(node), str(type(node.value))))
    value = node.value
    result = glean_unknown_symbol(value)
    # sys.stderr.write("result const: %s\n" % (result))
    if result is not None:
      node.z3 = result
    else:
      print((traceback.format_exc()))
      sys.stderr.write("error: cannot process value \"%s\"\n" % (value))
      exit(1)
      node.z3 = None

  def visit_Num(self, node):  # deprecated since 3.8, replaced by constant
    num = node.n
    if num == 0:
      node.z3 = z3.BoolVal(False)
    else:
      node.z3 = z3.BoolVal(True)

  def visit_Str(self, node):  # deprecated since 3.8, replaced by constant
    value = node.s
    result = glean_unknown_symbol(value)
    if result is not None:
      node.z3 = result
    else:
      print((traceback.format_exc()))
      sys.stderr.write("error: cannot process value \"%s\"\n" % (value))
      exit(1)
      node.z3 = None

  def visit_Name(self, node):
    # sys.stderr.write("name %s\n" % (str(node)))
    node.z3 = z3.Bool(node.id)
    # sys.stderr.write("name z3 %s\n" % (str(result)))
    # sys.stderr.write("name is_bool %s\n" % (str(z3.is_bool(result))))
    
  def visit_Compare(self, node):
    self.generic_visit(node)
    if len(node.ops) > 1:
      # kconfig constraints aren't expected to have multiple operators in a comparison expression
      assert(False)
    left = node.left.z3
    op = node.ops[0].name
    right = node.comparators[0].z3

    # model non-Boolean operators by creating a predicate variable.
    # TODO: model relational expressions and expressions between variables and strings in Z3
    predicate = str(ast.dump(node))
    node.z3 = z3.Bool("PREDICATE_%s" % (predicate))

    if z3.is_bool(right) and (str(right) == "y" or str(right) == "m") and z3.is_bool(left):
      assert op != "ne" # kextractor should not check for ne to m or y but instead wrap it in a "not" expression
      # print(right)
      option_name = str(left)
      if self.allow_tristate:
        # replace the option with its tristate variant
        # kclause then needs to add additional constraints the connect the boolean option with its tristate variants
        tristate_name = tristate_config_gen(option_name, str(right))
        node.z3 = z3.Bool(tristate_name)
        # TODO: record the fact that option_name tests tristate values, and add the biimplication to the whole kclause formula for it, i.e., CONFIG_A <-> (tristate_y_CONFIG_A || tristate_m_CONFIG_A)
      else:
        node.z3 = z3.Bool(option_name)
    else:
      # represent (in)equality between booleans and strings using z3 expressions
      if z3.is_string(left) and z3.is_string(right) or z3.is_bool(left) and z3.is_bool(right):
        if op == "eq":
          node.z3 = z3.simplify(z3.Not(z3.Distinct(left, right)))
        elif op == "ne":
          node.z3 = z3.simplify(z3.Distinct(left, right))
        # elif op == "lt":
        #   node.z3 = z3.Z3_mk_lt(z3.get_ctx(None), left.ast, right.ast)
        # elif op == "le":
        #   node.z3 = z3.simplify(z3.ULE(left, right))
        # elif op == "gt":
        #   node.z3 = z3.simplify(z3.UGT(left, right))
        # elif op == "ge":
        #   node.z3 = z3.simplify(z3.UGE(left, right))
        # else:
        #  assert(False)

  def visit_Eq(self, node):
    node.name = "eq"

  def visit_NotEq(self, node):
    node.name = "ne"

  def visit_Lt(self, node):
    node.name = "lt"

  def visit_LtE(self, node):
    node.name = "lte"

  def visit_Gt(self, node):
    node.name = "gt"

  def visit_GtE(self, node):
    node.name = "gte"

  # def default(self, node):
  #   # sys.stderr.write("trying to process default: \"%s\"\n" % (node))
  #   result = glean_unknown_symbol(node)
  #   # sys.stderr.write("result: %s\n" % (result))
  #   if result is not None:
  #     return result
  #   else:
  #     predicate = str(node)
  #     return z3.Bool("PREDICATE_%s" % (predicate))


# parse tree processing
class IdentifierCollector(ast.NodeVisitor):
  def __init__(self):
    self.identifiers = []

  def result(self):
    return self.identifiers

  def visit_Name(self, node):
    self.identifiers.append(node.id)

def get_identifiers(expr):
  try:
    tree = ast.parse(expr)
  except:
    sys.stderr.write("error: could not parse %s\n" % (line))
    sys.stderr.write(traceback.format_exc())
    sys.stderr.write("\n")
    return []
  visitor = IdentifierCollector()
  visitor.visit(tree)
  return visitor.result()

def convert_to_z3(expr, allow_tristate=True):
  # print(expr)
  try:
    tree = ast.parse(expr)
  except RuntimeError as e:
    sys.stderr.write("exception: %s\n" % (e))
    sys.stderr.write("could not convert expression to cnf\n%s\n" % (expr))
    exit(1)
    return []
  except Error as e:
    # handle broken expressions
    sys.stderr.write("exception: %s\n" % (e))
    sys.stderr.write("warning: couldn't parse %s\n" % (expr))
    exit(1)
    return []
  # sys.stderr.write("actual_expr %s\n" % (str(actual_expr)))
  visitor = Converter(allow_tristate=allow_tristate)
  # print(ast.dump(tree))
  visitor.visit(tree)
  z3_clause = visitor.result()
  # sys.stderr.write("z3_clause %s\n" % (str(z3_clause)))
  return z3.simplify(z3_clause)

if __name__ == '__main__':
  # tests
  print((convert_to_z3('((((not ((((CONFIG_GCOV_KERNEL and CONFIG_CC_IS_GCC and 1)) and (((1 and CONFIG_GCC_VERSION < "40700")) or ((1)))))) or (CONFIG_GCOV_FORMAT_3_4 or CONFIG_GCOV_FORMAT_4_7))) and (((not (CONFIG_GCOV_FORMAT_3_4 or CONFIG_GCOV_FORMAT_4_7)) or ((CONFIG_GCOV_KERNEL and CONFIG_CC_IS_GCC and 1)))))')))
  # print(convert_to_z3('((((not ((((1)) and (((1)) or ((1 and CONFIG_GCC_PLUGINS)) or ((1 and CONFIG_GCC_PLUGINS and ( not CONFIG_KASAN or CONFIG_KASAN_STACK!="1"))) or ((1 and CONFIG_GCC_PLUGINS and ( not CONFIG_KASAN or CONFIG_KASAN_STACK!="1"))) or ((1 and CONFIG_CC_HAS_AUTO_VAR_INIT)))))) or (CONFIG_INIT_STACK_NONE or CONFIG_GCC_PLUGIN_STRUCTLEAK_USER or CONFIG_GCC_PLUGIN_STRUCTLEAK_BYREF or CONFIG_GCC_PLUGIN_STRUCTLEAK_BYREF_ALL or CONFIG_INIT_STACK_ALL))) and (((not (CONFIG_INIT_STACK_NONE or CONFIG_GCC_PLUGIN_STRUCTLEAK_USER or CONFIG_GCC_PLUGIN_STRUCTLEAK_BYREF or CONFIG_GCC_PLUGIN_STRUCTLEAK_BYREF_ALL or CONFIG_INIT_STACK_ALL)) or ((1)))))'))
  # print(convert_to_z3('((((not ((((1)) and (((1 and CONFIG_X86_64)) or ((1)) or ((1 and CONFIG_EXPERT and  not CONFIG_STACKDEPOT)))))) or (CONFIG_UNWINDER_ORC or CONFIG_UNWINDER_FRAME_POINTER or CONFIG_UNWINDER_GUESS))) and (((not (CONFIG_UNWINDER_ORC or CONFIG_UNWINDER_FRAME_POINTER or CONFIG_UNWINDER_GUESS)) or ((1)))))'))
  # print(get_identifiers('((((not ((((1)) and (((1 and CONFIG_X86_64)) or ((1)) or ((1 and CONFIG_EXPERT and  not CONFIG_STACKDEPOT)))))) or (CONFIG_UNWINDER_ORC or CONFIG_UNWINDER_FRAME_POINTER or CONFIG_UNWINDER_GUESS))) and (((not (CONFIG_UNWINDER_ORC or CONFIG_UNWINDER_FRAME_POINTER or CONFIG_UNWINDER_GUESS)) or ((1)))))'))



  
