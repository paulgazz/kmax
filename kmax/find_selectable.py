import traceback
import sys
import ast
import regex

# Documentation of ast and the visitors: https://greentreesnakes.readthedocs.io/en/latest/nodes.html

int_pattern = regex.compile("^[0-9]+$")

# This class is part of the selectable algorithm, described in the FindSelectable class
class SelectableVisitor(ast.NodeVisitor):
  def __init__(self, find_selectable):
    ast.NodeVisitor.__init__(self)
    self.find_selectable = find_selectable
    self.selectable = None

  def result(self):
    return self.selectable

  def visit_Expr(self, node):
    self.generic_visit(node)
    node.selectable = node.value.selectable
    self.selectable = node.selectable

  def visit_BoolOp(self, node):
    self.generic_visit(node)
    operands = []
    for value in node.values:
      operands.append(value.selectable)
    if node.op.name == "and":
      node.selectable = True
      for operand in operands:
        node.selectable = node.selectable and operand
    elif node.op.name == "or":
      node.selectable = False
      for operand in operands:
        node.selectable = node.selectable or operand
    else:
      assert(False)

  def visit_And(self, node):
    node.name = "and"

  def visit_Or(self, node):
    node.name = "or"

  def visit_Not(self, node):
    node.name = "not"

  def visit_UnaryOp(self, node):
    self.generic_visit(node)
    operand = node.operand.selectable
    if node.op.name == "not":
      node.selectable = True
    else:
      assert(False)

  def visit_Constant(self, node):
    value = node.value
    if int_pattern.match(value):
      num = int(value)
      if num == 0:
        node.selectable = False
      else:
        node.selectable = True
    else:
      node.selectable = False

  def visit_Num(self, node):  # deprecated since 3.8, replaced by constant
    num = node.n
    if num == 0:
      node.selectable = False
    else:
      node.selectable = True

  def visit_Str(self, node):  # deprecated since 3.8, replaced by constant
    node.selectable = False

  def visit_Name(self, node):
    option = node.id
    if option in list(self.find_selectable.selectable_options.keys()):
      node.selectable = self.find_selectable.selectable_options[option]
    else:
      node.selectable = self.find_selectable.get_selectable_one(option)

  def visit_Compare(self, node):
    self.generic_visit(node)
    if len(node.ops) > 1:
      # kconfig constraints aren't expected to have multiple operators in a comparison expression
      assert(False)
    left = node.left.selectable
    right = node.comparators[0].selectable
    node.selectable = left or right

# This class implements the selectable algorithm, which is an
# overapproximation of the set of configuration options that are
# available for a given architecture.  It works by recursively
# following the dependencies of configuration options to see if they
# ultimately depend on undeclared options.
class FindSelectable:
  def __init__(self, dep_exprs, rev_dep_exprs):
    self.dep_exprs = dep_exprs
    self.rev_dep_exprs = rev_dep_exprs
    
    # mapping from option name to bool, True for selectable, False for
    # not.  no entry means not yet known
    self.selectable_options = {}

  def get_selectable(self, pending_options):
    while len(pending_options) > 0:
      current_option = pending_options.pop()
      self.get_selectable_one(current_option)
    return self.selectable_options

  def get_selectable_one(self, current_option):
    if current_option not in list(self.selectable_options.keys()):  # not yet memoized
      # if no (direct or reverse) dependencies, assume it is selectable
      if current_option not in list(self.dep_exprs.keys()) and current_option not in list(self.rev_dep_exprs.keys()):
        self.selectable_options[current_option] = True
      else:
        result = False
        if current_option in list(self.dep_exprs.keys()):
          try:
            tree = ast.parse(self.dep_exprs[current_option])
          except RuntimeError as e:
            sys.stderr.write("exception: %s\n" % (e))
            sys.stderr.write("could not process expression\n%s\n" % (expr))
            exit(1)
            return False
          except Error as e:
            # handle broken expressions
            sys.stderr.write("exception: %s\n" % (e))
            sys.stderr.write("warning: couldn't parse %s\n" % (expr))
            exit(1)
            return False
          visitor = SelectableVisitor(self)
          visitor.visit(tree)
          result = result or visitor.result()

        if current_option in list(self.rev_dep_exprs.keys()):
          try:
            tree = ast.parse(self.rev_dep_exprs[current_option])
          except RuntimeError as e:
            sys.stderr.write("exception: %s\n" % (e))
            sys.stderr.write("could not process expression\n%s\n" % (expr))
            exit(1)
            return []
          except Error as e:
            # handle broken expressions
            sys.stderr.write("exception: %s\n" % (e))
            sys.stderr.write("warning: couldn't parse %s\n" % (expr))
            exit(1)
            return []
          visitor = SelectableVisitor(self)
          visitor.visit(tree)
          result = result or visitor.result()
        #
        self.selectable_options[current_option] = result
      #
    #
    return self.selectable_options[current_option]
