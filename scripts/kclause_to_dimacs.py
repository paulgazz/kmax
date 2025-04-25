import pickle
import z3
import sys

def get_kclause_constraints(kclause_file):
  try:
    with open(kclause_file, 'r') as fp:
      kclause = pickle.load(fp)
  except UnicodeDecodeError as ex:
    sys.stderr.write("detected binary pickle file\n")
    with open(kclause_file, 'rb') as fp:
      kclause = pickle.load(fp)

  kclause_constraints = {}
  for var in list(kclause.keys()):
    kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in kclause[var] ]

  constraints = []
  for var in list(kclause_constraints.keys()):
    for z3_clause in kclause_constraints[var]:
      constraints.extend(z3_clause)

  return constraints

if len(sys.argv) > 1:
  kclause_file = sys.argv[1]
else:
  kclause_file = ".kmax/kclause/x86_64/kclause"
  
constraints = get_kclause_constraints(kclause_file)

goal = z3.Goal()
goal.add(constraints)
goal = z3.Then("simplify", "elim-and", "tseitin-cnf")(goal)[0] # use Then(...) instead of Tactic(...)
print(goal.dimacs())
