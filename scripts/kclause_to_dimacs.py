import pickle
import z3

def get_kclause_constraints(kclause_file):
  with open(kclause_file, 'r') as fp:
    # kclause, defined_vars, used_vars = pickle.load(fp)
    kclause = pickle.load(fp)

    kclause_constraints = {}
    for var in list(kclause.keys()):
      kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in kclause[var] ]

    constraints = []
    for var in list(kclause_constraints.keys()):
      for z3_clause in kclause_constraints[var]:
        constraints.extend(z3_clause)

    return constraints

constraints = get_kclause_constraints(".kmax/kclause/x86_64/kclause")

solver = z3.Solver()

use_tseitin = True

if use_tseitin:
  g = z3.Goal()
  g.add(constraints)
  t = z3.Tactic('tseitin-cnf')
  solver.add(g)
else:
  solver.add(constraints)

print((solver.dimacs()))
