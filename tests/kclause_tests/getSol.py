import sys
import os
import z3
import pickle


def get_kclause_solutions(kclause_file):
    with open(kclause_file, 'rb') as fp:
        # read pickle file
        kclause = pickle.load(fp)

        kclause_constraints = {}
        for var in list(kclause.keys()):
            kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in kclause[var] ]

        constraints = []
        for var in list(kclause_constraints.keys()):
            for z3_clause in kclause_constraints[var]:
                constraints.extend(z3_clause)

        # initialize solver
        s = z3.Solver()
        s.add(constraints)

        count = 0
        # enumerate solutions
        while s.check() == z3.sat:
            count += 1
            m = s.model()
            print(m)
            # Create a new constraint the blocks the current model
            block = []
            for d in m:
                # d is a declaration
                #if d.arity() > 0:
                #    raise Z3Exception("uninterpreted functions are not supported")
                # create a constant from declaration
                c = d()
                #if is_array(c) or c.sort().kind() == Z3_UNINTERPRETED_SORT:
                #    raise Z3Exception("arrays and uninterpreted sorts are not supported")
                block.append(c != m[d])
                s.add(z3.Or(block))

        if count == 0:
            print("No solution found")


if __name__ == '__main__':
    filename = sys.argv[1]

    get_kclause_solutions(filename)

