import z3, pickle, os, glob, argparse

parser = argparse.ArgumentParser(description="Create composite kclause formulas files from kclause files in place.")
helptxt="The path to the .kmax folder in which the kclause formulas files are to be converted to composite kclause formulas files."
parser.add_argument('-k', '--kmax-path', default=None, type=str, required=True, help=helptxt)
kmax_path = parser.parse_args().kmax_path

assert os.path.exists(kmax_path) and os.path.isdir(kmax_path)

all_kclause_files = glob.glob(os.path.join(kmax_path, "kclause", "*", "kclause"))

for f in all_kclause_files:
    assert os.path.isfile(f)

for kclause_file in all_kclause_files:
    print(("Processing %s" % kclause_file))
    with open(kclause_file, 'rb') as fp:
        kclause = pickle.load(fp)

        kclause_constraints = {}
        for var in list(kclause.keys()):
            kclause_constraints[var] = [ z3.parse_smt2_string(clause) for clause in kclause[var] ]

        vec = z3.AstVector()
        for var in list(kclause_constraints.keys()):
            for z3_clause in kclause_constraints[var]:
                for cl in z3_clause:
                    vec.push(cl)
        
        constraints = vec

        solver = z3.Solver()
        solver.add(constraints)

        composite_kclause_file = kclause_file
        with open(composite_kclause_file, 'w') as fp:
            fp.write(solver.to_smt2())
        print(("Written the composite kclause file to '%s'" % composite_kclause_file))
        