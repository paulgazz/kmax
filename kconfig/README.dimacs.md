

# Generating a DIMACS version of a Kconfig feature model

`check_dep --dimacs` will output a special format (proto-dimacs) that
can be converted to dimacs using the accompanying `dimacs.py` script.

    check_dep --dimacs config/Config.in | tee axtls.kmax | python ~/research/repos/kmax/kconfig/dimacs.py > axtls.dimacs
    
# Proto-DIMACS output grammar

    // whole file
    file := line*
    line := bool_line | nonbool_line | clause_line | boolchoice_line | dep_line

    // lines
    bool_line := 'bool' config_var value?
    nonbool_line := 'bool' config_var value?
    clause_line := 'clause' clause_elem+
    bool_choice_line := 'bool_choice' config_var+ '|' '(' expr ')'
    dep_line := 'dep' config_var '(' expr ')'

    // expressions
    value := string
    clause_elem := '-'? config_var
    expr := expr 'and' expr | expr 'or' expr | 'not' expr | config_var | nonbool_expr | '1' | '0'

    config_var := 'SPECIAL_ROOT_VARIABLE' | string

## Semantics

- `SPECIAL_ROOT_VARIABLE` is used for top-level configuration
  variables with no dependencies.  To make these into SAT clauses for
  a feature model, they all depend on a single root variable.
- `clause`s are symbolic dimacs cnf clauses, where instead of numbers,
  they use the string name of the variable
- `bool_choice` is a mutually-exclusive choice between the given
  config vars.  The entire choice can have a dependency.  Depedencies
  on the individual choice variables' dependencies are expressed with
  separate `dep` lines.
- `dep`s are a kconfig dependency.  selecting `config_var` implies
  that the `expr` holds true.
- the `expr` may contain non-boolean relations, which can themselves
  be treated as a boolean variable.  1 and 0 mean true and false
  respectively.

# DIMACS comment format

- `c variable_number CONFIG_VAR bool|nonbool DEFAULT_VALUE?`

# TODO

- default values for bools
- what to do with conditions on defaults? 
- when converting to dimacs, add extra booleans when any expression
  depends on tristate `y` or `m` individually.  this will enable
  on-demand support representation of tristate variables
- finish description (and check_dep implementation) of `nonbool_expr`
