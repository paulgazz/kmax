

# Generating a DIMACS version of a Kconfig feature model

`check_dep --dimacs` will output a special format (proto-dimacs) that
can be converted to dimacs using the accompanying `dimacs.py` script.

    check_dep --dimacs config/Config.in | tee axtls.kmax | python ~/research/repos/kmax/kconfig/dimacs.py > axtls.dimacs
    
# Proto-DIMACS output grammar

    // whole file
    file := line*
    line := bool_line | nonbool_line | clause_line | boolchoice_line | dep_line

    // lines
    bool_line := 'bool' config_var selectability
    def_bool_line := 'def_bool' config_var bool_value '(' expr ')'
    nonbool_line := 'bool' config_var selectability type_name
    def_nonbool_line := 'def_nonbool' config_var nonbool_value '|' '(' expr ')'
    clause_line := 'clause' clause_elem+
    bool_choice_line := 'bool_choice' config_var+ '|' '(' expr ')'
    dep_line := dep_name config_var '(' expr ')'
    dep_name := 'dep' | 'rev_dep'

    // expressions
    bool_value := '1' | '0'
    selectability := 'selectable' | 'nonselectable'
    nonbool_value := string
    type_name := 'string' 'nonstring'
    clause_elem := '-'? config_var
    expr := expr 'and' expr | expr 'or' expr | 'not' expr | config_var | nonbool_expr | '1' | '0'

    config_var := 'SPECIAL_ROOT_VARIABLE' | string

## Semantics

- All `bool_line`s, `def_bool_line`s, and `nonbool_lines`s should come first in the file,
  which `check_dep` ensures.
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
  that the `expr` holds true.  `rev_dep` identifies those that come
  from a reverse dependency.  we can assume these lines come after the
  definition of the variable with `bool_line`, etc, and that `rev_dep`
  comes after `dep`.
- the `expr` may contain non-boolean relations, which can themselves
  be treated as a boolean variable.  1 and 0 mean true and false
  respectively.
- `def_bool` defines (possibly multiple) defaults for a boolean
  variable.  This is only meant for nonselectable booleans, since it
  will constrain a variable to that value.
- `def_nonbool` defines (possibly multilpe) defaults for variable
  nonboolean.  This is for both selectable and nonselectable to ensure
  that the build system will get some value.

# DIMACS comment format

- `c variable_number CONFIG_VAR bool|choice_bool|hidden_bool|nonbool|string|int DEFAULT_VALUE?`
- `c variable_number GHOST_BOOL_NUM_NAME nonbool_var_name DEFAULT_VALUE`

# TODO

- when converting to dimacs, add extra booleans when any expression
  depends on tristate `y` or `m` individually.  this will enable
  on-demand support representation of tristate variables
- finish description (and check_dep implementation) of `nonbool_expr`
