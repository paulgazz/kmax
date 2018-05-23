

# Generating a DIMACS version of a Kconfig feature model

`check_dep --dimacs` will output a special format (proto-dimacs) that
can be converted to dimacs using the accompanying `dimacs.py` script.

    check_dep --dimacs config/Config.in | tee axtls.kmax | python ~/research/repos/kmax/kconfig/dimacs.py > axtls.dimacs
    
# Proto-DIMACS output grammar

    // whole file
    file := line*
    line := config_line | prompt_line | nonbool_line | clause_line | boolchoice_line | dep_line

    // lines
    config_line := 'config' config_var type_name
    prompt_line := 'prompt' config_var '(' expr ')'
    def_bool_line := 'def_bool' config_var bool_value '(' expr ')'
    def_nonbool_line := 'def_nonbool' config_var nonbool_value '|' '(' expr ')'
    clause_line := 'clause' clause_elem+
    bool_choice_line := 'bool_choice' config_var+ '|' '(' expr ')'
    dep_line := dep_name config_var '(' expr ')'
    dep_name := 'dep' | 'rev_dep'

    // expressions
    type_name := 'bool' | 'string' | 'number'
    bool_value := '1' | '0'
    nonbool_value := string
    clause_elem := '-'? config_var
    expr := expr 'and' expr | expr 'or' expr | 'not' expr | config_var | nonbool_expr | '1' | '0'

    config_var := string

## Semantics

- All `config_line`s should come before anything else related to the declared config var.
- All `prompt_line`s, `def_bool_line`s, and `def_non_line`s should come before dependencies.
- A config with no `prompt_line` is unconditionally nonvisible to the user.
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
- `def_nonbool` defines (possibly multiple) defaults for variable
  nonboolean.

# DIMACS comment format

- `c variable_number CONFIG_VAR bool|choice_bool|hidden_bool|nonbool|string|int DEFAULT_VALUE?`
- `c variable_number GHOST_BOOL_NUM_NAME nonbool_var_name DEFAULT_VALUE`
