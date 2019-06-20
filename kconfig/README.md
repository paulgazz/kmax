The Kconfig parser in this directory has been copied from the
linux-4.19.50/scripts/kconfig directory.  (We used to have to copy
`zconf.hash.c_shipped` to `zconf.hash.c`.)  The following minor
changes have been made:

1. In `expr.c`, the `static` keyword has been removed from
   `expr_compare_type` so it can be used by `check_dep.c`.

2. In `expr.h`, `struct symbol` is given two more fields:

        bool searched;
        bool depends;
3. 	In `expr.h`, `struct property` is given an extra field in order to
       save a select's original dependency `if` dependency, if any.

        struct expr *original_expr;

    This is used in conjunction with a change in `menu.c` that saves
    the original original after parsing the select line.
    
          if (P_SELECT == type) {
            // hang on to the original for kmax
            prop->original_expr = prop->visible.expr;
          }

    The reason this is done is to avoid clause blowup in dimacs due to
    a config's entire dependencies between conjoined with select's
    `if` dependencies.  Our Boolean formulae already account for
    dependencies and don't need them on the select.

## Running on Linux

    check_dep --dimacs -e SRCARCH=x86 -e srctree=./ Kconfig | tee kconfig.kmax

