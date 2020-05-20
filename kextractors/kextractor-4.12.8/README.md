The Kconfig parser in this directory has been copied from the
linux-4.12.8/scripts/kconfig directory.  `zconf.hash.c_shipped` has
been copied to `zconf.hash.c`.  The following minor changes have been
made:

1. In `expr.c`, the `static` keyword has been removed from
   `expr_compare_type` so it can be used by `check_dep.c`.

2. In `expr.h`, `struct symbol` is given two more fields:

        bool searched;
        bool depends;
