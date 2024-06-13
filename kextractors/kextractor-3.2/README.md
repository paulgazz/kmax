The Kconfig parser in this directory has been copied from the
linux-4.12.8/scripts/kconfig directory.  `zconf.hash.c_shipped` has
been copied to `zconf.hash.c`.  The following minor changes have been
made:

In `expr.h`, `struct symbol` is given two more fields:

    bool searched;
    bool depends;
