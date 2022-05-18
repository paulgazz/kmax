1. copied all source files from next-20210426/scripts/kconfig, including the generated lexer and parser
2. copied the Makefile from kextractors/kextractor-next-20200430 and added menu.c to its list of source files
3. removed some superfluous code from kextractor.c (write_config and the EVERYNO and EVERYDEF actions)
4. updated kextractor_extension.c to export the updated module name, next-20210426
5. updated kmax/kextractcommon to add the new module
6. updated setup.py to add the new module
