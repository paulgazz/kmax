This is the legacy version of Kmax based on BDDs

## Download and collect all compilation units

This will download and collect all compilation units and presence
conditions from v4.0 of the Linux kernel source.

    # from the top-level kmax source directory
    python analysis/collect_buildsystem.py 4.0 x86
    
## Full run on BusyBox, using the BDD version of Kmax

    # setup busybox source
    cd ~/src/
    git clone https://git.busybox.net/busybox

    # extract kbuild contraints per file 
    cd ~/src/busybox
    git checkout 1_28_1
    ~/research/repos/kmax/scripts/busybox_configs.py -B ~/src/busybox/
    # ~/src/busybox/unit_pc now has a list of files and their presence conditions

    # extract kconfig constraints
    cd ~/src/busybox
    check_dep --dimacs Config.in | tee kconfig.kmax | python ~/research/repos/kmax/kconfig/dimacs.py --remove-bad-selects --include-nonvisible-bool-defaults --remove-orphaned-nonvisibles --comment-format-v2 | tee kconfig.dimacs
    # kconfig.dimacs now has a dimacs file containing the kconfig constraints

    # get all configuration variables used in each source file (depends on SuperC)
    cd ~/src/busybox/
    rm include/autoconf.h
    cut -f2 -d' ' unit_pc | sed 's/\.o$/\.c/' | grep -v "miscutils/setserial.c" | while read i; do echo $i; timeout 30s java xtc.lang.cpp.SuperC -I include/ -I libbb/ -preprocessor -configurationVariables $i > $i.superc 2>&1; done
    find | grep ".superc$" | xargs cat | grep "$config_var " | cut -f2 -d' ' | sort | uniq | egrep "(CONFIG_|ENABLE_)"
