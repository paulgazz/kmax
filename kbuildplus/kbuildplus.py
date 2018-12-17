#!/usr/bin/env python

import sys
import os
import re
import argparse
import subprocess as sp
import pycudd
import _pycudd
import tempfile

from pymake import parser, parserdata, data, functions
from collections import defaultdict

import z3
import pdb
import vcommon as CM
trace = pdb.set_trace

mlog = None

import settings



if __name__ == '__main__':
    
    aparser = argparse.ArgumentParser("find interactions from Kbuild Makefile")
    ag = aparser.add_argument
    ag('makefile',
       nargs="*",
       type=str,
       help="""the name of a Linux Makefiles or subdirs""")
    
    ag("--log_level", "-log_level",
       help="set logger info",
       type=int, 
       choices=range(5),
       default = 3)    
    
    ag('-t',
       '--table',
       action="store_true",
       help="""show symbol table entries""")
    
    ag('-g',
       '--get-presence-conds',
       action="store_true",
       help="""\
    get presence conds for each compilation units""")
    
    ag('-r',
       '--recursive',
       action="store_true",
       help="""\
    recursively enter subdirectories""")

    ag('-C',
       '--config-vars',
       type=str,
       help="""the name of a KConfigData file containing configuration variable data""")

    ag('-B',
       '--boolean-configs',
       action="store_true",
       help="""\
    Treat all configuration variables as Boolean variables""")

    ag('--case-study',
       type=str,
       help="""avail options: busybox/linux""")

    args = aparser.parse_args()

    # logger_level = CM.getLogLevel(args.logger_level)
    # mlog = CM.getLogger(__name__, logger_level)

    if args.log_level != settings.logger_level and 0 <= args.log_level <= 4:
        settings.logger_level = args.log_level
    settings.logger_level = CM.getLogLevel(settings.logger_level)

    mlog = CM.getLogger(__name__, settings.logger_level)    
    if __debug__:
        mlog.warn("DEBUG MODE ON. Can be slow! (Use python -O ... for optimization)")

    settings.do_table = args.table
    settings.get_presence_conds = args.get_presence_conds
    settings.do_recursive = args.recursive
    settings.do_boolean_configs = args.boolean_configs


    from analysis import GeneralAnalysis, BusyboxAnalysis
    if args.case_study == "busybox":
        inp = args.makefile[0]
        settings.do_boolean_configs = True
        analysis = BusyboxAnalysis(inp)

    else:
        inp = args.makefile
        analysis = GeneralAnalysis(inp)

    analysis.run()
    analysis.analyze()
    

            


# 663
# compilation units 1
# library units 587
# recon_allunits 588
# 75
# scripts 24
# 51
# hostprogs 5
# 46
# old e2fsprogs dir 0
# 46
# unused 16
# 31
# not built commented out 2
# 29
# examples 7
# 23
# 14 set(['archival/libarchive/lzo1x_c.c', 'libbb/pw_encrypt_md5.c', 'libbb/xatonum_template.c', 'networking/nc_bloaty.c', 'sysklogd/logger.c', 'util-linux/fdisk_sgi.c', 'libbb/pw_encrypt_des.c', 'sysklogd/syslogd.c', 'util-linux/fdisk_aix.c', 'coreutils/od_bloaty.c', 'libbb/pw_encrypt_sha.c', 'util-linux/fdisk_sun.c', 'util-linux/fdisk_gpt.c', 'util-linux/fdisk_osf.c'])
# included c files 21
# 2
# set(['klibc-utils/minips.c', 'klibc-utils/run-init.c'])

