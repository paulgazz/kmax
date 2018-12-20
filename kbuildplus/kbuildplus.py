#!/usr/bin/env python
if __name__ == '__main__':
    
    import argparse    
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


    from vcommon import getLogLevel , getLogger
    import settings
    if args.log_level != settings.logger_level and 0 <= args.log_level <= 4:
        settings.logger_level = args.log_level

    settings.logger_level = getLogLevel(settings.logger_level)
    mlog = getLogger(__name__, settings.logger_level)    
    if __debug__:
        mlog.warn("DEBUG MODE ON. Can be slow! (Use python -O ... for optimization)")

    settings.do_table = args.table
    settings.do_recursive = args.recursive
    settings.do_boolean_configs = args.boolean_configs

    import analysis
    case_study = args.case_study
    if not case_study:
        inp = args.makefile
        myAnalysis = analysis.GeneralAnalysis(inp)
    else:
        case_study = case_study.lower()
        inp = args.makefile[0]

        if case_study == "busybox":
            settings.do_boolean_configs = True
            myAnalysis = analysis.BusyboxCaseStudy(inp)
        elif case_study == "linux":
            settings.do_boolean_configs = True
            myAnalysis = analysis.LinuxCaseStudy(inp)

    myAnalysis.run()
    myAnalysis.analyze()
    

            


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

