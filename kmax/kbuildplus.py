#!/usr/bin/env python

if __name__ == '__main__':
    import argparse    
    from kmax.vcommon import getLogLevel , getLogger
    import kmax.settings
    import kmax.analysis

    aparser = argparse.ArgumentParser("find interactions from Kbuild Makefiles")
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

    ag('-D',
       '--define',
       action='append',
       help="""\
    define a makefile variable""")

    ag('-B',
       '--boolean-configs',
       action="store_true",
       default=True,
       help="""\
    Treat all configuration variables as Boolean variables""")

    ag('-T',
       '--tristate-configs',
       action="store_true",
       help="""\
    Treat all Boolean configuration variables as tri-state variables""")

    ag('-F',
       '--file-analysis',
       action="store_true",
       help="""\
    Also perform C file analysis""")

    ag('--unit-pc-format',
       action="store_true",
       help="""\
    Output presence conditions in the original Kmax unit_pc format""")

    # ag('--case-study',
    #    type=str,
    #    help="""avail options: busybox/linux""")

    args = aparser.parse_args()

    if args.log_level != kmax.settings.logger_level and 0 <= args.log_level <= 4:
        kmax.settings.logger_level = args.log_level

    kmax.settings.logger_level = getLogLevel(kmax.settings.logger_level)
    mlog = getLogger(__name__, kmax.settings.logger_level)    
    if __debug__:
        mlog.warn("DEBUG MODE ON. Can be slow! (Use python -O ... for optimization)")

    kmax.settings.do_table = args.table
    kmax.settings.do_recursive = args.recursive
    if not args.tristate_configs:
        kmax.settings.do_boolean_configs = args.boolean_configs
    kmax.settings.unit_pc_format = args.unit_pc_format
    kmax.settings.defines = args.define

    # case_study = args.case_study
    # if not case_study:
    #     inp = args.makefile
    #     print inp
    #     myAnalysis = kmax.analysis.GeneralAnalysis(inp)
    # else:
    #     case_study = case_study.lower()
    #     inp = args.makefile[0]

    #     if case_study == "busybox":
    #         kmax.settings.do_boolean_configs = True
    #         myAnalysis = kmax.analysis.BusyboxCaseStudy(inp)
    #         kmax.settings.do_recursive = True
    #     elif case_study == "linux":
    #         kmax.settings.do_boolean_configs = True
    #         inp = args.makefile
    #         myAnalysis = kmax.analysis.LinuxCaseStudy(inp)
    #         kmax.settings.do_recursive = False
    #     elif case_study == "tests":
    #         myAnalysis = kmax.analysis.Tests(inp)

    inp = args.makefile
    print inp

    from kmax.alg import Run
    myrun = Run()
    myrun.run(inp)
    mlog.info("results01:\n{}".format(myrun.results))

    if args.file_analysis:
        from kmax.analysis import FileAnalysis
        FileAnalysis.analyze(myrun.results)
