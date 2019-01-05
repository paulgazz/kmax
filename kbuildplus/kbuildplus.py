#!/usr/bin/env python
if __name__ == '__main__':    

    import argparse    
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
        elif case_study == "tests":
            myAnalysis = analysis.Tests(inp)

    myAnalysis.run()
    myAnalysis.analyze()
    
