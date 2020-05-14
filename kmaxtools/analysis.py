import re
import os
import pdb
trace = pdb.set_trace
import z3
try:
    import cPickle as pickle
except ImportError:  #Python3
    import pickle
import sys

import kmaxtools.vcommon as CM

import kmaxtools.settings
mlog = CM.getLogger(__name__, kmaxtools.settings.logger_level)

class FileAnalysis:
    @classmethod
    def chgext(cls, filename, f, t):
        if f is None or filename.endswith(f):
            return filename[:-2] + t
        
    @classmethod
    def hostprog_otoc(cls, filename):
        """host programs don't have a .o extension, but their components
        might if it's a composite"""
        if not filename.endswith('.o'):
            filename = filename + '.o'
        return cls.chgext(filename, '.o', '.c')

    @classmethod
    def otoc(cls, filename):
        return cls.chgext(filename, '.o', '.c')

    @classmethod
    def otoS(cls, filename):
        return cls.chgext(filename, '.o', '.S')

    @classmethod
    def ctoo(cls, filename):
        return chgext(filename, '.c', '.o')
    
    @classmethod
    def mkc(cls, filename):
        return cls.chgext(filename, None, '.c')

    @staticmethod
    def get_all_c_files(path):
        assert os.path.isdir(path)
        cmd = 'find {} -type f | grep "\.c$" | sort | uniq'.format(path)
        files, _ = CM.vcmd(cmd)
        files = set([os.path.normpath(x.strip('\n'))
                     for x in files.split()])
        return files
        
    @staticmethod
    def get_included_c_files(path):
        """get source files that include c files"""
        
        path = os.path.abspath(path)
        cmd = r'find {} -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"'.format(path)
        rs, _  = CM.vcmd(cmd)
        rs = [s.split(':', 1) for s in rs.split('\n') if s]
        #search for string #include "file.c"
        msearch = lambda s: re.search(r"\".*\.c\"", s)
        
        assert all(len(s) == 2 and msearch(s[1]) for s in rs), rs
        rs = [(os.path.dirname(s[0]), msearch(s[1]).group(0)[1:-1]) for s in rs]
        rs = set(os.path.join(fdir, fname) for fdir, fname in rs)
        return rs

    @staticmethod
    def analyze(results):
        #print 'world', results.results.subdir_pcs, results.subdir_pcs
        
        def print_set(s, name):
            if s:
                mlog.info("{} {}: {}".format(len(s), name, ', '.join(s))) 

        import time
        st = time.time()

        # find all subdirs with source in them
        import glob
        
        unit_files = (results.compilation_units | results.library_units |
                      results.hostprog_units | results.unconfigurable_units)
        
        subdirs = set(os.path.dirname(f) for f in unit_files)
        all_c_files = set()
        for d in subdirs:
            all_c_files.update([os.path.normpath(x) for x in glob.glob(os.path.join(d, "*.c"))])

        assert all(os.path.isfile(f) for f in all_c_files), all_c_files

        # find all compilation units without a corresponding .c file
        unmatched_units = set()
        asm_compilation_units = set()
        for unit in results.compilation_units:            
            S_file = FileAnalysis.otoS(unit)
            if os.path.isfile(S_file):
                asm_compilation_units.add(S_file)
            else:
                c_file = FileAnalysis.otoc(unit)
                if not os.path.isfile(c_file):
                    unmatched_units.add(c_file)

        #assert not unmatched_units, unmatched_units
        #assert not asm_compilation_units, asm_compilation_units

        # get source files that include c files
        included_c_files = set()
        out, _ = CM.vcmd(r'find . -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"')
        for line in out.split("\n"):
          parts = line.split(":", 1)
          if parts is not None:
            infile = parts[0]
            if len(parts) > 1:
              m = re.search(r"\".*\.c\"", parts[1])
              if m is not None:
                included = m.group(0)[1:-1]
                included = os.path.join(os.path.dirname(infile), included)
                included = os.path.relpath(os.path.realpath(included))
                included_c_files.add(included)

        # only need the files in the current source subtree
        included_c_files.intersection_update(all_c_files)

        # filtering
        # find all asm-offsets.c files, for these are compiled by the root
        # Kbuild file into offsets
        re_offsets_file = re.compile(r'arch/[^/]+/kernel/asm-offsets\.c')
        offsets_files = [f for f in all_c_files if re_offsets_file.match(x)]
        assert not offsets_files, offsets_files

        # find all .c files without a corresponding compilation unit, starting
        # with all c files
        unidentified_c_files = set(all_c_files)
        
        cu_c_files = [FileAnalysis.otoc(f) for f in results.compilation_units] #cu
        lib_c_files = [FileAnalysis.otoc(filename) for filename in results.library_units] #lib cu
        hostprog_c_files = [FileAnalysis.hostprog_otoc(f)  for f in results.hostprog_units]
        unconfig_c_files = [FileAnalysis.hostprog_otoc(f) for f in results.unconfigurable_units]
        extra_targets_c_files = [FileAnalysis.hostprog_otoc(f) for f in results.extra_targets]   
        used_c_files = set(cu_c_files + lib_c_files + hostprog_c_files + unconfig_c_files +
                           extra_targets_c_files + list(results.clean_files) + list(offsets_files))

        unidentified_c_files -= used_c_files

        # removing other c files
        # separate out .c files from the staging directory
        unidentified_staging_c_files = [f for f in unidentified_c_files 
                                        if "drivers/staging" in os.path.dirname(x)]
        unidentified_c_files -= set(unidentified_staging_c_files)

        # separate out .c files with "skeleton" in their name.  this is a
        # heuristic to find example drivers that aren't actually compiled.

        unidentified_skeleton_c_files = [f for f in unidentified_c_files 
                                         if "skeleton" in os.path.basename(x)]
        unidentified_c_files -= set(unidentified_skeleton_c_files)


        #remove .c files that aren't compilation units, because they are
        #included in other c files
        unidentified_c_files -= included_c_files

        # separate out generators heuristically.  look for "mk" or
        # "gen[^a-zA-Z]" in their name

        # perhaps we can find generators a better way, e.g., by looking for
        # the c file in the makefile

        # look for unexpanded variables or function calls
        re_unexpanded = re.compile(r'.*\$\(.*\).*')
        files = (results.compilation_units | results.library_units | results.hostprog_units |
                 results.unconfigurable_units | results.extra_targets | results.clean_files)
        unexpanded_units = set(FileAnalysis.otoc(f) for f in files if re_unexpanded.match(f))
        #remove files with unexpanded var names
        unmatched_units -= unexpanded_units

        # remove c files specified in the clean-files and in targets, since
        # these can be auto-generated c files
        import fnmatch        
        generated_c_files = set()
        for c in (results.clean_files | results.c_file_targets):
            pattern = re.compile(fnmatch.translate(c))
            for filename in unmatched_units:
                if pattern.match(filename):
                    generated_c_files.add(filename)
        unmatched_units.difference_update(generated_c_files)

        # # cache the list of working kbuild files
        # if args.excludes_file != None:
        #   with open(args.excludes_file, "w") as f:
        #     pickle.dump(excludes, f, 0)

        #print_set(toplevel_dirs, "toplevel_dirs")  # list of directories started from
        print_set(all_c_files, "all_c_files")  # all .c files in used and visited subdirs
        print_set(asm_compilation_units, "asm_compilation_units")  # compilation units with a .S file
        #print_set(subdirs, "subdirectory")  # subdirectory visited by kbuild
        #print_set(used_subdirectory, "used_subdirectory")  # subdirs containing compilation units
        print_set(results.compilation_units, "compilation_units")  # compilation units referenced by kbuild
        print_set(results.composites, "composites")  # compilation units that are composites
        print_set(results.library_units, "library_units")  # library units referenced by kbuild
        print_set(results.hostprog_units, "hostprog_units")
        print_set(results.unconfigurable_units, "unconfigurable_units")
        print_set(results.extra_targets, "extra_targets")
        print_set(results.clean_files, "clean_files")
        print_set(results.c_file_targets, "c_file_targets")
        print_set(generated_c_files, "generated_c_files")
        print_set(unmatched_units, "unmatched_units")
        print_set(included_c_files, "included_c_files")
        print_set(offsets_files, "offsets_files")
        print_set(unidentified_c_files, "unidentified_c_files")
        #print_set(unidentified_staging_c_files, "unidentified_staging_c_files")
        #print_set(unidentified_skeleton_c_files, "unidentified_skeleton_c_files")
        #print_set(unexpanded_compilation_units, "unexpanded_compilation_units")
        #print_set(unexpanded_library_units, "unexpanded_library_units")
        #print_set(unexpanded_hostprog_units, "unexpanded_hostprog_units")
        #print_set(unexpanded_unconfigurable_units, "unexpanded_unconfigurable_units")
        #print_set(unexpanded_extra_targets, "unexpanded_extra_targets")
        #print_set(unexpanded_subdirs, "unexpanded_subdirs")
        #print_set(broken, "broken")
        mlog.info("time: {}".format(time.time() - st))
    

# class GeneralAnalysis:
#     def __init__(self, path):
#         self.makefiles = path
#         # self.makefiles = set([os.path.abspath(f) for f in path
#         #                     if os.path.isfile(f) or os.path.isdir(f)])
#         mlog.info("analyzing {} files/dirs".format(len(self.makefiles)))

#     def run(self):
        
#         myrun = Run()
#         myrun.run(self.makefiles)
#         self.results = myrun.results

#     @property
#     def subdirectories(self):
#         return frozenset(self.results.subdirs)

#     @property
#     def compilation_units(self):
#         return frozenset(self.results.compilation_units)

#     @property
#     def composites(self):
#         return frozenset(self.results.composites)
    
#     @property
#     def library_units(self):
#         return frozenset(self.results.library_units)

#     @property
#     def hostprog_composites(self):
#         assert not self.results.hostprog_composites, self.results.hostprog_composites        
#         return frozenset(self.results.hostprog_composites)
#     @property
#     def hostprog_units(self):
#         return frozenset(self.results.hostprog_units)

#     @property    
#     def unconfigurable_units(self):
#         #/home/tnguyen/Dropbox/git/kmax-dev/tests/kbuild/missing_computed_variable
#         return frozenset(self.results.unconfigurable_units)
    
#     @property
#     def extra_targets(self):
#         assert not self.results.extra_targets, self.results.extra_targets
#         return frozenset(self.results.extra_targets)

#     @property
#     def clean_files(self):
#         return frozenset(self.results.clean_files)

#     @property
#     def c_file_targets(self):
#         assert not self.results.c_file_targets, self.results.c_file_targets
#         return frozenset(self.results.c_file_targets)

#     @property
#     def presence_conditions(self):
#         t = z3.Tactic('ctx-solver-simplify')
#         tseitin = z3.Tactic('tseitin-cnf')
#         presence_conditions = []
#         for path in self.results.presence_conditions.keys():
#             # presence_conditions.append((path, "{}".format(z3.simplify(self.results.presence_conditions[path]))))
#             presence_conditions.append((path, "{}".format(t(z3.simplify(self.results.presence_conditions[path])).as_expr())))
#             # presence_conditions.append((path, "{}".format(tseitin(t(z3.simplify(self.results.presence_conditions[path]))).as_expr())))
#         return frozenset(presence_conditions)

#     # @property
#     # def unit_pcs(self):
#     #     return self.results.unit_pcs

#     # @property
#     # def subdir_pcs(self):
#     #     return self.results.subdir_pcs
        

#     def analyze(self):

#     @classmethod
#     def chgext(cls, filename, f, t):
#         if f is None or filename.endswith(f):
#             return filename[:-2] + t
        
#     @classmethod
#     def hostprog_otoc(cls, filename):
#         """host programs don't have a .o extension, but their components
#         might if it's a composite"""
#         if not filename.endswith('.o'):
#             filename = filename + '.o'
#         return cls.chgext(filename, '.o', '.c')

#     @classmethod
#     def otoc(cls, filename):
#         return cls.chgext(filename, '.o', '.c')

#     @classmethod
#     def otoS(cls, filename):
#         return cls.chgext(filename, '.o', '.S')

#     @classmethod
#     def ctoo(cls, filename):
#         return chgext(filename, '.c', '.o')
    
#     @classmethod
#     def mkc(cls, filename):
#         return cls.chgext(filename, None, '.c')

#     @staticmethod
#     def get_all_c_files(path):
#         assert os.path.isdir(path)
#         cmd = 'find {} -type f | grep "\.c$" | sort | uniq'.format(path)
#         files, _ = CM.vcmd(cmd)
#         files = set([os.path.normpath(x.strip('\n'))
#                      for x in files.split()])
#         return files
        
#     @staticmethod
#     def get_included_c_files(path):
#         """get source files that include c files"""
        
#         path = os.path.abspath(path)
#         cmd = r'find {} -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"'.format(path)
#         rs, _  = CM.vcmd(cmd)
#         rs = [s.split(':', 1) for s in rs.split('\n') if s]
#         #search for string #include "file.c"
#         msearch = lambda s: re.search(r"\".*\.c\"", s)
        
#         assert all(len(s) == 2 and msearch(s[1]) for s in rs), rs
#         rs = [(os.path.dirname(s[0]), msearch(s[1]).group(0)[1:-1]) for s in rs]
#         rs = set(os.path.join(fdir, fname) for fdir, fname in rs)
#         return rs


# class Tests(GeneralAnalysis):
#     def __init__(self, topdir):
#         assert os.path.isdir(topdir), topdir
#         self.topdir = os.path.abspath(topdir)

#         files =[os.path.join(self.topdir, f) for f in os.listdir(self.topdir)]
#         self.makefiles = sorted(f for f in files if os.path.isfile(f))
#                 #for i in ~/Dropbox/git/kmax-dev/tests/kbuild/*; do echo "testing" $i &>> out ; kmax.py -g $i &>> out ; done
    

# class CaseStudy(GeneralAnalysis):
#     def __init__(self, topdir):
#         assert os.path.isdir(topdir)
        
#         self.topdir = os.path.abspath(topdir)
#         self.makefiles = set(os.path.join(self.topdir,d) for d in self.subdirs)
#         for d in list(self.makefiles):
#             if not (os.path.isdir(d) or os.path.isfile(d)):  #dir or makefile
#                 mlog.warn('{} not found .. removing'.format(d))
#                 self.makefiles.remove(d)

# class BusyboxCaseStudy(CaseStudy):
#     subdirs = set([
#       "applets/",
#       "archival/",
#       "archival/libarchive/",
#       "console-tools/",
#       "coreutils/",
#       "coreutils/libcoreutils/",
#       "debianutils/",
#       "klibc-utils/",
#       "e2fsprogs/",
#       "editors/",
#       "findutils/",
#       "init/",
#       "libbb/",
#       "libpwdgrp/",
#       "loginutils/",
#       "mailutils/",
#       "miscutils/",
#       "modutils/",
#       "networking/",
#       "networking/libiproute/",
#       "networking/udhcp/",
#       "printutils/",
#       "procps/",
#       "runit/",
#       "selinux/",
#       "shell/",
#       "sysklogd/",
#       "util-linux/",
#       "util-linux/volume_id/"
#     ])
    
#     additional_included = [
#       "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
#       "archival/libarchive/unxz/xz_dec_lzma2.c",
#       "archival/libarchive/unxz/xz_dec_stream.c",

#       "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
#       "archival/libarchive/bz/bzlib.c",
#       "archival/libarchive/bz/compress.c",
#       "archival/libarchive/bz/huffman.c",

#       "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
#       "archival/libarchive/unxz/xz_dec_lzma2.c",
#       "archival/libarchive/unxz/xz_dec_stream.c",

#       "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
#       "archival/libarchive/bz/bzlib.c",
#       "archival/libarchive/bz/compress.c",
#       "archival/libarchive/bz/huffman.c",

#       "archival/libarchive/unxz/xz_dec_bcj.c", # included in archival/libarchive/decompress_unxz.c
#       "archival/libarchive/unxz/xz_dec_lzma2.c",
#       "archival/libarchive/unxz/xz_dec_stream.c",

#       "archival/libarchive/bz/blocksort.c", # included in archival/bzip2.c
#       "archival/libarchive/bz/bzlib.c",
#       "archival/libarchive/bz/compress.c",
#       "archival/libarchive/bz/huffman.c"
#     ]
#     additional_hostprogs = [
#         "networking/ssl_helper/ssl_helper.c", # built by networking/ssl_helper/ssl_helper.sh
#         "networking/ssl_helper-wolfssl/ssl_helper.c" # built by networking/ssl_helper-wolfssl/ssl_helper.sh
#     ]

#     # explanations for busybox 1.25.0
#     explanations = {
#       "examples": [
#         "networking/httpd_ssi.c", # example program
#         "networking/httpd_indexcgi.c",

#         "shell/ash_test/printenv.c", # test program compiled and run in shell/ash_test/run-all
#         "shell/ash_test/recho.c",
#         "shell/ash_test/zecho.c",

#         "applets/individual.c", # example wrapper program

#         "networking/ntpd_simple.c", # for busybox 1_22_stable
#       ],

#       "unused": [
#         "util-linux/volume_id/unused_highpoint.c",  # unused source
#         "util-linux/volume_id/unused_hpfs.c",
#         "util-linux/volume_id/unused_isw_raid.c",
#         "util-linux/volume_id/unused_lsi_raid.c",
#         "util-linux/volume_id/unused_lvm.c",
#         "util-linux/volume_id/unused_mac.c",
#         "util-linux/volume_id/unused_minix.c",
#         "util-linux/volume_id/unused_msdos.c",
#         "util-linux/volume_id/unused_nvidia_raid.c",
#         "util-linux/volume_id/unused_promise_raid.c",
#         "util-linux/volume_id/unused_silicon_raid.c",
#         "util-linux/volume_id/unused_ufs.c",
#         "util-linux/volume_id/unused_via_raid.c",

#         "libbb/hash_md5prime.c", # commented out in libbb/Kbuild
#         "libbb/bb_strtod.c",

#         "networking/tc.c", # CONFIG_TC commented out of networking/Config.in
#       ],

#       "not built commented out": [
#         "editors/patch_bbox.c", # not built
#         "editors/patch_toybox.c",
#       ],
#     }
    
    
#     def analyze(self):
#         all_c_files = self.get_all_c_files(self.topdir)
#         len_all_c_files = len(all_c_files)

#         unit_files = self.compilation_units | self.library_units
#         unit_files = set(self.mkc(f) for f in unit_files)
#         all_c_files -= unit_files
        
#         additional_included = set(os.path.join(self.topdir, f)
#                                   for f in self.additional_included)
#         included_c_files = self.get_included_c_files(self.topdir)
#         all_included = included_c_files | additional_included
#         #print "included c files", len(all_included)
#         all_c_files -= all_included
        
#         prefix = os.path.join(self.topdir, "scripts/")
#         script_files = set(f for f in all_c_files if f.startswith(prefix))
#         #print "scripts", len(script_files)        
#         all_c_files -= script_files

#         hostprog_files = set(f + ".c" for f in self.hostprog_units)
#         additional_hostprogs = set(os.path.join(self.topdir, f)
#                                    for f in self.additional_hostprogs)
#         hostprog_files |= additional_hostprogs
#         #print "hostprogs", len(hostprog_files)
#         all_c_files -= hostprog_files

#         # busy 1_22_stable has an unused directory of source files
#         prefix = os.path.join(self.topdir, "e2fsprogs/old_e2fsprogs")
#         old_e2fsprogs = set(f for f in all_c_files if f.startswith(prefix))
#         #print "old e2fsprogs dir", len(old_e2fsprogs)
#         all_c_files -= old_e2fsprogs
        
#         for k in self.explanations:
#           print k, len(self.explanations[k])
#           fs = set(os.path.join(self.topdir, f) for f in self.explanations[k])
#           all_c_files -= fs
#           print len(all_c_files)
          
#         # This will be empty if kmax got all C files correctly.  The
#         # explanations needs to contain all C files guaranteed to not be part
#         # of the build.

#         #print some info
#         mlog.info("results00:\n{}".format(self.results))
        
#         d = [("all c files", len_all_c_files),
#              ("units", len(unit_files)),
#              ("included c files", len(all_included)),
#              ("scripts", len(script_files)),
#              ("hostprogs", len(hostprog_files)),
#              ("old e2fsprogs dir", len(old_e2fsprogs)),
#              ("unaccounted c files", len(all_c_files)),
#              ("unaccounted c files", ' '.join(all_c_files))
#         ]
#         s = ', '.join("{}: {}".format(k,v) for k,v in d)
#         mlog.info(s)
        

        
# class LinuxCaseStudy(GeneralAnalysis):
#     # subdirs = set([
#     #     'arch/x86/Makefile',
#     #     'ipc',
#     #     'arch/x86/pci',
#     #     'fs',
#     #     'kernel',
#     #     'arch/x86/video',
#     #     'arch/x86/power',
#     #     'security',
#     #     'sound',
#     #     'arch/x86',
#     #     'lib',
#     #     'mm',
#     #     'drivers',
#     #     'firmware',
#     #     'crypto',
#     #     'arch/x86/oprofile',
#     #     'init',
#     #     'usr',
#     #     'net',
#     #     'arch/x86/lib'
#     #     'block',
#     #     'arch/x86/math-emu'
#     # ])
    
#     def analyze(self):
#         pickle.dump((self.compilation_units,
#                      self.library_units,
#                      self.hostprog_units,
#                      self.unconfigurable_units,
#                      self.extra_targets,
#                      self.clean_files,
#                      self.c_file_targets,
#                      self.subdirectories,
#                      self.composites,
#                      self.presence_conditions), sys.stdout, 0)
        
#         # #print 'world', self.results.subdir_pcs, self.subdir_pcs
        
#         # def print_set(s, name):
#         #     if s:
#         #         mlog.info("{} {}: {}".format(len(s), name, ', '.join(s))) 

#         # import time
#         # st = time.time()
        
#         # # find all subdirs with source in them
#         # import glob
        
#         # unit_files = (self.compilation_units | self.library_units |
#         #               self.hostprog_units | self.unconfigurable_units)
        
#         # subdirs = set(os.path.dirname(f) for f in unit_files)
#         # all_c_files = set()
#         # for d in subdirs:
#         #     all_c_files.update([os.path.normpath(x) for x in glob.glob(os.path.join(d, "*.c"))])

#         # assert all(os.path.isfile(f) for f in all_c_files), all_c_files

#         # # find all compilation units without a corresponding .c file
#         # unmatched_units = set()
#         # asm_compilation_units = set()
#         # for unit in self.compilation_units:            
#         #     S_file = self.otoS(unit)
#         #     if os.path.isfile(S_file):
#         #         asm_compilation_units.add(S_file)
#         #     else:
#         #         c_file = self.otoc(unit)
#         #         if not os.path.isfile(c_file):
#         #             unmatched_units.add(c_file)

#         # #assert not unmatched_units, unmatched_units
#         # #assert not asm_compilation_units, asm_compilation_units


#         # # get source files that include c files
#         # included_c_files = set()
#         # out, _ = CM.vcmd(r'find . -name "*.[c|h]" | xargs grep -H "^#.*include.*\.c[\">]"')
#         # for line in out.split("\n"):
#         #   parts = line.split(":", 1)
#         #   if parts is not None:
#         #     infile = parts[0]
#         #     if len(parts) > 1:
#         #       m = re.search(r"\".*\.c\"", parts[1])
#         #       if m is not None:
#         #         included = m.group(0)[1:-1]
#         #         included = os.path.join(os.path.dirname(infile), included)
#         #         included = os.path.relpath(os.path.realpath(included))
#         #         included_c_files.add(included)

#         # # only need the files in the current source subtree
#         # included_c_files.intersection_update(all_c_files)

#         # # filtering
#         # # find all asm-offsets.c files, for these are compiled by the root
#         # # Kbuild file into offsets
#         # re_offsets_file = re.compile(r'arch/[^/]+/kernel/asm-offsets\.c')
#         # offsets_files = [f for f in all_c_files if re_offsets_file.match(x)]
#         # assert not offsets_files, offsets_files

#         # # find all .c files without a corresponding compilation unit, starting
#         # # with all c files
#         # unidentified_c_files = set(all_c_files)
        
#         # cu_c_files = [self.otoc(f) for f in self.compilation_units] #cu
#         # lib_c_files = [self.otoc(filename) for filename in self.library_units] #lib cu
#         # hostprog_c_files = [self.hostprog_otoc(f)  for f in self.hostprog_units]
#         # unconfig_c_files = [self.hostprog_otoc(f) for f in self.unconfigurable_units]
#         # extra_targets_c_files = [self.hostprog_otoc(f) for f in self.extra_targets]   
#         # used_c_files = set(cu_c_files + lib_c_files + hostprog_c_files + unconfig_c_files +
#         #                    extra_targets_c_files + list(self.clean_files) + list(offsets_files))

#         # unidentified_c_files -= used_c_files

#         # # removing other c files
#         # # separate out .c files from the staging directory
#         # unidentified_staging_c_files = [f for f in unidentified_c_files 
#         #                                 if "drivers/staging" in os.path.dirname(x)]
#         # unidentified_c_files -= set(unidentified_staging_c_files)

#         # # separate out .c files with "skeleton" in their name.  this is a
#         # # heuristic to find example drivers that aren't actually compiled.

#         # unidentified_skeleton_c_files = [f for f in unidentified_c_files 
#         #                                  if "skeleton" in os.path.basename(x)]
#         # unidentified_c_files -= set(unidentified_skeleton_c_files)


#         # #remove .c files that aren't compilation units, because they are
#         # #included in other c files
#         # unidentified_c_files -= included_c_files

#         # # separate out generators heuristically.  look for "mk" or
#         # # "gen[^a-zA-Z]" in their name

#         # # perhaps we can find generators a better way, e.g., by looking for
#         # # the c file in the makefile

#         # # look for unexpanded variables or function calls
#         # re_unexpanded = re.compile(r'.*\$\(.*\).*')
#         # files = (self.compilation_units | self.library_units | self.hostprog_units |
#         #          self.unconfigurable_units | self.extra_targets | self.clean_files)
#         # unexpanded_units = set(self.otoc(f) for f in files if re_unexpanded.match(f))
#         # #remove files with unexpanded var names
#         # unmatched_units -= unexpanded_units

#         # # remove c files specified in the clean-files and in targets, since
#         # # these can be auto-generated c files
#         # import fnmatch        
#         # generated_c_files = set()
#         # for c in (self.clean_files | self.c_file_targets):
#         #     pattern = re.compile(fnmatch.translate(c))
#         #     for filename in unmatched_units:
#         #         if pattern.match(filename):
#         #             generated_c_files.add(filename)
#         # unmatched_units.difference_update(generated_c_files)

#         # # # cache the list of working kbuild files
#         # # if args.excludes_file != None:
#         # #   with open(args.excludes_file, "w") as f:
#         # #     pickle.dump(excludes, f, 0)

#         # mlog.info("results01:\n{}".format(self.results))


        
#         # #print_set(toplevel_dirs, "toplevel_dirs")  # list of directories started from
#         # print_set(all_c_files, "all_c_files")  # all .c files in used and visited subdirs
#         # print_set(asm_compilation_units, "asm_compilation_units")  # compilation units with a .S file
#         # #print_set(subdirs, "subdirectory")  # subdirectory visited by kbuild
#         # #print_set(used_subdirectory, "used_subdirectory")  # subdirs containing compilation units
#         # print_set(self.compilation_units, "compilation_units")  # compilation units referenced by kbuild
#         # print_set(self.composites, "composites")  # compilation units that are composites
#         # print_set(self.library_units, "library_units")  # library units referenced by kbuild
#         # print_set(self.hostprog_units, "hostprog_units")
#         # print_set(self.unconfigurable_units, "unconfigurable_units")
#         # print_set(self.extra_targets, "extra_targets")
#         # print_set(self.clean_files, "clean_files")
#         # print_set(self.c_file_targets, "c_file_targets")
#         # print_set(generated_c_files, "generated_c_files")
#         # print_set(unmatched_units, "unmatched_units")
#         # print_set(included_c_files, "included_c_files")
#         # print_set(offsets_files, "offsets_files")
#         # print_set(unidentified_c_files, "unidentified_c_files")
#         # #print_set(unidentified_staging_c_files, "unidentified_staging_c_files")
#         # #print_set(unidentified_skeleton_c_files, "unidentified_skeleton_c_files")
#         # #print_set(unexpanded_compilation_units, "unexpanded_compilation_units")
#         # #print_set(unexpanded_library_units, "unexpanded_library_units")
#         # #print_set(unexpanded_hostprog_units, "unexpanded_hostprog_units")
#         # #print_set(unexpanded_unconfigurable_units, "unexpanded_unconfigurable_units")
#         # #print_set(unexpanded_extra_targets, "unexpanded_extra_targets")
#         # #print_set(unexpanded_subdirs, "unexpanded_subdirs")
#         # #print_set(broken, "broken")
#         # mlog.info("time: {}".format(time.time() - st))
