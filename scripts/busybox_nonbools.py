import sys

# adapted from busybox/scripts/kconfig/confdata.c, but made to be
# configuration-independent by wrapping both the yes/no answers with
# an #ifdef

for line in sys.stdin:
  instr, data = line.strip().split(" ", 1)
  if (instr == "config"):
    varname, typename = data.split(" ", 1)
    assert(varname.startswith("CONFIG_"))
    configname = varname[7:]
    if typename == "bool" or "tristate":
      print(("""
#ifdef CONFIG_%s
# define CONFIG_%s 1
# define ENABLE_%s 1
# ifdef MAKE_SUID
#  define IF_%s(...) __VA_ARGS__ \"CONFIG_%s\"
# else
#  define IF_%s(...) __VA_ARGS__
# endif
# define IF_NOT_%s(...)
#else
# undef CONFIG_%s
# define ENABLE_%s 0
# define IF_%s(...)
# define IF_NOT_%s(...) __VA_ARGS__
#endif
""" % (configname, configname, configname, configname, configname, configname, configname, configname, configname, configname, configname)))
    elif typename == "string":
      pass
    elif typename == "number":
      pass
    else:
      print("unexpected config type")
      exit(1)
