import sys
import re
import numpy

config_re = re.compile("CONFIG_[A-Za-z0-9_\.]+")

units = {}
subdirs = {}
for i, line in enumerate(sys.stdin):
  elems = line.strip().split(' ', 2)
  typename = elems[0]
  if typename in ("unit_pc", "subdir_pc"):
    name = elems[1]
    config = elems[2]
    if typename == "unit_pc":
      units[name] = config
    elif typename == "subdir_pc":
      subdirs[name] = config


unconfigured = 0
configured = 0
total = 0
num_configs = {}
config_expressions = {}
for name in units:
  total += 1

  # collect configs of path components
  configs = []
  
  # see if any directories in its path are configured
  # the unit_pc file should be relative paths with no ending /
  has_configured_dir = False
  components = name.split("/")
  # start from 1 to ignore top-level subdirs which are always unconfigured
  # -1 to ignore the file name itselfb
  for i in range(1, len(components) - 1):
    subpath = "/".join(components[0:i+1])
    if (subpath in subdirs):
      configs.append(subdirs[subpath])
      if subdirs[subpath] != "1":
        has_configured_dir = True
    else:
      sys.stderr.write(subpath + "\n")

  # check whether file is always included (unconfigured) or
  # conditionally included (configured)
  configs.append(units[name])
  if units[name] != "1":
    configured += 1
  else:
    if has_configured_dir:
      configured += 1
    else:
      unconfigured += 1

  # count number of config vars controlling the file
  total_configs_used = 0
  full_expression = ""
  delim = ""
  for config in configs:
    matches = config_re.findall(config)
    total_configs_used += len(matches)
    full_expression = full_expression + delim + "(" + config + ")"
  num_configs[name] = total_configs_used
  config_expressions[name] = full_expression

config_sizes = num_configs.values()

sys.stderr.write("configured %d\n" % (configured))
sys.stderr.write("unconfigured %d\n" % (unconfigured))
sys.stderr.write("total %d\n" % (total))
sys.stderr.write("sanity check: sum equals total? %d\n" % ((configured+unconfigured)==total))

sys.stderr.write("\ndistribution of the number of configs per file %d")
for pct in (0, 25, 50, 75, 90, 99, 100):
  sys.stderr.write("%dth_percentile %d" % (pct, numpy.percentile(config_sizes, pct)))
sys.stderr.write("mean %d\n" % (numpy.mean(config_sizes)))
sys.stderr.write("std %d\n" % (numpy.std(config_sizes)))

for name in num_configs:
  print "%s,%d,%s" % (name, num_configs[name], config_expressions[name])
