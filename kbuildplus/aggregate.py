#!/usr/bin/env python

# aggregate per-file constraints in the unit_pc format
# see ../README.md for a description of the unit_pc format
# this example:
#   unit_pc dirname1/filename1.o CONFIG_A || CONFIG_B
#   subdir_pc dirname1/ CONFIG_DIR
#
# becomes:
#   full_pc dirname1/filename1.o CONFIG_DIR && (CONFIG_A || CONFIG_B)
#

import sys

splitlines = sys.stdin.readlines()

unit_pc_lines = splitlines
unit_pc_lines = filter(lambda x: x.startswith("unit_pc "), unit_pc_lines)

subdir_pc_lines = splitlines
subdir_pc_lines = filter(lambda x: x.startswith("subdir_pc "), subdir_pc_lines)

unit_pcs = dict([ line.split(" ", 2)[1:3] for line in unit_pc_lines ])
subdir_pcs = dict([ line.split(" ", 2)[1:3] for line in subdir_pc_lines ])

full_pcs = []

for path, cond in unit_pcs.iteritems():
  subpath, basename = path.rsplit('/', 1)
  elems = subpath.rsplit('/')
  pc = unit_pcs[path].strip()
  for i in reversed(range(0, len(elems))):
    subarray = elems[0:(len(elems) - i)]
    subsubpath = '/'.join(subarray) + "/"
    if subsubpath in subdir_pcs.keys():
      sub_pc = subdir_pcs[subsubpath].strip()
      if sub_pc != "1":
        pc = pc + " && " + sub_pc
  print "full_pc {} {}".format(path, pc)
