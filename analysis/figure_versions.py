# Kmax
# Copyright (C) 2012-2015 Paul Gazzillo
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import sys
import os
import csv
import string
import math
from pychart import *
import kmaxdata

versions_file = kmaxdata.versions_datafile

theme.get_options()

versions = chart_data.read_csv(versions_file, "%s,%d,%d,%s,%s\n")
vmap = {}

# Convert dates given month a year to a decimal year by dividing the
# base-0 month by 12 and adding it to the year
for d in versions:
  vmap[d[0]] = [ float(d[2]) + (float(d[1]) - 1) / 12, d[3], d[4] ]

print vmap

gen_interval = lambda interval: lambda min, max: [int(math.floor(min))]+range(int((min + interval) / interval) * interval, int((max + interval) / interval) * interval, interval)+[int(math.ceil(max))]

width = 440
height = 75
major_tics = 5
minor_tics = 1
major_tic_len = 4
minor_tic_len = 0
minyear = int(math.floor(min(x[0] for x in vmap.values())))
maxyear = int(math.ceil(max(x[0] for x in vmap.values())))

can = canvas.init(None, 'pdf')
size = (width, height)

datalabel = 'Version Notes'

ar = area.T(size = size, legend = None,
            x_range = (minyear, maxyear),
            x_axis = axis.X(format="%d", label="Year",
                            tic_len = major_tic_len,
                            minor_tic_len = minor_tic_len,
                            tic_interval = gen_interval(major_tics),
                            minor_tic_interval = gen_interval(minor_tics)),
            y_range = (0, None),
            y_axis = None,
            y_grid_style = None)

ytop = ar.loc[1] + ar.size[1]
ybot = ar.loc[1]

data = []
for label in vmap.keys():
  year = vmap[label][0]
  data.append([vmap[label][0], 0])
ar.add_plot(line_plot.T(line_style=line_style.default, data=data, label='Versions'))
ar.draw()  


# display maps version label to (vertical offset, horizontal offset)
# no box: (6, 12)
# no box, raised: (17, 12)
v_lower = 30
v_center = 65
v_upper = 100
# box left hoffset: 0 (can nudge to -1)
display = {
  '0.99.2': (v_upper, 'center'),
  '2.5.45': (v_upper, 'center'),
  '2.6.30': (v_upper, 31),
  '2.6.32': (v_upper, -1),
  '1.1.67': (v_center, 'center'),
  '2.5.5': (v_center, 'center'),
  '2.6.24': (v_center, 'center'),
  '2.6.31': (v_lower, 'center'),
}

# default display
mod = 0
for label in sorted([ x for x in vmap.keys() if x not in display.keys() ], key=lambda x: x):
  if mod == 0:
    display[label] = (6, 'center')
  else:
    display[label] = (17, 'center')
  mod = (mod + 1) % 2

for label in sorted(vmap.keys(), key=lambda x: -display[x][0]): # lower boxes drawn last
  year = vmap[label][0]
  voffset = display[label][0]
  hoffset = display[label][1]
  intrinsic = vmap[label][1]
  extrinsic = vmap[label][2]
  text = label + '\n' + intrinsic + extrinsic
  lstyle = line_style.black
  if len(intrinsic) == 0 and len(extrinsic) == 0:
    box = False
  else:
    box = True

  x1 = ar.x_pos(year)
  x2 = x1
  y1 = ybot
  y2 = ybot + voffset
  if box:
    if len(extrinsic) > 0:
      radius = 100
    else:
      radius = 0
    can.line(lstyle, x1, y1, x2, y2)
    tb = text_box.T(text=text,
                    line_style=lstyle,
                    fill_style=fill_style.white,
                    right_fudge=5,
                    left_fudge=5,
                    bottom_fudge=5,
                    top_fudge=1,
                    loc=(x1, y2 + 6),
                    callout=True,
                    callout_shift=0,
                    radius=radius)
    _, _, width, _ = tb.get_dimension()
    if hoffset == 'left':
      hoffset = 0
    elif hoffset == 'center':
      hoffset = int(width / 2) - tb.left_fudge
    elif hoffset == 'right':
      hoffset = int(width) - tb.right_fudge - tb.right_fudge
    tb.loc = (x1 - hoffset, y2 + 6)
    tb.callout_shift=hoffset
    tb.draw()
  else:
    can.line(lstyle, x1, y1, x2, y2)
    tb = text_box.T(text=text,
                    loc=(x1, y2 + 2),
                    right_fudge = 0, left_fudge = 0,
                    bottom_fudge = 2, top_fudge = 0,
                    line_style = line_style.white,
                    fill_style = fill_style.white)
    _, _, width, _ = tb.get_dimension()
    if hoffset == 'left':
      hoffset = 0
    elif hoffset == 'center':
      hoffset = int(width / 2) - tb.left_fudge
    elif hoffset == 'right':
      hoffset = int(width) - tb.right_fudge - tb.right_fudge
    tb.loc = (x1 - hoffset, y2 + 2)
    tb.draw()

can.close()

# can.show(ar.x_pos(1992), ar.y_pos(500), "/a45{}Dow Jones")

# ar = area.T(size = size, legend=None, x_range=(1992, 2013), y_range = (0, 500),
#             x_axis = axis.X(format="%d", offset=200, tic_len=-6,
#                                            label_offset=(50, 0),
#                                            label="Version"),
#             y_axis = None)
# ar.add_plot(line_plot.T(data=[ [1,989], [2, 953], [3, 948], [4, 968], [5, 989] ]))
            
# ar.draw()

# can.show(ar.x_pos(4), ar.y_pos(970), "/a50{}S&P 500")
