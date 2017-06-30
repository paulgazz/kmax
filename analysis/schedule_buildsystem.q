#!/bin/sh
#PBS -V
#PBS -l nodes=1:ppn=4,walltime=8:00:00,mem=8GB
#PBS -N collect_buildsystem
#PBS -M pcg234@nyu.edu
#PBS -m abe
#PBS -e localhost:/scratch/pcg234/kmax/logs/${PBS_JOBNAME}${PBS_JOBID}.err
#PBS -o localhost:/scratch/pcg234/kmax/logs/${PBS_JOBNAME}${PBS_JOBID}.out

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

# Find parser statistics all selected versions of the Linux kernel.
# Needs 8GB mem as set above.  To submit, use an array of jobs: "qsub
# -t 0-15 schedule_buildsystem.q"

module load python/intel/2.7.6

# array[0]="0.01"
# array[1]="0.99.2"
array[2]="1.0"
array[3]="1.1.67"
array[4]="1.2.0"
array[5]="2.0"
array[6]="2.2.0"
array[7]="2.4.0"
array[8]="2.5.5"
array[9]="2.5.45"
array[10]="2.6.0"
array[11]="2.6.1"
array[12]="2.6.11"
array[13]="2.6.12"
array[14]="2.6.13"
array[15]="2.6.14"
array[16]="2.6.15"
array[17]="2.6.16"
array[18]="2.6.17"
array[19]="2.6.18"
array[20]="2.6.19"
array[21]="2.6.20"
array[22]="2.6.21"
array[23]="2.6.22"
array[24]="2.6.23"
array[25]="2.6.24"
array[26]="2.6.25"
array[27]="2.6.26"
array[28]="2.6.27"
array[29]="2.6.28"
array[30]="2.6.29"
array[31]="2.6.30"
array[32]="2.6.31"
array[33]="2.6.32"
array[34]="2.6.33"
array[35]="2.6.33.3"
array[36]="2.6.33"
array[37]="2.6.34"
array[38]="2.6.35"
array[39]="2.6.36"
array[40]="2.6.37"
array[41]="2.6.38"
array[42]="2.6.39"
array[43]="3.0"
array[44]="3.1"
array[45]="3.2"
array[46]="3.3"
array[47]="3.4"
array[48]="3.5"
array[49]="3.6"
array[50]="3.7"
array[51]="3.8"
array[52]="3.9"
array[53]="3.10"
array[54]="3.11"
array[55]="3.12"
array[56]="3.13"
array[57]="3.14"
array[58]="3.15"
array[59]="3.16"
array[60]="3.17"
array[61]="3.18"
array[62]="3.19"
array[63]="3.19"
array[64]="4.0"
array[65]="4.1"


echo ${PBS_ARRAYID} ${array[PBS_ARRAYID]}

python ${KMAX_ROOT}/analysis/collect_buildsystem.py ${array[PBS_ARRAYID]} ${arch} > /scratch/pcg234/kmax/out/${PBS_JOBNAME}${PBS_JOBID}.out 2> /scratch/pcg234/kmax/out/${PBS_JOBNAME}${PBS_JOBID}.err
