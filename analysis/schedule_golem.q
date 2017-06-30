#!/bin/sh
#PBS -V
#PBS -l nodes=1:ppn=8,walltime=24:00:00,mem=8GB
#PBS -N collect_golem
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

# Run golem: "qsub -t 0-50 schedule_golem.q"

module load python/intel/2.7.6

array[0]="3.19 alpha"
array[1]="3.19 arc"
array[2]="3.19 arm64"
array[3]="3.19 arm"
array[4]="3.19 avr32"
array[5]="3.19 blackfin"
array[6]="3.19 c6x"
array[7]="3.19 cris"
array[8]="3.19 frv"
array[9]="3.19 hexagon"
array[10]="3.19 ia64"
array[11]="3.19 m32r"
array[12]="3.19 m68k"
array[13]="3.19 metag"
array[14]="3.19 microblaze"
array[15]="3.19 mips"
array[16]="3.19 mn10300"
array[17]="3.19 nios2"
array[18]="3.19 openrisc"
array[19]="3.19 parisc"
array[20]="3.19 powerpc"
array[21]="3.19 s390"
array[22]="3.19 score"
array[23]="3.19 sh"
array[24]="3.19 sparc"
array[25]="3.19 tile"
array[26]="3.19 unicore32"
array[27]="3.19 x86"
array[28]="3.19 xtensa"
array[29]="2.6.33.3 alpha"
array[30]="2.6.33.3 arm"
array[31]="2.6.33.3 avr32"
array[32]="2.6.33.3 blackfin"
array[33]="2.6.33.3 cris"
array[34]="2.6.33.3 frv"
array[35]="2.6.33.3 h8300"
array[36]="2.6.33.3 ia64"
array[37]="2.6.33.3 m32r"
array[38]="2.6.33.3 m68knommu"
array[39]="2.6.33.3 m68k"
array[40]="2.6.33.3 microblaze"
array[41]="2.6.33.3 mips"
array[42]="2.6.33.3 mn10300"
array[43]="2.6.33.3 parisc"
array[44]="2.6.33.3 powerpc"
array[45]="2.6.33.3 s390"
array[46]="2.6.33.3 score"
array[47]="2.6.33.3 sh"
array[48]="2.6.33.3 sparc"
array[49]="2.6.33.3 x86"
array[50]="2.6.33.3 xtensa"


echo ${PBS_ARRAYID} ${array[PBS_ARRAYID]}

python ${KMAX_ROOT}/analysis/collect_golem.py ${array[PBS_ARRAYID]} > /scratch/pcg234/kmax/out/${PBS_JOBNAME}${PBS_JOBID}.out 2> /scratch/pcg234/kmax/out/${PBS_JOBNAME}${PBS_JOBID}.err
