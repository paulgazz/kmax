#!/bin/sh
#PBS -V
#PBS -l nodes=1:ppn=4,walltime=8:00:00,mem=8GB
#PBS -N collect_presenceconditions
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

# Find presence conditions.  Needs 8GB mem as set above to run SuperC.
# To submit, use an array of jobs: "qsub -t 0-39 -v
# version="3.2",arch="x86" $KMAX_ROOT/analysis/schedule_presenceconditions.q"

if [[ "${version}" == "" || "${arch}" == "" ]]; then
    echo "USAGE: qsub -t 0-NJOBS -v version=version,arch=arch schedule_presenceconditions.q"
    exit 1
fi

module load python/intel/2.7.6

echo ${PBS_ARRAYID}

python ${KMAX_ROOT}/analysis/collect_presenceconditions.py -j ${PBS_ARRAYID} ${version} ${arch}
