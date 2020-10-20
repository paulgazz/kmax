#!/bin/bash

#$1: test kconfig file (in kclause folder)

kextract -o ./$1.extract --extract ./$1
kclause < ./$1.extract > ./$1.pickle
python3 getSol.py $1.pickle > $1.sol

echo ""
echo ">> Kconfig file:"
cat $1

echo ""
echo ">> Kextract result:"
cat $1.extract

echo ""
echo ">> Kclause result:"
cat $1.pickle

echo ""
echo ""
echo ">> Possible solutions:"
cat $1.sol

