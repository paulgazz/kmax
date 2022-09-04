# Given two configuration files, compute and print the difference count.

if [ "$#" -ne 2 ]; then
  echo "Illegal number of parameters!"
  echo "Provide two arguments, each a path to a Linux configuration file."
  exit -1
fi

cfg1_path=$1
cfg2_path=$2

if [ ! -f "$cfg1_path" ]; then
  echo "Cannot find a configuration file at \"$cfg1_path\""
  exit -1
fi

if [ ! -f "$cfg2_path" ]; then
  echo "Cannot find a configuration file at \"$cfg2_path\""
  exit -1
fi

difference=$(comm <(grep "^CONFIG" ${cfg1_path} | sort) <(grep "^CONFIG" ${cfg2_path} | sort) -3 | wc -l)
echo $difference
