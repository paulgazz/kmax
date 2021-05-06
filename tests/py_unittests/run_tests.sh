#!/bin/bash

test_ws="$HOME/kmax-tests/"

if [[ -d "${test_ws}" ]]
then
  echo "ERROR: The test workspace directory \"${test_ws}\" exists. Remove the directory before running the tests."
  exit 1
fi

echo "Test files will be saved in \"${test_ws}\"."

# run from script location: will assume the file hierarchy in script directory
cd "$( dirname "${BASH_SOURCE[0]}" )"

# get linux 5.4.4 source
echo "Preparing the Linux kernel source to be used by the tests.."
mkdir -p ${test_ws}
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.4.tar.xz -P ${test_ws}
tar -xf ${test_ws}/linux-5.4.4.tar.xz -C ${test_ws}
ksrc=$(realpath ${test_ws}/linux-5.4.4)
arch_ksrc=$(realpath ${test_ws}/linux-5.4.4-arch)
klocalizer_ksrc=$(realpath ${test_ws}/linux-5.4.4-klocalizer)
cp -r ${ksrc} ${arch_ksrc}
mv ${ksrc} ${klocalizer_ksrc}
echo "Done preparing the Linux kernel source."

# run tests for kmax.Arch
echo "Starting testing kmax.Arch.."
LINUX_KSRC=${arch_ksrc} python3 -m unittest test_arch.py -v
echo "Done testing kmax.Arch."

# run tests for kmax.Klocalizer
echo "Starting testing kmax.Klocalizer.."
LINUX_KSRC=${klocalizer_ksrc} python3 -m unittest test_klocalizer.py -v
echo "Done testing kmax.Klocalizer."

echo "Done with all the tests."
echo "Test files are saved in \"${test_ws}\". Remove the directory before running the tests again."