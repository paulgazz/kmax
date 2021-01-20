#!/bin/bash

# get linux 5.4.4 source
echo "Preparing the Linux kernel source to be used by the tests.."
mkdir -p ~/kmax-tests/
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.4.tar.xz -P ~/kmax-tests/
tar -xf ~/kmax-tests/linux-5.4.4.tar.xz -C ~/kmax-tests/
ksrc=$(realpath ~/kmax-tests/linux-5.4.4)
arch_ksrc=$(realpath ~/kmax-tests/linux-5.4.4-arch)
klocalizer_ksrc=$(realpath ~/kmax-tests/linux-5.4.4-klocalizer)
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