#!/bin/bash

# Test --for-unmet-free and --allow-unmet-for options for klocalizer

# Input: kernel source
if [[ "${#}" < "1" ]]; then
  echo "USAGE: $(basename ${0}) KSRC"
  echo "  KSRC         The path to the kernel source directory (tests are reproducible for v5.4.4)."
  exit 1
fi

KSRC=$(realpath $1)

# Test case paths
inp1="assets/unmetdd_constraints_for_GPIOLIB_IRQCHIP_by_PINCTRL_BCM2835.smt2"
inp2="assets/unmetdd_constraints_for_GRO_CELLS_by_MACSEC.smt2"

inp1="$(realpath $(dirname $0)/$inp1)"
inp2="$(realpath $(dirname $0)/$inp2)"

# Check if the required folders/files exist
if [ ! -d "$KSRC" ]; then
  echo "The directory '${KSRC}' doesn't exist."
  exit 1
fi

if [ ! -f "$inp1" ] || [ ! -f "$inp2" ]; then
  echo "Cannot find some of the input files."
  exit 1
fi

# From now on, we are on the kernel directory
cd $KSRC
make kernelversion > /dev/null 2>&1

if [ ! "$?" -eq "0" ]; then
  echo "The input directory does not look like a kernel source directory: `make kernelversion` failed!."
  exit 1
fi

# Check the exit code ("$?") to see if the last operation was success or fail, and print the result.
# Inputs: $1: Expected exit code
check_success() {
    exit_code=$?
    expected=$1
    if [ $expected -eq $exit_code ]; then
        result="PASS"
    else
        result="FAIL (exit code: $exit_code, expected: $expected)"
    fi

    echo $result 1>&2
    echo ""
}

# Test case 1: unmetdd_constraints_for_GPIOLIB_IRQCHIP_by_PINCTRL_BCM2835.smt2 (inp1)
klocalizer -a=x86_64 --constraints-file-smt2=$inp1; check_success 0 # should pass
klocalizer -a=x86_64 --constraints-file-smt2=$inp1 --force-unmet-free; check_success 11 # should fail
klocalizer -a=x86_64 --constraints-file-smt2=$inp1 --force-unmet-free --allow-unmet-for CONFIG_GPIOLIB_IRQCHIP; check_success 0 # should pass

# Test case 2: unmetdd_constraints_for_GRO_CELLS_by_MACSEC.smt2 (inp2)
# This is a more complex test case. With the constraints file (inp2), we ask
# klocalizer to localize a config in which GRO_CELLS is selected by MACSEC
# but GRO_CELLS's dependency condition is not satisfied. When we use the
# options "--force-unmet-free --allow-unmet-for CONFIG_GRO_CELLS", klocalizer
# still fails because MACSEC depends on NETDEVICES and ETHERNET, which share
# the same direct dependency (NET) with GRO_CELLS. Consequently, it is not
# possible to create a unmet direct dependency issue with (GRO_CELLS, MACSEC)
# with forcing NETDEVICES and ETHERNET to be unmet free. Therefore, when we
# add those symbols to --allow-unmet-for list, the test passes, resulting in
# multiple unmet direct dependency warnings.
klocalizer -a=powerpc --constraints-file-smt2=$inp2; check_success 0 # should pass
klocalizer -a=powerpc --constraints-file-smt2=$inp2 --force-unmet-free; check_success 11 # should fail
klocalizer -a=powerpc --constraints-file-smt2=$inp2 --force-unmet-free --allow-unmet-for CONFIG_GRO_CELLS; check_success 11 # should fail
klocalizer -a=powerpc --constraints-file-smt2=$inp2 --force-unmet-free --allow-unmet-for CONFIG_GRO_CELLS CONFIG_NETDEVICES CONFIG_ETHERNET; check_success 0 # should pass