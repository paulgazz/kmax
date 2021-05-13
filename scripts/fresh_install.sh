#!/bin/bash

set -x

## This script shows how to create a fresh install of kmax in a new
## virtual machine and run the getting started test.

## create a fresh debian VM
# mkdir ~/kmax_fresh_install/
# cd ~/kmax_fresh_install/
# vagrant init ubuntu/groovy64; vagrant up; vagrant ssh

# install system libraries
sudo apt update
sudo apt install -y python3-pip python3-venv flex bison bc libssl-dev  # needed for klocalizer
sudo apt-get install libelf-dev # needed to compile linux in some configs

# install the latest kmax in a python virtual environment
python3 -m venv kmax_env
source kmax_env/bin/activate
pip3 install --pre -U kmax

# get linux source code
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.12.tar.xz
tar -xvf linux-5.12.tar.xz
cd linux-5.12/

# run klocalizer and build the resulting config
klocalizer drivers/usb/storage/alauda.o
make ARCH=x86_64 olddefconfig
make ARCH=x86_64 clean drivers/usb/storage/alauda.o
