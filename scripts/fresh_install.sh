## This script shows how to create a fresh install of kmax in a new
## virtual machine and run the getting started test.

## create a fresh debian VM
# mkdir ~/kmax_fresh_install/
# cd ~/kmax_fresh_install/
# vagrant init ubuntu/groovy64
# vagrant up
# vagrant ssh

## install and test kmax inside the VM
sudo apt update
sudo apt install -y python3-pip flex bison bc libssl-dev  # needed for klocalizer
sudo apt-get install libelf-dev # needed to compile linux in some configs
sudo pip3 install kmax --pre
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.12.tar.xz
tar -xvf linux-5.12.tar.xz
cd linux-5.12/
klocalizer drivers/usb/storage/alauda.o
make ARCH=x86_64 olddefconfig
make ARCH=x86_64 clean drivers/usb/storage/alauda.o


# sudo apt install -y python3-pip python3-venv flex bison bc libssl-dev libelf-dev
# python3 -m venv kmax_env  # create the environment
# source kmax_env/bin/activate  # enter the environment
# pip3 install kmax  # install kmax in the environment
# wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.tar.xz
# tar -xvf linux-5.4.tar.xz
# cd linux-5.4/
# klocalizer drivers/usb/storage/alauda.o
# make ARCH=x86_64 olddefconfig
# make ARCH=x86_64 clean drivers/usb/storage/alauda.o
