## This scripts shows how to create a fresh install of kmax in a new
## virtual machine and run the getting started test.

## create a fresh debian VM
# mkdir ~/kmax_fresh_install/
# cd ~/kmax_fresh_install/
# vagrant init debian/buster64
# vagrant up
# vagrant ssh

## install and test kmax inside the VM
sudo apt install -y python3-pip flex bison bc libssl-dev
sudo pip3 install kmaxtools --pre
wget https://cdn.kernel.org/pub/linux/kernel/v5.x/linux-5.4.tar.xz
tar -xvf linux-5.4.tar.xz
cd linux-5.4/
klocalizer drivers/usb/storage/alauda.o
make ARCH=x86_64 olddefconfig
make ARCH=x86_64 clean drivers/usb/storage/alauda.o
