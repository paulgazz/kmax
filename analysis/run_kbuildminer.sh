## Setup
# sudo apt-get install maven
# git clone https://github.com/ckaestne/KBuildMiner.git
# cd KBuildMiner/
# mvn compile
# mvn dependency:build-classpath -Dmdep.outputFile=.classpath-scala
# git clone ~/Work/master_linux_instance/ linux
# cd linux; git checkout 2.6.33.3; cd ..
# cp linux/arch/x86/Makefile linux/tmpMake
# ./run.sh gsd.buildanalysis.linux.KBuildMinerMain --topFolders tmpMake,block,crypto,drivers,firmware,fs,init,ipc,kernel,lib,mm,net,security,sound --codebase ./linux --pcOutput ./x86.pcr
# cat x86.pcr | cut -f1 -d: | sort | uniq | wc -l
# diff -y kmax_x86.txt  kbuildminer_x86.txt  | egrep "<|\||>" | grep -v "\.S"

## Data collection
# for version in "3.19" "2.6.33.3"; do
#   cd linux; git checkout v$version; cd ..
#   for arch in $(ls linux/arch/ | grep -v Kconfig); do
#     pcrfile="pcr_$version$arch.pcr"
#     sorted="kbuildminer_$version$arch.txt"
#     cp linux/arch/$arch/Makefile linux/tmpMake
#     ./run.sh gsd.buildanalysis.linux.KBuildMinerMain --topFolders tmpMake,block,crypto,drivers,firmware,fs,init,ipc,kernel,lib,mm,net,security,sound --codebase ./linux --pcOutput $pcrfile
#     cat $pcrfile | cut -f1 -d: | sort | uniq > $sorted
#   done
# done

## Running time.  The first is a warm-up run.
for i in {1..6}; do
  version="3.19"
  # version="2.6.33.3"
  cd linux; git checkout v$version; cd ..
  arch="x86"
  pcrfile="pcr_$version$arch.pcr"
  sorted="kbuildminer_$version$arch.txt"
  cp linux/arch/$arch/Makefile linux/tmpMake
  /usr/bin/time ./run.sh gsd.buildanalysis.linux.KBuildMinerMain --topFolders tmpMake,block,crypto,drivers,firmware,fs,init,ipc,kernel,lib,mm,net,security,sound --codebase ./linux --pcOutput $pcrfile 2>> kbuildminer_running_time_$version$arch.txt
  # cat $pcrfile | cut -f1 -d: | sort | uniq > $sorted
done
