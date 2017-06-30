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
for version in "3.19" "3.2" "2.6.33.3"; do
  cd linux; git checkout v$version; cd ..
  for arch in $(ls linux/arch/); do
    pcrfile="pcr_$version$arch.pcr"
    sorted="kbuildminer_$version$arch.txt"
    cp linux/arch/$arch/Makefile linux/tmpMake
    ./run.sh gsd.buildanalysis.linux.KBuildMinerMain --topFolders tmpMake,block,crypto,drivers,firmware,fs,init,ipc,kernel,lib,mm,net,security,sound --codebase ./linux --pcOutput $pcrfile
    cat $pcrfile | cut -f1 -d: | sort | uniq > $sorted
  done
done
