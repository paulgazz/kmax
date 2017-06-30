echo "configuration variables: find | grep -i config.in | xargs cat | grep -o "CONFIG_[A-Za-z0-9_]*" | sort | uniq | wc -l"
make ARCH=i386 clean mrproper
make ARCH=i386 symlinks
check_dep -C -d --everyyes arch/i386/config.in
make -i ARCH=i386 vmlinux > make.txt 2>&1
echo "compilation units: " `cat make.txt | grep "^gcc" | awk '{print$NF}' | grep "\.c$" | wc -l`
i386=`find -type f -name "*.c" | grep arch/i386 | wc -l`
nonarch=`find -type f -name "*.c" | grep -v "\./arch/" | wc -l`
echo "potential compilation units (i386 and nonarch): " $((i386+nonarch))
echo "all .c files: " `find -type f -name "*.c" | wc -l`
