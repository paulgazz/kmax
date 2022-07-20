# krepair evaluation scripts

## running the evaluation

```
# get a copy of the linux source
git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git linux

# extract the list of patch coverage conditions
mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
(cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist

# kick off a server providing the names of patches (designed this way to enable parallelized experiments)
java superc.util.FilenameService -server 55679 patchlist &

# run the evaluation
bash evaluation_client.sh localhost 55679 6h repair_results build_targets.json linux/ formulacache/ patchconditions/ x86_64 > evaluation_client.out 2>&1
```


## parallelized experiments

```
# clone a copy of the linux source for each experiment process
for i in {0..9}; do git clone https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git linux$i; done

# extract the list of patch coverage conditions
mkdir patchconditions; tar -C patchconditions -xvf final_patch_conditions_v512_v513.tar.gz
(cd patchconditions/x86_64/; ls *.cond | sed 's/\.cond//') | shuf --random-source=<(yes) > patchlist

# kick off a server providing the names of patches (designed this way to enable parallelized experiments)
java superc.util.FilenameService -server 55679 patchlist &

# run several evaluation processes
for i in {0..9}; do bash evaluation_client.sh localhost 55679 6h repair_results build_targets.json linux$i/ formulacache$i/ patchconditions/ x86_64 > evaluation_client$i 2>&1 & sleep 1; done
```
