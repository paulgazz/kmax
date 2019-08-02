for i in skas_analysis/* undertaker/* undertaker2/*; do
  path="dimacs/$(dirname ${i})"
  stem="$(basename ${i})"
  kmax="${path}/${stem}.kmax"
  dimacs="${path}/${stem}.dimacs"
  mkdir -p ${path}
  check_dep --dimacs "${i}" | tee "${kmax}" | python /home/paul/research/repos/kmax/kconfig/dimacs.py --remove-bad-selects --include-nonvisible-bool-defaults --remove-orphaned-nonvisibles | tee "${dimacs}"
done
