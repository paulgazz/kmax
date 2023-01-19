<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Evaluation](#evaluation)
  - [Sampling patches](#sampling-patches)
    - [Filtering out non-source code patches](#filtering-out-non-source-code-patches)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Evaluation

## Sampling patches

- clone the stable linux repo: git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git
- get commits from the last year
- filter in only those that touch code (.c/.h)
  - git log --until=2022-09-18 --since=2021-09-19 --no-merges
  - ... | grep ^commit | wc -l was 71,896
  - https://www.calculator.net/sample-size-calculator.html?type=1&cl=99&ci=5&pp=50&ps=71896&x=84&y=21
    - sample size 660 for 99% confidence in a 5% margin of error for a population of 71,896
- take a random sample
  - head -n660 /dev/urandom > randfile
  - git log --until=2022-09-18 --since=2021-09-19 --no-merges --pretty=format:%H | shuf --random-source=randfile | head -n660 > sample


### Filtering out non-source code patches

- run koverage on each commit
- check whether any lines exist included in the coverage report
- results in 507 patches
