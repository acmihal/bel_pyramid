#!/usr/bin/env bash

ls benchmarks/*.cnf.gz | parallel --plus kissat {} ">" {..}.cert

# Sort results by Kissat process-time.
find benchmarks -type f -name \*.cert \
| xargs -n 128 awk '/SIGINT/{R="SIGINT"} /s UNSAT/{R="UNSAT"} /s SAT/{R="SAT"} /process-time/{print FILENAME,R,$(NF-1)}' \
| sort -nk3 > benchmarks/sorted_runtimes.txt
