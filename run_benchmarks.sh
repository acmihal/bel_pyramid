#!/usr/bin/env bash

ls benchmarks/*.cnf.gz | parallel kissat {} ">" {.}.cert

# Sort results by Kissat process-time.
grep -H process-time benchmarks/*.cert | awk '{print $1, $(NF-1)}' | sort -n -k 2 | tee benchmarks/sorted_runtimes.txt
