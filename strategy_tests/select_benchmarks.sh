#!/usr/bin/env bash

cat << EOF1 > ../generate_benchmarks.sh
#!/usr/bin/env bash
mkdir -p benchmarks
parallel << EOF
EOF1

cat << EOF2 > selected_benchmarks.md
| Benchmark | Satisfiable? | Kissat Runtime (seconds) |
| --- | --- | --- |
EOF2

# 1. Take the 100 slowest SAT and UNSAT configurations.
# 2. Randomly choose 20 of those.
# 3. Print the name, result, and runtime in table format for README.md.
# 4. Get the cnf generation command line from the first comment in the cnf file.
# 5. Format the cnf generation command line for creating the benchmark and add to generate_benchmarks.sh

make_instances () {
    grep "$1" sorted_runtimes.txt \
    | tail -n 100 \
    | shuf -n 20 \
    | sort -nk3 \
    | tee >( awk '{sub(/^.*\//, ""); sub(/\.cert/, ""); OFS=" | "; print "| " $1,$2,$3 " |"}' >> selected_benchmarks.md ) \
    | awk '{gsub(/cert/, "cnf"); print $1}' \
    | xargs head -1 --quiet \
    | cut -d' ' -f2- \
    | awk '{sub(/^.*bel_pyramid/, "bel_pyramid"); sub(/--cnf cnf_.*\//, "--cnf benchmarks/"); print}' \
    | tee -a ../generate_benchmarks.sh
}

make_instances " UNSAT"
make_instances " SAT"

# Put the remaining stuff in the generate_benchmarks script.
cat << EOF3 >> ../generate_benchmarks.sh
EOF
gzip benchmarks/*.cnf
EOF3

