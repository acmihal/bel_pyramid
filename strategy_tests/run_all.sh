#!/usr/bin/env bash

run_with_kissat () {
    num_levels=$1
    file_base=$2
    cnf=cnf_${num_levels}/${file_base}.cnf
    cert=cert_${num_levels}/${file_base}.cert
    reimport=reimport_${num_levels}/${file_base}.txt
    shift 2
    bel_pyramid ${num_levels} --skip-solver --cnf $cnf $@
    timeout --signal INT 1h kissat $cnf > $cert
    bel_pyramid ${num_levels} --cert $cert > $reimport
}

export -f run_with_kissat

mkdir -p cnf_{3..5} cert_{3..5} reimport_{3..5}

python3 - << EOF | parallel --dry-run
from itertools import chain, combinations
import string
from bel_pyramid.strategies import StrategyMap

shorthand_table = str.maketrans('', '', string.ascii_lowercase)
shorthand_strategy_map = {strategy: strategy.translate(shorthand_table) for strategy in StrategyMap.keys()}
powerset = chain.from_iterable(combinations(StrategyMap.keys(), r) for r in range(len(StrategyMap)+1))

for ix, strategies in enumerate(powerset):
    basename = ''.join([f'_{shorthand_strategy_map[strategy]}' for strategy in strategies])
    strat_params = ' '.join([f'--strategy {strategy}' for strategy in strategies])
    print(f'run_with_kissat 3 bp3{basename} {strat_params}')
    print(f'run_with_kissat 4 bp4{basename} {strat_params}')
    if ix <= 20:
        print(f'run_with_kissat 5 bp5{basename} {strat_params}')
EOF

find cert_* -type f -name \*.cert \
| xargs -n 128 awk '/SIGINT/{R="SIGINT"} /s UNSAT/{R="UNSAT"} /s SAT/{R="SAT"} /process-time/{print FILENAME,R,$(NF-1)}' \
| sort -nk3 > sorted_runtimes.txt

