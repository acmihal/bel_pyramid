#!/usr/bin/env bash

mkdir -p benchmarks

# Requires GNU Parallel
parallel << EOF
bel_pyramid 4 --strategy ZRing --strategy ConstructiveTripleDiagonal --cnf benchmarks/bp4_zring_ctd.cnf --skip-solver
bel_pyramid 5 --strategy YStep --strategy ConstructiveTripleDiagonal --cnf benchmarks/bp5_ystep_ctd.cnf --skip-solver
bel_pyramid 5 --strategy YStep --strategy ConstructiveTripleDiagonal --finite-domain enum --cnf benchmarks/bp5_ystep_ctd_enum.cnf --skip-solver
bel_pyramid 4 --strategy YStep --strategy ZRing --cnf benchmarks/bp5_ystep_zring.cnf --skip-solver
bel_pyramid 4 --strategy ConstructiveBottom --cnf benchmarks/bp4_cbottom.cnf --skip-solver
bel_pyramid 4 --strategy ConstructiveShell --cnf benchmarks/bp4_cshell.cnf --skip-solver
bel_pyramid 4 --strategy ConstructiveDiagonal --cnf benchmarks/bp4_cdiag.cnf --skip-solver
bel_pyramid 4 --cnf benchmarks/bp4.cnf --skip-solver
bel_pyramid 5 --strategy ConstructiveTripleDiagonal --cnf benchmarks/bp5_ctd.cnf --skip-solver
bel_pyramid 4 --strategy LabelPermutation --cnf benchmarks/bp4_lp.cnf --skip-solver
bel_pyramid 4 --finite-domain enum --cnf benchmarks/bp4_enum.cnf --skip-solver
bel_pyramid 5 --strategy ConstructiveTripleDiagonal --finite-domain enum --cnf benchmarks/bp5_ctd_enum.cnf --skip-solver
bel_pyramid 4 --strategy AntiMirror --cnf benchmarks/bp4_am.cnf --skip-solver
bel_pyramid 5 --strategy LabelPermutation --strategy ConstructiveTripleDiagonal --cnf benchmarks/bp5_lp_ctd.cnf --skip-solver
EOF

gzip benchmarks/*.cnf

