#!/usr/bin/env bash
mkdir -p benchmarks
parallel << EOF
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CB_FPBEQ_FPBLE.cnf --strategy ConstructiveBottom --strategy FacePBEQ --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_LP_FPBLE_ZR_YS.cnf --strategy CakeSliceOrdering --strategy LabelPermutation --strategy FacePBLE --strategy ZRing --strategy YStep
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CSO_LP_FPBLE_ZR_YS.cnf --strategy TopCubeOrdering --strategy CakeSliceOrdering --strategy LabelPermutation --strategy FacePBLE --strategy ZRing --strategy YStep
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_AM_IXA_LP_FPBLE.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy AntiMirror --strategy IncreasingXAxis --strategy LabelPermutation --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_CSO_IXA_LP_FPBLE.cnf --strategy BottomCenter012 --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy LabelPermutation --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_CSO_IXA_LP.cnf --strategy BottomCenter012 --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy LabelPermutation
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_AM_IXA_LP.cnf --strategy CakeSliceOrdering --strategy AntiMirror --strategy IncreasingXAxis --strategy LabelPermutation
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CB_LP.cnf --strategy TopCubeOrdering --strategy ConstructiveBottom --strategy LabelPermutation
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CB_LP_FPBLE.cnf --strategy TopCubeOrdering --strategy ConstructiveBottom --strategy LabelPermutation --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CB_LP_FPBLE.cnf --strategy ConstructiveBottom --strategy LabelPermutation --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_AM_IXA_LPI.cnf --strategy BottomCenter012 --strategy AntiMirror --strategy IncreasingXAxis --strategy LabelPermutationImportance
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CB_CSO_LP_FPBEQ_FPBLE.cnf --strategy ConstructiveBottom --strategy CakeSliceOrdering --strategy LabelPermutation --strategy FacePBEQ --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_CSO_AM_IXA.cnf --strategy BottomCenter012 --strategy CakeSliceOrdering --strategy AntiMirror --strategy IncreasingXAxis
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_AM_IXA.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy AntiMirror --strategy IncreasingXAxis
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CSO_AM_IXA.cnf --strategy TopCubeOrdering --strategy CakeSliceOrdering --strategy AntiMirror --strategy IncreasingXAxis
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_IXA_LPI.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy IncreasingXAxis --strategy LabelPermutationImportance
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_AM_IXA_FPBLE.cnf --strategy BottomCenter012 --strategy AntiMirror --strategy IncreasingXAxis --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_AM_IXA_FPBLE.cnf --strategy TopCubeOrdering --strategy AntiMirror --strategy IncreasingXAxis --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_AM_IXA_FPBLE.cnf --strategy AntiMirror --strategy IncreasingXAxis --strategy FacePBLE
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_IXA_LPI_FPBLE.cnf --strategy BottomCenter012 --strategy IncreasingXAxis --strategy LabelPermutationImportance --strategy FacePBLE
bel_pyramid 5 --skip-solver --cnf benchmarks/bp5_CSO.cnf --strategy CakeSliceOrdering
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_IXA_LP_FPBEQ_ZR.cnf --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy LabelPermutation --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_IXA_ZR.cnf --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy ZRing
bel_pyramid 5 --skip-solver --cnf benchmarks/bp5.cnf
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_CSO_LP_FPBEQ_ZR.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy CakeSliceOrdering --strategy LabelPermutation --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CTD_IXA_ZR.cnf --strategy ConstructiveTripleDiagonal --strategy IncreasingXAxis --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_IXA_FPBLE_ZR.cnf --strategy TopCubeOrdering --strategy IncreasingXAxis --strategy FacePBLE --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_IXA_FPBEQ_ZR.cnf --strategy IncreasingXAxis --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_CSO_FPBEQ_FPBLE_ZR.cnf --strategy BottomCenter012 --strategy CakeSliceOrdering --strategy FacePBEQ --strategy FacePBLE --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_IXA_LP_FPBEQ_FPBLE_ZR.cnf --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy LabelPermutation --strategy FacePBEQ --strategy FacePBLE --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CSO_ZR.cnf --strategy TopCubeOrdering --strategy CakeSliceOrdering --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_CSO_IXA_FPBLE_ZR.cnf --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy FacePBLE --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_AM_FPBEQ_ZR.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy AntiMirror --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_CSO_AM_FPBEQ_FPBLE_ZR.cnf --strategy BottomCenter012 --strategy CakeSliceOrdering --strategy AntiMirror --strategy FacePBEQ --strategy FacePBLE --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_LPI_FPBEQ_ZR.cnf --strategy LabelPermutationImportance --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_AM_FPBEQ_ZR.cnf --strategy BottomCenter012 --strategy AntiMirror --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_CSO_IXA_LP_ZR.cnf --strategy TopCubeOrdering --strategy CakeSliceOrdering --strategy IncreasingXAxis --strategy LabelPermutation --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_LP_FPBEQ_ZR.cnf --strategy BottomCenter012 --strategy LabelPermutation --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_TCO_LP_FPBEQ_ZR.cnf --strategy TopCubeOrdering --strategy LabelPermutation --strategy FacePBEQ --strategy ZRing
bel_pyramid 4 --skip-solver --cnf benchmarks/bp4_BC012_TCO_LP_FPBLE_ZR.cnf --strategy BottomCenter012 --strategy TopCubeOrdering --strategy LabelPermutation --strategy FacePBLE --strategy ZRing
EOF
gzip benchmarks/*.cnf
