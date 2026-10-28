#!/usr/bin/env bash
set -euo pipefail
export LEAN_NUM_THREADS=8
lake env lean -E warning --root="$RUN_INPUTS" -c "$RUN_OUT/AreaBench.c" "$RUN_INPUTS/AreaBench.lean"
lake env leanc -O3 -DNDEBUG -DLEAN_EXPORTING -c "$RUN_OUT/AreaBench.c" -o "$RUN_OUT/AreaBench.o"
lake env lean --run "$RUN_INPUTS/NativeBenchLink.lean" .lake/build/bin/ix.rsp "$RUN_OUT/AreaBench.rsp" "$RUN_OUT/AreaBench.o"
lake env leanc -o "$RUN_OUT/area-bench" @"$RUN_OUT/AreaBench.rsp"
/usr/bin/time -v "$RUN_OUT/area-bench"
