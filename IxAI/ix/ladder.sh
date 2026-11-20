#!/usr/bin/env bash
# Compress an exported aggregate root to a PLONK certificate with this project's pinned copy of
# the L3 compression ladder (ix/toolchain: binary, CUDA libraries, artifacts, Ignition SRS and a
# manifest whose base and cache are inside the project), through heavy.sh.
#   ladder.sh ROOT_DIR OUT_DIR
# Each prove, check or compression run is capped at STEP_CAP seconds (default 1800) after the
# gate grants the machine; waiting for the gate does not count.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
T="$here/toolchain"
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export IX_KZG_SRS="$T/base/target/compress-wrap/params/bn254-ignition-main-197/srs.bin"
export IX_PARAMS_DIR="$T/base/target/compress-wrap/params"
export IX_KZG_CUDA_SRS_CACHE=1 IX_PROFILE=pinned
exec "$here/heavy.sh" timeout "${STEP_CAP:-1800}" /usr/bin/time -v -o "$2.time" "$here/ixw" compress aiur-ladder-run \
  --ladder "$T/l3.json" --ladder-blake3 "$(cat "$T/l3.json.blake3")" \
  --root-dir "$1" --out "$2"
