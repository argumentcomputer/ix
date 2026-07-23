#!/usr/bin/env bash
# Execute or prove the Ix kernel typecheck on SP1, with the BLAKE3_COMPRESS
# precompile enabled. Defaults to proving Nat.add_comm (nataddcomm.ixe) on CPU.
#
# Usage:
#   scripts/prove-ix.sh                       # prove nataddcomm.ixe on CPU
#   SP1_PROVER=cuda scripts/prove-ix.sh       # prove on GPU
#   scripts/prove-ix.sh --execute             # execute only (no proof)
#   IXE=/path/to/foo.ixe scripts/prove-ix.sh  # a different env
#   scripts/prove-ix.sh --meta                # Meta mode instead of Anon
# Extra flags after the script name pass through to sp1-host.
#
# The cargo deps (sp1-sdk/sp1-build/sp1-zkvm) come from the argumentcomputer/sp1
# fork's `blake3-precompile` branch. But two runtime pieces are prebuilt
# binaries that can't come from a crate registry and must be produced from a
# local checkout of that same fork:
#   1. sp1-core-executor-runner-binary — the host spawns execution children
#      from it; it embeds the JIT syscall dispatch, so it must know the new
#      BLAKE3_COMPRESS syscall or the child panics `invalid syscall number`.
#   2. ~/.sp1/bin/sp1-gpu-server (GPU only) — install once via
#      ${SP1_FORK_DIR}/sp1-gpu/scripts/install-fork-gpu-server.sh.
# Point SP1_FORK_DIR at that checkout (machine-local; default below).
#
# WITHOUT_VK_VERIFICATION=1 is required: the BLAKE3 chip's recursion shapes
# aren't in the bundled vk_map.bin, so the production vk-allowlist check would
# reject the proof. The fork's `experimental` feature (wired into sp1-host's
# sp1-sdk dep) honors this env var on the verifier side. NOT production-safe —
# drop both once a vk_map.bin including the new chip is regenerated.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SP1_WS="$(cd "${SCRIPT_DIR}/.." && pwd)"          # ~/ix/sp1
IX_ROOT="$(cd "${SP1_WS}/.." && pwd)"             # ~/ix

SP1_FORK_DIR="${SP1_FORK_DIR:-/home/ubuntu/sp1-fork/sp1}"
RUNNER_BIN="${SP1_FORK_DIR}/target/release/sp1-core-executor-runner-binary"
IXE="${IXE:-${IX_ROOT}/nataddcomm.ixe}"
PROVER="${SP1_PROVER:-cpu}"

if [[ ! -f "${IXE}" ]]; then
    echo "[prove-ix] error: env file not found: ${IXE}" >&2
    exit 1
fi

# Step 1: build the BLAKE3-aware runner-binary from the fork checkout. Always
# run (no-op ~1s when nothing changed); a stale binary panics with
# `invalid syscall number` on the precompile.
echo "[prove-ix] building sp1-core-executor-runner-binary in ${SP1_FORK_DIR}..."
(cd "${SP1_FORK_DIR}" && cargo build --release -p sp1-core-executor-runner-binary)

# Step 2: GPU only — clear stale gpu-server/sockets and plant the fork's
# runner-binary where the bundled gpu-server expects it. The gpu-server
# extracts its own include_bytes!'d runner to /tmp/sp1-native-runner-bin-{HASH}
# only if no file is already there; pre-writing ours wins that race.
if [[ "${PROVER}" == "cuda" ]]; then
    pkill -KILL -x sp1-gpu-server 2>/dev/null || true
    rm -f /tmp/sp1-cuda-*.sock
    GPU_SERVER="${HOME}/.sp1/bin/sp1-gpu-server"
    if [[ ! -x "${GPU_SERVER}" ]]; then
        echo "[prove-ix] error: ${GPU_SERVER} not found." >&2
        echo "[prove-ix] install it: ${SP1_FORK_DIR}/sp1-gpu/scripts/install-fork-gpu-server.sh" >&2
        exit 1
    fi
    EXPECTED_NAME=$(strings "${GPU_SERVER}" | grep -oE 'sp1-native-runner-bin-[0-9a-f]{64}' | head -1)
    if [[ -z "${EXPECTED_NAME}" ]]; then
        echo "[prove-ix] error: could not extract runner-binary hash from ${GPU_SERVER}" >&2
        exit 1
    fi
    PLANTED="/tmp/${EXPECTED_NAME}"
    cp -f "${RUNNER_BIN}" "${PLANTED}"
    chmod +x "${PLANTED}"
    echo "[prove-ix] planted fork runner-binary at ${PLANTED}"
fi

# Step 3: env + run.
export SP1_CORE_RUNNER_OVERRIDE_BINARY="${RUNNER_BIN}"
export WITHOUT_VK_VERIFICATION=1
export SP1_PROVER="${PROVER}"
export RUST_LOG="${RUST_LOG:-info}"

cd "${SP1_WS}"
echo "[prove-ix] prover=${PROVER}  ixe=${IXE}"
if [[ "${PROVER}" == "cuda" ]]; then
    exec cargo run --release -p sp1-host --features cuda -- --ixe "${IXE}" "$@"
else
    exec cargo run --release -p sp1-host -- --ixe "${IXE}" "$@"
fi
