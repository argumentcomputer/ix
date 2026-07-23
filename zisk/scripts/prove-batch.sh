#!/usr/bin/env bash
# Prove one or many typechecker inputs in a single warm Zisk process and
# aggregate every leaf proof into one recursive proof.
#
# All proving happens in one binary invocation: the prover is set up once
# and the GPU/CUDA context stays warm across every input, so the proofman
# init + GPU kernel cold-start is paid exactly once for the whole batch
# (see the README's Zisk notes on cold-start).
#
# Usage:
#   scripts/prove-batch.sh --gpu --ixe ../nataddcomm.ixe
#   scripts/prove-batch.sh --gpu --ixe ../nataddcomm.ixe --ixe ../stringappend.ixe
#   scripts/prove-batch.sh --gpu --ixe ../init.ixe --shard-bytes 250000
#   scripts/prove-batch.sh --execute --ixe ../nataddcomm.ixe   # VM only, no proof
# All flags pass straight through to zisk-host (--gpu, --ixe (repeatable),
# --shard-bytes/--shard-consts, --agg-arity, --max-witness-stored, ...).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ZISK_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${ZISK_DIR}"

# Memory watchdog: SIGKILLs the prover if used RAM exceeds MEM_LIMIT_GIB
# (default 200 GiB). Override with MEM_LIMIT_GIB=... See mem-guard.sh.
source "${SCRIPT_DIR}/mem-guard.sh"

# Pin the CUDA JIT compile cache to its 4 GB hard max. The driver caches
# compiled proving kernels (PTX->SASS) under ~/.nv/ComputeCache and reuses
# them across processes — that's what keeps a second run warm. The default
# cap is ~1 GB and our cache already sits at it; as the batch JITs more
# kernel variants (bigger envs, more state-machine shapes), an under-sized
# cap forces LRU eviction and intermittent re-JIT cold spikes mid-batch.
# Raising it removes that failure mode (cost is only disk).
export CUDA_CACHE_MAXSIZE="${CUDA_CACHE_MAXSIZE:-4294967296}"

export RUST_LOG="${RUST_LOG:-info}"

run_guarded cargo run --release --bin zisk-host -- "$@"
