#!/usr/bin/env bash
# train_run.sh OUT_DIR [STAGE...] : the training run's Aiur root, proven from its inputs alone: the
# 30 `Fixed::train_block` execution packages and the `AiurExec` block aggregator in
# .truthmines/aiur/aiurexec-block (packages/block-NNN.ixa, aiur-exec.ixa). Stages, in order
# (default: all of them):
#
#   roots     30 block batch roots (batch_root, one normalized shard each) into OUT/roots, then the
#             aggregator's key and identity blob for the block program into OUT/id
#   tree      the 59-node aggregation tree (aiur_exec_tree --prefix block) into OUT/tree; leaves
#             and joins interleave, executions on host threads beside one resident device prover
#   wraps     two normalized wraps of the tree's top (aiur_exec wrap): the streamed top is 2-3
#             trace shards, a wrap is one; then the last wrap laid out as OUT/run-root
#             (root-vk.bin, root-claims.bin, root-proof.bin, out.bin, allowed.bin), the
#             directory the combined certificate's join consumes as its run root
#   check     aiur_exec_check of OUT/run-root against the specification
#             (.truthmines/combined/spec): 30 chained executions of 20 steps each
#
# A stage first removes its own outputs, so nothing from an earlier run is reused. Each of the
# first three is one gated job (ix/heavy.sh) under a memory-capped scope; check needs no GPU and
# runs directly. Each stage appends `stage<TAB>seconds` to OUT/stages.tsv, timed inside its job
# (gate waits excluded); logs and `/usr/bin/time -v` output are OUT/STAGE.{log,time}, the tree's
# stdout/stderr OUT/tree.{out,err} and its 1 s GPU samples OUT/tree.gpu.csv. Exits non-zero at
# the first stage that fails.
#
# Settings: AIUR_GPU_TRACE=generated (function circuits populated on the device), the tree
# driver's defaults otherwise (cells per shard, record ceiling, one executor thread per core).
# Overridable:
#   MAX_RAM    the tree's host budget in GiB (--max-ram), default 170; MEM_CAP the scope's hard
#              limit above it, default MAX_RAM + 10. A run with the machine to itself can use 200.
#   TREE_FLAGS further aiur_exec_tree flags, e.g. `--exec-jobs 12`
#   TOOLS      the CUDA builds of batch_root, aiur_exec, aiur_exec_tree and aiur_exec_check
#   MULTI_STARK_LIB  the directory of the libmulti_stark_cuda.so those builds were linked against
#   STDCXX_LIB       the directory of the libstdc++.so.6 aiur_exec_tree loads (default: found below)
#   CUDA_PRELOAD     the system CUDA driver library, which the Nix-built binaries need preloaded
#   INPUTS     the directory holding packages/ and aiur-exec.ixa; SPEC the check's specification
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ix="$(dirname "$here")"
project="$(dirname "$ix")"
self="$here/$(basename "$0")"
fork="${AIUREXEC_CHECKOUT:-/home/sam/repos/forks/ix-aiurexec}"
tools="${TOOLS:-$fork/target/release/examples}"
# The examples carry no runpath for their CUDA library; this is the multi-stark build the CUDA
# examples were linked with (the target holds a second build of it with other features).
lib="${MULTI_STARK_LIB:-$fork/target/release/build/multi-stark-3f7bed377d2c9460/out}"
cuda_preload="${CUDA_PRELOAD:-/usr/lib/x86_64-linux-gnu/libcuda.so.1}"
# aiur_exec_tree also needs libstdc++, and its Nix loader never searches the system's library
# directories (nor does the build's runpath exist). The default is the Nix gcc runtime built
# against the same glibc as the binary's loader, so libc is not mixed.
stdcxx_lib() {
  local glibc d
  glibc=$(readelf -l "$tools/aiur_exec_tree" | sed -n 's|.*interpreter: \(/nix/store/[^/]*\)/.*|\1|p')
  [ -n "$glibc" ] || return 0
  for d in /nix/store/*-gcc-*-lib; do
    readelf -d "$d/lib/libstdc++.so.6" 2>/dev/null | grep -q "$glibc/lib" && { echo "$d/lib"; return 0; }
  done
}
stdcxx="${STDCXX_LIB:-$(stdcxx_lib)}"
[ -n "$stdcxx" ] || { echo "no libstdc++ for $tools/aiur_exec_tree's glibc; set STDCXX_LIB" >&2; exit 1; }
inputs="${INPUTS:-$project/.truthmines/aiur/aiurexec-block}"
spec="${SPEC:-$project/.truthmines/combined/spec}"
ram="${MAX_RAM:-170}"
mem_cap="${MEM_CAP:-$((ram + 10))}"
cap="${STEP_CAP:-1800}"
blocks=30
steps=20
ax="$inputs/aiur-exec.ixa"

export LD_LIBRARY_PATH="$lib:$stdcxx${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LD_PRELOAD="$cuda_preload"
export AIUR_GPU_TRACE="${AIUR_GPU_TRACE:-generated}"

now() { date +%s.%N; }
since() { awk -v a="$1" -v b="$(now)" 'BEGIN { printf "%.3f", b - a }'; }

# Inside a gated job: run one stage and record its wall time.
if [ "${1:-}" = "--stage" ]; then
  stage=$2; out=$3
  t0=$(now)
  case "$stage" in
    roots)
      rm -rf "$out/roots" "$out/id"; mkdir -p "$out/roots"
      for i in $(seq -f %03g 0 $((blocks - 1))); do
        "$tools/batch_root" "$inputs/packages/block-$i.ixa" "$out/roots/block-$i" \
          > "$out/roots/block-$i.log" 2>&1 || { echo "batch_root failed: block $i" >&2; exit 1; }
      done
      echo "roots	$(since "$t0")" >> "$out/stages.tsv"
      t0=$(now)
      "$tools/aiur_exec" identity "$ax" "$out/roots/block-000/root-vk.bin" \
        "$out/roots/block-000/root-claims.bin" "$out/id" > "$out/identity.log" 2>&1 \
        || { echo "identity failed" >&2; exit 1; }
      stage=identity ;;
    tree)
      rm -rf "$out/tree" "$out/tree.out" "$out/tree.err"; mkdir -p "$out/tree"
      nvidia-smi --query-gpu=timestamp,index,memory.used,utilization.gpu \
        --format=csv,noheader,nounits --loop-ms=1000 > "$out/tree.gpu.csv" 2>/dev/null &
      smi=$!
      # shellcheck disable=SC2086
      "$tools/aiur_exec_tree" "$ax" "$out/id" "$out/roots" "$out/tree" "$blocks" --prefix block \
        --max-ram "$ram" ${TREE_FLAGS:-} > "$out/tree.out" 2> "$out/tree.err"
      status=$?
      kill "$smi" 2>/dev/null
      [ $status -eq 0 ] || { echo "aiur_exec_tree exit $status: $(tail -1 "$out/tree.err")" >&2; exit 1; } ;;
    wraps)
      rm -rf "$out/top" "$out/run-root"; mkdir -p "$out/top"
      prev=$(tail -1 "$out/tree.out")
      [ -f "$prev/proof.bin" ] || { echo "no tree top in $out/tree.out" >&2; exit 1; }
      for k in 1 2; do
        "$tools/aiur_exec" wrap "$ax" "$out/id" "$prev" "$out/top/wrap$k" > "$out/top/wrap$k.log" 2>&1 \
          || { echo "wrap $k failed: $(tail -1 "$out/top/wrap$k.log")" >&2; exit 1; }
        prev=$out/top/wrap$k
      done
      "$tools/aiur_exec" root "$prev" "$out/id" "$out/run-root" > "$out/top/root.log" 2>&1 \
        || { echo "root layout failed" >&2; exit 1; } ;;
    *) echo "unknown stage $stage" >&2; exit 2 ;;
  esac
  echo "$stage	$(since "$t0")" >> "$out/stages.tsv"
  exit 0
fi

[ $# -ge 1 ] || { echo "usage: train_run.sh OUT_DIR [roots|tree|wraps|check]..." >&2; exit 2; }
out=$(mkdir -p "$1" && cd "$1" && pwd) || exit 1
shift
[ $# -gt 0 ] || set -- roots tree wraps check
log() { echo "$(date +%T) $*" | tee -a "$out/train_run.log"; }
log "start: stages $*; MAX_RAM $ram, MEM_CAP $mem_cap, AIUR_GPU_TRACE $AIUR_GPU_TRACE, TREE_FLAGS ${TREE_FLAGS:-none}, tools $tools"
for stage in "$@"; do
  case "$stage" in
    roots|tree|wraps)
      "$ix/heavy.sh" systemd-run --user --scope -q -p MemoryMax="${mem_cap}G" -p MemorySwapMax=0 -- \
        /usr/bin/time -v -o "$out/$stage.time" timeout "$cap" "$self" --stage "$stage" "$out" \
        > "$out/$stage.log" 2>&1 \
        || { log "$stage FAILED: $(tail -2 "$out/$stage.log" | tr '\n' ' ')"; exit 1; }
      log "$stage done: $(grep -E "^$stage	" "$out/stages.tsv" | tail -1 | cut -f2) s" ;;
    check)
      t0=$(now)
      "$tools/aiur_exec_check" "$ax" "$inputs/packages/block-000.ixa" "$out/run-root" \
        "$spec/args.txt" "$spec/output.txt" "$blocks" "$steps" > "$out/check.log" 2>&1
      status=$?
      echo "check	$(since "$t0")" >> "$out/stages.tsv"
      [ $status -eq 0 ] && grep -q '^ACCEPT' "$out/check.log" \
        || { log "check FAILED (exit $status): $(tail -2 "$out/check.log" | tr '\n' ' ')"; exit 1; }
      log "check: $(grep '^ACCEPT' "$out/check.log")" ;;
    *) echo "unknown stage $stage" >&2; exit 2 ;;
  esac
done
log "done"
