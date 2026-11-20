#!/usr/bin/env bash
# run.sh TAG ENV.ixe NAME... : instrumented IxVM execution (no proof) of the named claims with the
# kernel-hints build of ix. Writes runs/TAG.{log,jsonl,time} on the NVMe and runs/TAG.done (exit
# status) when finished. Must run outside the command sandbox: the build opens the CUDA device.
set -u
N=/opt/dlami/nvme/ix-ai/kernel-hints/runs
tag=$1; ixe=$2; shift 2
mkdir -p "$N"; rm -f "$N/$tag.done" "$N/$tag.jsonl"
export IX_BIN=/home/sam/repos/forks/ix-kernel-hints/.lake/build/bin/ix
# The nix-built CUDA library resolves dlopen through nix's loader, which does not search the
# system driver directory.
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export RUST_BACKTRACE=1
export IX_KERNEL_HINTS_TRACE="$N/$tag.jsonl"
/usr/bin/time -v -o "$N/$tag.time" systemd-run --user --scope -q -p MemoryMax=180G -- \
  timeout 7200 /home/sam/repos/ix-ai-pipeline/ix/ixw check --ixe "$ixe" --keep-going "$@" \
  > "$N/$tag.log" 2>&1
echo $? > "$N/$tag.done"
