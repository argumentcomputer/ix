#!/usr/bin/env bash
# variants.sh VARIANT... : for each hint variant (a gen_variant.py spec, or `file:EDITS.tsv`), patch
# a copy of the Mathlib environment's hint section and run the instrumented IxVM execution of the
# sample claims, all variants in parallel. Writes runs/VARIANT.{log,jsonl,time,done} on the NVMe.
# Run it inside one memory-capped scope, outside the command sandbox (the build opens the CUDA
# device):  ix/heavy.sh systemd-run --user --scope -q -p MemoryMax=180G -- ix/hints/variants.sh ...
set -u
H=/home/sam/repos/ix-ai-pipeline/ix/hints
N=/opt/dlami/nvme/ix-ai/kernel-hints
S=/home/sam/repos/ix-ai-pipeline/.truthmines/store/mathlib-d13f23b
export IX_BIN=/home/sam/repos/forks/ix-kernel-hints/.lake/build/bin/ix
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
export RUST_BACKTRACE=1
mkdir -p $N/runs $N/envs
[ -f $N/env-hints.tsv ] || python3 -I $H/ixe_hints.py dump $S/env.ixe $N/env-hints.tsv
mapfile -t names < <(cut -f2 $H/sample.tsv)
for v in "$@"; do
  tag=$(echo "$v" | tr ':/' '__')
  (
    rm -f $N/runs/$tag.done $N/runs/$tag.jsonl
    case "$v" in
      file:*) cp "${v#file:}" $N/runs/$tag.edits ;;
      *) python3 -I $H/gen_variant.py $N/env-hints.tsv "$v" $N/runs/$tag.edits > $N/runs/$tag.gen ;;
    esac
    python3 -I $H/ixe_hints.py patch $S/env.ixe $N/runs/$tag.edits $N/envs/$tag.ixe
    IX_KERNEL_HINTS_TRACE=$N/runs/$tag.jsonl /usr/bin/time -v -o $N/runs/$tag.time \
      timeout ${VARIANT_CAP:-3600} /home/sam/repos/ix-ai-pipeline/ix/ixw check --ixe $N/envs/$tag.ixe \
      --keep-going "${names[@]}" > $N/runs/$tag.log 2>&1
    echo $? > $N/runs/$tag.done
    rm -f $N/envs/$tag.ixe
  ) &
done
wait
