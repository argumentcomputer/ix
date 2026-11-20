#!/usr/bin/env bash
# exp.sh VARIANT... : for each hint variant, patch a copy of the Mathlib env's §3 hints and run
# the instrumented IxVM execution of the sample claims, writing runs/VARIANT.{log,jsonl}.
# A variant is `default`, a gen_variant.py spec, or `file:EDITS.tsv`.
set -u
H=/tmp/claude-30033/-home-sam-repos-ix-ci-merge-tests/1ff7afee-07d4-4f1e-9d25-ce35af5f21a0/scratchpad/hints
N=/opt/dlami/nvme/ix-ai/kernel-hints
S=/home/sam/repos/ix-ai-pipeline/.truthmines/store/mathlib-d13f23b
export IX_BIN=/home/sam/repos/forks/ix-kernel-hints/.lake/build/bin/ix
mkdir -p $N/runs; rm -f $N/runs/exp.done
mapfile -t names < <(cut -f2 $H/sample.tsv)
for v in "$@"; do
  tag=$(echo "$v" | tr ':/' '__')
  if [ "$v" = default ]; then
    ixe=$S/env.ixe
  else
    case "$v" in
      file:*) cp "${v#file:}" $N/runs/$tag.edits ;;
      *) python3 -I $H/gen_variant.py $H/env-hints.tsv "$v" $N/runs/$tag.edits ;;
    esac
    python3 -I $H/ixe_hints.py patch $S/env.ixe $N/runs/$tag.edits $N/variant.ixe
    ixe=$N/variant.ixe
  fi
  rm -f $N/runs/$tag.jsonl
  IX_KERNEL_HINTS_TRACE=$N/runs/$tag.jsonl $H/check.sh $ixe $N/runs/$tag.log "${names[@]}"
done
echo "$*" > $N/runs/exp.done
