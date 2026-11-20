#!/usr/bin/env bash
# Certify claims about constants of an Ixon env and record them in the local Truth Mines index.
#
#   certify.sh ENV.ixe eval  INPUT_NAME OUTPUT_NAME   # Eval: INPUT normalizes to OUTPUT
#   certify.sh ENV.ixe check THEOREM_NAME             # Check: the constant is well-typed
#
# Each run builds the claim in the local store, proves it on the GPU, verifies the proof and
# appends one line to .truthmines/index.tsv:
#   kind  name  subject-address  output-address  claim  proof  prove-seconds  proof-bytes  status
# Each prove, check or compression run is capped at STEP_CAP seconds (default 1800) after the
# gate grants the machine; waiting for the gate does not count.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ixw="$here/ixw"
heavy="$here/heavy.sh"
index="$(dirname "$here")/.truthmines/index.tsv"
env="$1"; kind="$2"; shift 2
addr() { "$ixw" addr-of --ixe "$env" "$1" 2>/dev/null | tail -1; }
binding() {
  "$heavy" timeout "${STEP_CAP:-1800}" "$ixw" prove-binding "$env" --gpu-device 0 2>&1 | grep -o 'binding claim for [0-9a-f]*' | head -1 | awk '{print $4}'
}
case "$kind" in
  eval)
    name="$1"; in_addr=$(addr "$1"); out_addr=$(addr "$2")
    claim=$("$ixw" claim eval --binding "$(binding)" "$in_addr" "$out_addr" | tail -1)
    start=$(date +%s.%N)
    out=$("$heavy" timeout "${STEP_CAP:-1800}" "$ixw" prove --ixe "$env" --claim "$claim" --gpu-device 0 2>&1 || true)
    proof=$(printf '%s\n' "$out" | tail -1)
    reason=$(printf '%s\n' "$out" | grep -oE 'illegal operation \(.*' | head -1 || true)
    ;;
  check)
    name="$1"; in_addr=$(addr "$1"); out_addr="-"; claim="(by name)"
    start=$(date +%s.%N)
    out=$("$heavy" timeout "${STEP_CAP:-1800}" "$ixw" prove --ixe "$env" "$1" --gpu-device 0 2>&1 || true)
    proof=$(printf '%s\n' "$out" | tail -1)
    reason=$(printf '%s\n' "$out" | grep -oE 'illegal operation \(.*|not found in .*' | head -1 || true)
    ;;
  *) echo "unknown kind $kind" >&2; exit 2 ;;
esac
secs=$(echo "$(date +%s.%N) - $start" | bc)
if [[ ! "$proof" =~ ^[0-9a-f]{64}$ ]]; then
  printf '%s\t%s\t%s\t%s\t%s\t-\t%.1f\t-\tFAILED: %s\n' "$kind" "$name" "$in_addr" "$out_addr" "$claim" "$secs" "${reason:-$proof}" | tee -a "$index"
  exit 1
fi
verdict=$("$heavy" timeout "${STEP_CAP:-1800}" "$ixw" verify "$proof" 2>&1 | grep -E '^ok:|fail|error' | head -1)
store="$(dirname "$here")/.truthmines/.ix/store"
bytes=$(stat -c %s "$store/${proof:0:2}/${proof:2:2}/${proof:4:2}/${proof:6}" 2>/dev/null || echo -)
status=$([[ "$verdict" == ok:* ]] && echo verified || echo "UNVERIFIED: $verdict")
printf '%s\t%s\t%s\t%s\t%s\t%s\t%.1f\t%s\t%s\n' "$kind" "$name" "$in_addr" "$out_addr" "$claim" "$proof" "$secs" "$bytes" "$status" | tee -a "$index"
