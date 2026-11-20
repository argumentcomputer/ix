#!/usr/bin/env bash
# End-to-end determinism test, per numeric format: the untrusted Python trainer must reproduce
# the Lean specification bit for bit, with reductions in either order, and the checker must
# reject a trajectory that differs in one bit of one weight.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build ixai >/dev/null
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
ixai=.lake/build/bin/ixai

for fmt in fx bf16 f32; do
  $ixai --format "$fmt" data "$out/data.txt" >/dev/null
  $ixai --format "$fmt" train "$out/lean.txt" >/dev/null
  python3 -I shell/train.py "$out/data.txt" "$out/py.txt" >/dev/null
  python3 -I shell/train.py "$out/data.txt" "$out/rev.txt" --reverse-reductions >/dev/null
  python3 -I shell/train.py "$out/data.txt" "$out/bad.txt" --tamper 317 >/dev/null
  job=default; [ "$fmt" = fx ] || job="default-$fmt"
  cmp -s "$out/py.txt" "$out/lean.txt" || { echo "FAIL ($fmt): Python differs from the specification"; exit 1; }
  cmp -s "$out/rev.txt" "$out/lean.txt" || { echo "FAIL ($fmt): reduction order changed the result"; exit 1; }
  $ixai check "$out/py.txt" --job "$job" >/dev/null || { echo "FAIL ($fmt): checker rejected the honest run"; exit 1; }
  if $ixai check "$out/bad.txt" --job "$job" >/dev/null; then echo "FAIL ($fmt): checker accepted a tampered run"; exit 1; fi
  echo "PASS ($fmt): bit-identical in both reduction orders; honest run accepted; tampered run rejected"
done
