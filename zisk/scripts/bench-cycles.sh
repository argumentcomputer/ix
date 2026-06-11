#!/usr/bin/env bash
# Cycle benchmark for the Zisk leaf guest across the standard input suite.
#
# Runs each dumped guest stdin in ~/benchdata/zisk-inputs through ziskemu,
# records steps (-m) and checks the committed `failures` publics word (-c,
# u32 word index 10) is zero — a non-zero value means the kernel REJECTED a
# constant and the run is invalid for benchmarking.
#
# Usage:
#   bench-cycles.sh <label> [elf]        # full suite
#   BENCH_ONLY="int16rxc vectorextract" bench-cycles.sh <label>
#
# Results append to ~/benchdata/zisk-bench.tsv: label, git-rev, input, steps.
# Inputs were dumped via `zisk-host --dump-input` (see zisk_guest_profiling
# memory / scripts/mergesort-250k.sh for provenance).

set -euo pipefail

LABEL="${1:?usage: bench-cycles.sh <label> [elf]}"
ELF="${2:-/home/ubuntu/ix/zisk/guest/target/elf/riscv64ima-zisk-zkvm-elf/release/zisk-guest}"
INPUTS_DIR="$HOME/benchdata/zisk-inputs"
OUT="$HOME/benchdata/zisk-bench.tsv"
ZISKEMU="$HOME/.zisk/bin/ziskemu"
REV="$(git -C /home/ubuntu/ix rev-parse --short HEAD 2>/dev/null || echo unknown)$(git -C /home/ubuntu/ix diff --quiet 2>/dev/null || echo +dirty)"

# Suite ordered smallest-first so failures surface fast.
SUITE="${BENCH_ONLY:-stringappend natgcdcomm rbmap nataddcomm binsearch mergesort int16rxc int32rxc int64rxc vectorextract}"

input_path() {
  case "$1" in
    mergesort) echo "$INPUTS_DIR/mergesort-whole.bin" ;;
    *) echo "$INPUTS_DIR/input-$1.bin" ;;
  esac
}

printf '%-15s %-22s %16s  %s\n' "LABEL" "INPUT" "STEPS" "REV"
for name in $SUITE; do
  bin="$(input_path "$name")"
  [ -f "$bin" ] || { echo "missing input: $bin" >&2; exit 1; }
  steps="$("$ZISKEMU" -e "$ELF" -i "$bin" -m 2>&1 | grep -oP 'steps=\K[0-9]+')"
  failures="$("$ZISKEMU" -e "$ELF" -i "$bin" -c 2>&1 | sed -n '11p')"
  if [ "$failures" != "00000000" ]; then
    echo "FAIL $name: kernel failures word = $failures (run invalid)" >&2
    exit 1
  fi
  printf '%-15s %-22s %16s  %s\n' "$LABEL" "$name" "$steps" "$REV"
  printf '%s\t%s\t%s\t%s\n' "$LABEL" "$REV" "$name" "$steps" >> "$OUT"
done
