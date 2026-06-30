#!/usr/bin/env bash
# Compile one library env to a `.ixe` from a checked-out repo, then benchmark the
# given backend over a manifest, emitting the neutral results JSON
#   { "<name>": { "<metric>": <number>, ... }, ... }
# that bench.py compare consumes.
#
#   run.sh <repo_dir> <env> <backend> <mode> <names_file> <out_json>
#     repo_dir : checked-out worktree (has .lake/build/bin/{ix,bench-typecheck})
#     env      : initStd | lean | mathlib
#     backend  : aiur | zisk | sp1
#     mode     : execute | prove
#
# `ix` / `bench-typecheck` are taken from <repo_dir> (so base measures base's
# code, PR the PR's — the caller puts <repo_dir>/.lake/build/bin on PATH). The
# zkVM hosts run from <repo_dir>/<backend>. Per-constant subprocesses for the
# zkVM hosts so one OOM/timeout drops only that row.
set -uo pipefail

repo=${1:?repo_dir}; benv=${2:?env}; backend=${3:?backend}; mode=${4:?mode}
names=${5:?names}; out=${6:?out}
# Absolute repo path: the zkVM branch cd's into the host workspace, so the .ixe
# path passed to the host must not be relative to the original cwd.
repo=$(cd "$repo" && pwd)
: > "$out"
emit_empty() { [ -s "$out" ] || echo '{}' > "$out"; }

case "$benv" in
  initStd) module=CompileInitStd ;;
  lean)    module=CompileLean ;;
  mathlib) module=CompileMathlib ;;
  *) echo "unknown env: $benv" >&2; exit 2 ;;
esac

ixe="$repo/$benv.ixe"
echo "::group::ix compile $module → $benv.ixe ($backend/$mode)"
"$repo/.lake/build/bin/ix" compile "$repo/Benchmarks/Compile/$module.lean" --out "$ixe"
echo "::endgroup::"

case "$backend" in
  aiur)
    # bench-typecheck runs Phase 1 (execute) always; Phase 2 (prove) unless
    # --execute-only. It writes the neutral JSON itself via --json.
    args=(--ixe "$ixe" --manifest "$names" --json "$out")
    if [ "$mode" = execute ]; then
      bench-typecheck "${args[@]}" --execute-only || true
    else
      bench-typecheck "${args[@]}" --texray 2> tx.log || true
      # Fold texray's proving RSS high-water mark into every entry (max over
      # spans; $2+0 stops at the first non-digit) — same parse as aiur-bench.yml.
      rss=$(awk -F'peak-rss-bytes=' 'NF>1 && $2+0>m {m=$2+0} END {if (m>0) print m}' tx.log)
      if [ -n "${rss:-}" ] && [ -s "$out" ]; then
        jq --argjson rss "$rss" 'map_values(. + {"peak-rss": $rss})' "$out" > "$out.t" \
          && mv "$out.t" "$out" || true
      fi
    fi
    emit_empty
    ;;

  zisk|sp1)
    host="${backend}-host"; work="$repo/$backend"
    tmp=$(mktemp -d)
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      log="$tmp/$(printf '%s' "$c" | tr '/ .:' '____').log"
      if [ "$mode" = execute ]; then
        ( cd "$work" && timeout 25m cargo run --quiet --release --bin "$host" -- \
            --execute --ixe "$ixe" --constant "$c" --skip-deps ) > "$log" 2>&1 \
          || { echo "::warning::$backend execute '$c' failed/timed out; dropping"; continue; }
        cyc=$(grep -oE 'cycles: [0-9]+'   "$log" | head -1 | grep -oE '[0-9]+')
        fail=$(grep -oE 'failures: [0-9]+' "$log" | head -1 | grep -oE '[0-9]+')
        if [ -n "${cyc:-}" ] && [ "${fail:-1}" = 0 ]; then
          jq -n --arg n "$c" --argjson v "$cyc" '{($n): {cycles: $v}}'
        else
          echo "::warning::$backend '$c': no clean 'cycles:'/'failures: 0'; dropping"
        fi
      else
        # prove (single-leaf, GPU runner only — the workflow gates this cell).
        ( cd "$work" && timeout 60m cargo run --quiet --release --bin "$host" -- \
            --gpu --ixe "$ixe" --constant "$c" --skip-deps ) > "$log" 2>&1 \
          || { echo "::warning::$backend prove '$c' failed/timed out; dropping"; continue; }
        secs=$(grep -oE 'prove [0-9.]+s'   "$log" | head -1 | grep -oE '[0-9.]+')
        steps=$(grep -oE '\([0-9]+ steps\)' "$log" | head -1 | grep -oE '[0-9]+')
        fail=$(grep -oE 'failures=[0-9]+'  "$log" | head -1 | grep -oE '[0-9]+')
        if [ -n "${secs:-}" ] && [ "${fail:-1}" = 0 ]; then
          jq -n --arg n "$c" --argjson t "$secs" --argjson s "${steps:-0}" \
            '{($n): {"prove-time": $t, steps: $s}}'
        else
          echo "::warning::$backend prove '$c': no clean prove line; dropping"
        fi
      fi
    done < "$names" | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  *) echo "unknown backend: $backend" >&2; exit 2 ;;
esac
echo "rows in $out: $(jq 'length' "$out" 2>/dev/null || echo '?')"
