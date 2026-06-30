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
if [ "${REUSE_IXE:-0}" = 1 ] && [ -f "$ixe" ]; then
  echo "reusing existing $ixe (REUSE_IXE)"
else
  echo "::group::ix compile $module → $benv.ixe ($backend/$mode)"
  "$repo/.lake/build/bin/ix" compile "$repo/Benchmarks/Compile/$module.lean" --out "$ixe"
  echo "::endgroup::"
fi

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
    # Build the host once so per-constant timing excludes compilation, and run the
    # binary directly under `/usr/bin/time` — a `timeout`/`cargo run` wrapper would
    # report the wrapper's RSS, not the host's. (No per-constant timeout in execute
    # mode; the job-level timeout bounds a hang.)
    echo "::group::cargo build $host"
    ( cd "$work" && cargo build --quiet --release --bin "$host" )
    echo "::endgroup::"
    bin="$work/target/release/$host"
    # ZisK's ASM microservices mmap the ROM with MAP_LOCKED, needing unlimited
    # locked memory (the Zisk book's DefaultLimitMEMLOCK=infinity). The warp
    # runner caps the memlock hard limit and can't be rebooted, so raise it
    # in-session as root; the host children inherit it. Without this the ASM
    # services die with `mmap(rom) errno=11`. SP1 needs no such raise.
    [ "$backend" = zisk ] && sudo prlimit --pid $$ --memlock=unlimited:unlimited
    tmp=$(mktemp -d)
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      log="$tmp/$slug.out"; tmf="$tmp/$slug.time"
      if [ "$mode" = execute ]; then
        # `/usr/bin/time -f '%e %M'` → elapsed seconds + max RSS (kB).
        ( cd "$work" && /usr/bin/time -f '%e %M' -o "$tmf" \
            "$bin" --execute --ixe "$ixe" --constant "$c" --skip-deps ) > "$log" 2>>"$log" \
          || { echo "::warning::$backend execute '$c' failed; dropping"; continue; }
        fail=$(grep -oE 'failures[:=] ?[0-9]+' "$log" | head -1 | grep -oE '[0-9]+')
        if [ "${fail:-1}" != 0 ]; then
          echo "::warning::$backend '$c': nonzero/missing failures; dropping"; continue
        fi
        # Total cycles: sharded prints "total cycles: N", single prints "cycles: N".
        cyc=$(grep -oE 'total cycles: [0-9]+' "$log" | tail -1 | grep -oE '[0-9]+')
        [ -z "$cyc" ] && cyc=$(grep -oE 'cycles: [0-9]+' "$log" | tail -1 | grep -oE '[0-9]+')
        [ -z "$cyc" ] && { echo "::warning::$backend '$c': no cycle count; dropping"; continue; }
        secs=$(awk 'NR==1{print $1}' "$tmf"); rssk=$(awk 'NR==1{print $2}' "$tmf")
        rss=$(( ${rssk:-0} * 1024 ))
        tput=$(awk -v c="$cyc" -v s="${secs:-0}" 'BEGIN{ if (s>0) printf "%.0f", c/s; else print 0 }')
        # Per-shard "cycles=<n>" lines appear only for sharded runs.
        mapfile -t sh < <(grep -oE 'cycles=[0-9]+' "$log" | grep -oE '[0-9]+')
        base="cycles:\$cyc, \"execute-time\":\$secs, throughput:\$tput, \"peak-rss\":\$rss"
        if [ "${#sh[@]}" -gt 0 ]; then
          maxsh=$(printf '%s\n' "${sh[@]}" | sort -n | tail -1)
          jq -n --arg n "$c" --argjson cyc "$cyc" --argjson secs "${secs:-0}" \
                --argjson tput "$tput" --argjson rss "$rss" \
                --argjson nsh "${#sh[@]}" --argjson maxsh "$maxsh" \
            "{(\$n): {$base, shards:\$nsh, \"max-shard-cycles\":\$maxsh}}"
        else
          jq -n --arg n "$c" --argjson cyc "$cyc" --argjson secs "${secs:-0}" \
                --argjson tput "$tput" --argjson rss "$rss" \
            "{(\$n): {$base}}"
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
