#!/usr/bin/env bash
# Compile one library env to a `.ixe` from a checked-out repo (unless REUSE_IXE),
# then benchmark the given backend, emitting the neutral results JSON
#   { "<name>": { "<metric>": <number>, ... }, ... }
# that bench.py compare / the bencher jobs consume.
#
#   run.sh <repo_dir> <env> <backend> <mode> <names_file> <out_json>
#     repo_dir : checked-out worktree (has .lake/build/bin/{ix,bench-typecheck})
#     env      : initStd | lean | mathlib
#     backend  : aiur | zisk | sp1 | native
#     mode     : execute | prove
#
# `ix` / `bench-typecheck` come from <repo_dir> (so base measures base's code, PR
# the PR's — the caller puts <repo_dir>/.lake/build/bin on PATH). aiur / zisk /
# sp1 run one subprocess per constant so a failure/timeout drops only that row;
# native is whole-env (`ix check --anon`, the parallel out-of-circuit kernel) and
# ignores <names_file>, keyed by the env.
set -uo pipefail

repo=${1:?repo_dir}; benv=${2:?env}; backend=${3:?backend}; mode=${4:?mode}
names=${5:?names}; out=${6:?out}
# Absolute repo path: the zkVM branch cd's into the host workspace, so the .ixe
# path passed to the host must not be relative to the original cwd.
repo=$(cd "$repo" && pwd)
: > "$out"
emit_empty() { [ -s "$out" ] || echo '{}' > "$out"; }

# `$benv` is used verbatim for the `.ixe` filename (bench-pr compiles `initStd.ixe`;
# the bencher jobs reuse the compile job's cached `InitStd.ixe`), and lowercased
# only to pick the Compile module.
case "$(printf '%s' "$benv" | tr '[:upper:]' '[:lower:]')" in
  initstd) module=CompileInitStd ;;
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

tmp=$(mktemp -d)

case "$backend" in
  aiur)
    # One bench-typecheck subprocess per constant (isolation + per-constant
    # peak-rss). Phase 1 (execute) always runs; Phase 2 (prove) unless
    # --execute-only. bench-typecheck writes the neutral per-constant JSON.
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      res="$tmp/$slug.json"
      if [ "$mode" = execute ]; then
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --execute-only \
          || { echo "::warning::aiur execute '$c' failed; dropping"; continue; }
      else
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --texray 2> "$tmp/$slug.tx" \
          || { echo "::warning::aiur prove '$c' failed (OOM/timeout); dropping"; continue; }
        # Fold texray's proving RSS high-water mark (max over spans; awk's $2+0
        # stops at the first non-digit) into this constant's entry.
        rss=$(awk -F'peak-rss-bytes=' 'NF>1 && $2+0>m {m=$2+0} END {if (m>0) print m}' "$tmp/$slug.tx")
        if [ -n "${rss:-}" ] && [ -s "$res" ]; then
          jq --argjson rss "$rss" 'map_values(. + {"peak-rss": $rss})' "$res" > "$res.t" \
            && mv "$res.t" "$res" || true
        fi
      fi
      [ -s "$res" ] && cat "$res"
    done < "$names" | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  zisk|sp1)
    host="${backend}-host"; work="$repo/$backend"
    # Build the host once so per-constant timing excludes compilation. Order is
    # `timeout … /usr/bin/time … host`: timeout bounds a runaway constant while
    # /usr/bin/time still measures the host directly (its child), so RSS/elapsed
    # are the host's, not a wrapper's.
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
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      log="$tmp/$slug.out"; tmf="$tmp/$slug.time"
      if [ "$mode" = execute ]; then
        ( cd "$work" && timeout 25m /usr/bin/time -f '%e %M' -o "$tmf" \
            "$bin" --execute --ixe "$ixe" --constant "$c" --skip-deps ) > "$log" 2>>"$log" \
          || { echo "::warning::$backend execute '$c' failed/timed out; dropping"; continue; }
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

  native)
    # Native out-of-circuit Rust kernel, whole env across available_parallelism
    # workers — far faster than proving; ignores <names_file>. ix check is a
    # single multi-threaded process so /usr/bin/time -f '%M' is the true peak RSS.
    # `##check## <elapsed_ms> <passed> <failures> <total>` is the machine line.
    log="$tmp/native.out"; tmf="$tmp/native.time"
    /usr/bin/time -f '%e %M' -o "$tmf" ix check "$ixe" --anon > "$log" 2>>"$log" \
      || { echo "::warning::native check failed"; emit_empty; exit 0; }
    line=$(grep '^##check##' "$log" | tail -1)
    elapsed_ms=$(echo "$line" | awk '{print $2}')
    failures=$(echo "$line" | awk '{print $4}'); total=$(echo "$line" | awk '{print $5}')
    if [ -z "${total:-}" ] || [ "${failures:-1}" != 0 ]; then
      echo "::warning::native check: nonzero/missing failures or no ##check## line"; emit_empty; exit 0
    fi
    rssk=$(awk 'NR==1{print $2}' "$tmf"); rss=$(( ${rssk:-0} * 1024 ))
    check_s=$(awk -v e="$elapsed_ms" 'BEGIN{printf "%.3f", e/1000}')
    tput=$(awk -v t="$total" -v e="$elapsed_ms" 'BEGIN{ if (e>0) printf "%.2f", t*1000/e; else print 0 }')
    jq -n --arg n "$benv" --argjson c "$total" --argjson s "$check_s" \
          --argjson tp "$tput" --argjson rss "$rss" \
      '{($n): {constants:$c, "check-time":$s, throughput:$tp, "peak-rss":$rss}}' > "$out"
    emit_empty
    ;;

  *) echo "unknown backend: $backend" >&2; exit 2 ;;
esac
echo "rows in $out: $(jq 'length' "$out" 2>/dev/null || echo '?')"
