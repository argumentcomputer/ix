#!/usr/bin/env bash
# Compile one library env to a `.ixe` from a checked-out repo (unless REUSE_IXE),
# then benchmark the given backend, emitting the neutral results JSON
#   { "<name>": { "<metric>": <number>, ... }, ... }
# that bench.py compare / the bencher jobs consume.
#
#   run.sh <repo_dir> <env> <backend> <mode> <names_file> <out_json>
#     repo_dir : checked-out worktree (has .lake/build/bin/{ix,bench-typecheck})
#     env      : initStd | lean | mathlib  (any case; used verbatim for <env>.ixe)
#     backend  : aiur | zisk | sp1 | native
#     mode     : execute | prove
#
# `ix` / `bench-typecheck` come from <repo_dir> (so base measures base's code, PR
# the PR's — the caller puts <repo_dir>/.lake/build/bin on PATH). Each constant
# is its own subprocess (a failure/timeout drops only that row). Only JSON is
# written to stdout — tool output and `::warning::`/`::notice::` go to logs /
# stderr so they never corrupt the merged JSON stream.
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
  echo "reusing existing $ixe (REUSE_IXE)" >&2
else
  echo "::group::ix compile $module → $benv.ixe ($backend/$mode)"
  "$repo/.lake/build/bin/ix" compile "$repo/Benchmarks/Compile/$module.lean" --out "$ixe"
  echo "::endgroup::"
fi

tmp=$(mktemp -d)

case "$backend" in
  aiur)
    # One bench-typecheck per constant (isolation + per-constant peak-rss).
    # Execute mode → Phase 1 only (--execute-only). Prove mode → prove each
    # constant whose Aiur fft-cost fits the prover RAM ceiling (~128 GB at
    # 2.34 GB per billion fft), else fall back to execute-only so a too-large
    # single-shard prove never OOM-kills the job.
    csv="$repo/Benchmarks/Vectors.csv"
    ceil=${AIUR_PROVE_MAX_FFT:-50000000000}
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      res="$tmp/$slug.json"
      do_prove=0
      if [ "$mode" = prove ]; then
        fft=$(awk -F, -v n="$c" '$1==n {print $6}' "$csv" 2>/dev/null)
        if [ -n "${fft:-}" ] && [ "$fft" -le "$ceil" ]; then
          do_prove=1
        else
          echo "::notice::aiur: '$c' fft=${fft:-?} exceeds $ceil (~128 GB); execute-only" >&2
        fi
      fi
      if [ "$do_prove" = 1 ]; then
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --texray \
          > "$tmp/$slug.log" 2> "$tmp/$slug.tx" \
          || { echo "::warning::aiur prove '$c' failed (OOM/timeout); dropping" >&2; continue; }
        # Fold texray's proving RSS high-water mark (max over spans; awk's $2+0
        # stops at the first non-digit) into this constant's entry.
        rss=$(awk -F'peak-rss-bytes=' 'NF>1 && $2+0>m {m=$2+0} END {if (m>0) print m}' "$tmp/$slug.tx")
        if [ -n "${rss:-}" ] && [ -s "$res" ]; then
          jq --argjson rss "$rss" 'map_values(. + {"peak-rss": $rss})' "$res" > "$res.t" \
            && mv "$res.t" "$res" || true
        fi
      else
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --execute-only > "$tmp/$slug.log" 2>&1 \
          || { echo "::warning::aiur execute '$c' failed; dropping" >&2; continue; }
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
          || { echo "::warning::$backend execute '$c' failed/timed out; dropping" >&2; continue; }
        fail=$(grep -oE 'failures[:=] ?[0-9]+' "$log" | head -1 | grep -oE '[0-9]+')
        if [ "${fail:-1}" != 0 ]; then
          echo "::warning::$backend '$c': nonzero/missing failures; dropping" >&2; continue
        fi
        # Total cycles: sharded prints "total cycles: N", single prints "cycles: N".
        cyc=$(grep -oE 'total cycles: [0-9]+' "$log" | tail -1 | grep -oE '[0-9]+')
        [ -z "$cyc" ] && cyc=$(grep -oE 'cycles: [0-9]+' "$log" | tail -1 | grep -oE '[0-9]+')
        [ -z "$cyc" ] && { echo "::warning::$backend '$c': no cycle count; dropping" >&2; continue; }
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
          || { echo "::warning::$backend prove '$c' failed/timed out; dropping" >&2; continue; }
        secs=$(grep -oE 'prove [0-9.]+s'   "$log" | head -1 | grep -oE '[0-9.]+')
        steps=$(grep -oE '\([0-9]+ steps\)' "$log" | head -1 | grep -oE '[0-9]+')
        fail=$(grep -oE 'failures=[0-9]+'  "$log" | head -1 | grep -oE '[0-9]+')
        if [ -n "${secs:-}" ] && [ "${fail:-1}" = 0 ]; then
          jq -n --arg n "$c" --argjson t "$secs" --argjson s "${steps:-0}" \
            '{($n): {"prove-time": $t, steps: $s}}'
        else
          echo "::warning::$backend prove '$c': no clean prove line; dropping" >&2
        fi
      fi
    done < "$names" | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  native)
    # Native out-of-circuit Rust kernel (far faster than proving). Two views,
    # both via the `##check## <elapsed_ms> <passed> <failures> <total>` line
    # (ix check is a single multi-threaded process so /usr/bin/time -f '%M' is the
    # true peak RSS): the whole env in parallel (`--anon`, keyed by env), and a
    # per-primary subject check (`--consts`, keyed by constant) for an
    # apples-to-apples baseline next to the zkVM `--skip-deps` execute.
    native_one() {  # <label> <ix-check-args…>  → prints one JSON object
      local label="$1"; shift
      local log="$tmp/n.out" tmf="$tmp/n.time"
      /usr/bin/time -f '%e %M' -o "$tmf" ix check "$ixe" "$@" > "$log" 2>>"$log" \
        || { echo "::warning::native '$label' check failed; dropping" >&2; return; }
      local line ems fl tot
      line=$(grep '^##check##' "$log" | tail -1)
      ems=$(echo "$line" | awk '{print $2}'); fl=$(echo "$line" | awk '{print $4}'); tot=$(echo "$line" | awk '{print $5}')
      { [ -n "${tot:-}" ] && [ "${fl:-1}" = 0 ]; } \
        || { echo "::warning::native '$label': bad ##check## / failures; dropping" >&2; return; }
      local rssk rss cs tp
      rssk=$(awk 'NR==1{print $2}' "$tmf"); rss=$(( ${rssk:-0} * 1024 ))
      cs=$(awk -v e="$ems" 'BEGIN{printf "%.3f", e/1000}')
      tp=$(awk -v t="$tot" -v e="$ems" 'BEGIN{ if (e>0) printf "%.2f", t*1000/e; else print 0 }')
      jq -n --arg n "$label" --argjson c "$tot" --argjson s "$cs" --argjson tp "$tp" --argjson rss "$rss" \
        '{($n): {constants:$c, "check-time":$s, throughput:$tp, "peak-rss":$rss}}'
    }
    {
      native_one "$benv" --anon
      while IFS= read -r c; do
        [ -z "$c" ] && continue
        native_one "$c" --consts "$c"
      done < "$names"
    } | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  *) echo "unknown backend: $backend" >&2; exit 2 ;;
esac
echo "rows in $out: $(jq 'length' "$out" 2>/dev/null || echo '?')" >&2
