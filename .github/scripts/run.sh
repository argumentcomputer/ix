#!/usr/bin/env bash
# Compile one library env to a `.ixe` from a checked-out repo (unless REUSE_IXE),
# then benchmark the given backend, emitting the neutral results JSON
#   { "<name>": { "<metric>": <number>, ... }, ... }
# that bench.py compare / the bencher jobs consume.
#
#   run.sh <repo_dir> <env> <backend> <mode> <names_file> <out_json>
#     repo_dir : checked-out worktree (has .lake/build/bin/{ix,bench-typecheck})
#     env      : initStd | lean | mathlib  (any case; used verbatim for <env>.ixe)
#     backend  : aiur | zisk | sp1 | ooc
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

# Fold a tool's per-phase span timings (tracing-texray JSONL, one
# `{"span":"…","seconds":N}` per closed span, possibly repeated per shard) into
# its per-constant results file under a `phases` object, summed by span name —
# the source bench.py renders as the comparative drill-down. No-op if the tool
# emitted no spans.
merge_phases() {  # <results.json> <spans.jsonl>
  local res="$1" spans="$2" ph
  [ -s "$spans" ] || return 0
  ph=$(jq -s 'reduce .[] as $o ({}; .[$o.span] += $o.seconds)' "$spans" 2>/dev/null)
  [ -n "$ph" ] && [ "$ph" != "{}" ] || return 0
  jq --argjson ph "$ph" 'map_values(. + {phases: $ph})' "$res" > "$res.p" \
    && mv "$res.p" "$res" || true
}

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
      res="$tmp/$slug.json"; spans="$tmp/$slug.spans"
      do_prove=0
      if [ "$mode" = prove ]; then
        fft=$(awk -F, -v n="$c" '$1==n {print $6}' "$csv" 2>/dev/null)
        if [ -n "${fft:-}" ] && [ "$fft" -le "$ceil" ]; then
          do_prove=1
        else
          echo "::notice::aiur: '$c' fft=${fft:-?} exceeds $ceil (~128 GB); execute-only" >&2
        fi
      fi
      # bench-typecheck self-reports peak-rss (texray tree sampler) in its --json;
      # --texray-json captures the per-phase aiur/*, stark/* timings.
      if [ "$do_prove" = 1 ]; then
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --texray-json "$spans" \
          > "$tmp/$slug.log" 2>&1 \
          || { echo "::warning::aiur prove '$c' failed (OOM/timeout); dropping" >&2; continue; }
      else
        bench-typecheck --ixe "$ixe" "$c" --json "$res" --execute-only \
          --texray-json "$spans" > "$tmp/$slug.log" 2>&1 \
          || { echo "::warning::aiur execute '$c' failed; dropping" >&2; continue; }
      fi
      merge_phases "$res" "$spans"
      [ -s "$res" ] && cat "$res"
    done < "$names" | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  zisk|sp1)
    host="${backend}-host"; work="$repo/$backend"
    # Build the host once so per-constant timing excludes compilation. The host
    # self-measures and writes its own neutral results JSON via `--json`
    # (cycles/execute-time/throughput/peak-rss for execute; prove-time/… for
    # prove), so there is nothing to grep — `timeout` only bounds a runaway
    # constant.
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
    # zisk proves with `--gpu`; sp1 selects the GPU prover via its env/features.
    gpu=; [ "$backend" = zisk ] && gpu=--gpu
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      res="$tmp/$slug.json"; log="$tmp/$slug.log"; spans="$tmp/$slug.spans"
      if [ "$mode" = execute ]; then
        ( cd "$work" && timeout 25m "$bin" --execute --ixe "$ixe" \
            --constant "$c" --skip-deps --json "$res" --texray-json "$spans" ) \
          > "$log" 2>&1 \
          || { echo "::warning::$backend execute '$c' failed/timed out; dropping" >&2; continue; }
      else
        # prove (GPU runner only — the workflow gates this cell).
        ( cd "$work" && timeout 60m "$bin" $gpu --ixe "$ixe" \
            --constant "$c" --skip-deps --json "$res" --texray-json "$spans" ) \
          > "$log" 2>&1 \
          || { echo "::warning::$backend prove '$c' failed/timed out; dropping" >&2; continue; }
      fi
      # The host writes $res only on a clean (zero-failure) run.
      merge_phases "$res" "$spans"
      [ -s "$res" ] && cat "$res"
    done < "$names" | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  ooc)
    # Out-of-circuit Rust kernel (far faster than proving). Two views, both keyed
    # off the structured line
    #   `##check## <elapsed_ms> <passed> <failures> <total> <peak-rss-bytes>`
    # (peak-rss from ix check's tracing-texray tree sampler): the whole env in
    # parallel (`--anon`, keyed by env), and a per-primary subject check
    # (`--consts`, keyed by constant) for an apples-to-apples baseline next to
    # the zkVM `--skip-deps` execute.
    ooc_one() {  # <label> <ix-check-args…>  → prints one JSON object
      local label="$1"; shift
      local log="$tmp/n.out"
      ix check-rs "$ixe" "$@" > "$log" 2>>"$log" \
        || { echo "::warning::ooc '$label' check failed; dropping" >&2; return; }
      local line ems fl tot rss
      line=$(grep '^##check##' "$log" | tail -1)
      ems=$(echo "$line" | awk '{print $2}'); fl=$(echo "$line" | awk '{print $4}')
      tot=$(echo "$line" | awk '{print $5}'); rss=$(echo "$line" | awk '{print $6}')
      { [ -n "${tot:-}" ] && [ "${fl:-1}" = 0 ]; } \
        || { echo "::warning::ooc '$label': bad ##check## / failures; dropping" >&2; return; }
      local cs tp
      cs=$(awk -v e="$ems" 'BEGIN{printf "%.3f", e/1000}')
      tp=$(awk -v t="$tot" -v e="$ems" 'BEGIN{ if (e>0) printf "%.2f", t*1000/e; else print 0 }')
      jq -n --arg n "$label" --argjson c "$tot" --argjson s "$cs" --argjson tp "$tp" \
            --argjson rss "${rss:-0}" \
        '{($n): {constants:$c, "check-time":$s, throughput:$tp, "peak-rss":$rss}}'
    }
    {
      ooc_one "$benv" --anon
      while IFS= read -r c; do
        [ -z "$c" ] && continue
        ooc_one "$c" --consts "$c"
      done < "$names"
    } | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  *) echo "unknown backend: $backend" >&2; exit 2 ;;
esac
echo "rows in $out: $(jq 'length' "$out" 2>/dev/null || echo '?')" >&2
