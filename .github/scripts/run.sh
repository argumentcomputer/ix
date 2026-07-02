#!/usr/bin/env bash
# Compile one library env to a `.ixe` from a checked-out repo (unless REUSE_IXE),
# then benchmark the given backend, emitting the neutral results JSON
#   { "<name>": { "<metric>": <number>, ... }, ... }
# that bench.py compare / the bencher jobs consume.
#
#   run.sh <repo_dir> <env> <backend> <mode> <names_file> <out_json>
#     repo_dir : checked-out worktree (has .lake/build/bin/{ix,bench-typecheck})
#     env      : initStd | lean | mathlib  (any case; used verbatim for <env>.ixe)
#     backend  : aiur | zisk | sp1 | ooc | compile
#     mode     : execute | prove | compile
#
# `ix` / `bench-typecheck` come from <repo_dir> (so base measures base's code, PR
# the PR's — the caller puts <repo_dir>/.lake/build/bin on PATH). For the
# per-constant backends (aiur, zisk, sp1, ooc), each name is its own subprocess
# so a failure/timeout drops only that row. The `compile` backend is per-env
# (the env slug is the benchmark name) and measures the compile step directly.
# Only JSON is written to stdout — tool output and `::warning::`/`::notice::`
# go to logs / stderr so they never corrupt the merged JSON stream.
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

# Background RAM watchdog. Every ~3 s, sum RSS across `root_pid` and every
# descendant (via `ps -eo pid,ppid,rss` + a small BFS); when the total exceeds
# `max_gb`, touch `marker` and SIGKILL the whole process GROUP (the root is
# started with `setsid`, so `kill -- -pid` reaches every descendant, not just
# depth-1 children). Callers detect the kill by testing `-f "$marker"` after
# wait. The 3 s cadence can lose a fast spike to the kernel OOM killer first —
# callers treat exit 137 without a marker as OOM too.
watch_ram_kill() {  # <root_pid> <max_gb> <marker>
  local root_pid=$1 max_gb=$2 marker=$3
  local max_kb=$((max_gb * 1024 * 1024)) total_kb
  while kill -0 "$root_pid" 2>/dev/null; do
    total_kb=$(ps -eo pid,ppid,rss --no-headers 2>/dev/null | awk -v root="$root_pid" '
      { rss[$1]=$3; parent[$1]=$2 }
      END {
        alive[root]=1; changed=1
        while (changed) {
          changed=0
          for (p in parent) if (alive[parent[p]] && !alive[p]) { alive[p]=1; changed=1 }
        }
        s=0; for (p in alive) s += rss[p]+0
        print s
      }')
    if [ -n "$total_kb" ] && [ "$total_kb" -gt "$max_kb" ]; then
      echo "::warning::RAM watchdog: killing pid=$root_pid tree-RSS=${total_kb}kB > ${max_kb}kB (~${max_gb} GB)" >&2
      : > "$marker"
      kill -KILL -- "-$root_pid" 2>/dev/null || kill -KILL "$root_pid" 2>/dev/null || true
      return
    fi
    sleep 3
  done
}

# Merge the OOM sentinel into a constant's results file, PRESERVING any
# metrics measured before the kill (bench-typecheck persists Phase-1
# fft-cost/execute-time before the prove starts). bench.py compare renders
# `OOM` only for the metrics that are absent.
mark_oom() {  # <results.json> <name>
  local res="$1" c="$2"
  if [ -s "$res" ]; then
    jq --arg n "$c" '.[$n] = ((.[$n] // {}) + {oom: true})' "$res" > "$res.o" \
      && mv "$res.o" "$res" \
      || jq -n --arg n "$c" '{($n): {oom: true}}' > "$res"
  else
    jq -n --arg n "$c" '{($n): {oom: true}}' > "$res"
  fi
}

# `$benv` is used verbatim for the `.ixe` filename (bench-pr compiles `initStd.ixe`;
# the bencher jobs reuse the compile job's cached `InitStd.ixe`), and lowercased
# only to pick the Compile module. `$benv_cc` is the CamelCase form — the
# canonical BENCHMARK KEY for env-keyed rows (ooc whole-env, compile), so the
# PR side (`initStd`) and the bencher side (`InitStd`, from bench-main's
# matrix.bench) agree on one name.
case "$(printf '%s' "$benv" | tr '[:upper:]' '[:lower:]')" in
  initstd) module=CompileInitStd; benv_cc=InitStd ;;
  lean)    module=CompileLean;    benv_cc=Lean ;;
  mathlib) module=CompileMathlib; benv_cc=Mathlib ;;
  flt)     module=CompileFLT;     benv_cc=FLT ;;
  *) echo "unknown env: $benv" >&2; exit 2 ;;
esac

# Tool resolution: prefer the in-tree build (so base measures base's code, PR
# the PR's), fall back to PATH — CI restores cached binaries onto PATH instead
# of building in-tree.
resolve_bin() {  # <name> → prints the path, or fails
  local name="$1" in_tree="$repo/.lake/build/bin/$1"
  if [ -x "$in_tree" ]; then printf '%s' "$in_tree"
  else command -v "$name" || { echo "::error::$name not found (in-tree or PATH)" >&2; return 2; }
  fi
}
ix_bin=$(resolve_bin ix) || exit 2

tmp=$(mktemp -d)
compile_log="$tmp/compile.log"

# `compile` backend needs a fresh compile to measure — never honor REUSE_IXE.
ixe="$repo/$benv.ixe"
if [ "${REUSE_IXE:-0}" = 1 ] && [ "$backend" != compile ] && [ -f "$ixe" ]; then
  echo "reusing existing $ixe (REUSE_IXE)" >&2
else
  echo "::group::ix compile $module → $benv.ixe ($backend/$mode)"
  "$ix_bin" compile "$repo/Benchmarks/Compile/$module.lean" \
    --out "$ixe" 2>&1 | tee "$compile_log"
  echo "::endgroup::"
fi

case "$backend" in
  aiur)
    # One bench-typecheck per constant (isolation + per-constant peak-rss).
    # Execute mode → Phase 1 only (--execute-only). Prove mode → always attempt
    # a full prove (no tier gate), bounded two ways: a RAM watchdog SIGKILLs
    # the process group when tree-RSS nears the runner's ceiling (the constant
    # then records the `oom: true` sentinel — merged into any Phase-1 metrics
    # already measured — so bench.py compare renders `OOM` instead of dropping
    # the row), and a wall-clock `timeout` bounds a runaway prove. `$out` is
    # re-merged after every constant so a job-level kill mid-loop still leaves
    # the completed rows on disk.
    ceiling_gb=${AIUR_PROVE_MAX_RSS_GB:-120}
    bt_bin=$(resolve_bin bench-typecheck) || exit 2
    rows="$tmp/rows"; mkdir -p "$rows"
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      res="$tmp/$slug.json"; spans="$res.spans"; oom="$tmp/$slug.oom"
      rm -f "$oom"
      # bench-typecheck self-reports peak-rss (texray tree sampler) in its --json;
      # with --texray + --json it also writes per-phase aiur/*, stark/* timings
      # to `<json>.spans` for the drill-down.
      if [ "$mode" = execute ]; then
        timeout "${AIUR_EXECUTE_TIMEOUT:-25m}" \
          "$bt_bin" --ixe "$ixe" --consts "$c" --json "$res" --execute-only --texray \
          > "$tmp/$slug.log" 2>&1 \
          || { echo "::warning::aiur execute '$c' failed/timed out; dropping" >&2; continue; }
      else
        # setsid: bench-typecheck leads its own process group so the watchdog's
        # group-kill reaches every descendant.
        setsid timeout "${AIUR_PROVE_TIMEOUT:-50m}" \
          "$bt_bin" --ixe "$ixe" --consts "$c" --json "$res" --texray \
          > "$tmp/$slug.log" 2>&1 &
        bt_pid=$!
        watch_ram_kill "$bt_pid" "$ceiling_gb" "$oom" &
        w_pid=$!
        wait "$bt_pid" 2>/dev/null; bt_exit=$?
        kill "$w_pid" 2>/dev/null || true
        wait "$w_pid" 2>/dev/null || true
        # Exit 137 (SIGKILL) without our marker = the kernel OOM killer beat
        # the 3 s sampling window — still an OOM, label it as one.
        if [ -f "$oom" ] || [ "$bt_exit" -eq 137 ]; then
          echo "::warning::aiur prove '$c' OOM-killed (marker=$([ -f "$oom" ] && echo watchdog || echo kernel), ceiling ${ceiling_gb} GB)" >&2
          mark_oom "$res" "$c"
        elif [ "$bt_exit" -ne 0 ]; then
          echo "::warning::aiur prove '$c' failed (exit $bt_exit); dropping" >&2
          continue
        fi
      fi
      merge_phases "$res" "$spans"
      if [ -s "$res" ]; then
        cp "$res" "$rows/$slug.json"
        jq -s 'reduce .[] as $o ({}; . + $o)' "$rows"/*.json > "$out" 2>/dev/null || true
      fi
    done < "$names"
    emit_empty
    ;;

  zisk|sp1)
    # zkVM prove is not currently wired up (no GPU runner), so this branch runs
    # execute only. The workflow filters `zisk|sp1 prove` at parse time.
    if [ "$mode" != execute ]; then
      echo "::error::$backend $mode: only execute mode is supported" >&2
      emit_empty; exit 2
    fi
    host="${backend}-host"; work="$repo/$backend"
    # Build the host once so per-constant timing excludes compilation. The host
    # self-measures and writes its own neutral results JSON via `--json`
    # (cycles/execute-time/throughput/peak-rss), so there is nothing to grep —
    # `timeout` only bounds a runaway constant.
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
    ceiling_gb=${ZKVM_EXECUTE_MAX_RSS_GB:-120}
    rows="$tmp/rows"; mkdir -p "$rows"
    while IFS= read -r c; do
      [ -z "$c" ] && continue
      slug=$(printf '%s' "$c" | tr '/ .:' '____')
      res="$tmp/$slug.json"; log="$tmp/$slug.log"; spans="$res.spans"; oom="$tmp/$slug.oom"
      rm -f "$oom"
      # Full-closure check (no --skip-deps) so this is directly comparable to
      # the ooc `ix check-rs --anon --consts` run — the delta then isolates the
      # in-circuit-vs-out-of-circuit overhead rather than mixing in subject-
      # only vs full-closure scope. Full closures are RAM-unbounded (the ASM
      # microservices mmap multi-GB ROMs on top of the guest trace), so the
      # same watchdog as the aiur prove path guards the runner.
      # `exec setsid`: the subshell (whose pid is $!) replaces itself with the
      # session leader, so the watchdog's group-kill (`kill -- -$!`) reaches
      # the host and every descendant — without a plain subshell wrapper whose
      # pgid would be run.sh's own.
      ( cd "$work" && exec setsid timeout 25m "$bin" --execute --ixe "$ixe" \
          --consts "$c" --json "$res" --texray ) \
        > "$log" 2>&1 &
      zk_pid=$!
      watch_ram_kill "$zk_pid" "$ceiling_gb" "$oom" &
      w_pid=$!
      wait "$zk_pid" 2>/dev/null; zk_exit=$?
      kill "$w_pid" 2>/dev/null || true
      wait "$w_pid" 2>/dev/null || true
      if [ -f "$oom" ] || [ "$zk_exit" -eq 137 ]; then
        echo "::warning::$backend execute '$c' OOM-killed (marker=$([ -f "$oom" ] && echo watchdog || echo kernel), ceiling ${ceiling_gb} GB)" >&2
        mark_oom "$res" "$c"
      elif [ "$zk_exit" -ne 0 ]; then
        echo "::warning::$backend execute '$c' failed/timed out (exit $zk_exit); dropping" >&2
        continue
      fi
      # The host writes $res only on a clean (zero-failure) run. `$out` is
      # re-merged per constant so a job-level kill keeps completed rows.
      merge_phases "$res" "$spans"
      if [ -s "$res" ]; then
        cp "$res" "$rows/$slug.json"
        jq -s 'reduce .[] as $o ({}; . + $o)' "$rows"/*.json > "$out" 2>/dev/null || true
      fi
    done < "$names"
    emit_empty
    ;;

  ooc)
    # Out-of-circuit Rust kernel (far faster than proving). Two views, both keyed
    # off the structured line
    #   `##check## <elapsed_ms> <passed> <failures> <total> <peak-rss-bytes>`
    # (peak-rss from ix check's tracing-texray tree sampler): the whole env in
    # parallel (`--anon`, keyed by env), and a per-primary check
    # (`--anon --consts`, keyed by constant) that runs the constant's FULL
    # dependency closure in anon mode — the same mode and scope as the zkVM
    # execute above, so the delta isolates in-circuit vs out-of-circuit
    # overhead rather than mixing in closure-size or metadata effects.
    ooc_one() {  # <label> <ix-check-args…>  → prints one JSON object
      local label="$1"; shift
      local log="$tmp/n.out"
      "$ix_bin" check-rs "$ixe" "$@" > "$log" 2>>"$log" \
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
      # Whole-env row keyed by the CamelCase env slug so the PR side matches
      # what bench-main.yml uploads to bencher (matrix.bench, e.g. `InitStd`).
      ooc_one "$benv_cc" --anon
      while IFS= read -r c; do
        [ -z "$c" ] && continue
        ooc_one "$c" --anon --consts "$c"
      done < "$names"
    } | jq -s 'reduce .[] as $o ({}; . + $o)' > "$out" 2>/dev/null
    emit_empty
    ;;

  compile)
    # `ix compile <env>.lean → <env>.ixe` is the benchmark; the compile step
    # above always ran fresh for this backend (REUSE_IXE ignored) and teed to
    # `$compile_log`. `ix compile` emits `##benchmark## <elapsed_ms> <bytes>
    # <constants>` which we parse into the neutral results shape. The bencher
    # benchmark name is the CamelCase env slug (matches bench-main.yml's
    # matrix.bench keys: `InitStd`, `Lean`, `Mathlib`, `FLT`).
    line=$(grep '^##benchmark##' "$compile_log" 2>/dev/null | tail -1)
    if [ -z "$line" ]; then
      echo "::warning::compile: no ##benchmark## line in $compile_log; dropping" >&2
      emit_empty
    else
      elapsed_ms=$(echo "$line" | awk '{print $2}')
      bytes=$(echo "$line" | awk '{print $3}')
      constants=$(echo "$line" | awk '{print $4}')
      elapsed_s=$(awk -v e="$elapsed_ms" 'BEGIN{printf "%.3f", e/1000}')
      throughput=$(awk -v c="$constants" -v e="$elapsed_ms" \
        'BEGIN{ if (e>0) printf "%.2f", c*1000/e; else print 0 }')
      jq -n --arg n "$benv_cc" \
            --argjson t "$elapsed_s" --argjson b "$bytes" \
            --argjson c "$constants" --argjson tp "$throughput" \
        '{($n): {"compile-time":$t,"file-size":$b,"constants":$c,"throughput":$tp}}' \
        > "$out"
    fi
    ;;

  *) echo "unknown backend: $backend" >&2; exit 2 ;;
esac
echo "rows in $out: $(jq 'length' "$out" 2>/dev/null || echo '?')" >&2
