/-
  `ix validate-lean <file.lean>`: run the pure-Lean Ix pipeline validation
  against the Lean environment for any file — the `Ix.Tc` counterpart to
  `ix validate` (which drives the Rust implementation's 8-phase pipeline).

  Phases (all pure-Lean):

    1. Compile (Lean → Ixon)          — the full pure-Lean pipeline
                                        (canon → graph → ground →
                                        condense → aux-aware parallel
                                        compile → serialize)
    2. Serde gate (pure)              — `deEnv` parses the compiled bytes,
                                        `serEnv` reproduces them byte-exactly
    3. Kernel anon roundtrip (pure)   — every constant ingressed, egressed
                                        back to Ixon, canonically compared;
                                        projections byte-exact
    4. Kernel meta roundtrip (pure)   — whole env meta-ingressed, egressed
                                        to `Ix.ConstantInfo`, compared
                                        against the elaborated env with
                                        Rust `compare_envs` semantics
    5. Decompile (Ixon → Lean)        — the full decompile driver (Pass 1
                                        aux-skip → flags → Pass 2 aux
                                        regeneration/recovery), compared
                                        hash-identical against the
                                        canonicalized source

  Starting from a Lean FILE (like `ix validate`) is what makes phase 4
  possible: the elaborated environment is the comparison oracle. For an
  external `.ixe` with no Lean source (`--env`), only the oracle-free
  phases 2–3 run; 1/4/5 report skipped.

  Separate from the `lake test` binary for the same reason as `validate`:
  large files' transitive imports (e.g. Mathlib via
  `Benchmarks/Compile/CompileMathlib.lean`) must not become compile-time
  deps of the test suite.
-/
module
public import Cli
public import Ix.Common
public import Ix.CanonM
public import Ix.CompileM
public import Ix.CompileDriver
public import Ix.DecompileM
public import Ix.DecompileDriver
public import Ix.DecompileRoundtrip
public import Ix.Meta
public import Ix.Tc
public import Ix.Cli.ValidateCmd

public section

open System (FilePath)

namespace Ix.Cli.ValidateLeanCmd

open Ix.Tc

/-- Phase outcome for the final report. -/
inductive PhaseResult where
  | passed (detail : String)
  | failed (detail : String)
  | stubbed (detail : String)
  | skipped (detail : String)

def PhaseResult.render : PhaseResult → String
  | .passed d => s!"PASS  {d}"
  | .failed d => s!"FAIL  {d}"
  | .stubbed d => s!"STUB  {d}"
  | .skipped d => s!"SKIP  {d}"

def PhaseResult.isFailure : PhaseResult → Bool
  | .failed _ => true
  | _ => false

/-- Append a phase result AND emit its section heading immediately, in
    `ix validate`'s style (`[validate-aux] Phase: … / n pass, m fail`),
    flushing stdout. Incremental + flushed output is load-bearing: the
    stage-1 whole-Mathlib run was OOM-killed mid-phase with every
    completed phase's result still sitting in the block-buffered stdout,
    leaving no evidence of how far it got. -/
def pushPhase (phases : Array (String × PhaseResult))
    (entry : String × PhaseResult) : IO (Array (String × PhaseResult)) := do
  IO.println s!"[validate-lean] Phase: {entry.1}"
  IO.println s!"  {entry.2.render}"
  (← IO.getStdout).flush
  return phases.push entry

def runValidateLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let ixe? := (p.flag? "env").map (·.as! String)
  let path? : Option String := (p.variableArgsAs! String)[0]?
  if ixe?.isNone && path?.isNone then
    p.printError "error: must specify <path> to a Lean source file (or --env <file>)"
    return 1

  -- Sources: either elaborate a Lean file (full pipeline, oracle
  -- available) or read a pre-compiled `.ixe` (phases 2–3 only).
  let fullOracle := p.hasFlag "full-oracle"
  let mut phases : Array (String × PhaseResult) := #[]
  let mut bytes : ByteArray := .empty
  let mut leanEnv? : Option Lean.Environment := none
  -- Phase 5's decompile oracle, in one of two forms. The default is a
  -- per-name 64-bit DIGEST of the canonicalized source (derived
  -- `Hashable`, same field coverage as the `BEq` used by `--full-oracle`,
  -- O(1) at the hash-consed Name/Level/Expr leaves), collected by the
  -- STREAMING compile driver during its transient canon pass — the
  -- whole-env canon map is never materialized at all, which at
  -- whole-Mathlib scale is the difference between fitting in RAM and
  -- swapping.
  -- `--full-oracle` keeps the old whole-env view: full structural BEq per
  -- constant plus the decompiler's per-recovery debug track — use it to
  -- debug a digest mismatch on a filtered (`--ns`) closure.
  let mut canonView? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none
  let mut canonDigests? : Option (Std.HashMap Ix.Name UInt64) := none

  match ixe?, path? with
  | some ixePath, _ =>
    IO.println s!"Running pure-Lean Ix validator on {ixePath} (no Lean source: phases 1/4/5 skipped)"
    bytes ← IO.FS.readBinFile ixePath
    phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
      .skipped "pre-compiled .ixe input — no Lean source to compile")
  | none, some pathStr =>
    IO.println s!"Running pure-Lean Ix validator on {pathStr}"
    buildFile pathStr
    let leanEnv ← getFileEnv pathStr
    leanEnv? := some leanEnv
    -- Optional namespace filter, same semantics as `ix validate`.
    let constList ← match p.flag? "ns" with
      | none => pure leanEnv.constants.toList
      | some flag =>
        let raw := flag.as! String
        let prefixes := parsePrefixes raw
        if prefixes.isEmpty then
          IO.println s!"[validate-lean] warning: --ns '{raw}' parsed to empty list; validating full env"
          pure leanEnv.constants.toList
        else
          let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
            if prefixes.any (·.isPrefixOf n) then some n else none
          IO.println s!"[validate-lean] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
          let closed := collectDeps leanEnv seeds
          IO.println s!"[validate-lean] filter: {closed.length} constants after transitive-dep closure"
          pure closed
    IO.println s!"Total constants: {constList.length}"
    IO.println "[validate-lean] phase 1: compiling (pure-Lean pipeline)..."
    (← IO.getStdout).flush
    -- Phase 1: compile through the PURE-LEAN pipeline (canon → graph →
    -- ground → condense → aux-aware parallel compile → serialize).
    let compileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 32
    let t0 ← IO.monoMsNow
    match ← Ix.CompileM.compileLeanConsts constList
        (numWorkers := compileWorkers) with
    | .error e =>
      phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
        .failed s!"pure-Lean pipeline: {e}")
    | .ok out =>
      bytes := out.bytes
      if fullOracle then
        -- Materialize the whole canon view post-hoc (chunk-parallel).
        -- The streaming compile never builds it; canon is per-constant
        -- deterministic, so this equals the view the compile read
        -- through its on-demand fallback.
        let constArr := constList.toArray
        let chunkSize := max 1 ((constArr.size + 31) / 32)
        let chunkArr := Ix.CanonM.chunks constArr chunkSize
        let tasks := chunkArr.map fun chunk =>
          Task.spawn fun _ => Ix.CanonM.canonChunk chunk
        let mut view : Std.HashMap Ix.Name Ix.ConstantInfo := {}
        for task in tasks do
          for (n, ci) in task.get do
            view := view.insert n ci
        canonView? := some view
      else
        -- The streamed canon pass already digested every input
        -- constant; the whole-env canon map never existed.
        canonDigests? := some out.digests
      let t1 ← IO.monoMsNow
      if out.cenv.ungrounded.size > 0 then
        let shown := out.cenv.ungrounded.toList.take 3
        let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
        phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
          .failed (s!"{out.cenv.ungrounded.size} per-block compile \
failure(s) ({out.bytes.size} bytes, {t1 - t0}ms)\n" ++
            String.intercalate "\n" msgs))
      else
        phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
          .passed s!"pure-Lean pipeline: {out.bytes.size} bytes, \
{out.blockCount} blocks, {out.ungroundedCount} ungrounded ({t1 - t0}ms)")
  | none, none => unreachable!

  -- Phase 2: pure serde gate — streaming: every unit parsed with the
  -- pure reader, re-serialized with the pure writer, compared against
  -- its input span (gapless coverage + order/root/trailing contracts),
  -- one unit at a time. Constants and §5 metadata stay byte windows;
  -- the whole-env structured materialization (a >100 GiB spike at
  -- whole-Mathlib scale, with the Lean oracle env still pinned for
  -- phase 4) never happens.
  IO.println "[validate-lean] phase 2: serde gate (streaming)..."
  (← IO.getStdout).flush
  let t0 ← IO.monoMsNow
  let parts? ← match serdeGateStreaming bytes with
    | .error e =>
      phases ← pushPhase phases ("2. Serde (streaming)", .failed e)
      pure none
    | .ok parts =>
      let t1 ← IO.monoMsNow
      phases ← pushPhase phases ("2. Serde (streaming)",
        .passed s!"streaming gate: {parts.env.consts.size} consts / \
{parts.namedRows.size} named rows; writer byte-identical per unit ({t1 - t0}ms)")
      pure (some parts)
  -- The lazy parts' backing buffer is the same array; drop the extra
  -- reference so exactly one image stays live.
  bytes := .empty

  match parts? with
  | none =>
    -- Serde failed: nothing downstream can run.
    phases ← pushPhase phases ("3. Kernel anon roundtrip", .skipped "serde gate failed")
    phases ← pushPhase phases ("4. Kernel meta roundtrip", .skipped "serde gate failed")
  | some parts =>
    -- Phase 3: anon structural roundtrip (named-independent: works off
    -- the lazy consts windows). Memory-diagnosis knobs:
    -- `IX_ANON_CAP=<n>` bisects the work list; `IX_SKIP_PHASES=3,5`
    -- skips phases outright to isolate another phase's footprint.
    let skipPhases := ((← IO.getEnv "IX_SKIP_PHASES").getD "").splitOn ","
    if skipPhases.contains "3" then
      phases ← pushPhase phases ("3. Kernel anon roundtrip", .skipped "IX_SKIP_PHASES")
    else
      IO.println "[validate-lean] phase 3: kernel anon roundtrip..."
      (← IO.getStdout).flush
      let anonCap := (← IO.getEnv "IX_ANON_CAP").bind (·.toNat?)
      let anonSeq := (← IO.getEnv "IX_ANON_SEQ").isSome
      let anonCut := ((← IO.getEnv "IX_ANON_STAGE").bind (·.toNat?)).getD 0
      let t0 ← IO.monoMsNow
      let (rows, err?) := anonRoundtripEnv parts.env anonCap anonSeq anonCut
      let t1 ← IO.monoMsNow
      phases ← pushPhase phases ("3. Kernel anon roundtrip",
        match err? with
        | none => .passed s!"{rows} constants structurally preserved ({t1 - t0}ms)"
        | some e => .failed s!"after {rows} rows: {e}")
      if (← IO.getEnv "IX_ANON_HOLD").isSome then
        IO.println "[hold] phase 3 returned; sleeping 60s (memory probe)"
        (← IO.getStdout).flush
        IO.sleep 60000
        IO.println "[hold] done"
        (← IO.getStdout).flush
    -- Phase 4: meta roundtrip (needs the elaborated env as oracle) —
    -- streaming: per-chunk materialize → chunk-local ingress → egress →
    -- compare → drop; the whole-env merged MetaEnv never exists.
    match leanEnv? with
    | none =>
      phases ← pushPhase phases ("4. Kernel meta roundtrip",
        .skipped "no Lean source env to compare against (--env mode)")
    | some leanEnv =>
      IO.println "[validate-lean] phase 4: kernel meta roundtrip (streaming)..."
      (← IO.getStdout).flush
      let t0 ← IO.monoMsNow
      -- IX_META_EAGER=1: the pre-streaming whole-env driver (memory
      -- diagnosis oracle; needs the full named table materialized AND
      -- the merged whole-env MetaEnv — closure-scale only).
      let metaResult ← if (← IO.getEnv "IX_META_EAGER").isSome then
          pure <| parts.materializeAllNamed.bind fun fullEnv =>
            metaRoundtripEnv leanEnv fullEnv
        else
          pure <| metaRoundtripEnvStreaming leanEnv parts
      match metaResult with
      | .error e =>
        phases ← pushPhase phases ("4. Kernel meta roundtrip", .failed e)
      | .ok report =>
        let t1 ← IO.monoMsNow
        let counts := s!"checked {report.checked}, notFound {report.notFound}, \
                        skippedAux {report.skippedAux}, \
                        skippedSurgery {report.skippedSurgery} ({t1 - t0}ms)"
        if report.errorCount == 0 then
          phases ← pushPhase phases ("4. Kernel meta roundtrip", .passed counts)
        else
          let shown := report.errors.toSubarray 0 (min 5 report.errors.size)
          let msgs := shown.toArray.map fun (n, m) => s!"    ✗ {n}: {m}"
          phases ← pushPhase phases ("4. Kernel meta roundtrip",
            .failed (s!"{report.errorCount} comparison error(s); {counts}\n" ++
              String.intercalate "\n" msgs.toList))

  -- The Lean source env's job ends with phase 4 — release it before the
  -- decompile phase so its elaboration overlay can be reclaimed (the
  -- compacted import region stays mapped either way).
  leanEnv? := none

  -- Phase 5: decompile through the full pure-Lean driver (Pass 1
  -- aux-skip → Pass 1.5 flags → Pass 2 aux regeneration/recovery).
  -- With a Lean source (path mode) the canonicalized env is the oracle:
  -- every reconstructed constant must match it, both directions — by
  -- per-name digest (default) or full structural BEq (`--full-oracle`,
  -- which also switches the decompiler's per-recovery debug track on by
  -- passing the view as `origEnv?`). In `--env` mode the phase runs
  -- oracle-free (decompile errors only).
  let skipPhases5 := ((← IO.getEnv "IX_SKIP_PHASES").getD "").splitOn ","
  let ixonEnvForDecompile? : Option (Except String Ixon.Env) :=
    if skipPhases5.contains "5" then none
    else parts?.map (·.materializeAll)
  match ixonEnvForDecompile? with
  | none =>
    phases ← pushPhase phases ("5. Decompile",
      .skipped (if skipPhases5.contains "5" then "IX_SKIP_PHASES"
                else "serde gate failed"))
  | some (Except.error e) =>
    phases ← pushPhase phases ("5. Decompile",
      .failed s!"named metadata materialization: {e}")
  | some (Except.ok ixonEnv) =>
    IO.println "[validate-lean] phase 5: decompiling (full driver)..."
    (← IO.getStdout).flush
    let t0 ← IO.monoMsNow
    let decompileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 16
    let (decompiled, errs, _p2st) ←
      Ix.DecompileM.decompileEnvFullParallel ixonEnv canonView?
        (numWorkers := decompileWorkers)
    let t1 ← IO.monoMsNow
    if !errs.isEmpty then
      let shown := errs.toList.take 5
      let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
      phases ← pushPhase phases ("5. Decompile",
        .failed (s!"{errs.size} decompile error(s) \
({decompiled.size} constants, {t1 - t0}ms)\n" ++
          String.intercalate "\n" msgs))
    else
      match canonView?, canonDigests? with
      | some view, _ =>
        let mut nMatch := (0 : Nat)
        let mut mismatches : Array Ix.Name := #[]
        let mut missing := (0 : Nat)
        for (name, info) in decompiled do
          match view.get? name with
          | some orig =>
            if info == orig then nMatch := nMatch + 1
            else mismatches := mismatches.push name
          | none => missing := missing + 1
        for (name, _) in view do
          if !decompiled.contains name then
            missing := missing + 1
            if mismatches.size < 10 then
              mismatches := mismatches.push name
        if mismatches.isEmpty && missing == 0 then
          phases ← pushPhase phases ("5. Decompile",
            .passed s!"{nMatch} constants reconstructed hash-identical \
to the canonicalized source ({t1 - t0}ms)")
        else
          let msgs := mismatches.toList.take 5 |>.map (s!"    ✗ {·.pretty}")
          phases ← pushPhase phases ("5. Decompile",
            .failed (s!"{mismatches.size} mismatch(es), {missing} \
missing; {nMatch} matched ({t1 - t0}ms)\n" ++
              String.intercalate "\n" msgs))
      | none, some digs =>
        let mut nMatch := (0 : Nat)
        let mut mismatches : Array Ix.Name := #[]
        let mut missing := (0 : Nat)
        for (name, info) in decompiled do
          match digs.get? name with
          | some d =>
            if hash info == d then nMatch := nMatch + 1
            else mismatches := mismatches.push name
          | none => missing := missing + 1
        for (name, _) in digs do
          if !decompiled.contains name then
            missing := missing + 1
            if mismatches.size < 10 then
              mismatches := mismatches.push name
        if mismatches.isEmpty && missing == 0 then
          phases ← pushPhase phases ("5. Decompile",
            .passed s!"{nMatch} constants reconstructed digest-identical \
to the canonicalized source ({t1 - t0}ms)")
        else
          let msgs := mismatches.toList.take 5 |>.map (s!"    ✗ {·.pretty}")
          phases ← pushPhase phases ("5. Decompile",
            .failed (s!"{mismatches.size} digest mismatch(es), {missing} \
missing; {nMatch} matched ({t1 - t0}ms) — rerun with --full-oracle \
--ns <namespace> for a structural diff\n" ++
              String.intercalate "\n" msgs))
      | none, none =>
        phases ← pushPhase phases ("5. Decompile",
          .passed s!"oracle-free: {decompiled.size} constants decompiled, \
0 errors ({t1 - t0}ms)")

  -- Recap (each phase already printed its section heading when it
  -- completed), then a `RESULT:` line matching `ix validate`'s.
  IO.println ""
  IO.println "[validate-lean] phase summary:"
  for (name, result) in phases do
    IO.println s!"[validate-lean]   {name}: {result.render}"
  let failures := phases.filter (·.2.isFailure)
  IO.println s!"[validate-lean] RESULT: {failures.size} total failures"
  (← IO.getStdout).flush
  return if failures.isEmpty then 0 else 1

end Ix.Cli.ValidateLeanCmd

open Ix.Cli.ValidateLeanCmd in
def validateLeanCmd : Cli.Cmd := `[Cli|
  "validate-lean" VIA runValidateLeanCmd;
  "Validate a Lean file through the pure-Lean Ix pipeline (compile [stub] → serde → kernel anon+meta roundtrips → decompile [stub])"

  FLAGS:
    ns  : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are validated; transitive deps are pulled in automatically."
    env : String; "Validate a pre-compiled .ixe instead of a Lean file (oracle-free: runs serde + anon roundtrip only)"
    workers : Nat; "Worker count for the parallel phases (compile phase 1, decompile phase 5); default 32 for compile, 16 for decompile. Lower at whole-Mathlib scale — memory scales with workers (phase 1 at 32 peaks past 116 GiB there; 8 is a safe whole-Mathlib setting on a 128 GiB box)."
    «full-oracle»; "Phase 5 comparison via the full canonicalized env (structural BEq per constant + the decompiler's per-recovery debug track) instead of the default per-name digests. Holds a whole extra env copy through phase 5 — use on --ns-filtered closures to debug a digest mismatch."

  ARGS:
    ...path : String; "Path to the Lean source file whose env should be validated (omit with --env)."
]

end
