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
  external `.ixe` with no Lean source (`--ixe`), only the oracle-free
  phases 2–3 run; 1/4/5 report skipped.

  Separate from the `lake test` binary for the same reason as `validate`:
  large files' transitive imports (e.g. Mathlib via
  `Benchmarks/Compile/CompileMathlib.lean`) must not become compile-time
  deps of the test suite.
-/
module
public import Cli
public import Ix.Common
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

def runValidateLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let ixe? := (p.flag? "ixe").map (·.as! String)
  let path? : Option String := (p.variableArgsAs! String)[0]?
  if ixe?.isNone && path?.isNone then
    p.printError "error: must specify <path> to a Lean source file (or --ixe <file>)"
    return 1

  -- Sources: either elaborate a Lean file (full pipeline, oracle
  -- available) or read a pre-compiled `.ixe` (phases 2–3 only).
  let mut phases : Array (String × PhaseResult) := #[]
  let mut bytes : ByteArray := .empty
  let mut leanEnv? : Option Lean.Environment := none
  -- Canonicalized source view (phase 1's canon output) — phase 5's
  -- decompile oracle.
  let mut canonView? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none

  match ixe?, path? with
  | some ixePath, _ =>
    IO.println s!"Running pure-Lean Ix validator on {ixePath} (no Lean source: phases 1/4/5 skipped)"
    bytes ← IO.FS.readBinFile ixePath
    phases := phases.push ("1 compile",
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
    -- Phase 1: compile through the PURE-LEAN pipeline (canon → graph →
    -- ground → condense → aux-aware parallel compile → serialize).
    let t0 ← IO.monoMsNow
    match ← Ix.CompileM.compileLeanConsts constList with
    | .error e =>
      phases := phases.push ("1 compile",
        .failed s!"pure-Lean pipeline: {e}")
    | .ok out =>
      bytes := out.bytes
      canonView? := some out.cenv.env.consts
      let t1 ← IO.monoMsNow
      if out.cenv.ungrounded.size > 0 then
        let shown := out.cenv.ungrounded.toList.take 3
        let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
        phases := phases.push ("1 compile",
          .failed (s!"{out.cenv.ungrounded.size} per-block compile \
failure(s) ({out.bytes.size} bytes, {t1 - t0}ms)\n" ++
            String.intercalate "\n" msgs))
      else
        phases := phases.push ("1 compile",
          .passed s!"pure-Lean pipeline: {out.bytes.size} bytes, \
{out.blockCount} blocks, {out.ungroundedCount} ungrounded ({t1 - t0}ms)")
  | none, none => unreachable!

  -- Phase 2: pure serde gate.
  let t0 ← IO.monoMsNow
  let ixonEnv? ← match serdeGate bytes with
    | .error e =>
      phases := phases.push ("2 serde", .failed e)
      pure none
    | .ok env =>
      let t1 ← IO.monoMsNow
      phases := phases.push ("2 serde",
        .passed s!"deEnv parsed {env.consts.size} consts / {env.named.size} named; serEnv byte-identical ({t1 - t0}ms)")
      pure (some env)

  match ixonEnv? with
  | none =>
    -- Serde failed: nothing downstream can run.
    phases := phases.push ("3 kernel anon roundtrip", .skipped "serde gate failed")
    phases := phases.push ("4 kernel meta roundtrip", .skipped "serde gate failed")
  | some ixonEnv =>
    -- Phase 3: anon structural roundtrip.
    let t0 ← IO.monoMsNow
    let (rows, err?) := anonRoundtripEnv ixonEnv
    let t1 ← IO.monoMsNow
    phases := phases.push ("3 kernel anon roundtrip",
      match err? with
      | none => .passed s!"{rows} constants structurally preserved ({t1 - t0}ms)"
      | some e => .failed s!"after {rows} rows: {e}")
    -- Phase 4: meta roundtrip (needs the elaborated env as oracle).
    match leanEnv? with
    | none =>
      phases := phases.push ("4 kernel meta roundtrip",
        .skipped "no Lean source env to compare against (--ixe mode)")
    | some leanEnv =>
      let t0 ← IO.monoMsNow
      match metaRoundtripEnv leanEnv ixonEnv with
      | .error e =>
        phases := phases.push ("4 kernel meta roundtrip", .failed e)
      | .ok report =>
        let t1 ← IO.monoMsNow
        let counts := s!"checked {report.checked}, notFound {report.notFound}, \
                        skippedAux {report.skippedAux}, \
                        skippedSurgery {report.skippedSurgery} ({t1 - t0}ms)"
        if report.errorCount == 0 then
          phases := phases.push ("4 kernel meta roundtrip", .passed counts)
        else
          let shown := report.errors.toSubarray 0 (min 5 report.errors.size)
          let msgs := shown.toArray.map fun (n, m) => s!"    ✗ {n}: {m}"
          phases := phases.push ("4 kernel meta roundtrip",
            .failed (s!"{report.errorCount} comparison error(s); {counts}\n" ++
              String.intercalate "\n" msgs.toList))

  -- Phase 5: decompile through the full pure-Lean driver (Pass 1
  -- aux-skip → Pass 1.5 flags → Pass 2 aux regeneration/recovery).
  -- With a Lean source (path mode) the canonicalized env is the oracle:
  -- every reconstructed constant must be hash-identical, both
  -- directions. In `--ixe` mode the phase runs oracle-free (decompile
  -- errors only).
  match ixonEnv? with
  | none =>
    phases := phases.push ("5 decompile", .skipped "serde gate failed")
  | some ixonEnv =>
    let t0 ← IO.monoMsNow
    let (decompiled, errs, _p2st) :=
      Ix.DecompileM.decompileEnvFull ixonEnv canonView?
    let t1 ← IO.monoMsNow
    if !errs.isEmpty then
      let shown := errs.toList.take 5
      let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
      phases := phases.push ("5 decompile",
        .failed (s!"{errs.size} decompile error(s) \
({decompiled.size} constants, {t1 - t0}ms)\n" ++
          String.intercalate "\n" msgs))
    else
      match canonView? with
      | some view =>
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
          phases := phases.push ("5 decompile",
            .passed s!"{nMatch} constants reconstructed hash-identical \
to the canonicalized source ({t1 - t0}ms)")
        else
          let msgs := mismatches.toList.take 5 |>.map (s!"    ✗ {·.pretty}")
          phases := phases.push ("5 decompile",
            .failed (s!"{mismatches.size} mismatch(es), {missing} \
missing; {nMatch} matched ({t1 - t0}ms)\n" ++
              String.intercalate "\n" msgs))
      | none =>
        phases := phases.push ("5 decompile",
          .passed s!"oracle-free: {decompiled.size} constants decompiled, \
0 errors ({t1 - t0}ms)")

  IO.println ""
  for (name, result) in phases do
    IO.println s!"[validate-lean] phase {name}: {result.render}"
  let failures := phases.filter (·.2.isFailure)
  IO.println ""
  IO.println s!"[validate-lean] {failures.size} phase failure(s)"
  return if failures.isEmpty then 0 else 1

end Ix.Cli.ValidateLeanCmd

open Ix.Cli.ValidateLeanCmd in
def validateLeanCmd : Cli.Cmd := `[Cli|
  "validate-lean" VIA runValidateLeanCmd;
  "Validate a Lean file through the pure-Lean Ix pipeline (compile [stub] → serde → kernel anon+meta roundtrips → decompile [stub])"

  FLAGS:
    ns  : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are validated; transitive deps are pulled in automatically."
    ixe : String; "Validate a pre-compiled .ixe instead of a Lean file (oracle-free: runs serde + anon roundtrip only)"

  ARGS:
    ...path : String; "Path to the Lean source file whose env should be validated (omit with --ixe)."
]

end
