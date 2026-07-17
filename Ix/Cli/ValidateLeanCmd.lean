/-
  `ix validate-lean <file.lean>`: run the pure-Lean Ix pipeline validation
  against the Lean environment for any file — the `Ix.Tc` counterpart to
  `ix validate` (which drives the Rust implementation's 8-phase pipeline).

  Phases (stubs marked — the pure-Lean compiler and decompiler are not
  implemented yet, so those sections delegate or skip loudly):

    1. Compile (Lean → Ixon)          [STUB: via the Rust FFI compiler]
    2. Serde gate (pure)              — `deEnv` parses the compiled bytes,
                                        `serEnv` reproduces them byte-exactly
    3. Kernel anon roundtrip (pure)   — every constant ingressed, egressed
                                        back to Ixon, canonically compared;
                                        projections byte-exact
    4. Kernel meta roundtrip (pure)   — whole env meta-ingressed, egressed
                                        to `Ix.ConstantInfo`, compared
                                        against the elaborated env with
                                        Rust `compare_envs` semantics
    5. Decompile (Ixon → Lean)        [STUB: not yet implemented, skipped]

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
    -- Phase 1: compile. The pure-Lean compiler is stale, so this phase is
    -- a stub that delegates to the Rust FFI compiler; it becomes a real
    -- phase when `Ix.CompileM` is revived.
    let t0 ← IO.monoMsNow
    let dir ← IO.FS.createTempDir
    let out := dir / "validate-lean.ixe"
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI constList out.toString
    bytes ← IO.FS.readBinFile out
    IO.FS.removeDirAll dir
    let t1 ← IO.monoMsNow
    phases := phases.push ("1 compile",
      .stubbed s!"pure-Lean compiler not implemented — compiled via Rust FFI ({bytes.size} bytes, {t1 - t0}ms)")
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

  -- Phase 5: decompile (pure-Lean decompiler not implemented).
  phases := phases.push ("5 decompile",
    .stubbed "pure-Lean decompiler not implemented — skipped")

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
