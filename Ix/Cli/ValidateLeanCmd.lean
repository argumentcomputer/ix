module
public import Cli
public import Ix.Common
public import Ix.CanonM
public import Ix.CompileM
public import Ix.ModeCheck
public import Ix.CompileDriver
public import Ix.CompileCertified
public import Ix.DecompileM
public import Ix.DecompileDriver
public import Ix.KernelFidelity.Egress
public import Ix.KernelFidelity.Reader
public import Ix.Meta
public import Ix.Cli.ValidateCmd
public import Ix.RoleBinding.Compile
public import Ix.SemanticContract

/-!
  `ix validate-lean <file.lean>`: run the pure-Lean Ix pipeline validation
  against the Lean environment for any file.

  Phases (all pure-Lean):

    1. Compile (Lean → Ixon)          — the certified pure-Lean pipeline
                                        and the role binding `ix compile-lean`
                                        adds (`Ix.CompileM.compileAndFinalize`):
                                        the later phases read the bytes
                                        compile-lean writes
    2. Serde gate (pure)              — verified lazy parsing, with exact
                                        writer bytes per serialized unit
    3. Projection/block-order fidelity — IxCK reconstructs the projections;
                                        exact bytes, coverage and block order
    4. Source/reader fidelity         — IxCK's reader compared with a direct
                                        translation of the Lean source;
                                        complete named-source coverage
    5. Decompile (Ixon → Lean)        — stored records read without a
                                        kernel, then inductive flags, compared
                                        hash-identical against the
                                        canonicalized source

  Starting from a Lean FILE is what makes phase 4
  possible: the elaborated environment is the comparison oracle. For an
  external `.ixe` with no Lean source (`--ixe`), only the oracle-free
  phases 2–3 run without an oracle; 1/4 report skipped and 5 checks
  decompilation errors without a source comparison.

  Separate from the `lake test` binary:
  large files' transitive imports (e.g. Mathlib via
  `Benchmarks/Compile/CompileMathlib.lean`) must not become compile-time
  deps of the test suite.
-/

public section

open System (FilePath)
open Ix.EnvScope

namespace Ix.Cli.ValidateLeanCmd

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

/-- The existing report rows, shared by successful and failed phases. -/
def phaseRows (phases : Array (String × PhaseResult)) : Lean.Json :=
  Lean.Json.arr <| phases.map fun (name, r) =>
    let (result, detail) := match r with
      | .passed d => ("pass", d)
      | .failed d => ("fail", d)
      | .stubbed d => ("stub", d)
      | .skipped d => ("skip", d)
    Lean.Json.mkObj
      [ ("name", Lean.Json.str name)
      , ("result", Lean.Json.str result)
      , ("detail", Lean.Json.str detail) ]

/-- An uncapped source run must compare every named source constant. Expected
reader declines retain their distinct verdicts in the full summary. -/
def readerResult (report : Tests.Ix.Kernel.ReaderFidelity.Report)
    (expected elapsedMs : Nat) : PhaseResult :=
  let detail := report.summary ++
    s!"\nsource coverage: {report.constants}/{expected} named constants\n({elapsedMs}ms)"
  if report.problems.isEmpty && report.unexplained.isEmpty && report.unmatched.isEmpty &&
      report.constants == expected then .passed detail else .failed detail

/-- Construction and access/IO errors become phase failures, so the CLI still
reaches its recap and JSON report. No limit or root restriction is applied. -/
def readerPhase (input : IO Tests.Ix.Kernel.ReaderFidelity.InputAccess) : IO PhaseResult := do
  let t0 ← IO.monoMsNow
  try
    let access ← input
    let report ← Tests.Ix.Kernel.ReaderFidelity.runAccess access
    return readerResult report access.names.size ((← IO.monoMsNow) - t0)
  catch e => return .failed s!"source/reader fidelity: {e}"

/-- Retain the projection report and the full reviewed failure predicate.
    This checks projection bytes, coverage and block order, not typing or
    a roundtrip of every constant body. -/
def projectionResult (report : Tests.Ix.Kernel.EgressFidelity.ProjectionReport)
    (elapsedMs : Nat) : PhaseResult :=
  let orderProblems := report.orderProblems
  let detail := report.summary ++
    String.join (orderProblems.map ("\nblock order: " ++ ·)) ++ s!"\n({elapsedMs}ms)"
  if report.problems.isEmpty && report.matched == report.compiled && orderProblems.isEmpty then
    .passed detail
  else .failed detail

/-- The old anonymous ingress diagnostics cannot select a partial version
    of the new fidelity pass. An explicitly skipped phase ignores them. -/
def retiredAnonOptions : IO (Array String) :=
  #["IX_ANON_CAP", "IX_ANON_STAGE", "IX_ANON_SEQ", "IX_ANON_HOLD"].filterM fun key =>
    return (← IO.getEnv key).isSome

/-- Append a phase result AND emit its section heading immediately
    (`[validate-lean] Phase: …` and its result line),
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
  let ixe? := (p.flag? "ixe").map (·.as! String)
  let path? : Option String := (p.variableArgsAs! String)[0]?
  if ixe?.isNone && path?.isNone then
    p.printError "error: must specify <path> to a Lean source file (or --ixe <file>)"
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
  -- O(1) at the hash-consed Name/Level/Expr leaves).
  -- `--full-oracle` keeps the whole-env view: full structural BEq per
  -- constant — use it to debug a digest mismatch on a filtered (`--ns`) closure.
  let mut canonView? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none
  let mut canonDigests? : Option (Std.HashMap Ix.Name UInt64) := none
  -- The records the role binding added to the compile (its support, certificate
  -- theorems and evidence): no Lean constant of the input is their source, so the
  -- source's reader comparison (phase 4) counts their constants as foreign.
  let mut bindingRecords : Array Address := #[]

  let mut reusingIxeWithSource := false
  match ixe?, path? with
  | some ixePath, none =>
    IO.println s!"Running pure-Lean Ix validator on {ixePath} (no Lean source: phases 1/4 skipped)"
    bytes ← IO.FS.readBinFile ixePath
    phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
      .skipped "pre-compiled .ixe input — no Lean source to compile")
  | some ixePath, some pathStr =>
    reusingIxeWithSource := true
    IO.println s!"Running pure-Lean Ix validator on {pathStr} with pre-compiled {ixePath}"
    let t0 ← IO.monoMsNow
    bytes ← IO.FS.readBinFile ixePath
    buildFile pathStr
    let fe ← getFileEnvCore pathStr
    let leanEnv := fe.env
    leanEnv? := some leanEnv
    let constList ← match p.flag? "ns" with
      | none => defaultConstList fe pathStr
      | some flag =>
        let raw := flag.as! String
        let prefixes := parsePrefixes raw
        if prefixes.isEmpty then
          IO.println s!"[validate-lean] warning: --ns '{raw}' parsed to empty list; validating full env"
          defaultConstList fe pathStr
        else
          let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
            if prefixes.any (·.isPrefixOf n) then some n else none
          IO.println s!"[validate-lean] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
          let closed := collectSelectedDeps leanEnv seeds
          IO.println s!"[validate-lean] filter: {closed.length} constants after transitive-dep closure"
          pure closed
    IO.println s!"Total constants: {constList.length}"
    let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv constList)
    let constArr := prepared.toArray
    let chunkSize := max 1 ((constArr.size + 31) / 32)
    let chunkArr := Ix.CanonM.chunks constArr chunkSize
    if fullOracle then
      let tasks := chunkArr.map fun chunk =>
        Task.spawn fun _ => Ix.CanonM.canonChunk chunk
      let mut view : Std.HashMap Ix.Name Ix.ConstantInfo := {}
      for task in tasks do
        for (n, ci) in task.get do
          view := view.insert n ci
      canonView? := some view
    else
      let tasks := chunkArr.map fun chunk =>
        Task.spawn fun _ => (Ix.CanonM.canonChunk chunk).map fun (n, ci) => (n, hash ci)
      let mut digs : Std.HashMap Ix.Name UInt64 :=
        Std.HashMap.emptyWithCapacity constArr.size
      for task in tasks do
        for (n, d) in task.get do
          digs := digs.insert n d
      canonDigests? := some digs
    let t1 ← IO.monoMsNow
    phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
      .passed s!"reused pre-compiled artifact {ixePath}: {bytes.size} bytes, \
{constList.length} source constants ({t1 - t0}ms)")
  | none, some pathStr =>
    IO.println s!"Running pure-Lean Ix validator on {pathStr}"
    buildFile pathStr
    let fe ← getFileEnvCore pathStr
    let leanEnv := fe.env
    leanEnv? := some leanEnv
    -- Optional namespace filter (`parsePrefixes`).
    let constList ← match p.flag? "ns" with
      | none => defaultConstList fe pathStr
      | some flag =>
        let raw := flag.as! String
        let prefixes := parsePrefixes raw
        if prefixes.isEmpty then
          IO.println s!"[validate-lean] warning: --ns '{raw}' parsed to empty list; validating full env"
          defaultConstList fe pathStr
        else
          let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
            if prefixes.any (·.isPrefixOf n) then some n else none
          IO.println s!"[validate-lean] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
          let closed := collectSelectedDeps leanEnv seeds
          IO.println s!"[validate-lean] filter: {closed.length} constants after transitive-dep closure"
          pure closed
    IO.println s!"Total constants: {constList.length}"
    IO.println "[validate-lean] phase 1: compiling (pure-Lean pipeline)..."
    (← IO.getStdout).flush
    -- Phase 1: compile through the certified PURE-LEAN pipeline and add the
    -- role binding as `ix compile-lean` does (`Ix.CompileM.compileAndFinalize`),
    -- so that the later phases read the bytes compile-lean writes. A partial
    -- compile is finalized too; its failures fail the phase below.
    let compileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 32
    let t0 ← IO.monoMsNow
    match ← Ix.CompileM.compileAndFinalize leanEnv constList compileWorkers
        (allowPartial := true) (modeCheck := Ix.ModeCheck.checkArtifact) with
    | .error e =>
      phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
        .failed s!"pure-Lean pipeline: {e}")
    | .ok (out, finalization) =>
      let bound : Except String (Ixon.Env × ByteArray) := match finalization with
        | .done artifact finalizedBytes => .ok (artifact, finalizedBytes)
        | .failed e => .error e
        | .refused => .error "the compile was not finalized"
      let added : Array Ix.Name := match bound with
        | .ok (artifact, _) => artifact.named.fold (init := #[]) fun acc n _ =>
            if out.env.named.contains n then acc else acc.push n
        | .error _ => #[]
      bytes := match bound with
        | .ok (_, finalizedBytes) => finalizedBytes
        | .error _ => (Ixon.serEnv out.env).toOption.getD .empty
      bindingRecords := match bound with
        | .ok (artifact, _) => artifact.consts.fold (init := #[]) fun acc a _ =>
            if out.env.consts.contains a then acc else acc.push a
        | .error _ => #[]
      -- The binding's own constants (role support and certificate theorems) are
      -- compared with their sources too: those of the input's environment, and
      -- the certificate theorems' (`IxCK.Kernel.PinGen.Certs`).
      let sources ← if added.all fun n => leanEnv.contains (Ix.SemanticContract.toLeanName n) then
          pure #[leanEnv]
        else pure #[leanEnv, ← Ix.RoleBinding.Compile.nativeCertSource]
      let addedConsts : Array (Lean.Name × Lean.ConstantInfo) := added.filterMap fun n =>
        let ln := Ix.SemanticContract.toLeanName n
        (sources.findSome? (·.find? ln)).map (ln, ·)
      let addedCanon := Ix.CanonM.canonChunk addedConsts
      let constArr := out.prepared.toArray
      let chunkSize := max 1 ((constArr.size + 31) / 32)
      let chunkArr := Ix.CanonM.chunks constArr chunkSize
      if fullOracle then
        let tasks := chunkArr.map fun chunk =>
          Task.spawn fun _ => Ix.CanonM.canonChunk chunk
        let mut view : Std.HashMap Ix.Name Ix.ConstantInfo := {}
        for task in tasks do
          for (n, ci) in task.get do
            view := view.insert n ci
        for (n, ci) in addedCanon do
          unless view.contains n do view := view.insert n ci
        canonView? := some view
      else
        let tasks := chunkArr.map fun chunk =>
          Task.spawn fun _ => (Ix.CanonM.canonChunk chunk).map fun (n, ci) => (n, hash ci)
        let mut digs : Std.HashMap Ix.Name UInt64 :=
          Std.HashMap.emptyWithCapacity constArr.size
        for task in tasks do
          for (n, d) in task.get do
            digs := digs.insert n d
        for (n, ci) in addedCanon do
          unless digs.contains n do digs := digs.insert n (hash ci)
        canonDigests? := some digs
      let t1 ← IO.monoMsNow
      let failures := out.failures.toMap
      match bound with
      | .error e =>
        phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
          .failed s!"role binding (as compile-lean adds it): {e}")
      | .ok (_, finalizedBytes) =>
        if !failures.isEmpty then
          let shown := failures.toList.take 3
          let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
          phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
            .failed (s!"{failures.size} per-block compile \
failure(s) ({finalizedBytes.size} bytes, {t1 - t0}ms)\n" ++
              String.intercalate "\n" msgs))
        else
          phases ← pushPhase phases ("1. Compile (pure-Lean pipeline)",
            .passed s!"pure-Lean pipeline with the role binding compile-lean adds: \
{finalizedBytes.size} bytes, {out.inputs} input constants, {failures.size} ungrounded, \
{added.size} names added by the binding ({addedCanon.size} with a source) ({t1 - t0}ms)")
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
  let parts? ← match Ixon.deEnvVerifiedLazy bytes with
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

  -- When validating a pre-compiled `.ixe` against a Lean source file, enrich
  -- the decompile oracle and foreign-record list with any role-binding
  -- constants present in the artifact outside the source environment (such as
  -- certificate theorems from `IxCK.Kernel.PinGen.Certs`).
  if reusingIxeWithSource then
    if let (some parts, some leanEnv) := (parts?, leanEnv?) then
      let missingNames : Array Ix.Name := parts.namedRows.filterMap fun row =>
        let inOracle := match canonView?, canonDigests? with
          | some view, _ => view.contains row.name
          | none, some digs => digs.contains row.name
          | none, none => true
        if inOracle then none else some row.name
      if !missingNames.isEmpty then
        let sources ← if missingNames.all fun n => leanEnv.contains (Ix.SemanticContract.toLeanName n) then
            pure #[leanEnv]
          else pure #[leanEnv, ← Ix.RoleBinding.Compile.nativeCertSource]
        let addedConsts : Array (Lean.Name × Lean.ConstantInfo) := missingNames.filterMap fun n =>
          let ln := Ix.SemanticContract.toLeanName n
          (sources.findSome? (·.find? ln)).map (ln, ·)
        let addedCanon := Ix.CanonM.canonChunk addedConsts
        if let some view := canonView? then
          let mut view := view
          for (n, ci) in addedCanon do
            unless view.contains n do view := view.insert n ci
          canonView? := some view
        if let some digs := canonDigests? then
          let mut digs := digs
          for (n, ci) in addedCanon do
            unless digs.contains n do digs := digs.insert n (hash ci)
          canonDigests? := some digs
      let foreignAddrs : Array Address := parts.namedRows.filterMap fun row =>
        let ln := Ix.SemanticContract.toLeanName row.name
        if leanEnv.contains ln then none else some row.addr
      bindingRecords := bindingRecords ++ foreignAddrs
      -- Also include unnamed role-binding records (`generated.support` and
      -- `generated.evidence` added by `Generated.emit` without `named` rows):
      -- every source record in a pre-finalized compile is either named directly
      -- in `parts.namedRows` or is the owning `p.block` of a named projection,
      -- so when `roleBinding` is present, the remaining unnamed records are
      -- exactly the binding's support/evidence records.
      if parts.env.roleBinding.isSome then
        let mut ownedBySource : Std.HashSet Address :=
          Std.HashSet.emptyWithCapacity parts.namedRows.size
        for row in parts.namedRows do
          let ln := Ix.SemanticContract.toLeanName row.name
          if leanEnv.contains ln then
            ownedBySource := ownedBySource.insert row.addr
            if let some lc := parts.env.consts[row.addr]? then
              if lc.len ≤ 64 then
                if let .ok tag := lc.peekTag then
                  if tag == .iPrj || tag == .cPrj || tag == .rPrj || tag == .dPrj then
                    if let .ok c := lc.get then
                      let block? : Option Address := match c.info with
                        | .iPrj p => some p.block
                        | .cPrj p => some p.block
                        | .rPrj p => some p.block
                        | .dPrj p => some p.block
                        | _ => none
                      if let some blk := block? then
                        ownedBySource := ownedBySource.insert blk
        let mut rbAddrs : Array Address := #[]
        for (a, _) in parts.env.consts.toList do
          unless ownedBySource.contains a do
            rbAddrs := rbAddrs.push a
        bindingRecords := bindingRecords ++ rbAddrs

  -- Phases 3, 4, and 5 all read `parts` read-only, so launch whichever are
  -- active concurrently on dedicated tasks and emit their phase reports in
  -- canonical order (3 → 4 → 5).
  let skipPhases := ((← IO.getEnv "IX_SKIP_PHASES").getD "").splitOn ","
  let decompileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 32
  match parts? with
  | none =>
    -- Serde failed: nothing downstream can run.
    leanEnv? := none
    phases ← pushPhase phases ("3. Projection/block-order fidelity", .skipped "serde gate failed")
    phases ← pushPhase phases ("4. Source/reader fidelity", .skipped "serde gate failed")
    phases ← pushPhase phases ("5. Decompile",
      .skipped (if skipPhases.contains "5" then "IX_SKIP_PHASES"
                else "serde gate failed"))
  | some parts =>
    -- Phase 3 task
    let p3Task? : Except PhaseResult (Task (Except IO.Error PhaseResult)) ←
      if skipPhases.contains "3" then
        pure (.error (.skipped "IX_SKIP_PHASES"))
      else do
        let retired ← retiredAnonOptions
        if !retired.isEmpty then
          pure (.error (.failed s!"retired anonymous-roundtrip diagnostics: {", ".intercalate retired.toList}; \
use IX_SKIP_PHASES=3 to skip this phase explicitly"))
        else do
          IO.println "[validate-lean] phase 3: projection/block-order fidelity..."
          let t ← IO.asTask (prio := .dedicated) do
            let t0 ← IO.monoMsNow
            let result := Tests.Ix.Kernel.EgressFidelity.projectionsAccess
              (Ix.KernelFidelity.RecordAccess.ofParts parts)
            let t1 ← IO.monoMsNow
            return match result with
              | .error e => .failed e
              | .ok report => projectionResult report (t1 - t0)
          pure (.ok t)

    -- Phase 4 task
    let p4Task? : Except PhaseResult (Task (Except IO.Error PhaseResult)) ←
      match leanEnv? with
      | none =>
        pure (.error (.skipped "no Lean source env to compare against (--ixe mode)"))
      | some leanEnv => do
        let eager := (← IO.getEnv "IX_META_EAGER").isSome
        IO.println s!"[validate-lean] phase 4: source/reader fidelity ({if eager then "eager diagnostic" else "lazy"})..."
        let t ← IO.asTask (prio := .dedicated) do
          readerPhase do
            if eager then
              -- Explicit whole-store diagnostic, using the preserved eager
              -- wrapper. The default never materializes the full named store.
              let fullEnv ← IO.ofExcept parts.materializeAllNamed
              let input ← Tests.Ix.Kernel.ReaderFidelity.Input.ofEnv leanEnv fullEnv
              let access := Tests.Ix.Kernel.ReaderFidelity.InputAccess.ofInput input
              return { access with foreign := access.foreign ++ bindingRecords }
            else
              let access ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.InputAccess.ofParts leanEnv parts)
              return { access with foreign := access.foreign ++ bindingRecords }
        pure (.ok t)

    -- Release the outer reference to `leanEnv` so it can be reclaimed as soon
    -- as phase 4 completes.
    leanEnv? := none

    -- Phase 5 task
    let p5Task? : Except PhaseResult (Task (Except IO.Error PhaseResult)) ←
      if skipPhases.contains "5" then
        pure (.error (.skipped "IX_SKIP_PHASES"))
      else do
        IO.println "[validate-lean] phase 5: decompiling (full driver)..."
        let t ← IO.asTask (prio := .dedicated) do
          let t0 ← IO.monoMsNow
          match parts.materializeAll with
          | .error e =>
            return .failed s!"named metadata materialization: {e}"
          | .ok ixonEnv =>
            let (decompiled, errs, _p2st) ←
              Ix.DecompileM.decompileEnvFullParallel ixonEnv canonView?
                (numWorkers := decompileWorkers)
            let t1 ← IO.monoMsNow
            if !errs.isEmpty then
              let shown := errs.toList.take 5
              let msgs := shown.map fun (n, m) => s!"    ✗ {n.pretty}: {m.take 160}"
              return .failed (s!"{errs.size} decompile error(s) \
({decompiled.size} constants, {t1 - t0}ms)\n" ++
                String.intercalate "\n" msgs)
            else
              let decArr := decompiled.toArray
              let cmpChunkSize := max 1024 ((decArr.size + max 1 decompileWorkers - 1) / max 1 decompileWorkers)
              let numCmpChunks := (decArr.size + cmpChunkSize - 1) / cmpChunkSize
              match canonView?, canonDigests? with
              | some view, _ =>
                let cmpTasks := (Array.range numCmpChunks).map fun c =>
                  let lo := c * cmpChunkSize
                  let hi := min ((c + 1) * cmpChunkSize) decArr.size
                  Task.spawn fun _ => Id.run do
                    let mut nMatch : Nat := 0
                    let mut mismatches : Array Ix.Name := #[]
                    let mut missing : Nat := 0
                    for (name, info) in decArr.extract lo hi do
                      match view.get? name with
                      | some orig =>
                        if info == orig then nMatch := nMatch + 1
                        else mismatches := mismatches.push name
                      | none => missing := missing + 1
                    return (nMatch, mismatches, missing)
                let mut nMatch : Nat := 0
                let mut mismatches : Array Ix.Name := #[]
                let mut missing : Nat := 0
                for task in cmpTasks do
                  let (nm, mm, ms) := task.get
                  nMatch := nMatch + nm
                  mismatches := mismatches ++ mm
                  missing := missing + ms
                for (name, _) in view do
                  if !decompiled.contains name then
                    missing := missing + 1
                    if mismatches.size < 10 then
                      mismatches := mismatches.push name
                if mismatches.isEmpty && missing == 0 then
                  return .passed s!"{nMatch} constants reconstructed hash-identical \
to the canonicalized source ({t1 - t0}ms)"
                else
                  let msgs := mismatches.toList.take 5 |>.map (s!"    ✗ {·.pretty}")
                  return .failed (s!"{mismatches.size} mismatch(es), {missing} \
missing; {nMatch} matched ({t1 - t0}ms)\n" ++
                    String.intercalate "\n" msgs)
              | none, some digs =>
                let cmpTasks := (Array.range numCmpChunks).map fun c =>
                  let lo := c * cmpChunkSize
                  let hi := min ((c + 1) * cmpChunkSize) decArr.size
                  Task.spawn fun _ => Id.run do
                    let mut nMatch : Nat := 0
                    let mut mismatches : Array Ix.Name := #[]
                    let mut missing : Nat := 0
                    for (name, info) in decArr.extract lo hi do
                      match digs.get? name with
                      | some d =>
                        if hash info == d then nMatch := nMatch + 1
                        else mismatches := mismatches.push name
                      | none => missing := missing + 1
                    return (nMatch, mismatches, missing)
                let mut nMatch : Nat := 0
                let mut mismatches : Array Ix.Name := #[]
                let mut missing : Nat := 0
                for task in cmpTasks do
                  let (nm, mm, ms) := task.get
                  nMatch := nMatch + nm
                  mismatches := mismatches ++ mm
                  missing := missing + ms
                for (name, _) in digs do
                  if !decompiled.contains name then
                    missing := missing + 1
                    if mismatches.size < 10 then
                      mismatches := mismatches.push name
                if mismatches.isEmpty && missing == 0 then
                  return .passed s!"{nMatch} constants reconstructed digest-identical \
to the canonicalized source ({t1 - t0}ms)"
                else
                  let msgs := mismatches.toList.take 5 |>.map (s!"    ✗ {·.pretty}")
                  return .failed (s!"{mismatches.size} digest mismatch(es), {missing} \
missing; {nMatch} matched ({t1 - t0}ms) — rerun with --full-oracle \
--ns <namespace> for a structural diff\n" ++
                    String.intercalate "\n" msgs)
              | none, none =>
                return .passed s!"oracle-free: {decompiled.size} constants decompiled, \
0 errors ({t1 - t0}ms)"
        pure (.ok t)

    (← IO.getStdout).flush

    let awaitPhase (t? : Except PhaseResult (Task (Except IO.Error PhaseResult))) : IO PhaseResult := do
      match t? with
      | .error r => return r
      | .ok task =>
        match ← IO.wait task with
        | .ok r => return r
        | .error e => throw e

    let r3 ← awaitPhase p3Task?
    phases ← pushPhase phases ("3. Projection/block-order fidelity", r3)
    let r4 ← awaitPhase p4Task?
    phases ← pushPhase phases ("4. Source/reader fidelity", r4)
    let r5 ← awaitPhase p5Task?
    phases ← pushPhase phases ("5. Decompile", r5)

  -- Recap (each phase already printed its section heading when it
  -- completed), then a `RESULT:` line.
  IO.println ""
  IO.println "[validate-lean] phase summary:"
  for (name, result) in phases do
    IO.println s!"[validate-lean]   {name}: {result.render}"
  let failures := phases.filter (·.2.isFailure)
  IO.println s!"[validate-lean] RESULT: {failures.size} total failures"
  (← IO.getStdout).flush

  -- `--report`: machine-readable phase table + verdict, the
  -- `ix compile --report` shape (the fidelity suites' gate).
  if let some flag := p.flag? "report" then
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (1 : Nat))
      , ("tool", Lean.Json.str "validate-lean")
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("input", Lean.Json.str (ixe?.getD (path?.getD "")))
      , ("ns", (p.flag? "ns").map (Lean.Json.str <| ·.as! String)
          |>.getD Lean.Json.null)
      , ("phases", phaseRows phases)
      , ("totalFailures", Lean.toJson failures.size)
      , ("passed", Lean.toJson failures.isEmpty) ]
    IO.FS.writeFile (flag.as! String) (report.pretty ++ "\n")

  return if failures.isEmpty then 0 else 1

end Ix.Cli.ValidateLeanCmd

open Ix.Cli.ValidateLeanCmd in
def validateLeanCmd : Cli.Cmd := `[Cli|
  "validate-lean" VIA runValidateLeanCmd;
  "Validate a Lean file through compilation, serde, projection/block-order fidelity, source/reader fidelity and decompilation"

  FLAGS:
    ns  : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are validated; transitive deps are pulled in automatically."
    ixe : String; "Validate a pre-compiled .ixe (with <path>, skips Phase 1 recompilation while keeping source/reader and decompile-oracle checks; without <path>, runs oracle-free phases 2-3 and 5)"
    report : String; "Write a machine-readable JSON report (phase table + pass/fail) to this path."
    workers : Nat; "Worker count for the parallel phases (compile phase 1, decompile phase 5); default 32. Lower at whole-Mathlib scale — memory scales with workers (phase 1 at 32 peaks past 116 GiB there; 8 is a safe whole-Mathlib setting on a 128 GiB box)."
    «full-oracle»; "Phase 5 comparison via the full canonicalized env (structural BEq per constant) instead of the default per-name digests. Holds a whole extra env copy through phase 5 — use on --ns-filtered closures to debug a digest mismatch."

  ARGS:
    ...path : String; "Path to the Lean source file whose env should be validated (omit with --ixe)."
]

end
