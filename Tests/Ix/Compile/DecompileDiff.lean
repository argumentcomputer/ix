/-
  Cross-compiler decompilation inventory — D0 of the decompiler port.

  Rust-compiles the shared aux fixture corpus (`validateAuxClosure` — the
  same corpus the aux-gen-diff gates run on), decompiles the resulting
  Ixon env with the pure-Lean `Ix.DecompileM`, and compares every
  reconstructed constant against the SOURCE `Ix.Environment` by full
  structural equality (`ConstantInfo` BEq — hash-based at the
  Name/Level/Expr leaves, so this is Rust `check_decompile`'s
  `get_hash` comparison at full fidelity).

  Failures are classified into the port's milestone buckets:

    - `callsite` errors — bodies with surgered call-site metadata the
      pure-Lean decompiler cannot replay yet (D1);
    - `aux` names (`isAuxGenSuffix`) — decompiled from the REGENERATED
      canonical constants, expected to mismatch the source's Lean-native
      originals until Pass 2 recovery lands (D3);
    - `plain` mismatches / other errors — the D0 gate: must be ZERO.

  Coverage is checked in both directions: decompiled-but-not-in-source
  (synthetic/alias artifacts) and in-source-but-not-decompiled (skipped
  kinds), each bucketed aux/plain.

  Invoked via `lake test -- --ignored decompile-diff`.
-/
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.DecompileDriver
import Ix.CallSiteSurgery
import Lean
import LSpec
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.AuxGenDiff

namespace Tests.Compile.DecompileDiff

private def sample (xs : Array Ix.Name) (n : Nat := 12) : String :=
  ", ".intercalate ((xs.toList.take n).map (·.pretty))

/-- Aux-family by LINEAGE: the name itself carries an aux-gen suffix, or
    any ancestor does — covering the constructors of synthesized `.below`
    inductives (`Even.below.zero`), which Rust's Pass 2 recovers together
    with their parent. -/
private partial def isAuxLineage (n : Ix.Name) : Bool :=
  if Ix.AuxGen.isAuxGenSuffix n then
    true
  else
    match n with
    | .str parent _ _ => isAuxLineage parent
    | .num parent _ _ => isAuxLineage parent
    | .anonymous _ => false

def run (env : Lean.Environment) : IO UInt32 := do
  IO.println "[decompile-diff] collecting fixture closure..."
  let filtered := validateAuxClosure env
  IO.println s!"[decompile-diff] {filtered.length} constants"

  IO.println "[decompile-diff] Rust compile (rsCompilePhases)..."
  let raw ← Ix.CompileM.rsCompilePhasesFFI filtered
  let rawEnv := raw.rawEnv.toEnvironment
  let rustEnv := raw.compileEnv.toEnv
  IO.println s!"[decompile-diff] Rust: {rustEnv.named.size} named, {rustEnv.consts.size} consts"

  IO.println "[decompile-diff] Lean decompile (full driver: Pass 1 → 1.5 → 2)..."
  let t0 ← IO.monoMsNow
  let origView : Std.HashMap Ix.Name Ix.ConstantInfo := rawEnv.consts
  let (decompiled, errors, p2st) :=
    Ix.DecompileM.decompileEnvFull rustEnv (some origView)
  IO.println s!"[decompile-diff]   {decompiled.size} constants, {errors.size} errors in {(← IO.monoMsNow) - t0}ms"

  -- Error classification.
  let mut callSiteErrs : Array Ix.Name := #[]
  let mut auxErrs : Array Ix.Name := #[]
  let mut otherErrs : Array (Ix.Name × String) := #[]
  for (n, e) in errors do
    if (e.splitOn "call-site surgery").length > 1 then
      callSiteErrs := callSiteErrs.push n
    else if isAuxLineage n then
      auxErrs := auxErrs.push n
    else
      otherErrs := otherErrs.push (n, e)

  -- Forward comparison: every decompiled constant vs the source env.
  let mut plainMatch := (0 : Nat)
  let mut auxMatch := (0 : Nat)
  let mut plainMismatch : Array Ix.Name := #[]
  let mut auxMismatch : Array Ix.Name := #[]
  let mut notInSource : Array Ix.Name := #[]
  for (name, info) in decompiled do
    match rawEnv.consts.get? name with
    | none => notInSource := notInSource.push name
    | some orig =>
      if info == orig then
        if isAuxLineage name then
          auxMatch := auxMatch + 1
        else
          plainMatch := plainMatch + 1
      else
        if isAuxLineage name then
          auxMismatch := auxMismatch.push name
        else
          plainMismatch := plainMismatch.push name

  -- Reverse coverage: source constants never reconstructed. Errored
  -- names are already counted above; exclude them here so the buckets
  -- partition cleanly.
  let mut errNames : Ix.Set Ix.Name := {}
  for (n, _) in errors do
    errNames := errNames.insert n
  let mut missingAux : Array Ix.Name := #[]
  let mut missingPlain : Array Ix.Name := #[]
  for (name, _) in rawEnv.consts do
    if !decompiled.contains name && !errNames.contains name then
      if isAuxLineage name then
        missingAux := missingAux.push name
      else
        missingPlain := missingPlain.push name

  IO.println ""
  IO.println s!"[decompile-diff] decompiled {decompiled.size} constants, {errors.size} errors"
  IO.println s!"[decompile-diff]   plain: {plainMatch} matched, {plainMismatch.size} mismatched  (D0 gate — must be 0)"
  if !plainMismatch.isEmpty then
    IO.println s!"[decompile-diff]     mismatch e.g. {sample plainMismatch}"
  IO.println s!"[decompile-diff]   aux-family: {auxMatch} matched, {auxMismatch.size} mismatched  (red until D3 original recovery)"
  if !auxMismatch.isEmpty then
    IO.println s!"[decompile-diff]     mismatch e.g. {sample auxMismatch}"
  IO.println s!"[decompile-diff]   callsite errors: {callSiteErrs.size}  (D1 gate — must be 0)"
  if !callSiteErrs.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample callSiteErrs}"
  IO.println s!"[decompile-diff]   aux errors: {auxErrs.size}  (red until D3)"
  if !auxErrs.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample auxErrs}"
  IO.println s!"[decompile-diff]   other errors: {otherErrs.size}  (D0 gate — must be 0)"
  for (n, e) in otherErrs.toList.take 8 do
    IO.println s!"[decompile-diff]     {n.pretty}: {e.take 200}"
  IO.println s!"[decompile-diff]   decompiled-not-in-source: {notInSource.size}"
  if !notInSource.isEmpty then
    IO.println s!"[decompile-diff]     e.g. {sample notInSource}"
  IO.println s!"[decompile-diff]   missing from decompile: {missingAux.size} aux, {missingPlain.size} plain"
  if !missingPlain.isEmpty then
    IO.println s!"[decompile-diff]     plain e.g. {sample missingPlain}"

  let gateOk := plainMismatch.isEmpty && otherErrs.isEmpty
    && notInSource.isEmpty && missingPlain.isEmpty
    && callSiteErrs.isEmpty
  IO.println ""
  IO.println s!"[decompile-diff] D0+D1 gate (plain fidelity + callsite replay): {if gateOk then "PASS" else "FAIL"}"

  -- D2+D3 plan gate: the plans installed DURING Pass 2 (against the
  -- evolving work env, exactly Rust's ordering) must now reproduce the
  -- FRESH compile-side plans in full — nested and collapsed-member
  -- lines included.
  IO.println ""
  IO.println "[decompile-diff] D2+D3: Pass-2 plan parity..."
  let csPlans := p2st.callSitePlans
  let brecPlans := p2st.brecOnPlans
  let belowPlans := p2st.belowPlans
  let rehydrateErrs : Array String := #[]
  -- Render in the plans-dump format and compare to the Rust endpoint.
  let dumpBits (bits : Array Bool) : String :=
    String.ofList (bits.toList.map fun b => if b then '1' else '0')
  let dumpNats (xs : Array Nat) : String :=
    ",".intercalate (xs.toList.map fun x =>
      if x == Ix.AuxGen.PERM_OUT_OF_SCC then "out" else toString x)
  let mut rendered := ""
  let sortedCs := (csPlans.toList.map fun (n, p) => (n.pretty, p)).toArray
    |>.qsort (fun a b => a.1 < b.1)
  for (name, p) in sortedCs do
    let head := match p.headRewrite with
      | some h => s!"{h.targetRec.pretty}@{h.targetMotivePos}"
      | none => "none"
    rendered := rendered ++ s!"plan {name} params={p.nParams} smotives={p.nSourceMotives} sminors={p.nSourceMinors} indices={p.nIndices} mkeep={dumpBits p.motiveKeep} nkeep={dumpBits p.minorKeep} m2c={dumpNats p.sourceToCanonMotive} n2c={dumpNats p.sourceToCanonMinor} inblock={dumpBits p.sourceInBlock} head={head}\n"
  for (tag, m) in [("bplan", brecPlans), ("wplan", belowPlans)] do
    let sorted := (m.toList.map fun (n, p) => (n.pretty, p)).toArray
      |>.qsort (fun a b => a.1 < b.1)
    for (name, p) in sorted do
      rendered := rendered ++ s!"{tag} {name} params={p.nParams} smotives={p.nSourceMotives} indices={p.nIndices} mkeep={dumpBits p.motiveKeep} m2c={dumpNats p.sourceToCanonMotive}\n"
  let rustPlansDump ← Tests.Compile.AuxGenDiff.rsAuxGenDumpPlansFFI filtered
  let rustPlanLines := String.intercalate "\n"
    ((rustPlansDump.splitOn "\n").filter fun l =>
      l.startsWith "plan " || l.startsWith "bplan " || l.startsWith "wplan ")
  let renderedLines := String.intercalate "\n"
    ((rendered.splitOn "\n").filter (· != ""))
  -- Set-level diagnostic: which plan names are missing/extra vs fresh.
  let planNameSet (dump : String) : Ix.Set String := Id.run do
    let mut s : Ix.Set String := {}
    for l in dump.splitOn "\n" do
      if l.startsWith "plan " then
        if let some n := (l.splitOn " ")[1]? then
          s := s.insert n
    return s
  let rustNames := planNameSet rustPlanLines
  let leanNames := planNameSet renderedLines
  let mut missingNames : Array String := #[]
  let mut extraNames : Array String := #[]
  for n in rustNames do
    if !leanNames.contains n then missingNames := missingNames.push n
  for n in leanNames do
    if !rustNames.contains n then extraNames := extraNames.push n
  if !missingNames.isEmpty || !extraNames.isEmpty then
    IO.println s!"[decompile-diff]   plan-name sets: {missingNames.size} missing (informational — `rec_N`/collapsed-member plans need D3's regenerated recursors in the work env), {extraNames.size} extra"
    IO.println s!"[decompile-diff]   missing e.g. {", ".intercalate (missingNames.toList.take 10)}"
    if !extraNames.isEmpty then
      IO.println s!"[decompile-diff]   extra e.g. {", ".intercalate (extraNames.toList.take 10)}"
  -- Gate semantics: `plan` lines must match the fresh compile FULLY,
  -- both directions. For derived `bplan`/`wplan` lines the fresh set
  -- must be a byte-exact SUBSET of ours: the decompile-side install
  -- derives additionally for EVAPORATED aux names (its existence guard
  -- consults the work env, which contains their Pass-1-decompiled
  -- surgered originals) — Rust's own decompile does the same
  -- (decompile.rs:4058-4080 `env.contains_key`), so fresh-vs-decompile
  -- extras there are inherent, not drift.
  let splitByPrefix (dump : String) (pfx : String) : List String :=
    (dump.splitOn "\n").filter (·.startsWith pfx)
  let planOnly (dump : String) : String :=
    String.intercalate "\n" (splitByPrefix dump "plan ")
  let d2PlansOk ← Tests.Compile.AuxGenDiff.compareDumps
    (planOnly rustPlanLines) (planOnly renderedLines)
  let mut derivedOk := true
  let mut nDerivedExtra := 0
  for pfx in ["bplan ", "wplan "] do
    let rustL := splitByPrefix rustPlanLines pfx
    let mineL := splitByPrefix renderedLines pfx
    let mineSet : Ix.Set String := mineL.foldl (fun s l => s.insert l) {}
    for l in rustL do
      if !mineSet.contains l then
        derivedOk := false
        IO.println s!"[decompile-diff]   fresh {pfx.trimAscii} line missing from Pass-2 plans: {l.take 200}"
    nDerivedExtra := nDerivedExtra + (mineL.length - rustL.length)
  let d2GateOk := d2PlansOk && derivedOk && rehydrateErrs.isEmpty
  IO.println s!"[decompile-diff] D2+D3 plan gate: {if d2GateOk then "PASS" else "FAIL"} ({sortedCs.size} plans full-parity; {brecPlans.size} bplans, {belowPlans.size} wplans with {nDerivedExtra} evaporated-name extras)"

  -- D3 gate composition: aux-family fidelity must now be total.
  let d3Ok := auxMismatch.isEmpty && auxErrs.isEmpty && missingAux.isEmpty
  IO.println s!"[decompile-diff] D3 gate (aux fidelity): {if d3Ok then "PASS" else "FAIL"}"

  return if gateOk && d2GateOk && d3Ok then 0 else 1

end Tests.Compile.DecompileDiff
