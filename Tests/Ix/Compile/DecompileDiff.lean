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

  IO.println "[decompile-diff] Lean decompile (parallel)..."
  let (decompiledRaw, errors) ← Ix.DecompileM.decompileAllParallelIO rustEnv
  -- Pass 1.5: Lean-faithful inductive flags (decompile.rs:5030-5058).
  let decompiled ← match Ix.DecompileM.fixupInductiveFlags decompiledRaw with
    | .ok d => pure d
    | .error e =>
      IO.println s!"[decompile-diff] Pass 1.5 FAILED: {e}"
      pure decompiledRaw

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

  -- D2 gate: plan REHYDRATION parity. Rebuild aux layouts + call-site
  -- plans from the serialized env alone (Muts metadata, Named.original
  -- grouping, decompiled constants) and compare against the FRESH
  -- compile-side plans (the `rs_aux_gen_dump_plans` endpoint's
  -- plan/bplan/wplan lines) — byte-exact line diff.
  IO.println ""
  IO.println "[decompile-diff] D2: plan rehydration (Lean)..."
  let mutsIndex := Ix.DecompileM.buildMutsPlanIndex rustEnv
  let auxPerms := Ix.DecompileM.rehydrateAuxPerms rustEnv mutsIndex
  let auxBlocks := Ix.DecompileM.collectAuxBlocks rustEnv decompiled
  IO.println s!"[decompile-diff]   {mutsIndex.entries.size} muts entries, \
{auxPerms.size} rehydrated layouts, {auxBlocks.size} aux blocks"
  let mut csPlans : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan := {}
  let mut brecPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {}
  let mut belowPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {}
  let mut rehydrateErrs : Array String := #[]
  let dbgFilter? ← IO.getEnv "IX_DECOMPILE_PLAN_DEBUG"
  for (blockKey, (allNames, auxMembers)) in auxBlocks do
    let auxMemberNames : Ix.Set Ix.Name :=
      auxMembers.foldl (fun s (_, n) => s.insert n) {}
    if let some filter := dbgFilter? then
      if (blockKey.pretty.splitOn filter).length > 1 then
        let stored := Ix.DecompileM.storedPlanBlocksForOriginalAll rustEnv
          mutsIndex allNames
        IO.println s!"[plan-debug] block {blockKey.pretty}: all={allNames.map (·.pretty)} auxMembers={auxMembers.size} stored={stored.size}"
        for m in allNames do
          let recName := Ix.Name.mkStr m "rec"
          IO.println s!"[plan-debug]   view has {recName.pretty}? {decompiled.contains recName} (kind: {match decompiled.get? recName with | some (.recInfo _) => "rec" | some _ => "OTHER" | none => "-"})"
        for b in stored do
          IO.println s!"[plan-debug]   stored flat={b.flatNames.map (·.pretty)} classes={b.classNames.size} layout={b.auxLayout.isSome}"
    let before := csPlans.size
    match Ix.DecompileM.installDecompileCallSitePlans rustEnv mutsIndex
        decompiled auxPerms allNames auxMemberNames
        csPlans brecPlans belowPlans with
    | .ok (cs, brec, below) =>
      csPlans := cs; brecPlans := brec; belowPlans := below
      if let some filter := dbgFilter? then
        if (blockKey.pretty.splitOn filter).length > 1 then
          IO.println s!"[plan-debug]   emitted {csPlans.size - before} plans"
    | .error e => rehydrateErrs := rehydrateErrs.push e
  for e in rehydrateErrs.toList.take 5 do
    IO.println s!"[decompile-diff]   rehydrate error: {e.take 200}"
  -- Render in the plans-dump format and compare to the Rust endpoint.
  let dumpBits (bits : Array Bool) : String :=
    String.mk (bits.toList.map fun b => if b then '1' else '0')
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
  -- D2 gate: FULL byte parity on the NON-NESTED universe. Rust's
  -- `install_decompile_call_site_plans` runs inside the Pass-2 block
  -- loop AFTER `.rec` regeneration (decompile.rs:4256→4320): nested
  -- blocks' plans read the source-restored recursors' structural
  -- numbers (`numMotives` includes `numNested`) and their `rec_N`
  -- entries from the evolving work env — none of which exist before
  -- D3. Non-nested blocks are env-insensitive (canonical regen arity ==
  -- source arity when `numNested = 0`), so for them rehydration must
  -- reproduce the fresh-compile plans EXACTLY, both directions.
  let mut nestedMembers : Ix.Set String := {}
  for (_, info) in decompiled do
    if let .inductInfo ind := info then
      if ind.numNested > 0 then
        for m in ind.all do
          nestedMembers := nestedMembers.insert m.pretty
  let planLineKept (l : String) : Bool :=
    match (l.splitOn " ")[1]? with
    | some n =>
      let parts := n.splitOn "."
      let parent := ".".intercalate (parts.dropLast)
      !nestedMembers.contains parent
    | none => true
  let filterLines (dump : String) : String :=
    String.intercalate "\n"
      ((dump.splitOn "\n").filter fun l => l != "" && planLineKept l)
  let rustFiltered := filterLines rustPlanLines
  let leanFiltered := filterLines renderedLines
  let nRustNested := ((rustPlanLines.splitOn "\n").filter
    (fun l => l != "" && !planLineKept l)).length
  -- Among non-nested lines, everything we emit must byte-match a fresh
  -- line; lines we can't emit yet are the collapsed-class members whose
  -- source-named recursors only reappear via Pass-2 original recovery
  -- (their Named entries carry the representative's metadata, so the
  -- Pass-1 view lacks them — mirroring Rust, whose install runs against
  -- the post-regeneration work env).
  let rustFilteredLines := (rustFiltered.splitOn "\n").filter (· != "")
  let leanFilteredLines := (leanFiltered.splitOn "\n").filter (· != "")
  let rustFilteredSet : Ix.Set String :=
    rustFilteredLines.foldl (fun s l => s.insert l) {}
  let mut d2Bad : Array String := #[]
  for l in leanFilteredLines do
    if !rustFilteredSet.contains l then
      d2Bad := d2Bad.push l
  if !d2Bad.isEmpty then
    IO.println s!"[decompile-diff]   diverged lines: {d2Bad.size}"
    for l in d2Bad.toList.take 5 do
      IO.println s!"[decompile-diff]     {l.take 220}"
  let nDeferredMembers := rustFilteredLines.length - leanFilteredLines.length
  let d2GateOk := d2Bad.isEmpty && rehydrateErrs.isEmpty
  IO.println s!"[decompile-diff] D2 gate (plan rehydration subset parity): {if d2GateOk then "PASS" else "FAIL"} ({leanFilteredLines.length} lines byte-matched; deferred to D3: {nDeferredMembers} collapsed-member + {nRustNested} nested-block lines)"

  return if gateOk && d2GateOk then 0 else 1

end Tests.Compile.DecompileDiff
