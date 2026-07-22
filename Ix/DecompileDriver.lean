/-
  Ix.DecompileDriver: decompilation driver passes above the per-constant
  core (`Ix.DecompileM`) — the Lean mirror of `decompile_env`'s pass
  structure (crates/compile/src/decompile.rs:4973-5330).

  Like `Ix.CompileDriver`, this sits ABOVE `Ix.AuxGen` (the per-constant
  core stays a leaf; the driver passes need the aux-gen machinery):

    Pass 1    parallel per-constant decompile — `Ix.DecompileM`
    Pass 1.5  Lean-faithful inductive flags (this module, D0)
    Pass 2    aux-original recovery — D3, not yet ported

  Definitions live in namespace `Ix.DecompileM` so call sites read
  uniformly with the core (same layout convention as `Ix.CompileDriver`
  defining into `Ix.CompileM`).
-/
module
public import Ix.Common
public import Ix.Environment
public import Ix.Ixon
public import Ix.DecompileM
public import Ix.CompileM
public import Ix.AuxGen.Nested
public import Ix.AuxGen.Surgery
public section

namespace Ix.DecompileM

/-- Pass 1.5: restore Lean-faithful inductive flags. Ixon deliberately
    does not store `numNested`/`isRec`/`isReflexive` (they are derivable),
    so `decompileInductive` stubs them; this pass recomputes them per
    original mutual group FROM THE DECOMPILED CONSTANTS via the aux-gen
    expansion machinery — mirroring Rust `decompile_env`'s Pass 1.5
    (decompile.rs:5030-5058), which calls the same
    `compute_lean_ind_flags` (ported as `Ix.AuxGen.computeLeanIndFlags`,
    nested.rs:1416).

    Groups key on `all[0]` (every member carries the same `all`, so
    first-seen insertion order is irrelevant). The flags computation runs
    in `CompileM` over a synthetic `CompileEnv` whose source env IS the
    decompiled map — the same self-referential view Rust passes. -/
def fixupInductiveFlags (decompiled : Std.HashMap Ix.Name Ix.ConstantInfo)
    : Except String (Std.HashMap Ix.Name Ix.ConstantInfo) := Id.run do
  let mut groups : Std.HashMap Ix.Name (Array Ix.Name) := {}
  for (_, info) in decompiled do
    if let .inductInfo v := info then
      if let some first := v.all[0]? then
        if !groups.contains first then
          groups := groups.insert first v.all
  let cenv := Ix.CompileM.CompileEnv.new { consts := decompiled }
  let mut result := decompiled
  for (key, all) in groups do
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := key, mutCtx := default, univCtx := [] }
    match Ix.CompileM.CompileM.run cenv blockEnv {}
        (Ix.AuxGen.computeLeanIndFlags all) with
    | .error e =>
      return .error s!"ind-flags fixup for block '{key.pretty}': {e}"
    | .ok (flags, _) =>
      for member in all do
        if let some (.inductInfo v) := result.get? member then
          result := result.insert member (.inductInfo { v with
            numNested := flags.numNested
            isRec := flags.isRec
            isReflexive := flags.isReflexive })
  return .ok result

/-! ## Plan rehydration — decompile.rs:3682-4087 (D2)

A DESERIALIZED env has empty in-memory plan state (`aux_perms` and the
call-site plan maps were compile-time only). Pass 2's regeneration and
any roundtrip recompiles need them back, reconstructed from what DID
survive serialization: the `Muts` metadata entries' class lists and
`AuxLayout` payloads. -/

/-- One `Muts`-tagged Named entry, class addresses resolved to names.
    Mirrors Rust `MutsIndexEntry` (decompile.rs). -/
structure MutsIndexEntry where
  classNames : Array (Array Ix.Name)
  flatNames : Array Ix.Name
  auxLayout : Option Ixon.AuxLayout
  deriving Inhabited

/-- Index of every Muts-tagged Named entry, plus a member-name → entry
    index for candidate lookup. Mirrors Rust `MutsPlanIndex`
    (`build_muts_plan_index`, decompile.rs:3839). -/
structure MutsPlanIndex where
  entries : Array MutsIndexEntry
  byMember : Std.HashMap Ix.Name (Array Nat)
  deriving Inhabited

/-- Resolve an address list through the env names table; `none` if any
    address is unnamed (Rust `names_from_addrs`, decompile.rs:3885). -/
private def namesFromAddrs (ixonEnv : Ixon.Env) (addrs : Array Address)
    : Option (Array Ix.Name) := Id.run do
  let mut out : Array Ix.Name := #[]
  for addr in addrs do
    match ixonEnv.names.get? addr with
    | some n => out := out.push n
    | none => return none
  return some out

/-- Mirrors Rust `build_muts_plan_index` (decompile.rs:3839): one scan
    over the named table collecting Muts metadata (sequential here;
    Rust parallelizes the same per-entry filter_map). -/
def buildMutsPlanIndex (ixonEnv : Ixon.Env) : MutsPlanIndex := Id.run do
  let mut entries : Array MutsIndexEntry := #[]
  for (_, named) in ixonEnv.named do
    if let .muts all auxLayout := named.constMeta.info then
      let mut classNames : Array (Array Ix.Name) := #[]
      let mut flatNames : Array Ix.Name := #[]
      let mut ok := true
      for cls in all do
        if !ok then continue
        match namesFromAddrs ixonEnv cls with
        | some names =>
          if names.isEmpty then
            ok := false
          else
            flatNames := flatNames ++ names
            classNames := classNames.push names
        | none => ok := false
      if ok && !flatNames.isEmpty then
        entries := entries.push { classNames, flatNames, auxLayout }
  let mut byMember : Std.HashMap Ix.Name (Array Nat) := {}
  for h : i in [:entries.size] do
    for name in entries[i].flatNames do
      byMember := byMember.alter name fun
        | some arr => some (arr.push i)
        | none => some #[i]
  return { entries, byMember }

/-- Source-order `all` (as names) from a member's Indc metadata
    (Rust `indc_source_all`, decompile.rs:3892). -/
private def indcSourceAll (ixonEnv : Ixon.Env) (name : Ix.Name)
    : Option (Array Ix.Name) := do
  let named ← ixonEnv.named.get? name
  match named.constMeta.info with
  | .indc _ _ _ all .. => namesFromAddrs ixonEnv all
  | _ => none

/-- Rehydrated aux layouts keyed by the SOURCE block's first name (Rust
    `stt.aux_perms` after `rehydrate_aux_perms_from_env`,
    decompile.rs:3682): for each Muts entry carrying a stored
    `AuxLayout`, the source-order `all` is read off the first canonical
    class representative's Indc metadata, and the layout is registered
    under `all[0]` (first entry wins — matching Rust's
    populate-if-absent). -/
def rehydrateAuxPerms (ixonEnv : Ixon.Env) (index : MutsPlanIndex)
    : Std.HashMap Ix.Name Ixon.AuxLayout := Id.run do
  let mut auxPerms : Std.HashMap Ix.Name Ixon.AuxLayout := {}
  for entry in index.entries do
    let some auxLayout := entry.auxLayout | continue
    let some firstClass := entry.classNames[0]? | continue
    let some firstRep := firstClass[0]? | continue
    let some repNamed := ixonEnv.named.get? firstRep | continue
    let sourceAllAddrs := match repNamed.constMeta.info with
      | .indc _ _ _ all .. => all
      | _ => #[]
    if sourceAllAddrs.isEmpty then continue
    let some sourceFirst := ixonEnv.names.get? sourceAllAddrs[0]! | continue
    if !auxPerms.contains sourceFirst then
      auxPerms := auxPerms.insert sourceFirst auxLayout
  return auxPerms

/-- A candidate plan block: canonical class layout + stored aux layout.
    Mirrors Rust `StoredPlanBlock` (decompile.rs:3781). -/
structure StoredPlanBlock where
  classNames : Array (Array Ix.Name)
  auxLayout : Option Ixon.AuxLayout
  flatNames : Array Ix.Name
  deriving Inhabited

/-- Persisted plan blocks whose members all belong to `originalAll` and
    whose Indc metadata confirms the same source block. Prefers minimal
    SCCs: a candidate that strictly contains a smaller candidate is
    dropped (a stale full-source block would recreate an over-merged
    plan). Mirrors Rust `stored_plan_blocks_for_original_all`
    (decompile.rs:3900). -/
def storedPlanBlocksForOriginalAll (ixonEnv : Ixon.Env)
    (index : MutsPlanIndex) (originalAll : Array Ix.Name)
    : Array StoredPlanBlock := Id.run do
  let originalSet : Ix.Set Ix.Name :=
    originalAll.foldl (fun s n => s.insert n) {}
  -- Candidate ids via the by-member index, sorted + deduped.
  let mut candidateIds : Array Nat := #[]
  for n in originalAll do
    if let some ids := index.byMember.get? n then
      candidateIds := candidateIds ++ ids
  let sortedIds := candidateIds.qsort (· < ·)
  let mut dedupIds : Array Nat := #[]
  for id in sortedIds do
    if dedupIds.back? != some id then
      dedupIds := dedupIds.push id
  let mut candidates : Array StoredPlanBlock := #[]
  let mut seen : Std.HashSet (List Ix.Name) := {}
  for id in dedupIds do
    let some entry := index.entries[id]? | continue
    if !entry.flatNames.all (originalSet.contains ·) then
      continue
    let sameSourceAll := entry.flatNames.any fun name =>
      match indcSourceAll ixonEnv name with
      | some sourceAll => sourceAll == originalAll
      | none => false
    if !sameSourceAll then
      continue
    let key := entry.flatNames.toList
    if seen.contains key then
      continue
    seen := seen.insert key
    candidates := candidates.push
      { classNames := entry.classNames
        auxLayout := entry.auxLayout
        flatNames := entry.flatNames }
  -- Minimal-SCC preference.
  return candidates.filter fun candidate => Id.run do
    let candidateSet : Ix.Set Ix.Name :=
      candidate.flatNames.foldl (fun s n => s.insert n) {}
    for other in candidates do
      if other.flatNames.size < candidate.flatNames.size
          && other.flatNames.all (candidateSet.contains ·) then
        return false
    return true

/-- Fallback when no persisted block matched: re-derive the canonical
    classes by running `sortConsts` over the block's (decompiled)
    inductives, pairing with the rehydrated aux layout. Mirrors Rust
    `fallback_plan_blocks_from_sort` (decompile.rs:3960) +
    `block_mut_consts_from_env` (decompile.rs:3742). -/
def fallbackPlanBlocksFromSort
    (decompiledView : Std.HashMap Ix.Name Ix.ConstantInfo)
    (auxPerms : Std.HashMap Ix.Name Ixon.AuxLayout)
    (allNames : Array Ix.Name)
    : Except String (Array StoredPlanBlock) := do
  let cenv := Ix.CompileM.CompileEnv.new { consts := decompiledView }
  let lo := allNames[0]?.getD Ix.Name.mkAnon
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let sorted ← match Ix.CompileM.CompileM.run cenv blockEnv {} (do
      let mut cs : Array Ix.MutConst := #[]
      for n in allNames do
        match ← Ix.CompileM.findConst n with
        | .inductInfo val => cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
        | other =>
          throw (.invalidMutualBlock s!"decompile aux plan: block member \
'{n.pretty}' is not an inductive ({other.getCnst.name.pretty})")
      Ix.CompileM.sortConsts cs.toList) with
    | .ok (sorted, _) => pure sorted
    | .error e => throw s!"decompile aux plan sort_consts: {e}"
  if sorted.isEmpty then
    return #[]
  let classNames : Array (Array Ix.Name) :=
    sorted.toArray.map fun cls => cls.toArray.map (·.name)
  let auxLayout := allNames[0]?.bind (auxPerms.get? ·)
  let flatNames := classNames.flatten
  return #[{ classNames, auxLayout, flatNames }]

/-- Group aux_gen constants (named entries with `original` set) by
    source mutual block, keyed on the decompiled root inductive's
    `all[0]`, carrying the block's `all` and its (kind, name) aux
    members. Mirrors the Pass-2 grouping (decompile.rs:5072-5093).
    Member-list order follows map iteration (Rust: DashMap) — consumers
    must be order-insensitive. -/
def collectAuxBlocks (ixonEnv : Ixon.Env)
    (decompiledView : Std.HashMap Ix.Name Ix.ConstantInfo)
    : Std.HashMap Ix.Name
        (Array Ix.Name × Array (Ix.AuxGen.AuxKind × Ix.Name)) := Id.run do
  let mut blocks : Std.HashMap Ix.Name
      (Array Ix.Name × Array (Ix.AuxGen.AuxKind × Ix.Name)) := {}
  for (name, named) in ixonEnv.named do
    if named.original.isNone then
      continue
    let some (kind, root) := Ix.AuxGen.classifyAuxGen name | continue
    let allNames := match decompiledView.get? root with
      | some (.inductInfo ind) => ind.all
      | _ => #[]
    if allNames.isEmpty then
      continue
    let blockKey := allNames[0]!
    blocks := blocks.alter blockKey fun
      | some (all, members) => some (all, members.push (kind, name))
      | none => some (allNames, #[(kind, name)])
  return blocks

/-- Install call-site plans for a decompiled aux block: persisted plan
    blocks (or the sort fallback), the layout-changed guards, and
    `computeCallSitePlans` over the decompiled env — inserting each
    plan (and the derived `.brecOn`/`.below` plans) only if absent.
    Mirrors Rust `install_decompile_call_site_plans`
    (decompile.rs:3991). Returns the updated plan maps. -/
def installDecompileCallSitePlans
    (ixonEnv : Ixon.Env) (index : MutsPlanIndex)
    (decompiledView : Std.HashMap Ix.Name Ix.ConstantInfo)
    (auxPerms : Std.HashMap Ix.Name Ixon.AuxLayout)
    (allNames : Array Ix.Name) (auxMemberNames : Ix.Set Ix.Name)
    (callSitePlans : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan)
    (brecOnPlans belowPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan)
    : Except String
        (Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan
          × Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan
          × Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan) := do
  if allNames.isEmpty then
    return (callSitePlans, brecOnPlans, belowPlans)
  let originalAll := allNames
  let mut planBlocks := storedPlanBlocksForOriginalAll ixonEnv index originalAll
  if planBlocks.isEmpty then
    planBlocks ← fallbackPlanBlocksFromSort decompiledView auxPerms allNames
  let mut callSitePlans := callSitePlans
  let mut brecOnPlans := brecOnPlans
  let mut belowPlans := belowPlans
  for block in planBlocks do
    if block.classNames.isEmpty then
      continue
    let userLayoutChanged := block.classNames.size < originalAll.size
      || (block.classNames.size == originalAll.size
        && (block.classNames.zip originalAll).any fun (cls, orig) =>
          cls[0]? != some orig)
    let auxLayoutChanged := match block.auxLayout with
      | some layout => layout.perm.zipIdx.any fun (canonicalI, sourceJ) =>
          canonicalI.toNat != Ix.AuxGen.PERM_OUT_OF_SCC
            && canonicalI.toNat != sourceJ
      | none => false
    if !userLayoutChanged && !auxLayoutChanged then
      continue
    let cenv := Ix.CompileM.CompileEnv.new { consts := decompiledView }
    let blockEnv : Ix.CompileM.BlockEnv :=
      { all := {}, current := originalAll[0]!, mutCtx := default, univCtx := [] }
    let plans ← match Ix.CompileM.CompileM.run cenv blockEnv {}
        (Ix.AuxGen.computeCallSitePlans block.classNames originalAll
          block.auxLayout) with
      | .ok (plans, _) => pure plans
      | .error e => throw s!"decompile aux plan compute_call_site_plans: {e}"
    for (name, plan) in plans do
      if let some breconName := Ix.AuxGen.recNameToBreconName name then
        if (auxMemberNames.contains breconName
              || decompiledView.contains breconName)
            && !brecOnPlans.contains breconName then
          brecOnPlans := brecOnPlans.insert breconName
            (Ix.AuxGen.BRecOnCallSitePlan.fromRecPlan plan)
      if let some belowName := Ix.AuxGen.recNameToBelowName name then
        if (auxMemberNames.contains belowName
              || decompiledView.contains belowName)
            && !belowPlans.contains belowName then
          belowPlans := belowPlans.insert belowName
            (Ix.AuxGen.BRecOnCallSitePlan.fromRecPlan plan)
      if !callSitePlans.contains name then
        callSitePlans := callSitePlans.insert name plan
  return (callSitePlans, brecOnPlans, belowPlans)

end Ix.DecompileM
