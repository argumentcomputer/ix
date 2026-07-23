/-
  Ix.DecompileDriver: decompilation driver passes above the per-constant
  core (`Ix.DecompileM`) — the Lean mirror of `decompile_env`'s pass
  structure (crates/compile/src/decompile.rs:4973-5330).

  Like `Ix.CompileDriver`, this sits ABOVE `Ix.AuxGen` (the per-constant
  core stays a leaf; the driver passes need the aux-gen machinery):

    Pass 1    parallel per-constant decompile — `Ix.DecompileM`
    Pass 1.5  Lean-faithful inductive flags (this module)
    Pass 2    aux regeneration + original recovery (this module, wave-parallel)

  Definitions live in namespace `Ix.DecompileM` so call sites read
  uniformly with the core (same layout convention as `Ix.CompileDriver`
  defining into `Ix.CompileM`).
-/
module
import Std.Sync
public import Ix.Common
public import Ix.Environment
public import Ix.Ixon
public import Ix.DecompileM
public import Ix.CompileM
public import Ix.AuxGen.Nested
public import Ix.AuxGen.Surgery
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Recursor
public import Ix.AuxGen.CasesOn
public import Ix.AuxGen.RecOn
public import Ix.AuxGen.Below
public import Ix.AuxGen.BRecOn
public import Ix.AuxGen.Patches
public import Ix.DecompileRoundtrip
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

/-! ## Plan rehydration — decompile.rs:3682-4087

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
        ((Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan
          × Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan
          × Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan)
          × (Array (Ix.Name × Ix.AuxGen.CallSitePlan)
          × Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan)
          × Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan))) := do
  if allNames.isEmpty then
    return ((callSitePlans, brecOnPlans, belowPlans), (#[], #[], #[]))
  let originalAll := allNames
  let mut planBlocks := storedPlanBlocksForOriginalAll ixonEnv index originalAll
  if planBlocks.isEmpty then
    planBlocks ← fallbackPlanBlocksFromSort decompiledView auxPerms allNames
  let mut callSitePlans := callSitePlans
  let mut brecOnPlans := brecOnPlans
  let mut belowPlans := belowPlans
  let mut newCs : Array (Ix.Name × Ix.AuxGen.CallSitePlan) := #[]
  let mut newBrec : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]
  let mut newBelow : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]
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
          newBrec := newBrec.push
            (breconName, Ix.AuxGen.BRecOnCallSitePlan.fromRecPlan plan)
      if let some belowName := Ix.AuxGen.recNameToBelowName name then
        if (auxMemberNames.contains belowName
              || decompiledView.contains belowName)
            && !belowPlans.contains belowName then
          belowPlans := belowPlans.insert belowName
            (Ix.AuxGen.BRecOnCallSitePlan.fromRecPlan plan)
          newBelow := newBelow.push
            (belowName, Ix.AuxGen.BRecOnCallSitePlan.fromRecPlan plan)
      if !callSitePlans.contains name then
        callSitePlans := callSitePlans.insert name plan
        newCs := newCs.push (name, plan)
  return ((callSitePlans, brecOnPlans, belowPlans), (newCs, newBrec, newBelow))

/-! ## Pass 2 — aux regeneration + original recovery

Mirror of `decompile_block_aux_gen` (decompile.rs:4128-4972) and the
Pass-2 loop of `decompile_env` (decompile.rs:5060-5330), on top of the
roundtrip substrate (`Ix.DecompileRoundtrip`) and the `Ix.AuxGen`
generators (recursor/casesOn/recOn/below/brecOn).

Deliberate deviations, none output-visible:
- The debug-track congruence check (decompile.rs:4938-4952,
  `congruence::const_alpha_eq`) is not ported — the decompile-diff gate
  compares every recovered constant against the source env by full
  hash-equality, which is strictly stronger on the same track.
- Topological order over aux blocks uses a deterministic Kahn queue
  (sorted keys) instead of Rust's reversed Tarjan key iteration; both
  satisfy the only requirement (dependency blocks first), and block
  outputs touch disjoint names beyond that.
- Rust's `KENV_CLEAR_ENTRIES` periodic kenv trim is a memory bound, not
  an input (content-addressed cache) — not mirrored.
- Env-var-gated progress/slow-block diagnostics are not ported. -/

/-- Immutable context of a Pass-2 run. -/
structure Pass2Ctx where
  ixonEnv : Ixon.Env
  mutsIndex : MutsPlanIndex
  /-- `name → addr` view of `ixonEnv.named` (Rust `resolve_addr`'s
      first hop on a deserialized state), precomputed once. -/
  nameToAddr : Std.HashMap Ix.Name Address
  /-- Debug-track source env (Rust `stt.lean_env`). -/
  origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo)

/-- Mutable state threaded through Pass 2. -/
structure Pass2St where
  /-- Generation-visible working env (Rust `work_env`), grows per block. -/
  workEnv : Std.HashMap Ix.Name Ix.ConstantInfo
  /-- Decompiled output env (Rust `dstt.env`). -/
  dstt : Std.HashMap Ix.Name Ix.ConstantInfo
  /-- Kernel bridge context, accumulated across blocks (cold start). -/
  kctx : Ix.AuxGen.AuxKernelCtx
  auxPerms : Std.HashMap Ix.Name Ixon.AuxLayout
  callSitePlans : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan := {}
  brecOnPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {}
  belowPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {}
  ingressed : Ix.Set Ix.Name := {}
  errors : Array (Ix.Name × String) := #[]
  /-- Wave-driver deltas: every insert into `dstt`/`workEnv`/the plan
      maps while processing the CURRENT block, so the parallel Pass-2
      driver can ship exactly one block's outputs from a worker to the
      merge loop. Reset per block by both drivers; content is otherwise
      redundant with the maps. -/
  deltaDstt : Array (Ix.Name × Ix.ConstantInfo) := #[]
  deltaWork : Array (Ix.Name × Ix.ConstantInfo) := #[]
  deltaCs : Array (Ix.Name × Ix.AuxGen.CallSitePlan) := #[]
  deltaBrec : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]
  deltaBelow : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]

instance : Inhabited Pass2St :=
  ⟨{ workEnv := {}, dstt := {}, kctx := Ix.AuxGen.AuxKernelCtx.new
     auxPerms := {} }⟩

/-- One block's outputs, as shipped from a wave worker to the merge
    loop of the parallel Pass-2 driver. Deliberately SLIM: the worker's
    grown kernel context, ingress set, and full env/plan maps stay
    task-local and are dropped when the worker's closure returns —
    shipping whole `Pass2St`s kept every in-flight worker's kernel env
    alive through the result channel (~100 GiB peak on the whole-env
    suite). -/
structure Pass2BlockOut where
  dsttD : Array (Ix.Name × Ix.ConstantInfo) := #[]
  workD : Array (Ix.Name × Ix.ConstantInfo) := #[]
  csD : Array (Ix.Name × Ix.AuxGen.CallSitePlan) := #[]
  brecD : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]
  belowD : Array (Ix.Name × Ix.AuxGen.BRecOnCallSitePlan) := #[]
  errors : Array (Ix.Name × String) := #[]
  deriving Inhabited

/-- Synthetic `CompileEnv` over an env view, with resolution maps from
    the serialized env (the deserialized-state mirror of `stt`). -/
def Pass2Ctx.cenvFor (ctx : Pass2Ctx)
    (view : Std.HashMap Ix.Name Ix.ConstantInfo) : Ix.CompileM.CompileEnv :=
  { env := { consts := view }
    nameToNamed := ctx.ixonEnv.named
    nameToAddr := ctx.nameToAddr
    constants := {}, blobs := {}, totalBytes := 0 }

/-- Run a `KBridgeM` action over the CURRENT work env, threading the
    kernel context. Returns the action result; the caller's state gets
    the updated `kctx`. -/
private def runK (ctx : Pass2Ctx) (st : Pass2St) (lo : Ix.Name)
    (act : Ix.AuxGen.AddrMaps → Ix.AuxGen.KBridgeM α)
    (view? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    : Except String (α × Ix.AuxGen.AuxKernelCtx) :=
  let cenv := ctx.cenvFor (view?.getD st.workEnv)
  let maps := Ix.AuxGen.AddrMaps.ofCompileEnv cenv
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  match Ix.CompileM.CompileM.run cenv blockEnv {} ((act maps).run st.kctx) with
  | .ok ((a, kctx'), _) => .ok (a, kctx')
  | .error e => .error (toString e)

/-- Run a plain `CompileM` action over the current work env. -/
private def runC (ctx : Pass2Ctx) (st : Pass2St) (lo : Ix.Name)
    (act : Ix.CompileM.CompileM α) : Except String α :=
  let cenv := ctx.cenvFor st.workEnv
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  match Ix.CompileM.CompileM.run cenv blockEnv {} act with
  | .ok (a, _) => .ok a
  | .error e => .error (toString e)

/-- Insert into `dstt`, recording the wave-driver delta. Every `dstt`
    insert in Pass 2 goes through this so the parallel driver can ship a
    block's outputs (see `Pass2St.deltaDstt`). -/
private def stPut (st : Pass2St) (n : Ix.Name) (ci : Ix.ConstantInfo)
    : Pass2St :=
  { st with dstt := st.dstt.insert n ci
            deltaDstt := st.deltaDstt.push (n, ci) }

/-- Insert into `workEnv`, recording the wave-driver delta. -/
private def stPutWork (st : Pass2St) (n : Ix.Name) (ci : Ix.ConstantInfo)
    : Pass2St :=
  { st with workEnv := st.workEnv.insert n ci
            deltaWork := st.deltaWork.push (n, ci) }

/-- Insert roundtripped/recovered entries into the decompiled env. -/
private def insertAll (st : Pass2St)
    (entries : Std.HashMap Ix.Name Ix.ConstantInfo) : Pass2St := Id.run do
  let mut st := st
  for (n, ci) in entries do
    st := stPut st n ci
  return st

/-- Recovery-or-fallback for a single aux name (the shared failure arm
    of Phases 1b/1c/2/4: `recover_aux_from_original` then the generated
    form — decompile.rs:4404-4412 et al.). -/
private def recoverOr (ctx : Pass2Ctx) (st : Pass2St) (name : Ix.Name)
    (generatedConsts : Std.HashMap Ix.Name Ix.ConstantInfo) : Pass2St := Id.run do
  let mut st := st
  match recoverAuxFromOriginal name ctx.ixonEnv st.workEnv ctx.origEnv? with
  | some entries =>
    for (n, ci) in entries do
      st := stPut st n ci
  | none =>
    if let some ci := generatedConsts.get? name then
      st := stPut st name ci
  return st

/-- Regenerate + roundtrip one aux block. Mirrors
    `decompile_block_aux_gen` (decompile.rs:4128-4972) phase for phase. -/
def decompileBlockAuxGen (ctx : Pass2Ctx) (st₀ : Pass2St)
    (allNames : Array Ix.Name)
    (auxMembers : Array (Ix.AuxGen.AuxKind × Ix.Name)) : Pass2St := Id.run do
  let mut st := st₀
  let lo := allNames[0]!
  let recordErr (st : Pass2St) (n : Ix.Name) (msg : String) : Pass2St :=
    { st with errors := st.errors.push (n, msg) }

  let mut generatedConsts : Std.HashMap Ix.Name Ix.ConstantInfo := {}

  -- Un-collapsed classes: each inductive in its own singleton class
  -- (decompile.rs:4157-4163, documented divergence from compile's
  -- sort-collapsed classes).
  let classes : Array (Array Ix.Name) := allNames.map (#[·])

  -- Ingress parents + their constructor-type references (:4166-4181).
  let mut ingressNames : Array Ix.Name := allNames
  for n in allNames do
    if let some ci := st.workEnv.get? n then
      let (refs, _) := Ix.GraphM.run { consts := st.workEnv } .init
        (Ix.graphConst ci)
      for r in refs do
        ingressNames := ingressNames.push r
  match runK ctx st lo (fun maps => do
      for n in ingressNames do
        Ix.AuxGen.ensureInKenvOf n maps) with
  | .ok (_, kctx') => st := { st with kctx := kctx' }
  | .error e => st := recordErr st lo s!"aux_gen ingress failed: {e}"

  -- Needed kinds (:4184-4192).
  let needsRec := auxMembers.any (·.1 == .recr)
  let needsBelow := auxMembers.any (·.1 == .below)
  let needsBelowRec := auxMembers.any (·.1 == .belowRec)
  let needsCasesOn := auxMembers.any (·.1 == .casesOnAux)
  let needsRecOn := auxMembers.any (·.1 == .recOnAux)
  let needsBrecon := auxMembers.any fun (k, _) =>
    k == .brecOn || k == .brecOnGo || k == .brecOnEq

  -- Phase 1: canonical recursors in SOURCE-WALK order — aux_layout is
  -- deliberately `none` so discovery order mirrors Lean's elaborator
  -- (decompile.rs:4194-4249; the layout stays rehydrated for surgery).
  let mut canonicalRecs : Array (Ix.Name × Ix.RecursorVal) := #[]
  let mut isProp := false
  if needsRec || needsRecOn || needsCasesOn || needsBelow
      || needsBelowRec || needsBrecon then
    match runK ctx st lo (fun maps =>
        Ix.AuxGen.generateCanonicalRecursorsWithLayout classes none none maps
          none none) with
    | .ok ((recs, p), kctx') =>
      canonicalRecs := recs
      isProp := p
      st := { st with kctx := kctx' }
    | .error e =>
      return recordErr st lo s!"aux_gen rec failed for {lo.pretty}: {e}"
  for (n, rv) in canonicalRecs do
    generatedConsts := generatedConsts.insert n (.recInfo rv)

  -- Insert .rec constants via roundtrip (:4256-4298).
  if needsRec then
    let recMembers : Ix.Set Ix.Name := auxMembers.foldl (init := {})
      fun s (k, n) => if k == .recr then s.insert n else s
    let recMutConsts : List Ix.MutConst :=
      (canonicalRecs.map fun (_, rv) => Ix.MutConst.recr rv).toList
    match roundtripBlock recMutConsts generatedConsts ctx.origEnv?
        st.workEnv ctx.ixonEnv st.callSitePlans st.brecOnPlans st.belowPlans with
    | .ok roundtripped =>
      for (n, ci) in roundtripped do
        if recMembers.contains n || st.workEnv.contains n then
          st := stPut st n ci
    | .error e =>
      for (n, rv) in canonicalRecs do
        if recMembers.contains n then
          st := stPut st n (.recInfo rv)
      st := recordErr st lo s!"roundtrip_block .rec failed: {e}"

  -- Sync generated constants into both envs (:4301-4317).
  let sync (st : Pass2St)
      (gen : Std.HashMap Ix.Name Ix.ConstantInfo) : Pass2St := Id.run do
    let mut st := st
    for (n, ci) in gen do
      if !st.workEnv.contains n then
        st := stPutWork st n ci
      if !st.dstt.contains n then
        st := stPut st n ci
    return st
  st := sync st generatedConsts

  -- Install call-site plans against the post-rec work env (:4320-4327) —
  -- this is where nested/collapsed-member plans become computable.
  let auxMemberNames : Ix.Set Ix.Name :=
    auxMembers.foldl (fun s (_, n) => s.insert n) {}
  match installDecompileCallSitePlans ctx.ixonEnv ctx.mutsIndex st.workEnv
      st.auxPerms allNames auxMemberNames
      st.callSitePlans st.brecOnPlans st.belowPlans with
  | .ok ((cs, brec, below), (newCs, newBrec, newBelow)) =>
    st := { st with callSitePlans := cs, brecOnPlans := brec, belowPlans := below
                    deltaCs := st.deltaCs ++ newCs
                    deltaBrec := st.deltaBrec ++ newBrec
                    deltaBelow := st.deltaBelow ++ newBelow }
  | .error e => st := recordErr st lo e

  -- Phases 1b/1c: .casesOn / .recOn wrappers (:4330-4520). Shared arm.
  let wrapPhase (st₀ : Pass2St)
      (baseGen : Std.HashMap Ix.Name Ix.ConstantInfo)
      (kind : Ix.AuxGen.AuxKind)
      (gen : Pass2St → Ix.Name → Ix.RecursorVal →
        Except String (Option Ix.AuxGen.AuxDef))
      : Pass2St × Std.HashMap Ix.Name Ix.ConstantInfo := Id.run do
    let mut st := st₀
    let mut newGen : Std.HashMap Ix.Name Ix.ConstantInfo := {}
    for (k, wName) in auxMembers do
      if k != kind then continue
      let indName? : Option Ix.Name := match wName with
        | .str parent _ _ => some parent
        | _ => none
      let some indName := indName? | continue
      let recName := Ix.Name.mkStr indName "rec"
      let recVal? : Option Ix.RecursorVal := match st.workEnv.get? recName with
        | some (.recInfo rv) => some rv
        | _ => match st.dstt.get? recName with
          | some (.recInfo rv) => some rv
          | _ => none
      let some recVal := recVal? | continue
      let mut auxDefOpt : Option Ix.AuxGen.AuxDef := none
      match gen st wName recVal with
      | .ok d => auxDefOpt := d
      | .error e => st := recordErr st wName e
      let some auxDef := auxDefOpt | continue
      -- Safety propagation: unsafe `.rec` forces the wrapper unsafe.
      let safetyL : Lean.DefinitionSafety :=
        if recVal.isUnsafe then .unsafe else .safe
      let asDefn : Ix.ConstantInfo := .defnInfo {
        cnst := { name := auxDef.name, levelParams := auxDef.levelParams,
                  type := auxDef.typ }
        value := auxDef.value
        hints := .abbrev
        safety := safetyL
        all := #[auxDef.name] }
      newGen := newGen.insert auxDef.name asDefn
      let mc : Ix.MutConst := .defn {
        name := auxDef.name
        levelParams := auxDef.levelParams
        type := auxDef.typ
        kind := .defn
        value := auxDef.value
        hints := .abbrev
        safety := if recVal.isUnsafe then .unsaf else .safe
        -- Lean emits `.casesOn`/`.recOn` as standalone defnDecls with
        -- `all = [self]` — must mirror or the source-form hash differs.
        all := #[auxDef.name] }
      let allGen := baseGen.fold (fun m k v => m.insert k v) newGen
      match roundtripBlock [mc] allGen ctx.origEnv? st.workEnv ctx.ixonEnv
          st.callSitePlans st.brecOnPlans st.belowPlans with
      | .ok roundtripped =>
        if roundtripped.isEmpty then
          st := recoverOr ctx st auxDef.name allGen
        else
          st := insertAll st roundtripped
      | .error e =>
        st := recoverOr ctx st auxDef.name allGen
        st := recordErr st auxDef.name e
    return (st, newGen)

  if needsCasesOn then
    let (st', gen) := wrapPhase st generatedConsts .casesOnAux
      fun stCur n rv => runC ctx stCur n (Ix.AuxGen.generateCasesOn n rv)
    st := st'
    generatedConsts := gen.fold (fun m k v => m.insert k v) generatedConsts
  if needsRecOn then
    let (st', gen) := wrapPhase st generatedConsts .recOnAux
      fun _ n rv => .ok (Ix.AuxGen.generateRecOn n rv)
    st := st'
    generatedConsts := gen.fold (fun m k v => m.insert k v) generatedConsts

  -- Phase 2: .below constants (:4522-4739).
  let mut belowConsts : Array Ix.AuxGen.BelowConstant := #[]
  if needsBelow || needsBelowRec || needsBrecon then
    match runK ctx st lo (fun maps =>
        Ix.AuxGen.generateBelowConstants classes canonicalRecs isProp maps) with
    | .ok (consts, kctx') =>
      belowConsts := consts
      st := { st with kctx := kctx' }
    | .error e =>
      st := recordErr st lo s!"aux_gen below failed for {lo.pretty}: {e}"
  let allBelowNames : Array Ix.Name := belowConsts.map fun bc =>
    match bc with
    | .indc i => i.name
    | .defn d => d.name
  for bc in belowConsts do
    match bc with
    | .defn d =>
      generatedConsts := generatedConsts.insert d.name (belowDefToLean d)
    | .indc i =>
      let (indVal, ctors) := belowIndcToLean i allBelowNames
      generatedConsts := generatedConsts.insert i.name (.inductInfo indVal)
      for ctor in ctors do
        generatedConsts := generatedConsts.insert ctor.cnst.name (.ctorInfo ctor)
  st := sync st generatedConsts

  if needsBelow then
    let belowMembers : Ix.Set Ix.Name := auxMembers.foldl (init := {})
      fun s (k, n) => if k == .below then s.insert n else s
    -- BelowIndc: one batched roundtrip (:4600-4637).
    let mut belowIndcMcs : List Ix.MutConst := []
    let mut belowIndcBuildErr := false
    for bc in belowConsts do
      if let .indc i := bc then
        let (indVal, _) := belowIndcToLean i allBelowNames
        match runC ctx st i.name (Ix.CompileM.MutConst.mkIndc indVal) with
        | .ok mc => belowIndcMcs := belowIndcMcs ++ [mc]
        | .error e =>
          st := recordErr st i.name s!"below indc mkIndc: {e}"
          belowIndcBuildErr := true
    if belowIndcBuildErr then
      belowIndcMcs := []
    if !belowIndcMcs.isEmpty then
      match roundtripBlock belowIndcMcs generatedConsts ctx.origEnv?
          st.workEnv ctx.ixonEnv st.callSitePlans st.brecOnPlans st.belowPlans with
      | .ok roundtripped => st := insertAll st roundtripped
      | .error e =>
        for bc in belowConsts do
          if let .indc i := bc then
            if belowMembers.contains i.name then
              st := recoverOr ctx st i.name generatedConsts
              st := recordErr st i.name e
    -- BelowDef: individual roundtrips, regen-track members only (:4639-4739).
    for bc in belowConsts do
      let .defn d := bc | continue
      if !belowMembers.contains d.name then continue
      let mc : Ix.MutConst := .defn {
        name := d.name, levelParams := d.levelParams, type := d.typ
        kind := .defn, value := d.value, hints := .abbrev
        safety := if d.isUnsafe then .unsaf else .safe
        all := #[d.name] }
      match roundtripBlock [mc] generatedConsts ctx.origEnv? st.workEnv
          ctx.ixonEnv st.callSitePlans st.brecOnPlans st.belowPlans with
      | .ok roundtripped => st := insertAll st roundtripped
      | .error e =>
        st := recoverOr ctx st d.name generatedConsts
        st := recordErr st d.name e

  -- Phase 3: .below.rec for Prop-level below inductives (:4741-4826).
  if needsBelowRec && isProp then
    let mut belowEnv := buildBlockEnv allNames st.workEnv
    let mut belowClasses : Array (Array Ix.Name) := #[]
    for bc in belowConsts do
      if let .indc i := bc then
        let (indVal, ctors) := belowIndcToLean i allBelowNames
        belowEnv := belowEnv.insert i.name (.inductInfo indVal)
        for ctor in ctors do
          belowEnv := belowEnv.insert ctor.cnst.name (.ctorInfo ctor)
        belowClasses := belowClasses.push #[i.name]
    if !belowClasses.isEmpty then
      match runK ctx st lo (fun maps =>
          Ix.AuxGen.generateCanonicalRecursorsWithOverlay belowClasses none
            none maps) (view? := some belowEnv) with
      | .ok ((belowRecs, _), kctx') =>
        st := { st with kctx := kctx' }
        let belowRecMembers : Ix.Set Ix.Name := auxMembers.foldl (init := {})
          fun s (k, n) => if k == .belowRec then s.insert n else s
        let mcs : List Ix.MutConst := (belowRecs.filterMap fun (n, rv) =>
          if belowRecMembers.contains n then some (Ix.MutConst.recr rv)
          else none).toList
        match roundtripBlock mcs generatedConsts ctx.origEnv? st.workEnv
            ctx.ixonEnv st.callSitePlans st.brecOnPlans st.belowPlans with
        | .ok roundtripped => st := insertAll st roundtripped
        | .error e =>
          for (n, rv) in belowRecs do
            if belowRecMembers.contains n then
              match recoverAuxFromOriginal n ctx.ixonEnv st.workEnv
                  ctx.origEnv? with
              | some entries =>
                for (en, eci) in entries do
                  st := stPut st en eci
              | none =>
                st := stPut st n (.recInfo rv)
              st := recordErr st n e
      | .error e =>
        st := recordErr st lo s!"aux_gen below.rec failed for {lo.pretty}: {e}"

  -- Sync + kenv below-population before brecOn (:4828-4841).
  st := sync st generatedConsts
  if !belowConsts.isEmpty then
    match runK ctx st lo (fun maps =>
        Ix.AuxGen.populateCanonKenvWithBelow belowConsts classes maps) with
    | .ok (_, kctx') => st := { st with kctx := kctx' }
    | .error e => st := recordErr st lo s!"populate_canon_kenv: {e}"

  -- Phase 4: .brecOn / .go / .eq (:4843-4936).
  if needsBrecon then
    match runK ctx st lo (fun maps =>
        Ix.AuxGen.generateBreconConstants classes canonicalRecs belowConsts
          isProp maps) with
    | .ok (breconDefs, kctx') =>
      st := { st with kctx := kctx' }
      for d in breconDefs do
        generatedConsts := generatedConsts.insert d.name (breconDefToLean d)
      let breconMembers : Ix.Set Ix.Name := auxMembers.foldl (init := {})
        fun s (k, n) =>
          if k == .brecOn || k == .brecOnGo || k == .brecOnEq then s.insert n
          else s
      for d in breconDefs do
        if !breconMembers.contains d.name then continue
        -- kind/hints/safety matrix (mirrors `brecon_def_to_lean` /
        -- `brecon_to_mut_const`): unsafe eq/Prop flip Thm → unsafe Defn
        -- with opaque hints.
        let isEq := match Ix.AuxGen.classifyAuxGen d.name with
          | some (.brecOnEq, _) => true
          | _ => false
        let wantsThm := (d.isProp || isEq) && !d.isUnsafe
        let kind : Ix.DefKind := if wantsThm then .thm else .defn
        let hints : Lean.ReducibilityHints :=
          if (d.isUnsafe && (d.isProp || isEq)) || wantsThm then .opaque
          else .abbrev
        let mc : Ix.MutConst := .defn {
          name := d.name, levelParams := d.levelParams, type := d.typ
          kind, value := d.value, hints
          safety := if d.isUnsafe then .unsaf else .safe
          all := #[d.name] }
        match roundtripBlock [mc] generatedConsts ctx.origEnv? st.workEnv
            ctx.ixonEnv st.callSitePlans st.brecOnPlans st.belowPlans with
        | .ok roundtripped =>
          if roundtripped.isEmpty then
            match recoverAuxFromOriginal d.name ctx.ixonEnv st.workEnv
                ctx.origEnv? with
            | some entries =>
              for (en, eci) in entries do
                st := stPut st en eci
            | none =>
              st := stPut st d.name (breconDefToLean d)
          else
            st := insertAll st roundtripped
        | .error e =>
          match recoverAuxFromOriginal d.name ctx.ixonEnv st.workEnv
              ctx.origEnv? with
          | some entries =>
            for (en, eci) in entries do
              st := stPut st en eci
          | none =>
            st := stPut st d.name (breconDefToLean d)
          st := recordErr st d.name e
    | .error e =>
      st := recordErr st lo s!"aux_gen brecOn failed for {lo.pretty}: {e}"

  return st

/-- Pass 2 driver: group aux blocks, topo-sort by cross-block deps, and
    regenerate each (decompile.rs:5060-5330 minus diagnostics). -/
def decompileEnvPass2 (ixonEnv : Ixon.Env)
    (pass1 : Std.HashMap Ix.Name Ix.ConstantInfo)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    : Pass2St := Id.run do
  let mutsIndex := buildMutsPlanIndex ixonEnv
  let auxPerms := rehydrateAuxPerms ixonEnv mutsIndex
  let blocks := collectAuxBlocks ixonEnv pass1
  let ctx : Pass2Ctx := {
    ixonEnv, mutsIndex
    nameToAddr := ixonEnv.named.fold (init := {})
      fun m n named => m.insert n named.addr
    origEnv? }
  -- name → block key (members + their ctors), then block deps
  -- (decompile.rs:5096-5133).
  let mut nameToBlock : Std.HashMap Ix.Name Ix.Name := {}
  for (blockKey, (allNames, _)) in blocks do
    for indName in allNames do
      nameToBlock := nameToBlock.insert indName blockKey
      if let some (.inductInfo v) := pass1.get? indName then
        for ctor in v.ctors do
          nameToBlock := nameToBlock.insert ctor blockKey
  let mut blockDeps : Std.HashMap Ix.Name (Ix.Set Ix.Name) := {}
  for (blockKey, (allNames, _)) in blocks do
    let mut deps : Ix.Set Ix.Name := {}
    -- Graph the parent inductives AND their constructors: the inductive
    -- constant alone doesn't carry field references (`List B` in
    -- `A | mk : List B → …` lives in the ctor's type), and evaporated
    -- `rec_N` plan computation needs the evaporation target's block
    -- (its REGENERATED recursor) merged before this block runs — the
    -- edge only exists through the ctor types.
    let mut graphNames : Array Ix.Name := allNames
    for indName in allNames do
      if let some (.inductInfo v) := pass1.get? indName then
        graphNames := graphNames ++ v.ctors
    for gname in graphNames do
      if let some ci := pass1.get? gname then
        let (refs, _) := Ix.GraphM.run { consts := pass1 } .init
          (Ix.graphConst ci)
        for r in refs do
          if let some depBlock := nameToBlock.get? r then
            if depBlock != blockKey then
              deps := deps.insert depBlock
    blockDeps := blockDeps.insert blockKey deps
  -- Deterministic Kahn topo (sorted keys; a cycle would stall — emit
  -- remaining keys sorted at the end, matching Rust's tolerance of
  -- degenerate orders).
  let sortedKeys := (blockDeps.toList.map (·.1)).toArray.qsort
    (fun a b => a.pretty < b.pretty)
  let mut remainingDeps := blockDeps
  let mut order : Array Ix.Name := #[]
  let mut emitted : Ix.Set Ix.Name := {}
  let mut progress := true
  while progress do
    progress := false
    for k in sortedKeys do
      if emitted.contains k then continue
      let deps := (remainingDeps.get? k).getD {}
      let ready := Id.run do
        for d in deps do
          if !emitted.contains d then return false
        return true
      if ready then
        order := order.push k
        emitted := emitted.insert k
        progress := true
  for k in sortedKeys do
    if !emitted.contains k then
      order := order.push k

  let mut st : Pass2St := {
    workEnv := pass1
    dstt := pass1
    kctx := Ix.AuxGen.AuxKernelCtx.new
    auxPerms }
  -- Cold-start kernel prelude (decompile.rs:5140-5142).
  match runK ctx st (Ix.Name.mkStr Ix.Name.mkAnon "PUnit") (fun maps => do
      Ix.AuxGen.ensurePreludeInKenvOf maps) with
  | .ok (_, kctx') => st := { st with kctx := kctx' }
  | .error e =>
    let errs := st.errors.push (Ix.Name.mkAnon, s!"prelude ingress: {e}")
    st := { st with errors := errs }

  for blockKey in order do
    let some (allNames, auxMembers) := blocks.get? blockKey | continue
    -- Per-block delta reset (bounded memory; the sequential driver
    -- doesn't read the deltas).
    st := { st with deltaDstt := #[], deltaWork := #[]
                    deltaCs := #[], deltaBrec := #[], deltaBelow := #[] }
    -- Transitive BFS ingress with global dedup (decompile.rs:5171-5186).
    let mut stack : Array Ix.Name := allNames
    let mut toIngress : Array Ix.Name := #[]
    while !stack.isEmpty do
      let name := stack.back!
      stack := stack.pop
      if st.ingressed.contains name then continue
      st := { st with ingressed := st.ingressed.insert name }
      toIngress := toIngress.push name
      if let some ci := st.workEnv.get? name then
        let (refs, _) := Ix.GraphM.run { consts := st.workEnv } .init
          (Ix.graphConst ci)
        for r in refs do
          if !st.ingressed.contains r then
            stack := stack.push r
    match runK ctx st blockKey (fun maps => do
        for n in toIngress do
          Ix.AuxGen.ensureInKenvOf n maps) with
    | .ok (_, kctx') => st := { st with kctx := kctx' }
    | .error e =>
      let errs := st.errors.push (blockKey, s!"block ingress: {e}")
      st := { st with errors := errs }
    st := decompileBlockAuxGen ctx st allNames auxMembers

  return st

/-- Parallel Pass 2: wave-based workers over the aux-block dependency
    graph, mirroring `Ix.CompileM.compileEnvParallelAux`. Each worker
    runs `decompileBlockAuxGen` against a SNAPSHOT of the merged state
    (persistent structures make the snapshot free) with a worker-local
    kernel context, and ships exactly its block's outputs via the
    `Pass2St.delta*` channels. The merge loop applies deltas in
    sorted-key order and replays the block's kenv ingress into the
    MASTER kernel context, so later snapshots stay warm — total ingress
    work stays at the sequential driver's level while the regeneration
    (the wall-clock dominator) fans out.

    Output-visible deviation: none for `dstt`/`workEnv`/plan maps
    (block outputs are disjoint per SCC and workers apply the same
    only-if-absent policies against a deps-complete snapshot; verified
    by the whole-env hash-identity suites). The `errors` array is
    ordered by (wave, block key) rather than topo order — diagnostic
    only.

    The default worker count is memory-bound, not core-bound: each
    in-flight block holds its regeneration state plus worker-local
    kernel-context additions, so 16 keeps peak RSS in check at
    whole-env scale. -/
def decompileEnvPass2Parallel (ixonEnv : Ixon.Env)
    (pass1 : Std.HashMap Ix.Name Ix.ConstantInfo)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    (numWorkers : Nat := 16)
    : IO Pass2St := do
  let mutsIndex := buildMutsPlanIndex ixonEnv
  let auxPerms := rehydrateAuxPerms ixonEnv mutsIndex
  let blocks := collectAuxBlocks ixonEnv pass1
  let ctx : Pass2Ctx := {
    ixonEnv, mutsIndex
    nameToAddr := ixonEnv.named.fold (init := {})
      fun m n named => m.insert n named.addr
    origEnv? }
  -- name → block key + block deps, exactly as the sequential driver.
  let mut nameToBlock : Std.HashMap Ix.Name Ix.Name := {}
  for (blockKey, (allNames, _)) in blocks do
    for indName in allNames do
      nameToBlock := nameToBlock.insert indName blockKey
      if let some (.inductInfo v) := pass1.get? indName then
        for ctor in v.ctors do
          nameToBlock := nameToBlock.insert ctor blockKey
  let mut blockDeps : Std.HashMap Ix.Name (Ix.Set Ix.Name) := {}
  for (blockKey, (allNames, _)) in blocks do
    let mut deps : Ix.Set Ix.Name := {}
    -- Graph the parent inductives AND their constructors: the inductive
    -- constant alone doesn't carry field references (`List B` in
    -- `A | mk : List B → …` lives in the ctor's type), and evaporated
    -- `rec_N` plan computation needs the evaporation target's block
    -- (its REGENERATED recursor) merged before this block runs — the
    -- edge only exists through the ctor types.
    let mut graphNames : Array Ix.Name := allNames
    for indName in allNames do
      if let some (.inductInfo v) := pass1.get? indName then
        graphNames := graphNames ++ v.ctors
    for gname in graphNames do
      if let some ci := pass1.get? gname then
        let (refs, _) := Ix.GraphM.run { consts := pass1 } .init
          (Ix.graphConst ci)
        for r in refs do
          if let some depBlock := nameToBlock.get? r then
            if depBlock != blockKey then
              deps := deps.insert depBlock
    blockDeps := blockDeps.insert blockKey deps

  let mut st : Pass2St := {
    workEnv := pass1
    dstt := pass1
    kctx := Ix.AuxGen.AuxKernelCtx.new
    auxPerms }
  match runK ctx st (Ix.Name.mkStr Ix.Name.mkAnon "PUnit") (fun maps => do
      Ix.AuxGen.ensurePreludeInKenvOf maps) with
  | .ok (_, kctx') => st := { st with kctx := kctx' }
  | .error e =>
    st := { st with
      errors := st.errors.push (Ix.Name.mkAnon, s!"prelude ingress: {e}") }

  -- BFS the not-yet-ingressed transitive closure of `allNames` and run
  -- the kenv ingress — the per-block prologue, shared by workers (vs
  -- their snapshot) and the master replay (vs the merged state).
  let ingressBlock (st₀ : Pass2St) (blockKey : Ix.Name)
      (allNames : Array Ix.Name) : Pass2St := Id.run do
    let mut st := st₀
    let mut stack : Array Ix.Name := allNames
    let mut toIngress : Array Ix.Name := #[]
    while !stack.isEmpty do
      let name := stack.back!
      stack := stack.pop
      if st.ingressed.contains name then continue
      st := { st with ingressed := st.ingressed.insert name }
      toIngress := toIngress.push name
      if let some ci := st.workEnv.get? name then
        let (refs, _) := Ix.GraphM.run { consts := st.workEnv } .init
          (Ix.graphConst ci)
        for r in refs do
          if !st.ingressed.contains r then
            stack := stack.push r
    match runK ctx st blockKey (fun maps => do
        for n in toIngress do
          Ix.AuxGen.ensureInKenvOf n maps) with
    | .ok (_, kctx') => st := { st with kctx := kctx' }
    | .error e =>
      st := { st with
        errors := st.errors.push (blockKey, s!"block ingress: {e}") }
    return st

  -- (Slim per-block result — see `Pass2BlockOut`: shipping whole
  -- `Pass2St`s held every in-flight worker's kernel env alive through
  -- the result channel and peaked at ~100 GiB on the whole-env suite.)
  let processBlock (snapshot : Pass2St) (blockKey : Ix.Name)
      (allNames : Array Ix.Name)
      (auxMembers : Array (Ix.AuxGen.AuxKind × Ix.Name))
      : Pass2BlockOut :=
    let st := { snapshot with
      errors := #[], deltaDstt := #[], deltaWork := #[]
      deltaCs := #[], deltaBrec := #[], deltaBelow := #[] }
    let st := ingressBlock st blockKey allNames
    let st := decompileBlockAuxGen ctx st allNames auxMembers
    { dsttD := st.deltaDstt, workD := st.deltaWork, csD := st.deltaCs
      brecD := st.deltaBrec, belowD := st.deltaBelow, errors := st.errors }

  -- Apply a completed block's deltas to the master state and replay its
  -- ingress into the master kernel context. Map merges are
  -- arrival-order-safe (block outputs are disjoint per SCC and workers
  -- already applied the only-if-absent policies against a deps-complete
  -- snapshot); the caller handles deterministic `errors` ordering.
  let mergeBlock (st₀ : Pass2St) (blockKey : Ix.Name)
      (allNames : Array Ix.Name) (out : Pass2BlockOut) : Pass2St := Id.run do
    let mut st := st₀
    for (n, ci) in out.workD do
      if !st.workEnv.contains n then
        st := { st with workEnv := st.workEnv.insert n ci }
    for (n, ci) in out.dsttD do
      st := { st with dstt := st.dstt.insert n ci }
    for (n, p) in out.csD do
      if !st.callSitePlans.contains n then
        st := { st with callSitePlans := st.callSitePlans.insert n p }
    for (n, p) in out.brecD do
      if !st.brecOnPlans.contains n then
        st := { st with brecOnPlans := st.brecOnPlans.insert n p }
    for (n, p) in out.belowD do
      if !st.belowPlans.contains n then
        st := { st with belowPlans := st.belowPlans.insert n p }
    return ingressBlock st blockKey allNames

  let workChan ← Std.CloseableChannel.Sync.new
    (α := Ix.Name × Array Ix.Name × Array (Ix.AuxGen.AuxKind × Ix.Name)
      × Pass2St)
  let resultChan ← Std.CloseableChannel.Sync.new
    (α := Ix.Name × Pass2BlockOut)
  let worker (_i : Nat) : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break
      | some (blockKey, allNames, auxMembers, snapshot) =>
        let out := processBlock snapshot blockKey allNames auxMembers
        discard <| resultChan.send (blockKey, out)
  let mut workerTasks : Array (Task (Except IO.Error Unit)) := #[]
  for i in [:numWorkers] do
    workerTasks := workerTasks.push (← IO.asTask (prio := .dedicated) (worker i))

  let mut remaining : Ix.Set Ix.Name := {}
  for (blockKey, _) in blocks do
    remaining := remaining.insert blockKey
  let mut merged : Ix.Set Ix.Name := {}

  while !remaining.isEmpty do
    let mut ready : Array Ix.Name := #[]
    for k in remaining do
      let deps := (blockDeps.get? k).getD {}
      let ok := Id.run do
        for d in deps do
          if remaining.contains d && !merged.contains d then return false
        return true
      if ok then ready := ready.push k
    -- Debug/bisection aid: 1-worker mode degenerates to 1-block waves —
    -- merge between every block, i.e. exact sequential-driver semantics
    -- through the parallel machinery.
    if numWorkers == 1 && ready.size > 1 then
      ready := (ready.qsort (fun a b => a.pretty < b.pretty)).take 1
    if ready.isEmpty then
      -- Degenerate cycle tolerance: mirror the sequential Kahn tail by
      -- running the rest one at a time (sorted), merging between.
      let mut rest : Array Ix.Name := #[]
      for k in remaining do rest := rest.push k
      rest := rest.qsort (fun a b => a.pretty < b.pretty)
      for k in rest do
        let some (allNames, auxMembers) := blocks.get? k | continue
        let out := processBlock st k allNames auxMembers
        st := mergeBlock st k allNames out
        st := { st with errors := st.errors ++ out.errors }
      remaining := {}
      break
    for k in ready do
      let some (allNames, auxMembers) := blocks.get? k | continue
      discard <| workChan.send (k, allNames, auxMembers, st)
    -- Merge each result as it arrives — holding a whole wave of results
    -- is exactly the memory cliff the slim deltas exist to avoid. Map
    -- contents are arrival-order-independent; errors are batched and
    -- appended in sorted-key order at wave end for determinism.
    let mut errBatch : Array (Ix.Name × Array (Ix.Name × String)) := #[]
    for _ in [:ready.size] do
      match ← resultChan.recv with
      | none => break
      | some (blockKey, out) =>
        let allNames := ((blocks.get? blockKey).map (·.1)).getD #[]
        st := mergeBlock st blockKey allNames out
        merged := merged.insert blockKey
        if !out.errors.isEmpty then
          errBatch := errBatch.push (blockKey, out.errors)
    errBatch := errBatch.qsort (fun a b => a.1.pretty < b.1.pretty)
    for (_, errs) in errBatch do
      st := { st with errors := st.errors ++ errs }
    for k in ready do
      remaining := remaining.erase k

  discard <| workChan.close
  return st

/-- Full decompile driver: Pass 1 (aux skipped) → Pass 1.5 flags →
    Pass 2 regeneration/recovery. Returns the decompiled env, the
    per-name errors from both passes, and the final Pass-2 state (plan
    maps for callers that recompile). -/
def decompileEnvFull (ixonEnv : Ixon.Env)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    : Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String) × Pass2St := Id.run do
  let (pass1Raw, pass1Errs) := decompileAllParallel ixonEnv
    (skip := fun n named =>
      named.original.isSome && Ix.AuxGen.isAuxGenSuffix n)
  let pass1 := match fixupInductiveFlags pass1Raw with
    | .ok fixed => fixed
    | .error _ => pass1Raw
  let st := decompileEnvPass2 ixonEnv pass1 origEnv?
  return (st.dstt, pass1Errs ++ st.errors, st)

/-- `decompileEnvFull` with the wave-parallel Pass 2
    (`decompileEnvPass2Parallel`). Same outputs — hash-identity is
    enforced by the whole-env decompile suites — with Pass-2 errors in
    merge order rather than topo order. -/
def decompileEnvFullParallel (ixonEnv : Ixon.Env)
    (origEnv? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none)
    (numWorkers : Nat := 16)
    : IO (Std.HashMap Ix.Name Ix.ConstantInfo × Array (Ix.Name × String)
      × Pass2St) := do
  -- `IX_DECOMPILE_WORKERS` overrides the worker count (memory/debug
  -- tuning); `0` selects the sequential Pass-2 driver.
  let numWorkers ← do
    match (← IO.getEnv "IX_DECOMPILE_WORKERS").bind (·.toNat?) with
    | some n => pure n
    | none => pure numWorkers
  let (pass1Raw, pass1Errs) := decompileAllParallel ixonEnv
    (skip := fun n named =>
      named.original.isSome && Ix.AuxGen.isAuxGenSuffix n)
  let pass1 := match fixupInductiveFlags pass1Raw with
    | .ok fixed => fixed
    | .error _ => pass1Raw
  if numWorkers == 0 then
    let st := decompileEnvPass2 ixonEnv pass1 origEnv?
    return (st.dstt, pass1Errs ++ st.errors, st)
  let st ← decompileEnvPass2Parallel ixonEnv pass1 origEnv? numWorkers
  return (st.dstt, pass1Errs ++ st.errors, st)

end Ix.DecompileM
