/-
  Ix.CompileDriver: the aux-aware compile-env driver.

  Port of the production scheduler semantics of
  `crates/compile/src/compile/env.rs` (`compile_env_with_options`,
  env.rs:146-990) and the per-block dispatch of `compile_const` /
  `compile_const_no_aux` (compile.rs:3249-3716), on top of the pure
  block compiler (`Ix.CompileM`) and the aux-generation tail
  (`Ix.AuxGen.CompileAux.compileMutualAuxTail`).

  This module sits ABOVE `Ix.AuxGen` (unlike Rust, where everything
  shares one crate): `Ix.CompileM` cannot invoke the aux tail without an
  import cycle, so the environment drivers live here.

  Deliberate deviations from Rust, none output-visible:
  - Sequential scheduling instead of work-stealing threads. Output maps
    are keyed by name/address. Name claims (`nameToAddr`,
    `auxNameToAddr`) and call-site plans are insert-once: a second claim
    at a different address, or a different plan, is the error Rust's
    insert-once claims raise (`checkBlockClaims`, single ownership).
    `Named` entries are last-wins overrides within one block's
    registrations, and constants and blobs are content-keyed. So
    scheduling order does not affect the result (Rust relies on the same
    property for its nondeterministic work-stealing order).
  - A fresh `AuxKernelCtx` per block instead of Rust's per-worker
    `KernelCtx` reused across blocks (cleared every `KENV_CLEAR_EVERY`).
    The kernel env is content-addressed, so reuse is a cache, not an
    input — the aux-gen-diff dump gates verified byte-identical aux
    output under fresh-per-block contexts.
  - `stt.aux_perms` is not accumulated (its only consumer is the
    decompiler, which is out of scope); the per-block `AuxLayout` still
    flows through the tail into plan computation and the re-registered
    `Muts` entries.
-/
module
import Std.Sync
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.CanonM
public import Ix.Ground
public import Ix.CompileM
public import Ix.Compile.Publication
public import Ix.AuxGen.CompileAux
public import Ix.Compile.SourceContract.Transport
public import Ix.Resource.Addressed
public section

namespace Ix.CompileM

open Ix.AuxGen (CallSitePlan BRecOnCallSitePlan)

/-- Pure `stt.resolve_addr` over the merged driver state
    (compile.rs:261-274): `name_to_addr` then `aux_name_to_addr`. -/
def resolveAddrPure (cenv : CompileEnv) (name : Name) : Option Address :=
  match cenv.nameToAddr.get? name with
  | some a => some a
  | none => cenv.auxNameToAddr.get? name

/-- The canonical key of a set of names: its earliest member in seed order
    (`aliasPrecedes`), `dflt` for the empty set. The drivers name a block by
    this key, never by the condensation's representative (the Tarjan root,
    which depends on the graph's iteration order and so differs between a
    closure compile, the whole compile and the Rust condensation) nor by the
    first element of a `Set` in iteration order. -/
def canonicalKey (dflt : Name) (names : Array Name) : Name :=
  names.foldl (init := names[0]?.getD dflt) fun k n => if aliasPrecedes n k then n else k

/-- `canonicalKey` of a block's member set. -/
def blockKey (lo : Name) (all : Set Name) : Name :=
  canonicalKey lo all.toArray

/-- Compile one SCC block WITH the aux-generation tail. Mirrors the
    `aux=true` route of `compile_const_inner` (compile.rs:3444-3716):
    singleton non-inductive constants take the plain single-constant
    path (no tail); mutual blocks and inductives (of any size) go
    through `compileMutualBlock` followed by `compileMutualAuxTail`
    (Rust `compile_mutual`, compile.rs:3719-4144).

    Between the primary compile and the tail, the members' projection
    addresses are inserted into `BlockState.blockNameToAddr` — Rust
    writes them into the global `name_to_addr` at exactly that point
    (compile.rs:3926/3946/3966), and the tail's aux compilation resolves
    sibling members through them. -/
def compileBlockWithAux (lo : Name) (all : Set Name)
    : CompileM (BlockResult × Option Ixon.AuxLayout
        × Std.HashMap Name CallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan) := do
  let const ← findConst lo
  let isIndBlock := match const with
    | .inductInfo _ | .ctorInfo _ => true
    | _ => false
  if all.size == 1 && !isIndBlock then
    let result ← compileConstantInfo const
    return (result, none, {}, {}, {})
  let mut cs : Array MutConst := #[]
  for n in all do
    match ← findConst n with
    | .inductInfo val => cs := cs.push (← MutConst.mkIndc val)
    | .defnInfo val => cs := cs.push (MutConst.fromDefinitionVal val)
    | .opaqueInfo val => cs := cs.push (MutConst.fromOpaqueVal val)
    | .thmInfo val => cs := cs.push (MutConst.fromTheoremVal val)
    | .recInfo val => cs := cs.push (.recr val)
    | _ => continue
  let sortedClasses ← sortConsts cs.toList
  let blockResult ← compileMutualBlock sortedClasses
  -- Alpha-collapsed standalone (single non-inductive class): Rust
  -- returns BEFORE the Muts registration and the aux tail
  -- (compile.rs:3872) — no synthetic Muts entry, no aux regeneration.
  let isMuts := match blockResult.block.info with
    | .muts _ => true
    | _ => false
  if !isMuts then
    return (blockResult, none, {}, {}, {})
  -- Primary member registrations, visible to the tail (compile.rs:3902+).
  for (name, proj, _) in blockResult.projections do
    let projAddr := Address.admissionHash (Ixon.ser proj)
    modifyBlockState fun st =>
      { st with blockNameToAddr := st.blockNameToAddr.insert name projAddr }
  -- Class ordering for `CompileEnv.blocks` (Rust `stt.blocks`,
  -- compile.rs:4048-4057 — registered after the standalone early
  -- return above, so only genuine mutual blocks record it).
  let blockResult := { blockResult with
    classNames := sortedClasses.toArray.map fun cls =>
      cls.toArray.map (·.name) }
  let cenv ← getCompileEnv
  let bstate ← getBlockState
  let maps := Ix.AuxGen.AddrMaps.ofCompileEnv cenv
    (aux := bstate.auxNameToAddr) (primary := bstate.blockNameToAddr)
  let (auxLayout?, plans, brecPlans, belowPlans) ←
    (Ix.AuxGen.compileMutualAuxTail cs sortedClasses blockResult.blockAddr
      maps).run' Ix.AuxGen.AuxKernelCtx.new
  return (blockResult, auxLayout?, plans, brecPlans, belowPlans)

/-- Run `compileBlockWithAux` purely, returning the tail outputs and the
    final block state. -/
def runBlockWithAux (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError
        (BlockResult × BlockState × Option Ixon.AuxLayout
          × Std.HashMap Name CallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan) := do
  let blockEnv : BlockEnv :=
    { all, current := lo, mutCtx := default, univCtx := [] }
  let ((result, layout?, plans, brecPlans, belowPlans), cache) ←
    CompileM.run cenv blockEnv {} (compileBlockWithAux lo all)
  pure (result, cache, layout?, plans, brecPlans, belowPlans)

/-! ## The no-aux (original-form) compile — compile.rs:3263-3440 -/

/-- Aux-gen phase of a promoted SCC, read off its first aux member. -/
private inductive NoAuxPhase where
  | recPhase | belowIndc | belowDef | belowRec | brecOn
  deriving BEq

/-- Compile the ORIGINAL Lean form of an aux_gen-rewritten SCC, without
    the aux tail. Mirrors `compile_const_no_aux` (compile.rs:3263): the
    SCC's `all` is re-derived from the members' Lean `.all` fields and
    filtered by the block's aux phase, so the no-aux block matches what
    decompilation's `roundtrip_block` produces. The result is EPHEMERAL:
    the driver promotes each member's original `(addr, meta)` into
    `Named.original` and stores no constants.

    Order note: Rust picks `lean_all` and the phase via first-match over
    the SCC's iteration order. Both are order-independent in practice —
    members of one aux SCC share the same Lean mutual block (`.all`) and
    a homogeneous phase family — which is what makes Rust's
    nondeterministic `FxHashSet` iteration sound; the Lean port inherits
    the same property. -/
def compileConstNoAuxPure (cenv : CompileEnv) (lo : Name) (all : Set Name)
    : Except CompileError (BlockResult × BlockState) := Id.run do
  let getConst (n : Name) : Option ConstantInfo := cenv.env.get? n
  -- The members in canonical order (`aliasPrecedes`), not in `Set`
  -- iteration order, so the first match below (`leanAll`, the phase) is a
  -- function of the member set. On valid input every member gives the same
  -- `.all` and the same phase family (the order note above), so the value is
  -- the one the iteration order gave.
  let members : Array Name := all.toArray.qsort aliasPrecedes
  -- Collect the Lean `.all` names from any constant in the SCC
  -- (compile.rs:3283-3299).
  let mut leanAll : Array Name := #[]
  for n in members do
    match getConst n with
    | some (.inductInfo v) => leanAll := v.all; break
    | some (.recInfo v) => leanAll := v.all; break
    | some (.defnInfo v) => leanAll := v.all; break
    | some (.thmInfo v) => leanAll := v.all; break
    | _ => continue
  -- Determine phase from the first aux_gen constant (compile.rs:3302-3334).
  let mut phase? : Option NoAuxPhase := none
  for n in members do
    if phase?.isSome then break
    if !cenv.auxGenExtraNames.contains n then continue
    match getConst n with
    | some (.recInfo _) =>
      phase? := match n with
        | .str (.str _ ps _) _ _ =>
          if ps == "below" || ps.startsWith "below_" then some .belowRec
          else some .recPhase
        | _ => some .recPhase
    | some (.inductInfo _) => phase? := some .belowIndc
    | some (.defnInfo _) | some (.thmInfo _) =>
      phase? := match n with
        | .str _ s _ =>
          if s == "below" || s.startsWith "below_" then some .belowDef
          else some .brecOn
        | _ => some .brecOn
    | _ => pure ()
  let run (target : Set Name) : Except CompileError (BlockResult × BlockState) :=
    let blockEnv : BlockEnv :=
      { all := target, current := lo, mutCtx := default, univCtx := []
        provenanceOnly := true }
    CompileM.run cenv blockEnv {} (compileConstant lo)
  let some phase := phase?
    | return run all
  -- Build the filtered set from the `.all` field based on phase
  -- (compile.rs:3340-3436).
  let mut filtered : Set Name := {}
  match phase with
  | .recPhase =>
    for n in all do
      if cenv.auxGenExtraNames.contains n then
        if let some (.recInfo _) := getConst n then
          filtered := filtered.insert n
  | .belowIndc =>
    for n in members do
      match getConst n with
      | some (.inductInfo v) =>
        for a in v.all do
          if cenv.auxGenExtraNames.contains a then
            if let some (.inductInfo bi) := getConst a then
              filtered := filtered.insert a
              for ctor in bi.ctors do
                filtered := filtered.insert ctor
        break
      | _ => continue
  | .belowDef =>
    for a in leanAll do
      if cenv.auxGenExtraNames.contains a then
        if let some (.defnInfo _) := getConst a then
          filtered := filtered.insert a
  | .belowRec =>
    for indName in leanAll do
      let belowRec := Name.mkStr indName "rec"
      if cenv.auxGenExtraNames.contains belowRec then
        if let some (.recInfo _) := getConst belowRec then
          filtered := filtered.insert belowRec
  | .brecOn =>
    for n in all do
      if cenv.auxGenExtraNames.contains n then
        filtered := filtered.insert n
    for a in leanAll do
      let base := Name.mkStr a "brecOn"
      if cenv.auxGenExtraNames.contains base then
        filtered := filtered.insert base
      for sub in ["go", "eq"] do
        let subName := Name.mkStr base sub
        if cenv.auxGenExtraNames.contains subName then
          filtered := filtered.insert subName
  if filtered.isEmpty then
    return run all
  return run filtered

/-! ## Driver state and merges -/

/-- Accumulated driver-level side maps that live OUTSIDE `CompileEnv`
    (the per-name hints and the name-component index). -/
structure DriverAcc where
  cenv : CompileEnv
  blockNames : Std.HashMap Address Ix.Name := {}
  defHints : Std.HashMap Name Lean.ReducibilityHints := {}
  /-- Names whose dependents must be released at the CURRENT block's
      completion beyond its own members: the aux names the block's tail
      registered (Rust `aux_gen_pending`, drained per completion —
      env.rs:860-870, pushed by the tail's aux registrations at
      mutual.rs:235/400/480). -/
  pending : Array Name := #[]

/-- Two producers claim one name at different addresses. Mirrors Rust
    `name_claim_conflict` (compile.rs), including the 12-hex-digit address
    prefixes. -/
def nameClaimConflict (name : Name) (existing claimed : Address) : CompileError :=
  .invalidMutualBlock s!"conflicting claims for name '{name.pretty}': already \
registered at {(toString existing).take 12}, claimed again at \
{(toString claimed).take 12}"

/-- The primary names a compiled block claims, with their addresses, in
    Rust's claim order: the lone constant of a block without projections,
    else each member projection. -/
def primaryClaims (lo : Name) (result : BlockResult) : Array (Name × Address) :=
  if result.projections.isEmpty then
    #[(lo, result.blockAddr)]
  else
    result.projections.map fun (name, proj, _) => (name, Address.admissionHash (Ixon.ser proj))

/-- Single ownership of the names a block claims (Rust
    `CompileState::claim_compiled_name` and `claim_aux_name`, and the checked
    plan inserts), checked against the LIVE driver state before anything is
    merged.

    Rust claims inside the block, against the shared state, in this order:
    - the primary names (`claim_compiled_name`): an `aux_name_to_addr` or a
      `name_to_addr` entry at another address is a conflict;
    - the aux tail's names (`claim_aux_name`): a `name_to_addr` entry
      (including this block's own primary names) or an earlier
      `aux_name_to_addr` claim at another address is a conflict, and an
      identical re-claim is a no-op;
    - the call-site plans: a different plan already registered under the
      name is a conflict.

    The Lean block computes against a snapshot and the driver merges
    afterwards, so the same checks run here, in the same order, with the
    same messages. In the sequential driver the snapshot is the live state;
    in the wave driver these checks are what catch two blocks of one wave
    claiming one name. A refused block merges nothing; the driver records
    the error for every member, like any other block failure.

    The aux claims are replayed from `auxNamed` in registration order:
    every claim in `Ix.AuxGen.CompileAux` registers its `Named` at the
    claimed address immediately before inserting the claim, and the
    synthetic `Muts` entries, the only other `auxNamed` entries, are not
    claims. -/
def checkBlockClaims (cenv : CompileEnv) (primary : Array (Name × Address))
    (cache : BlockState)
    (plans : Std.HashMap Name CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Name BRecOnCallSitePlan)
    : Except CompileError Unit := do
  let mut compiled : Std.HashMap Name Address := {}
  for (name, addr) in primary do
    if let some existing := cenv.auxNameToAddr.get? name then
      if existing != addr then throw (nameClaimConflict name existing addr)
    -- A second compiled claim at another address, by an earlier block or
    -- earlier in this block, is a conflict too: an overwrite would make the
    -- address a name keeps depend on which block merged last. An identical
    -- re-claim is a no-op, so valid input (where no name is compiled twice)
    -- merges the same values.
    if let some existing := (compiled.get? name).orElse fun _ => cenv.nameToAddr.get? name then
      if existing != addr then throw (nameClaimConflict name existing addr)
    compiled := compiled.insert name addr
  let mut claimed : Std.HashMap Name Address := {}
  for (name, named) in cache.auxNamed do
    unless cache.auxGenExtraNames.contains name && cache.auxNameToAddr.contains name do
      continue
    let addr := named.addr
    let registered := match compiled.get? name with
      | some a => some a
      | none => cenv.nameToAddr.get? name
    if let some existing := registered then
      if existing != addr then throw (nameClaimConflict name existing addr)
    let earlier := match claimed.get? name with
      | some a => some a
      | none => cenv.auxNameToAddr.get? name
    match earlier with
    | some existing =>
      if existing != addr then throw (nameClaimConflict name existing addr)
    | none => claimed := claimed.insert name addr
  for (name, plan) in plans do
    if let some existing := cenv.callSitePlans.get? name then
      if existing != plan then
        throw (.invalidMutualBlock s!"conflicting call-site plans for \
'{name.pretty}' — two blocks claim one source-indexed aux name")
  for (name, plan) in brecPlans do
    if let some existing := cenv.brecOnCallSitePlans.get? name then
      if existing != plan then
        throw (.invalidMutualBlock s!"conflicting brecOn call-site plans for \
'{name.pretty}' — two blocks claim one source-indexed aux name")
  for (name, plan) in belowPlans do
    if let some existing := cenv.belowCallSitePlans.get? name then
      if existing != plan then
        throw (.invalidMutualBlock s!"conflicting below call-site plans for \
'{name.pretty}' — two blocks claim one source-indexed aux name")

/-- Validate both the block's name claims (`checkBlockClaims`) and its
    anonymous payloads (`checkBlockContent`: a reused record or blob address
    must hold the same bytes) against the live state before publishing any
    output of this block. -/
def checkCompiledBlock (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    (cache : BlockState)
    (plans : Std.HashMap Name CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Name BRecOnCallSitePlan)
    : Except CompileError Unit := do
  checkBlockClaims cenv (primaryClaims lo result) cache plans brecPlans belowPlans
  checkBlockContent cenv result cache

/-- Merge one compiled block's outputs into the driver state, mirroring
    the Rust global-mutation order: block constant, member projections
    (primary `register_name` + `name_to_addr`, compile.rs:3902-3969),
    then the tail's aux constants, Named overrides (incl. the synthetic
    `Muts` entry and aliases), aux name→addr map, extra names, and
    call-site plans.

    Every caller first checks the block against the live state
    (`checkCompiledBlock`: single ownership of its names, and its records'
    and blobs' bytes) and merges only if the check passes: a conflict is an
    error and nothing is merged. The check is a separate step, not part of
    this function, so that the merge keeps consuming the driver state
    uniquely (a merge returning `Except` would keep the old state alive for
    the error branch and copy every map it inserts into). `Named` entries are
    overrides by design (the tail re-registers regenerated names and the
    `Muts` entry), as with Rust's `register_name`; content-keyed tables
    (constants, blobs) are unioned by content, which the check made
    conflict-free. -/
def mergeCompiledBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState)
    (plans : Std.HashMap Name CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Name BRecOnCallSitePlan) : DriverAcc := Id.run do
  let mut cenv := acc.cenv
  cenv := { cenv with
    totalBytes := cenv.totalBytes + result.blockBytes.size
    constants := cenv.constants.insert result.blockAddr result.blockBytes
    blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) cenv.blobs }
  -- Primary registrations.
  if result.projections.isEmpty then
    cenv := { cenv with
      nameToNamed := cenv.nameToNamed.insert lo
        { addr := result.blockAddr, constMeta := result.blockMeta }
      nameToAddr := cenv.nameToAddr.insert lo result.blockAddr }
  else
    for (name, proj, constMeta) in result.projections do
      let projBytes := Ixon.ser proj
      let projAddr := Address.admissionHash projBytes
      cenv := { cenv with
        totalBytes := cenv.totalBytes + projBytes.size
        constants := cenv.constants.insert projAddr projBytes
        nameToNamed := cenv.nameToNamed.insert name { addr := projAddr, constMeta }
        nameToAddr := cenv.nameToAddr.insert name projAddr }
  -- Aux tail outputs: stored constants, Named overrides (in registration
  -- order — LAST wins per name), aux resolution map, extra names, plans.
  for (addr, c) in cache.auxConsts do
    cenv := { cenv with constants := cenv.constants.insert addr (Ixon.ser c) }
  for (n, named) in cache.auxNamed do
    cenv := { cenv with nameToNamed := cenv.nameToNamed.insert n named }
  cenv := { cenv with
    auxNameToAddr := cache.auxNameToAddr.fold (fun m k v => m.insert k v)
      cenv.auxNameToAddr
    auxGenExtraNames := cache.auxGenExtraNames.fold (fun s n => s.insert n)
      cenv.auxGenExtraNames
    callSitePlans := plans.fold (fun m k v => m.insert k v) cenv.callSitePlans
    brecOnCallSitePlans := brecPlans.fold (fun m k v => m.insert k v)
      cenv.brecOnCallSitePlans
    belowCallSitePlans := belowPlans.fold (fun m k v => m.insert k v)
      cenv.belowCallSitePlans }
  -- Class-ordering registry (Rust `stt.blocks`, compile.rs:4048-4057):
  -- one entry per member, all pointing at the block's full ordering.
  if !result.classNames.isEmpty then
    for cls in result.classNames do
      for n in cls do
        cenv := { cenv with blocks := cenv.blocks.insert n result.classNames }
  let mut pending := acc.pending
  for (n, _) in cache.auxNameToAddr do
    pending := pending.push n
  return { acc with
    cenv
    blockNames := cache.blockNames.fold (fun m k v => m.insert k v) acc.blockNames
    defHints := cache.defHints.fold (fun m k v => m.insert k v) acc.defHints
    pending }

/-- Withdraw a failed source block's provisional auxiliary publication: its
    members leave every name table (`nameToAddr`, `auxNameToAddr`,
    `nameToNamed`, `auxGenExtraNames`, `blocks`, the hints) and the pending
    releases, and each is recorded as a failure with `msg`. Anonymous content
    and unrelated successful names remain available. Mirrors Rust
    `fail_aux_promotion` (env.rs). -/
def failAuxPromotion (acc : DriverAcc) (all : Set Name) (msg : String) : DriverAcc :=
  Id.run do
  let mut acc := acc
  for n in all do
    acc := { acc with
      cenv := { acc.cenv with
        nameToAddr := acc.cenv.nameToAddr.erase n
        auxNameToAddr := acc.cenv.auxNameToAddr.erase n
        nameToNamed := acc.cenv.nameToNamed.erase n
        auxGenExtraNames := acc.cenv.auxGenExtraNames.erase n
        blocks := acc.cenv.blocks.erase n
        ungrounded := acc.cenv.ungrounded.insert n msg }
      defHints := acc.defHints.erase n }
  return { acc with pending := acc.pending.filter (!all.contains ·) }

/-- The scheduler's promote-remaining pass over a pre-compiled block's
    members (Rust env.rs, after the original-form compile). Every claim is
    checked before any member is published: a member already in `nameToAddr`
    with an aux claim at a different address fails the whole block
    (`failAuxPromotion`, single ownership; the first conflict in canonical
    member order names it). Otherwise each member not yet registered takes
    its resolved address. Returns the members newly registered. -/
def promoteRemaining (acc : DriverAcc) (all : Set Name) : DriverAcc × Array Name := Id.run do
  for name in all.toArray.qsort aliasPrecedes do
    if let some existing := acc.cenv.nameToAddr.get? name then
      if let some claimed := acc.cenv.auxNameToAddr.get? name then
        if claimed != existing then
          return (failAuxPromotion acc all (toString (nameClaimConflict name existing claimed)), #[])
  let mut acc := acc
  let mut newNames : Array Name := #[]
  for name in all do
    match acc.cenv.nameToAddr.get? name with
    | some _ => pure ()
    | none =>
      if let some addr := resolveAddrPure acc.cenv name then
        acc := { acc with cenv := { acc.cenv with
          nameToAddr := acc.cenv.nameToAddr.insert name addr } }
        newNames := newNames.push name
  return (acc, newNames)

/-- Self-name address of a `ConstantMeta`, for the promote coherence
    check (Rust `promote_aux`, compile.rs:317-328). -/
def constMetaSelfName? (m : Ixon.ConstantMeta) : Option Address :=
  match m.info with
  | .defn n .. => some n
  | .axio n .. => some n
  | .quot n .. => some n
  | .indc n .. => some n
  | .ctor n .. => some n
  | .recr n .. => some n
  | _ => none

/-- Promote an aux_gen-compiled name: copy its aux address into the
    resolution map and graft the ORIGINAL `(addr, meta)` into the
    existing (regenerated) `Named` entry. Mirrors
    `CompileState::promote_aux` (compile.rs), including the meta self-name
    coherence check and the claim: a name already compiled at another
    address is a conflict, not an overwrite. -/
def promoteAuxDriver (cenv : CompileEnv) (name : Name)
    (origAddr : Address) (origMeta : Ixon.ConstantMeta)
    : Except CompileError CompileEnv := do
  if let some metaAddr := constMetaSelfName? origMeta then
    if metaAddr != name.getHash then
      throw (.invalidMutualBlock s!"promote_aux: name mismatch for \
'{name.pretty}' — compile_name address is {name.getHash} but meta name \
address is {metaAddr}")
  let mut cenv := cenv
  if let some auxAddr := cenv.auxNameToAddr.get? name then
    if let some existing := cenv.nameToAddr.get? name then
      if existing != auxAddr then throw (nameClaimConflict name existing auxAddr)
    cenv := { cenv with nameToAddr := cenv.nameToAddr.insert name auxAddr }
  if let some named := cenv.nameToNamed.get? name then
    let named' := { named with original := some (origAddr, origMeta) }
    cenv := { cenv with nameToNamed := cenv.nameToNamed.insert name named' }
  pure cenv

/-- Stage the entire original-form promotion in pure state: each member's
    original `(addr, meta)` (or the lone constant's), then the ephemeral
    compile's blobs, name components and hints (Rust `store_string`,
    `compile_name` and `def_hints` are unconditional; only constant and
    `Named` stores are aux-gated). Its blobs must agree with the published
    ones (`checkBlobContent`). On error the caller keeps none of these
    writes, then withdraws the failed block's earlier auxiliary bindings.
    Both driver paths use this same operation. -/
def promoteOriginalBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState) : Except CompileError DriverAcc := do
  checkBlobContent acc.cenv cache
  let promotions : Array (Name × Address × Ixon.ConstantMeta) :=
    if result.projections.isEmpty then
      #[(lo, result.blockAddr, result.blockMeta)]
    else
      result.projections.map fun (name, proj, constMeta) =>
        (name, Address.admissionHash (Ixon.ser proj), constMeta)
  let mut acc := acc
  for (name, origAddr, origMeta) in promotions do
    let cenv ← promoteAuxDriver acc.cenv name origAddr origMeta
    acc := { acc with cenv }
  return { acc with
    cenv := { acc.cenv with
      blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) acc.cenv.blobs }
    blockNames := cache.blockNames.fold (fun m k v => m.insert k v) acc.blockNames
    defHints := cache.defHints.fold (fun m k v => m.insert k v) acc.defHints }

/-- Finish a source block's promotion atomically: the original-form
    promotion (`promoteOriginalBlock`), then the remaining claims
    (`promoteRemaining`). A failure of either, or a member already recorded
    as failed (a failed cross-SCC subset), fails the whole block: the staged
    original metadata is discarded, even for members outside the scheduled
    block that the original-form compile visited, and the block is withdrawn
    (`failAuxPromotion`). Returns the members newly registered and whether
    the block failed. -/
def finishAuxPromotion (acc : DriverAcc) (lo : Name) (all : Set Name)
    (original : Option (BlockResult × BlockState)) : DriverAcc × Array Name × Bool := Id.run do
  let mut staged := acc
  if let some (result, cache) := original then
    match promoteOriginalBlock staged lo result cache with
    | .error e => return (failAuxPromotion acc all (toString e), #[], true)
    | .ok next => staged := next
  let (next, names) := promoteRemaining staged all
  for name in all.toArray.qsort aliasPrecedes do
    if let some msg := next.cenv.ungrounded.get? name then
      return (failAuxPromotion acc all msg, #[], true)
  return (next, names, false)

/-- The one readiness rule of both drivers: a source name (a member of a
    condensation block, `sourceOwned`) is ready only when its own block has
    completed, successfully or not (`settled`), never because a parent's
    provisional aux publication resolved it before its original-form
    promotion; a generated name without a source block is ready once it
    resolves. Failed blocks settle too, so their dependents run and report
    their missing reads. -/
def auxDependencyReady (sourceOwned : Name → Bool) (cenv : CompileEnv)
    (settled : Set Name) (name : Name) : Bool :=
  settled.contains name || (!sourceOwned name && (resolveAddrPure cenv name).isSome)

/-! ## Aux-gen prereq pre-compilation — env.rs:993-1140 -/

/-- Seed names for the aux_gen prereq closure — the exact Const refs
    aux_gen emits in generated `.below`/`.brecOn`/`.brecOn.eq` bodies
    (Rust `aux_gen_seed_names`, env.rs:1001). -/
def auxGenSeedNames : Array Name := Id.run do
  let root : Name := .mkAnon
  let eq := Name.mkStr root "Eq"
  let heq := Name.mkStr root "HEq"
  return #[
    Name.mkStr root "PUnit",
    Name.mkStr root "PProd",
    eq,
    Name.mkStr eq "refl",
    Name.mkStr eq "symm",
    Name.mkStr eq "ndrec",
    Name.mkStr root "rfl",
    heq,
    Name.mkStr heq "refl",
    Name.mkStr root "eq_of_heq",
    Name.mkStr root "True"]

/-- Pre-compile the transitive SCC closure of the aux_gen seed names in
    reverse-topological (dep-first) order, then move the compiled names
    from `nameToAddr` to `auxNameToAddr` so the scheduler's promotion
    pass recognizes and re-promotes them when their blocks come up.
    Mirrors `precompile_aux_gen_prereqs` (env.rs:1036-1140). -/
def precompileAuxGenPrereqs (blocks : Ix.CondensedBlocks) (acc₀ : DriverAcc)
    : Except String DriverAcc := Id.run do
  let seedReps := auxGenSeedNames.filterMap (blocks.lowLinks.get? ·)
  if seedReps.isEmpty then
    return .ok acc₀
  -- Iterative DFS post-order over the condensed graph (env.rs:1063-1097).
  let mut order : Array Name := #[]
  let mut visited : Set Name := {}
  -- Frame: (rep, isExit)
  let mut stack : Array (Name × Bool) := seedReps.map ((·, false))
  repeat
    match stack.back? with
    | none => break
    | some (rep, isExit) =>
      stack := stack.pop
      if isExit then
        order := order.push rep
      else
        if visited.contains rep then
          continue
        visited := visited.insert rep
        stack := stack.push (rep, true)
        if let some outRefs := blocks.blockRefs.get? rep then
          for referenced in outRefs do
            if let some depRep := blocks.lowLinks.get? referenced then
              if !visited.contains depRep then
                stack := stack.push (depRep, false)
  let mut acc := acc₀
  for rep₀ in order do
    let some all := blocks.blocks.get? rep₀ | continue
    -- The block is compiled under its canonical key.
    let rep := blockKey rep₀ all
    if acc.cenv.auxNameToAddr.contains rep then
      continue
    let failed (e : CompileError) : String := s!"aux_gen prereq pre-compile failed for SCC \
'{rep.pretty}' ({all.size} members): {e}. The SCC closure is traversed \
in reverse-topological order starting from the aux_gen seed names, so \
all transitive deps should be compiled before this — if you're hitting \
this, a dep relationship isn't captured in the ref graph, or the source \
env is inconsistent."
    match runBlockWithAux acc.cenv all rep with
    | .error e => return .error (failed e)
    | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
      -- A conflicting claim fails the pre-compile like a block error (Rust's
      -- claims raise inside `compile_const`).
      match checkCompiledBlock acc.cenv rep result cache plans brecPlans belowPlans with
      | .error e => return .error (failed e)
      | .ok () => acc := mergeCompiledBlock acc rep result cache plans brecPlans belowPlans
      -- Move compiled names → auxNameToAddr (env.rs:1119-1137). At this
      -- stage `nameToAddr` contains exactly the prereq registrations.
      let moved := acc.cenv.nameToAddr
      acc := { acc with cenv := { acc.cenv with
        nameToAddr := {}
        auxNameToAddr := moved.fold (fun m k v => m.insert k v)
          acc.cenv.auxNameToAddr } }
  return .ok acc

/-- Assemble the final `Ixon.Env` from the accumulated driver state
    (shared tail of both drivers: names index, name blobs, finalize_hints — the exact
    per-Named channel plus the per-address `anonHints` advisory map with
    order-independent merge). -/
def assembleEnv (acc : DriverAcc) : Ixon.Env × Nat × CompileEnv := Id.run do
  let cenv := acc.cenv
  let (addrToNameMap, namesMap, nameBlobs) :=
    cenv.nameToNamed.fold (init := ({}, acc.blockNames, {}))
      fun (addrMap, namesMap, blobs) name named =>
        -- The canonical alias, not the last one the fold met.
        let addrMap := insertCanonicalAlias addrMap named.addr name
        let (namesMap, blobs) :=
          Ixon.RawEnv.addNameComponentsWithBlobs namesMap blobs name
        (addrMap, namesMap, blobs)
  let allBlobs := nameBlobs.fold (fun m k v => m.insert k v) cenv.blobs
  let namedWithHints := cenv.nameToNamed.fold (init := {})
    fun m name named =>
      m.insert name { named with hints := acc.defHints.get? name }
  let anonHints := cenv.nameToNamed.fold (init := {}) fun m name named =>
    match acc.defHints.get? name with
    | some h => m.alter named.addr fun
      | some h₀ => some (Ixon.mergeHints h₀ h)
      | none => some h
    | none => m
  let ixonEnv : Ixon.Env := {
    consts := cenv.constants.fold (init := {})
      fun m a bytes => m.insert a { buf := bytes, len := bytes.size }
    named := namedWithHints
    blobs := allBlobs
    names := namesMap
    comms := {}
    addrToName := addrToNameMap
    anonHints
  }
  return (ixonEnv, cenv.totalBytes, cenv)

/-! ## Domain restriction: canonical inductive flags — env.rs:262-285 -/

/-- The input's inductive groups: each inductive's `all`, keyed by its first
    member, the first `all` met for a key kept (Rust `scan.ind_groups`,
    graph.rs:120). -/
def inductiveGroups (env : Ix.Environment) : Std.HashMap Name (Array Name) :=
  env.consts.fold (init := {}) fun groups _ ci =>
    match ci with
    | .inductInfo v =>
      match v.all[0]? with
      | some first => if groups.contains first then groups else groups.insert first v.all
      | none => groups
    | _ => groups

/-- Groups per task in `validateInductiveFlags`. -/
def inductiveFlagsChunk : Nat := 256

/-- The domain restriction of both drivers (Rust `validate_ind_groups`,
    env.rs:277): every input inductive group must carry the flags Lean
    computes for it (`isRec`, `isReflexive`, `numNested`;
    `Ix.AuxGen.validateIndGroup`), or the compile fails before any block is
    scheduled. The groups are checked on parallel tasks, in chunks of
    `inductiveFlagsChunk` in the order of their first members' hashes; the
    error reported is the first in that order (Rust reports one of them). -/
def validateInductiveFlags (env : Ix.Environment) : Except String Unit := Id.run do
  let groups := (inductiveGroups env).toArray.qsort fun a b =>
    a.1.getHash.cmpBytes b.1.getHash == .lt
  let cenv := CompileEnv.new env
  let blockEnv : BlockEnv :=
    { all := {}, current := .mkAnon, mutCtx := default, univCtx := [] }
  let chunks := (groups.size + inductiveFlagsChunk - 1) / inductiveFlagsChunk
  let tasks := (Array.range chunks).map fun c => Task.spawn fun _ => Id.run do
    for (_, all) in groups[c * inductiveFlagsChunk:(c + 1) * inductiveFlagsChunk] do
      if let .error e := CompileM.run cenv blockEnv {} (Ix.AuxGen.validateIndGroup all) then
        return some (toString e)
    return none
  for t in tasks do
    if let some e := t.get then return .error e
  return .ok ()

/-- The drivers' refusal of a condensation with a block that has no reference
    set: the scheduler would schedule such a block without its dependencies.
    `CondenseM.run` and the Rust condensation give every block one. The block
    named is the least by displayed name. -/
def missingBlockRefs? (blocks : Ix.CondensedBlocks) : Option String :=
  let missing := blocks.blocks.fold (init := #[]) fun (acc : Array Name) lo _ =>
    if blocks.blockRefs.contains lo then acc else acc.push lo
  match (missing.qsort fun a b => a.pretty < b.pretty)[0]? with
  | some lo => some s!"block {lo.pretty} has no condensation reference set"
  | none => none

/-! ## The aux-aware sequential driver -/

/-- Compile an entire environment with the FULL production pipeline
    semantics: aux-gen prereq pre-compilation, per-block aux tails
    (regeneration + call-site plans), the scheduler promotion pass with
    the no-aux original-form second compile (`Named.original`), and
    pending-aux dependency release. Sequential mirror of Rust
    `compile_env_with_options`' scheduler (env.rs:146-990; grounding and
    SCC condensation happen upstream of the `blocks` input, as in the
    Rust FFI phase split). An input inductive group with non-canonical
    flags fails the compile first (`validateInductiveFlags`).

    Per-block failures, and the names of a cross-SCC subset whose compile
    fails, are recorded in `ungrounded` per member and the scheduler
    continues (dependents cascade into `MissingConstant` failures recorded
    the same way) — mirroring env.rs:727-737. -/
def compileEnvAux (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (nameByHash : Std.HashMap Address Name := {})
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
  if let some msg := missingBlockRefs? blocks then return .error msg
  if let .error e := validateInductiveFlags env then return .error e
  let mut acc : DriverAcc := { cenv := { CompileEnv.new env with nameByHash, sharingLimits } }
  match precompileAuxGenPrereqs blocks acc with
  | .error e => return .error e
  | .ok a => acc := a

  let totalBlocks := blocks.blocks.size
  let mut blockInfo : Std.HashMap Name (Set Name × Nat) := {}
  let mut reverseDeps : Std.HashMap Name (Array Name) := {}
  for (lo, all) in blocks.blocks do
    let deps := match blocks.blockRefs.get? lo with
      | some d => d
      | none => {}
    blockInfo := blockInfo.insert lo (all, deps.size)
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]
  -- The ready blocks keyed by their canonical key (`blockKey`), the least
  -- taken first: the fold's order is the least-key-first topological order
  -- of the block graph, a function of the graph and the keys alone. It was
  -- a stack filled in `HashMap` iteration order, so the order depended on
  -- the condensation's representatives and the maps' histories. The output
  -- does not depend on the order on valid input, so this changes no value.
  let mut readyQueue : Std.TreeMap Name (Set Name) Ix.nameCompare := {}
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.insert (blockKey lo all) all

  let mut blocksCompleted : Nat := 0
  let mut lastPct : Nat := 0
  -- Deps already satisfied (released) — HashSet-style idempotent release
  -- mirrors Rust's `remaining.remove` (env.rs:838-856): a name can be
  -- released at most once per dependent.
  let mut released : Set Name := {}

  while !readyQueue.isEmpty do
    -- `lo` is the block's canonical key from here on.
    let some (lo, all) := readyQueue.minEntry? | break
    readyQueue := readyQueue.erase lo

    if (resolveAddrPure acc.cenv lo).isSome then
      -- Promotion path (env.rs:566-708): the block was pre-compiled into
      -- `auxNameToAddr` (prereqs or a parent block's aux tail).
      let anyAuxGen := Id.run do
        for n in all do
          if acc.cenv.auxGenExtraNames.contains n then return true
        return false
      let mut unresolvedNames : Array Name := #[]
      for n in all do
        if acc.cenv.nameToAddr.contains n then
          continue
        if (resolveAddrPure acc.cenv n).isSome then
          continue
        unresolvedNames := unresolvedNames.push n
      let mut auxIncomplete := false
      if !unresolvedNames.isEmpty then
        if anyAuxGen then
          auxIncomplete := true
          let missing := ", ".intercalate
            (unresolvedNames.toList.map (·.pretty))
          let msg := s!"aux_gen precompile incomplete for {lo.pretty}; \
missing canonical aliases: {missing}"
          acc := failAuxPromotion acc all msg
        else
          -- Cross-SCC compile of the unresolved subset (env.rs:617-651).
          let crossAll : Set Name :=
            unresolvedNames.foldl (fun s n => s.insert n) {}
          -- The subset is named by its canonical key, not by its first name
          -- in `Set` order.
          let clo := canonicalKey lo unresolvedNames
          -- The subset's names are failures of the compile when it fails or
          -- claims a name another block owns (Rust claims inside
          -- `compile_const`), recorded per name as Rust records them, and not
          -- registered: dependents get `MissingConstant` rather than broken
          -- data.
          let crossFailed (acc : DriverAcc) (e : CompileError) : DriverAcc := Id.run do
            let msg := toString e
            let mut acc := acc
            for n in unresolvedNames do
              acc := { acc with cenv := { acc.cenv with
                ungrounded := acc.cenv.ungrounded.insert n msg } }
            return acc
          match runBlockWithAux acc.cenv crossAll clo with
          | .error e => acc := crossFailed acc e
          | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
            match checkCompiledBlock acc.cenv clo result cache plans brecPlans
                belowPlans with
            | .error e => acc := crossFailed acc e
            | .ok () =>
              acc := mergeCompiledBlock acc clo result cache plans brecPlans belowPlans
              for n in unresolvedNames do
                acc := { acc with
                  cenv := { acc.cenv with
                    auxGenExtraNames := acc.cenv.auxGenExtraNames.insert n }
                  pending := acc.pending.push n }
      if !auxIncomplete then
        -- Compile the original Lean form and promote, atomically
        -- (`finishAuxPromotion`): a failure of the original-form compile, of
        -- its promotion, of a remaining claim, or of the cross-SCC subset
        -- withdraws the whole block.
        let original := if anyAuxGen then
          (compileConstNoAuxPure acc.cenv lo all).map some
        else .ok none
        match original with
        | .error e => acc := failAuxPromotion acc all (toString e)
        | .ok result =>
          let (next, _, _) := finishAuxPromotion acc lo all result
          acc := next
    else
      -- Normal path: compile the block with the aux tail.
      let fail (acc : DriverAcc) (e : CompileError) : DriverAcc := Id.run do
        -- Soft failure (env.rs:727-737): record per member; the
        -- scheduler keeps running and dependents cascade.
        let msg := toString e
        let mut acc := acc
        for m in all do
          acc := { acc with cenv := { acc.cenv with
            ungrounded := acc.cenv.ungrounded.insert m msg } }
        return acc
      match runBlockWithAux acc.cenv all lo with
      | .error e => acc := fail acc e
      | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
        -- A conflicting claim is a failure of this block (Rust raises it
        -- inside `compile_const`): nothing of it is merged.
        match checkCompiledBlock acc.cenv lo result cache plans brecPlans belowPlans with
        | .error e => acc := fail acc e
        | .ok () => acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans

    -- Release dependents: block members plus drained pending-aux names
    -- (env.rs:838-870).
    let pendingDrained := acc.pending
    acc := { acc with pending := #[] }
    let mut releaseNames : Array Name := #[]
    for n in all do
      releaseNames := releaseNames.push n
    -- Source-owned auxiliaries settle only when their own block finishes its
    -- original-form promotion (`auxDependencyReady`); generated names without
    -- a source block can release now.
    releaseNames := releaseNames ++ pendingDrained.filter (!blocks.lowLinks.contains ·)
    for name in releaseNames do
      if released.contains name then
        continue
      released := released.insert name
      if let some dependents := reverseDeps.get? name then
        for dependentLo in dependents do
          if let some (depAll, depCount) := blockInfo.get? dependentLo then
            let newCount := depCount - 1
            blockInfo := blockInfo.insert dependentLo (depAll, newCount)
            if newCount == 0 then
              readyQueue := readyQueue.insert (blockKey dependentLo depAll) depAll

    blocksCompleted := blocksCompleted + 1
    if dbg then
      let pct := (blocksCompleted * 100) / totalBlocks
      if pct >= lastPct + 10 then
        dbg_trace s!"  [CompileAux] {pct}% ({blocksCompleted}/{totalBlocks})"
        lastPct := pct

  if blocksCompleted != totalBlocks then
    return .error s!"Only compiled {blocksCompleted}/{totalBlocks} blocks \
- circular dependency?"

  return .ok (assembleEnv acc)

/-! ## The aux-aware parallel driver

Wave-based parallel version of `compileEnvAux`: each wave snapshots the accumulated
`CompileEnv`, workers compute a pure per-block outcome against the
snapshot, and the main thread applies the same merges as the sequential
driver. Blocks within a wave are dependency-independent, and every merge
is per-name-disjoint or content-keyed: two blocks of one wave that claim
one name at different addresses (or one plan key with different plans)
are refused by the merge-time check (`checkCompiledBlock`) against the live
state, as Rust's insert-once claims refuse them; so are conflicting
payloads at one record or blob address. Which of the two blocks
reports the conflict follows completion order, in both compilers. -/

/-- Pure per-block outcome computed by a wave worker. -/
inductive AuxBlockOutcome where
  /-- Normal path: full block compile + aux tail. -/
  | compiled (result : BlockResult) (cache : BlockState)
      (plans : Std.HashMap Name CallSitePlan)
      (brecPlans : Std.HashMap Name BRecOnCallSitePlan)
      (belowPlans : Std.HashMap Name BRecOnCallSitePlan)
  /-- Promotion path (env.rs:566-708): pre-compiled by prereqs or a
      parent's aux tail. `crossScc` carries the compiled unresolved
      subset (non-aux case), `crossFailure` its names and error when its
      compile fails; `incompleteMsg` the aux-incomplete failure;
      `noAux` the original-form compile for `Named.original` grafting;
      `noAuxFailMsg` its failure. The promote-remaining loop runs at
      merge time against the live env. -/
  | promoted
      (crossScc : Option (Name × BlockResult × BlockState
        × Std.HashMap Name CallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan))
      (crossNames : Array Name)
      (crossFailure : Option (Array Name × String))
      (incompleteMsg : Option String)
      (noAux : Option (BlockResult × BlockState))
      (noAuxFailMsg : Option String)
  /-- Normal-path compile failure — soft (env.rs:727-737). -/
  | failed (msg : String)

/-- Compute a block's outcome against a wave-snapshot env. Pure; mirrors
    the per-block body of `compileEnvAux`. -/
def auxBlockOutcome (cenv : CompileEnv) (lo : Name) (all : Set Name) :
    AuxBlockOutcome := Id.run do
  if (resolveAddrPure cenv lo).isSome then
    let anyAuxGen := Id.run do
      for n in all do
        if cenv.auxGenExtraNames.contains n then return true
      return false
    let mut unresolvedNames : Array Name := #[]
    for n in all do
      if cenv.nameToAddr.contains n then
        continue
      if (resolveAddrPure cenv n).isSome then
        continue
      unresolvedNames := unresolvedNames.push n
    let mut crossScc := none
    let mut crossNames : Array Name := #[]
    let mut crossFailure := none
    let mut incompleteMsg := none
    if !unresolvedNames.isEmpty then
      if anyAuxGen then
        let missing := ", ".intercalate (unresolvedNames.toList.map (·.pretty))
        incompleteMsg := some s!"aux_gen precompile incomplete for \
{lo.pretty}; missing canonical aliases: {missing}"
      else
        let crossAll : Set Name :=
          unresolvedNames.foldl (fun s n => s.insert n) {}
        -- Named by its canonical key, as in the sequential driver.
        let clo := canonicalKey lo unresolvedNames
        match runBlockWithAux cenv crossAll clo with
        | .error e => crossFailure := some (unresolvedNames, toString e)
        | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
          crossScc := some (clo, result, cache,
            plans, brecPlans, belowPlans)
          crossNames := unresolvedNames
    let mut noAux := none
    let mut noAuxFailMsg := none
    if anyAuxGen && incompleteMsg.isNone then
      match compileConstNoAuxPure cenv lo all with
      | .error e => noAuxFailMsg := some (toString e)
      | .ok out => noAux := some out
    return .promoted crossScc crossNames crossFailure incompleteMsg noAux noAuxFailMsg
  else
    match runBlockWithAux cenv all lo with
    | .error e => return .failed (toString e)
    | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
      return .compiled result cache plans brecPlans belowPlans

/-- Apply a worker outcome to the live driver state. Returns the names
    newly REGISTERED by this block (for rustRef fail-fast comparison), and
    whether the block failed at merge time: a conflicting claim or payload
    (`checkCompiledBlock`), or a failed promotion (`finishAuxPromotion`,
    which withdraws the block). The wave loop settles every completed
    block's members, failed or not (`auxDependencyReady`). -/
def applyAuxBlockOutcome (acc : DriverAcc) (lo : Name) (all : Set Name)
    (outcome : AuxBlockOutcome) : DriverAcc × Array Name × Bool := Id.run do
  let mut acc := acc
  let mut newNames : Array Name := #[]
  let recordFailure (acc : DriverAcc) (names : Array Name) (msg : String) : DriverAcc := Id.run do
    let mut acc := acc
    for m in names do
      acc := { acc with cenv := { acc.cenv with
        ungrounded := acc.cenv.ungrounded.insert m msg } }
    return acc
  match outcome with
  | .compiled result cache plans brecPlans belowPlans =>
    match checkCompiledBlock acc.cenv lo result cache plans brecPlans belowPlans with
    | .error e => return (recordFailure acc all.toArray (toString e), #[], true)
    | .ok () => acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans
    if result.projections.isEmpty then
      newNames := newNames.push lo
    else
      for (name, _, _) in result.projections do
        newNames := newNames.push name
    for (n, _) in cache.auxNamed do
      newNames := newNames.push n
  | .failed msg =>
    acc := recordFailure acc all.toArray msg
  | .promoted crossScc crossNames crossFailure incompleteMsg noAux noAuxFailMsg =>
    -- A failed cross-SCC subset: its names are failures, as in the
    -- sequential driver (and the block's promotion then fails as a whole).
    if let some (names, msg) := crossFailure then
      acc := recordFailure acc names msg
    if let some (clo, result, cache, plans, brecPlans, belowPlans) := crossScc then
      -- A conflicting claim or payload is a failure of the cross-SCC subset,
      -- as in the sequential driver: nothing of it is registered.
      match checkCompiledBlock acc.cenv clo result cache plans brecPlans belowPlans with
      | .error e =>
        acc := recordFailure acc crossNames (toString e)
      | .ok () =>
        acc := mergeCompiledBlock acc clo result cache plans brecPlans belowPlans
        if result.projections.isEmpty then
          newNames := newNames.push clo
        else
          for (name, _, _) in result.projections do
            newNames := newNames.push name
        for (n, _) in cache.auxNamed do
          newNames := newNames.push n
        for n in crossNames do
          acc := { acc with cenv := { acc.cenv with
            auxGenExtraNames := acc.cenv.auxGenExtraNames.insert n } }
    if let some msg := incompleteMsg then
      return (failAuxPromotion acc all msg, #[], true)
    if let some msg := noAuxFailMsg then
      return (failAuxPromotion acc all msg, #[], true)
    -- The original-form promotion and the remaining claims, atomically,
    -- against the LIVE env; registrations count for rustRef.
    let (next, promoted, failed) := finishAuxPromotion acc lo all noAux
    if failed then return (next, #[], true)
    acc := next
    newNames := newNames ++ promoted
  return (acc, newNames, false)

/-- Work item for the aux-aware parallel driver. -/
structure AuxWorkItem where
  lo : Name
  all : Set Name
  cenv : CompileEnv

instance : Inhabited AuxWorkItem where
  default := { lo := default, all := {}, cenv := default }

instance : Inhabited AuxBlockOutcome where
  default := .failed "uninitialized"

/-- The options of the Lean compile drivers. The drivers read no environment
    variable and no `/proc` file: the CLI parses these (`ix compile-lean`:
    `--sharing-limits` and `IX_SHARING_LIMITS`, `IX_LOG_BLOCKS`,
    `IX_COMPILE_DBG`) and passes them in. -/
structure DriverOptions where
  /-- Resource limits of the canonical sharing construction. -/
  sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits
  /-- Phase timings, and the parallel driver's wave and progress traces. -/
  dbg : Bool := false
  /-- The parallel driver's per-block BEGIN/END trace, gated to the tail of
      the run (snapshot above 600k constants), where the whole-Mathlib
      memory spike lives: it names the block a worker is inside when memory
      blows up. -/
  logBlocks : Bool := false
  /-- A memory reading for the traces, supplied by the caller (the CLI reads
      the process's resident set size); `none` prints none. -/
  memory : Option (IO String) := none

/-- Parallel aux-aware environment compile. Same output as
    `compileEnvAux` (see the module docstring for the intra-wave
    order-independence argument).

    `rustRef` enables fail-fast address comparison: after each block's
    merge, every name it registered is checked against the reference
    map; the first divergence aborts with the offending name. -/
def compileEnvParallelAux (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    (nameByHash : Std.HashMap Address Name := {})
    : IO (Except String (Ixon.Env × Nat × CompileEnv)) := do
  if let some msg := missingBlockRefs? blocks then return .error msg
  let totalBlocks := blocks.blocks.size
  let sharingLimits := opts.sharingLimits
  let dbg := opts.dbg

  if let .error e := validateInductiveFlags env then return .error e
  let mut acc : DriverAcc := { cenv := { CompileEnv.new env with nameByHash, sharingLimits } }
  match precompileAuxGenPrereqs blocks acc with
  | .error e => return .error e
  | .ok a => acc := a

  let workChan ← Std.CloseableChannel.Sync.new (α := AuxWorkItem)
  let resultChan ← Std.CloseableChannel.Sync.new
    (α := Name × Set Name × AuxBlockOutcome)

  -- Per-block BEGIN/END trace (`DriverOptions.logBlocks`), with the
  -- duration and the caller's memory reading at END.
  let logBlocks := opts.logBlocks
  let memory : IO String := match opts.memory with
    | some read => read
    | none => pure "?"
  let worker (_workerId : Nat) : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break
      | some item =>
        let logThis := logBlocks && item.cenv.constants.size > 600000
        if logThis then
          IO.println s!"  [block] BEGIN {item.lo.pretty} ({item.all.size} members)"
          (← IO.getStdout).flush
        let t0 ← IO.monoMsNow
        let outcome := auxBlockOutcome item.cenv item.lo item.all
        let t1 ← IO.monoMsNow
        if logThis then
          let mem ← memory
          IO.println s!"  [block] END {item.lo.pretty} {t1 - t0}ms rss {mem}"
          (← IO.getStdout).flush
        discard <| resultChan.send (item.lo, item.all, outcome)

  let mut workerTasks : Array (Task (Except IO.Error Unit)) := #[]
  for i in [:numWorkers] do
    let task ← IO.asTask (prio := .dedicated) (worker i)
    workerTasks := workerTasks.push task

  let mut remaining : Set Name := {}
  for (lo, _) in blocks.blocks do
    remaining := remaining.insert lo
  -- A source dependency settles at its own block's completion, successful
  -- or failed (`auxDependencyReady`): a parent's provisional aux publication
  -- cannot release it before its original-form promotion. Failed blocks
  -- settle too, so their dependents still run and fail with
  -- MissingConstant, recorded per member — mirroring the Rust scheduler's
  -- release-on-failure cascade.
  let mut settledNames : Set Name := {}

  if dbg then
    IO.println s!"  [Lean CompileAux] {totalBlocks} blocks, {numWorkers} workers"

  let mut waveNum := 0
  let mut compiled := 0

  while !remaining.isEmpty do
    waveNum := waveNum + 1
    let snapshot := acc.cenv
    let mut ready : Array (Name × Set Name) := #[]
    for lo in remaining do
      let some all := blocks.blocks.get? lo
        | discard <| workChan.close
          return .error s!"wave driver: block {lo.pretty} is not in the condensation"
      let deps := match blocks.blockRefs.get? lo with
        | some d => d
        | none => {}
      let depsOk := Id.run do
        for d in deps do
          if !auxDependencyReady blocks.lowLinks.contains snapshot settledNames d then
            return false
        return true
      if depsOk then
        ready := ready.push (lo, all)

    if ready.isEmpty then
      discard <| workChan.close
      return .error s!"Circular dependency detected: {remaining.size} \
blocks remaining but none ready"

    if dbg then
      let pct := (compiled * 100) / totalBlocks
      IO.println s!"  [Lean CompileAux] Wave {waveNum}: {ready.size} blocks ready, {pct}% ({compiled}/{totalBlocks})"

    -- A worker compiles the block under its canonical key, never under the
    -- condensation's representative (which stays the key of `remaining`).
    for (lo, all) in ready do
      discard <| workChan.send { lo := blockKey lo all, all, cenv := snapshot }

    for _ in [:ready.size] do
      match ← resultChan.recv with
      | none =>
        discard <| workChan.close
        return .error "Result channel closed unexpectedly"
      | some (lo, all, outcome) =>
        let (acc', newNames, _) := applyAuxBlockOutcome acc lo all outcome
        for n in all do
          settledNames := settledNames.insert n
        acc := acc'
        if let some rust := rustRef then
          for name in newNames do
            if let some rustAddr := rust.get? name then
              if let some named := acc.cenv.nameToNamed.get? name then
                if named.addr != rustAddr then
                  discard <| workChan.close
                  return .error s!"rustRef mismatch at {name.pretty}: \
lean={named.addr} rust={rustAddr} (block {lo.pretty})"
        compiled := compiled + 1
        -- Memory attribution trace: which driver-retained structure is
        -- growing (`DriverOptions.dbg`).
        if dbg && compiled % 20000 == 0 then
          let mem ← memory
          IO.println s!"  [compile-lean] {compiled}/{totalBlocks} blocks · \
rss {mem} · consts {acc.cenv.constants.size} \
({acc.cenv.totalBytes} B ser) · named {acc.cenv.nameToNamed.size} · \
blobs {acc.cenv.blobs.size} · plans {acc.cenv.callSitePlans.size}\
/{acc.cenv.brecOnCallSitePlans.size}/{acc.cenv.belowCallSitePlans.size} · \
auxNames {acc.cenv.auxNameToAddr.size}"
          (← IO.getStdout).flush

    for (lo, _) in ready do
      remaining := remaining.erase lo

  discard <| workChan.close

  if compiled != totalBlocks then
    return .error s!"Only compiled {compiled}/{totalBlocks} blocks - \
circular dependency?"

  return .ok (assembleEnv acc)

/-! ## The full pure-Lean pipeline

`Lean canon → ref graph → ground filter → condense → aux-aware parallel
compile → serialize` — the Lean-side mirror of Rust
`compile_env_with_options`' setup phases (env.rs:146-260) feeding the
scheduler. This is what `ix compile-lean` and `ix validate-lean`
phase 1 run.

Both drivers apply Rust's env-level domain restriction
(`validate_ind_groups`) first: an input inductive group whose stored flags
differ from the recomputed ones (`validateInductiveFlags`) fails the compile
before any block is scheduled. -/

/-- Result of the full pure-Lean compile pipeline. -/
structure LeanPipelineOut where
  /-- Canonical serialized environment (`Ixon.serEnv`). -/
  bytes : ByteArray
  /-- The assembled environment. -/
  env : Ixon.Env
  /-- Final driver state (per-block failures live in `cenv.ungrounded`). -/
  cenv : CompileEnv
  /-- Constants rejected by the pre-compile groundedness scan. -/
  ungroundedCount : Nat
  /-- SCC block count. -/
  blockCount : Nat
  /-- Per-name content digest of every INPUT constant's canonicalized
      form (derived `Hashable`), collected during the streamed canon
      pass. The whole-env canon map is never materialized; this is the
      phase-5 decompile oracle for `ix validate-lean`. -/
  digests : Std.HashMap Ix.Name UInt64 := {}
  /-- The input carries semantic contracts: its output is emitted only after
      the resource post-step (`Ix.CompileM.resourcePostStep`). -/
  annotated : Bool := false

/-- Run the full pure-Lean compile pipeline over a constant list.

    STREAMING: the whole-env canonicalized map is never materialized.
    The canon pass canonicalizes each constant TRANSIENTLY — extracting
    its reference set, immediate groundedness error, and content digest
    — then drops the canon form. The compile phase reads constants
    through `Environment.fallback?` (canon-on-demand against the pinned
    Lean constants), so a constant's canon form is live only while some
    block actually reads it: theorem-sized proof bodies exist once
    during the canon pass and once during their own block's compile,
    never all at once. Canon is per-constant deterministic (chunking is
    already arbitrary), so compiled output is byte-identical to the
    materialized pipeline.

    See the section docstring; phase timings print when `dbg` is set. -/
def inspectSemanticSource (source : Lean.ConstantInfo) : Except String Unit := do
  if !Ix.Compile.sourceHasSemanticContracts source then return
  let (canonical, _) := (Ix.CanonM.canonConst source).run {}
  let _ ← Ix.SemanticContract.inspect canonical.getCnst.type
  match canonical with
  | .defnInfo info => let _ ← Ix.SemanticContract.inspect info.value; pure ()
  | .thmInfo info => let _ ← Ix.SemanticContract.inspect info.value; pure ()
  | .opaqueInfo info => let _ ← Ix.SemanticContract.inspect info.value; pure ()
  | .axiomInfo _ => pure ()
  | _ => throw s!"annotated inductive/constructor/recursor transformations are unsupported: {source.name}"

def compileDecoratedConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    : IO (Except String LeanPipelineOut) := do
  let annotated := consts.any fun (_, source) => Ix.Compile.sourceHasSemanticContracts source
  for (name, source) in consts do
    if Ix.Compile.sourceHasAnnotations source then
      return .error s!"unresolved source binder contracts: {name}"
    match inspectSemanticSource source with
    | .error error => return .error error
    | .ok _ => pure ()
  let dbg := opts.dbg
  let tick (label : String) (t0 : Nat) : IO Nat := do
    let t1 ← IO.monoMsNow
    if dbg then
      IO.println s!"  [compile-lean] {label}: {t1 - t0}ms"
    pure t1
  let t0 ← IO.monoMsNow
  let constArr := consts.toArray
  -- 1a. Name pre-pass: canonical names only. Builds the lazy-lookup key
  --     map (Ix name → pinned Lean constant), the reverse name-hash
  --     view for `nameForAddr`, and the THIN ground-check env — ground
  --     checks read only name-existence and is-it-a-ctor
  --     (`groundExpr`/`groundConst`), so two shared placeholder
  --     constants stand in for every value.
  let placeholderCnst : Ix.ConstantVal :=
    ⟨.mkAnon, #[], Ix.Expr.mkSort Ix.Level.mkZero⟩
  let phAxiom : Ix.ConstantInfo :=
    .axiomInfo { cnst := placeholderCnst, isUnsafe := false }
  let phCtor : Ix.ConstantInfo := .ctorInfo
    { cnst := placeholderCnst, induct := .mkAnon, cidx := 0
      numParams := 0, numFields := 0, isUnsafe := false }
  let mut leanByIx : Std.HashMap Ix.Name (Lean.Name × Lean.ConstantInfo) := {}
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  let mut thinConsts : Ix.Map Ix.Name Ix.ConstantInfo := {}
  let mut ixArr : Array (Ix.Name × Lean.ConstantInfo) := #[]
  for (ln, lci) in constArr do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    leanByIx := leanByIx.insert ixn (ln, lci)
    nameByHash := nameByHash.insert ixn.getHash ixn
    thinConsts := thinConsts.insert ixn
      (if lci matches .ctorInfo _ then phCtor else phAxiom)
    ixArr := ixArr.push (ixn, lci)
  let thinEnv : Ix.Environment := { consts := thinConsts }
  let t ← tick s!"canon names ({ixArr.size} consts)" t0
  -- 1b/2/3a. Streamed canon (chunk-parallel): canonicalize, take refs +
  --     immediate ground error + digest. PROOF bodies (`thmInfo` /
  --     `opaqueInfo` — the bulk of a Mathlib-scale env, and never read
  --     by dependents' compiles) are dropped after extraction and
  --     re-canonicalized on demand for their own block only. CODE kinds
  --     (definitions, inductive families, recursors — what aux-gen and
  --     kernel ingress read from dependents, repeatedly and with
  --     retention) are KEPT and materialized as the shared `consts`
  --     map: one shared structure instead of a fresh unshared copy per
  --     on-demand read.
  let chunkSize := max 1 ((ixArr.size + numWorkers - 1) / numWorkers)
  let chunkArr := Ix.CanonM.chunks ixArr chunkSize
  let tasks := chunkArr.map fun chunk =>
    Task.spawn fun _ => Id.run do
      let mut state : Ix.CanonM.CanonState := {}
      let mut out : Array
        (Ix.Name × Ix.Set Ix.Name × Option Ix.GroundError × UInt64
          × Option Ix.ConstantInfo) := #[]
      for (ixn, lci) in chunk do
        let (ci, state') := StateT.run (Ix.CanonM.canonConst lci) state
        state := state'
        let (refs, _) :=
          Ix.GraphM.run { consts := {} } .init (Ix.graphConst ci)
        let groundErr? := match Ix.groundConstCheck ci thinEnv with
          | .ok _ => none
          | .error e => some e
        let keep? := match ci with
          | .thmInfo _ | .opaqueInfo _ => none
          | _ => some ci
        out := out.push (ixn, refs, groundErr?, hash ci, keep?)
      out
  let mut outRefs : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  let mut immediate : Ix.Map Ix.Name Ix.GroundError := {}
  let mut digests : Std.HashMap Ix.Name UInt64 := {}
  let mut codeConsts : Ix.Map Ix.Name Ix.ConstantInfo := {}
  for task in tasks do
    for (n, refs, gerr?, dig, keep?) in task.get do
      outRefs := outRefs.insert n refs
      if let some e := gerr? then
        immediate := immediate.insert n e
      digests := digests.insert n dig
      if let some ci := keep? then
        codeConsts := codeConsts.insert n ci
  let t ← tick s!"canon+graph+ground ({outRefs.size} nodes, \
{codeConsts.size} code kept, {outRefs.size - codeConsts.size} proofs streamed)" t
  let mut inRefs : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  for (n, refs) in outRefs do
    for r in refs do
      inRefs := inRefs.alter r fun
        | some s => some (s.insert n)
        | none => some (({} : Ix.Set Ix.Name).insert n)
  let ungrounded := Ix.proliferateUngrounded immediate inRefs
  let groundedOutRefs :=
    if ungrounded.isEmpty then outRefs
    else outRefs.fold (init := {}) fun m name refs =>
      if ungrounded.contains name then m
      else m.insert name (refs.fold (init := {}) fun s r =>
        if ungrounded.contains r then s else s.insert r)
  if dbg && !ungrounded.isEmpty then
    IO.println s!"  [compile-lean] {ungrounded.size} ungrounded constants filtered"
    for (n, e) in ungrounded.toList.take 5 do
      IO.println s!"    ungrounded: {n.pretty} ({repr e.kind})"
  let t ← tick s!"ground ({ungrounded.size} ungrounded)" t
  -- 4. Condense (Tarjan SCCs over the filtered graph).
  let condensed := Ix.CondenseM.run groundedOutRefs
  let t ← tick s!"condense ({condensed.blocks.size} blocks)" t
  -- 5. Aux-aware parallel compile against the HYBRID environment: code
  --    kinds are the materialized (shared) map; proof bodies
  --    canonicalize on demand from the pinned Lean constants and are
  --    dropped when their block's `CompileM.run` returns.
  let fallback : Ix.Name → Option Ix.ConstantInfo := fun n =>
    (leanByIx.get? n).bind fun (ln, lci) =>
      ((Ix.CanonM.canonChunk #[(ln, lci)])[0]?).map (·.2)
  let ixEnv : Ix.Environment :=
    { consts := codeConsts, fallback? := some fallback }
  match ← compileEnvParallelAux ixEnv condensed rustRef numWorkers opts
      nameByHash with
  | .error e => return .error e
  | .ok (ixonEnv, _, cenv) =>
    let t ← tick "compile" t
    -- The constants the groundedness scan rejected are failures of the
    -- compile, each with its named refusal (`GroundError.refusal`), as the
    -- Rust compiler records them: an input constant is never dropped
    -- without a record (`ix compile-lean` is fail-closed on them).
    let cenv := ungrounded.fold (init := cenv) fun c n e =>
      if c.ungrounded.contains n then c
      else { c with ungrounded := c.ungrounded.insert n (e.refusal ungrounded.contains) }
    if dbg && cenv.ungrounded.size > 0 then
      IO.println s!"  [compile-lean] {cenv.ungrounded.size} per-block compile failures"
      for (n, e) in cenv.ungrounded.toList.take 5 do
        IO.println s!"    failed: {n.pretty}: {e.take 200}"
    -- 6. Serialize. Resource validation is a post-step of the caller's
    -- (`Ix.CompileM.resourcePostStep`, `Ix.CompileResource`): semantic
    -- emission is atomic only through it, so an annotated input's output
    -- is emitted only after it (`annotated`).
    match Ixon.serEnv ixonEnv with
    | .error e => return .error s!"serEnv failed: {e}"
    | .ok bytes =>
      let _ ← tick s!"serialize ({bytes.size} bytes)" t
      return .ok {
        bytes
        env := ixonEnv
        cenv
        ungroundedCount := ungrounded.size
        blockCount := condensed.blocks.size
        digests
        annotated }

/-- Explicit frontend boundary: resolve occurrence contracts before
canonicalization. Resources are validated by the caller's post-step
(`Ix.CompileM.compileLeanInputValidated`). -/
def compileLeanInput (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {}) :
    IO (Except String LeanPipelineOut) := do
  let constants ← match input.prepare with
    | .ok constants => pure constants
    | .error error => return .error error
  compileDecoratedConsts constants rustRef numWorkers opts

/-- Compile an isolated source list, extracting its checked occurrence records. -/
def compileLeanConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {}) :
    IO (Except String LeanPipelineOut) := do
  let input ← match Ix.Compile.CompileInput.fromAnnotations consts with
    | .ok input => pure input
    | .error error => return .error (toString error)
  compileLeanInput input rustRef numWorkers opts

/-- Native compiler entrypoint with an explicitly committed resource profile. -/
@[extern "rs_compile_env_to_ixon_profile"]
opaque rsCompileEnvProfileFFI :
  @& List (Lean.Name × Lean.ConstantInfo) → @& ByteArray → IO Ixon.RawEnv

def rsCompileInput (input : Ix.Compile.CompileInput)
    (resourceProfile : Option Ix.Resource.Profile := none) : IO Ixon.Env := do
  let constants ← IO.ofExcept input.prepare
  let raw ← match resourceProfile with
    | none => rsCompileEnvFFI constants
    | some profile =>
      let _ ← IO.ofExcept profile.address
      rsCompileEnvProfileFFI constants profile.bytes
  return raw.toEnv

end Ix.CompileM



