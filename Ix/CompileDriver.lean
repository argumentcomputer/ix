/-
  Ix.CompileDriver: the aux-aware compile-env driver.

  Port of the production scheduler semantics of
  `crates/compile/src/compile/env.rs` (`compile_env_with_options`,
  env.rs:146-990) and the per-block dispatch of `compile_const` /
  `compile_const_no_aux` (compile.rs:3249-3716), on top of the pure
  block compiler (`Ix.CompileM`) and the aux-generation tail
  (`Ix.AuxGen.CompileAux.compileMutualAuxTail`).

  This module sits ABOVE `Ix.AuxGen` (unlike Rust, where everything
  shares one crate): `Ix.CompileM`'s own `compileEnv`/`compileEnvParallel`
  cannot invoke the aux tail without an import cycle, so the aux-aware
  driver lives here. The pre-existing drivers in `Ix.CompileM` remain as
  the plain no-aux-pipeline substrate.

  Deliberate deviations from Rust, none output-visible:
  - Sequential scheduling instead of work-stealing threads. Output maps
    are keyed by name/address. Name claims (`nameToAddr`,
    `auxNameToAddr`) and call-site plans are insert-once: a second claim
    at a different address, or a different plan, is the error Rust's
    insert-once scheduler raises (`checkBlockClaims`, A0's single
    ownership). `Named` entries are last-wins overrides within one block's
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
public import Ix.AuxGen.CompileAux
public import Ix.Compile.SourceContract.Transport
public import Ix.Resource.Validate
public import Ix.Compile.Pass.Driver
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
    (`aliasPrecedes`), `dflt` for the empty set. A7 (D9): the drivers name a
    block by this key, never by the condensation's representative (the
    Tarjan root, which depends on the graph's iteration order and so differs
    between a closure compile, the whole compile and the Rust condensation)
    nor by the first element of a `Set` in iteration order. -/
def canonicalKey (dflt : Name) (names : Array Name) : Name :=
  names.foldl (init := names[0]?.getD dflt) fun k n => if aliasPrecedes n k then n else k

/-- `canonicalKey` of a block's member set. -/
def blockKey (lo : Name) (all : Set Name) : Name :=
  canonicalKey lo all.toArray

/-- The Pass 3 reference fast path is queried with the driver's canonical
block key, not the condensation's Tarjan representative. Preserve missing
entries so malformed/incomplete reference caches still take the scanning
fallback; do not invent an empty reference set. -/
def canonicalBlockRefs (blocks : Ix.CondensedBlocks) : Std.HashMap Name (Set Name) :=
  blocks.blocks.fold (init := {}) fun refs lo all =>
    match blocks.blockRefs.get? lo with
    | some rs => refs.insert (blockKey lo all) rs
    | none => refs

/-- Source graph and code lookup retained by a streaming caller. O11a
queries inductives and definitions, so proof bodies need not be decoded. -/
structure SchedulingSource where
  refs : Ix.Map Name (Set Name)
  const? : Name → Option Ix.ConstantInfo

/-- Add source-determined sizeOf producer edges at the common driver
boundary, including direct sequential/wave callers. A pipeline that already
has the source graph supplies it, so streaming proof bodies are not decoded
again. These are scheduling edges, not changes to the source SCC partition. -/
def prepareSizeOfScheduling (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (source? : Option SchedulingSource := none) : Ix.CondensedBlocks :=
  let source := match source? with
    | some source => source
    | none => { const? := env.get?, refs :=
        blocks.lowLinks.fold (init := {}) fun refs n _ =>
          match env.get? n with
          | some ci => refs.insert n (Ix.Compile.Canon.refsConst ci)
          | none => refs.insert n {} }
  Ix.Compile.Pass.Opt.addSizeOfEdges source.const? source.refs blocks

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
    let result ← timedC .exprCompile (compileConstantInfo const)
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
  let sortedClasses := orderRecursorFamily (← sortConsts cs.toList)
  let blockResult ← timedC .exprCompile (compileMutualBlock sortedClasses)
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
    let projAddr := Address.blake3 (Ixon.ser proj)
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
  -- `tailBegin`/`tailEnd` count the tail's kernel ingress (`Ix.PhaseTimers`;
  -- both are the identity, and do nothing unless `IX_PHASE_TIMERS` is set).
  let kctx₀ := Ix.PhaseTimers.tailBegin lo Ix.AuxGen.AuxKernelCtx.new
  let ((auxLayout?, plans, brecPlans, belowPlans), kctx) ← timedC .auxTail
    ((Ix.AuxGen.compileMutualAuxTail cs sortedClasses blockResult.blockAddr
      maps).run kctx₀)
  let auxLayout? := Ix.PhaseTimers.tailEnd kctx.tcState.env.consts.size auxLayout?
  -- Pass 3 (`IX_PASS3=images`): a changed block registers no surgery plan;
  -- its Ix auxiliaries get their `_ix` display names and the block records
  -- its image-kind heads (`Ix.Compile.Pass.Driver.editChangedBlock`).
  if cenv.pass3 && Ix.Compile.Pass.isChanged cs blockResult.classNames auxLayout? then
    Ix.Compile.Pass.editChangedBlock cs blockResult.classNames auxLayout?
    return (blockResult, auxLayout?, {}, {}, {})
  -- A3V-IPB: an unchanged block's permuted `IndPredBelow` family
  if cenv.pass3 then
    Ix.Compile.Pass.editPermutedBelowFamily cs
  return (blockResult, auxLayout?, plans, brecPlans, belowPlans)

/-- Run `compileBlockWithAux` purely, returning the tail outputs and the
    final block state. -/
def runBlockWithAuxCore (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError
        (BlockResult × BlockState × Option Ixon.AuxLayout
          × Std.HashMap Name CallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan) := do
  let blockEnv : BlockEnv :=
    { all, current := lo, mutCtx := default, univCtx := [] }
  -- Pass 3: the block's members rewritten (Def 3.6) and its image constants
  -- compiled; identity when the switch is off.
  let (cenv, init) ← match Ix.Compile.Pass.prepareBlock cenv all lo with
    | .ok r => pure r
    | .error e => throw (.invalidMutualBlock e)
  let ((result, layout?, plans, brecPlans, belowPlans), cache) ←
    CompileM.run cenv blockEnv init (compileBlockWithAux lo all)
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
  -- A7 (D2c): the members in canonical order (`aliasPrecedes`), not in
  -- `Set` iteration order, so the first match below (`leanAll`, the phase)
  -- is a function of the member set. On valid input every member gives the
  -- same `.all` and the same phase family (the order note above), so the
  -- value is the one the iteration order gave.
  --
  -- The `auxGenExtraNames` reads are closure-determined on valid input: a
  -- name is in the set iff an aux tail claimed it, and the tail that claims
  -- a regenerated auxiliary or one of its Lean `.all` siblings is the tail
  -- of the owning inductive block, which every block of that family
  -- references and so precedes in every schedule (A7 report, D2c).
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

/-! ## Pass 3: the images of a changed block's Lean auxiliaries -/

/-- Pass 3: compile an image block (every member an image-kind auxiliary of
a changed block): the images under the Lean names, each with
`Named.original` = Lean's own form compiled without any rewrite (the
provenance decompile verifies against). -/
def runImageBlock (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError (BlockResult × BlockState) := do
  let imgs ← match Ix.Compile.Pass.compileImageBlock cenv all with
    | .ok r => pure r
    | .error e => throw (.invalidMutualBlock e)
  let (origRes, origCache) ← compileConstNoAuxPure cenv lo all
  let origs : Std.HashMap Name (Address × Ixon.ConstantMeta) :=
    if origRes.projections.isEmpty then ({} : Std.HashMap Name _).insert lo (origRes.blockAddr, origRes.blockMeta)
    else origRes.projections.foldl (init := {}) fun m (n, proj, cm) =>
      m.insert n (Address.blake3 (Ixon.ser proj), cm)
  let mut cache : BlockState := { blockBlobs := origCache.blockBlobs, blockNames := origCache.blockNames }
  let mut result? : Option BlockResult := none
  for (a, r, bs) in imgs do
    cache := { cache with
      auxConsts := cache.auxConsts.push (r.blockAddr, r.block)
      auxNamed := cache.auxNamed.push (a, { addr := r.blockAddr, constMeta := r.blockMeta
                                            original := origs.get? a })
      auxNameToAddr := cache.auxNameToAddr.insert a r.blockAddr
      blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) cache.blockBlobs
      blockNames := bs.blockNames.fold (fun m k v => m.insert k v) cache.blockNames
      defHints := bs.defHints.fold (fun m k v => m.insert k v) cache.defHints }
    if a == lo then result? := some r
  let some result := result? | throw (.invalidMutualBlock s!"Pass 3: no image for {lo.pretty}")
  return (result, cache)

/-- Compile one block with the aux tail (`runBlockWithAuxCore`); under Pass 3
an image block compiles to its images (`runImageBlock`). -/
def runBlockWithAux (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError
        (BlockResult × BlockState × Option Ixon.AuxLayout
          × Std.HashMap Name CallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan
          × Std.HashMap Name BRecOnCallSitePlan) := do
  if Ix.Compile.Pass.isImageBlock cenv all then
    let (result, cache) ← runImageBlock cenv all lo
    return (result, cache, none, {}, {}, {})
  runBlockWithAuxCore cenv all lo

/-! ## Driver state and merges -/

/-- Accumulated driver-level side maps that live OUTSIDE `CompileEnv`
    (mirrors the fields the pre-existing drivers thread manually). -/
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
    `name_claim_conflict` (compile.rs:470-482), including the 12-hex-digit
    address prefixes. -/
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
    result.projections.map fun (name, proj, _) => (name, Address.blake3 (Ixon.ser proj))

/-- Single ownership of the names a block claims (A0; Rust
    `CompileState::claim_compiled_name` and `claim_aux_name`,
    compile.rs:324-370, and the checked plan inserts, compile.rs:4990-5115),
    checked against the LIVE driver state before anything is merged.

    Rust claims inside the block, against the shared state, in this order:
    - the primary names (`claim_compiled_name`): an `aux_name_to_addr` or a
      `name_to_addr` entry at another address is a conflict (the second
      check since A7);
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
    -- A7 (a7s §6.2): a second compiled claim at another address, by an
    -- earlier block or earlier in this block, is a conflict too (Rust's
    -- `claim_compiled_name` now checks `name_to_addr` the same way). It
    -- was an overwrite, so the address a name kept depended on which block
    -- merged last; an identical re-claim stays a no-op, so valid input
    -- (where no name is compiled twice) merges the same values.
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
  -- Pass 3 (empty unless the switch is on): the reserved names a block
  -- registers (`_ix` display names, image constants `a._ix`) and its records
  -- are insert-once too: several components of one Lean block may register
  -- the same entry, never a different one.
  for (name, addr) in cache.auxNameToAddr do
    if Ix.Compile.Pass.hasReserved name then
      if let some existing := cenv.auxNameToAddr.get? name then
        if existing != addr then throw (nameClaimConflict name existing addr)
  -- A7 (D1): each record is checked against the live state AND against the
  -- block's own earlier records. The block's arrays are merged by a fold
  -- (`mergeCompiledBlock`), so two records of one key inside one block were
  -- last-wins: which one survived depended on the order the block's
  -- components pushed them. Now a differing second record is the same
  -- conflict as a differing record of another block, and an identical one
  -- is a no-op, so on valid input (no such pair) the merged maps are the
  -- same values as before.
  let mut heads : Std.HashMap Name Name := {}
  for (name, key) in cache.p3Heads do
    if let some existing := (heads.get? name).orElse fun _ => cenv.p3Heads.get? name then
      if existing != key then
        throw (.invalidMutualBlock s!"Pass 3: conflicting image-kind head '{name.pretty}'")
    heads := heads.insert name key
  let mut p3Blocks : Std.HashMap Name (Array Name) := {}
  for (key, all) in cache.p3Blocks do
    if let some existing := (p3Blocks.get? key).orElse fun _ => cenv.p3Blocks.get? key then
      if existing != all then
        throw (.invalidMutualBlock s!"Pass 3: conflicting Lean block '{key.pretty}'")
    p3Blocks := p3Blocks.insert key all
  let mut recs : Std.HashMap Name RecursorVal := {}
  for (name, rv) in cache.p3AuxRecs do
    if let some existing := (recs.get? name).orElse fun _ => cenv.p3CanonRecs.get? name then
      if existing != rv then
        throw (.invalidMutualBlock s!"Pass 3: conflicting canonical recursor '{name.pretty}'")
    recs := recs.insert name rv

/-- Merge one compiled block's outputs into the driver state, mirroring
    the Rust global-mutation order: block constant, member projections
    (primary `register_name` + `name_to_addr`, compile.rs:3902-3969),
    then the tail's aux constants, Named overrides (incl. the synthetic
    `Muts` entry and aliases), aux name→addr map, extra names, and
    call-site plans.

    Every caller first checks the block for single ownership against the
    live state (`checkBlockClaims`) and merges only if the check passes: a
    conflict is an error and nothing is merged. The check is a separate
    step, not part of this function, so that the merge keeps consuming the
    driver state uniquely (a merge returning `Except` would keep the old
    state alive for the error branch and copy every map it inserts into).
    `Named` entries are overrides by design (the tail re-registers
    regenerated names and the `Muts` entry), as with Rust's
    `register_name`; content-keyed tables (constants, blobs) are unioned by
    content. -/
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
      let projAddr := Address.blake3 projBytes
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
  -- Pass 3 records of a changed block (empty unless the switch is on).
  if cenv.pass3 then
    cenv := { cenv with
      p3CanonRecs := cache.p3AuxRecs.foldl (fun m (k, v) => m.insert k v) cenv.p3CanonRecs
      p3Heads := cache.p3Heads.foldl (fun m (k, v) => m.insert k v) cenv.p3Heads
      p3Blocks := cache.p3Blocks.foldl (fun m (k, v) => m.insert k v) cenv.p3Blocks }
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

/-- The scheduler's promote-remaining pass over a pre-compiled block's
    members (Rust env.rs:757-789). A member already in `nameToAddr` keeps
    its address; an aux claim on it at a different address is recorded as
    a conflict for that member (single ownership, A0) instead of being
    skipped silently. A member not yet registered takes its resolved
    address. Returns the members newly registered. -/
def promoteRemaining (acc : DriverAcc) (all : Set Name) : DriverAcc × Array Name := Id.run do
  let mut acc := acc
  let mut newNames : Array Name := #[]
  for name in all do
    match acc.cenv.nameToAddr.get? name with
    | some existing =>
      if let some claimed := acc.cenv.auxNameToAddr.get? name then
        if claimed != existing then
          let msg := toString (nameClaimConflict name existing claimed)
          acc := { acc with cenv := { acc.cenv with
            ungrounded := acc.cenv.ungrounded.insert name msg } }
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
    `CompileState::promote_aux` (compile.rs:309-350), including the
    meta self-name coherence check. -/
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
    cenv := { cenv with nameToAddr := cenv.nameToAddr.insert name auxAddr }
  if let some named := cenv.nameToNamed.get? name then
    let named' := { named with original := some (origAddr, origMeta) }
    cenv := { cenv with nameToNamed := cenv.nameToNamed.insert name named' }
  pure cenv

/-! ## Aux-gen seeds: scheduling dependencies (Rust: the prereq pre-pass, env.rs:993-1140) -/

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

/-- The aux-gen seeds of a compile: `auxGenSeedNames`, plus `And` under
    Pass 3 (images pack with `And` at Prop motives; `PProd` and `True` are
    seeds already), restricted to the names the condensation holds. -/
def auxGenSeeds (blocks : Ix.CondensedBlocks) (pass3 : Bool) : Array Name :=
  let seeds := if pass3 then auxGenSeedNames.push (Name.mkStr .mkAnon "And")
    else auxGenSeedNames
  seeds.filter blocks.lowLinks.contains

/-- The blocks of the seeds' closure (their representatives, in DFS
    post-order over the condensed graph; env.rs:1063-1097). -/
def auxGenSeedClosure (blocks : Ix.CondensedBlocks) (pass3 : Bool) : Array Name := Id.run do
  let seedReps := (auxGenSeeds blocks pass3).filterMap (blocks.lowLinks.get? ·)
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
  return order

/-- The scheduling dependencies of each block: its references, and for a
    block outside the seeds' closure also the seeds themselves.

    A7 (D2b). Aux tails emit references to the seeds (`PUnit`, `PProd`,
    `Eq`, …) that the Lean source of the block need not contain, so the
    seeds must be compiled before any tail runs. Rust (and the Lean drivers
    before A7) did that with a pre-pass (`precompile_aux_gen_prereqs`,
    env.rs:1036-1140) that compiled the seeds' closure before the schedule,
    moved the names into `aux_name_to_addr`, and re-promoted them when
    their own blocks came up. Here the seeds are ordinary dependencies of
    every block that is not in their closure (no cycle: nothing in the
    closure reaches such a block), and the seeds' blocks are compiled by
    the schedule like any other. Each seed block is compiled by the same
    `runBlockWithAux` on its own closure either way, its names end at the
    same addresses with the same `Named`, and the promotion route the
    pre-pass forced on them registered nothing else (the pre-pass skipped
    blocks an aux tail had claimed, which take the promotion route with
    their original-form compile in both versions), so the output is the
    same; the gates (Init+Std against both compilers,
    schedule identity) check it. The pre-pass's failure mode (one failing
    seed block failed the whole compile) becomes the ordinary per-block
    failure with its cascade. -/
def scheduleDeps (blocks : Ix.CondensedBlocks) (pass3 : Bool) : Std.HashMap Name (Set Name) :=
  Id.run do
  let seeds := auxGenSeeds blocks pass3
  let inClosure : Std.HashSet Name :=
    (auxGenSeedClosure blocks pass3).foldl (init := {}) (·.insert ·)
  let mut out : Std.HashMap Name (Set Name) := {}
  for (lo, _) in blocks.blocks do
    let refs := (blocks.blockRefs.get? lo).getD {}
    out := out.insert lo
      (if inClosure.contains lo then refs else seeds.foldl (·.insert ·) refs)
  return out

/-- Assemble the final `Ixon.Env` from the accumulated driver state
    (shared tail of both aux drivers, identical to the plain drivers'
    assembly: names index, name blobs, finalize_hints — the exact
    per-Named channel plus the per-address `anonHints` advisory map with
    order-independent merge). -/
def assembleEnv (acc : DriverAcc) : Ixon.Env × Nat × CompileEnv := Id.run do
  let cenv := acc.cenv
  let (addrToNameMap, namesMap, nameBlobs) :=
    cenv.nameToNamed.fold (init := ({}, acc.blockNames, {}))
      fun (addrMap, namesMap, blobs) name named =>
        -- A7 (D14): the canonical alias, not the last one the fold met.
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

/-- Pass 3: the first input name with a reserved `_ix` component (D14),
    as a rejection message. -/
def pass3ReservedInput? (blocks : Ix.CondensedBlocks) : Option String := Id.run do
  for (_, all) in blocks.blocks do
    for n in all do
      if let some msg := Ix.Compile.Pass.reservedInput? n then return some msg
  return none

/-! ## The aux-aware sequential driver -/

/-- Compile an entire environment with the FULL production pipeline
    semantics: the aux-gen seeds as scheduling dependencies (A7, D2b), per-block aux tails
    (regeneration + call-site plans), the scheduler promotion pass with
    the no-aux original-form second compile (`Named.original`), and
    pending-aux dependency release. Sequential mirror of Rust
    `compile_env_with_options`' scheduler (env.rs:146-990; grounding and
    SCC condensation happen upstream of the `blocks` input, as in the
    Rust FFI phase split).

    Per-block failures are recorded in `ungrounded` per member and the
    scheduler continues (dependents cascade into `MissingConstant`
    failures recorded the same way) — mirroring env.rs:727-737. -/
def compileEnvAux (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (nameByHash : Std.HashMap Address Name := {})
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (pass3 : Bool := false)
    (schedulingSource? : Option SchedulingSource := none)
    : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
  if pass3 then
    if let some msg := pass3ReservedInput? blocks then return .error msg
  -- Pass 3: the changed-clique hook's scheduling edges (`Ix.Compile.Pass.Cliques`)
  let (blocks, p3Cliques, p3CliqueRoots) :=
    if pass3 then Ix.Compile.Pass.scheduleCliques env blocks else (blocks, {}, {})
  let blocks := if pass3 then prepareSizeOfScheduling env blocks schedulingSource? else blocks
  let p3BlockRefs := if pass3 then canonicalBlockRefs blocks else {}
  let cenv0 : CompileEnv :=
    { CompileEnv.new env with nameByHash, sharingLimits, pass3, p3BlockRefs, p3Cliques, p3CliqueRoots }
  let mut acc : DriverAcc := { cenv := cenv0 }
  -- A7 (D2b): the aux-gen seeds are scheduling dependencies, not a pre-pass.
  let schedDeps := scheduleDeps blocks pass3

  let totalBlocks := blocks.blocks.size
  let mut blockInfo : Std.HashMap Name (Set Name × Nat) := {}
  let mut reverseDeps : Std.HashMap Name (Array Name) := {}
  for (lo, all) in blocks.blocks do
    let deps := (schedDeps.get? lo).getD {}
    blockInfo := blockInfo.insert lo (all, deps.size)
    for depName in deps do
      reverseDeps := reverseDeps.alter depName fun
        | some arr => some (arr.push lo)
        | none => some #[lo]
  -- A7 (D9): the ready blocks keyed by their canonical key (`blockKey`), the
  -- least taken first. The fold's order is then the least-key-first
  -- topological order of the block graph, a function of the graph and the
  -- keys alone. It was a stack filled in `HashMap` iteration order, so the
  -- order depended on the condensation's representatives and the maps'
  -- histories. The output does not depend on the order on valid input (the
  -- schedule-identity gate), so this changes no value; it makes the
  -- sequential driver the fold of design document §6.2 literally.
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
    -- A7 (D9): `lo` is the block's canonical key from here on.
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
          for m in all do
            acc := { acc with cenv := { acc.cenv with
              ungrounded := acc.cenv.ungrounded.insert m msg } }
        else
          -- Cross-SCC compile of the unresolved subset (env.rs:617-651).
          let crossAll : Set Name :=
            unresolvedNames.foldl (fun s n => s.insert n) {}
          -- A7 (D9): the subset is named by its canonical key, not by its
          -- first name in `Set` order.
          let clo := canonicalKey lo unresolvedNames
          match runBlockWithAux acc.cenv crossAll clo with
          | .error _ =>
            -- Rust logs and does NOT register failed names — dependents
            -- will get MissingConstant rather than broken data.
            pure ()
          | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
            -- A conflicting claim is a compile failure of the subset (Rust
            -- claims inside `compile_const`): nothing is registered.
            match checkBlockClaims acc.cenv (primaryClaims clo result) cache plans brecPlans
                belowPlans with
            | .error _ => pure ()
            | .ok () =>
              acc := mergeCompiledBlock acc clo result cache plans brecPlans belowPlans
              for n in unresolvedNames do
                acc := { acc with
                  cenv := { acc.cenv with
                    auxGenExtraNames := acc.cenv.auxGenExtraNames.insert n }
                  pending := acc.pending.push n }
      if anyAuxGen && !auxIncomplete then
        -- Compile the original Lean form and promote (env.rs:656-693).
        match compileConstNoAuxPure acc.cenv lo all with
        | .error e =>
          let msg := toString e
          for m in all do
            acc := { acc with cenv := { acc.cenv with
              ungrounded := acc.cenv.ungrounded.insert m msg } }
        | .ok (result, cache) =>
          -- Promote per member: original projection (addr, meta) — or the
          -- lone constant for singleton no-aux blocks.
          let promotions : Array (Name × Address × Ixon.ConstantMeta) :=
            if result.projections.isEmpty then
              #[(lo, result.blockAddr, result.blockMeta)]
            else
              result.projections.map fun (name, proj, constMeta) =>
                (name, Address.blake3 (Ixon.ser proj), constMeta)
          let mut promoteFailed := false
          for (name, origAddr, origMeta) in promotions do
            if promoteFailed then continue
            match Ix.PhaseTimers.withPhase .noAux acc.cenv
              (promoteAuxDriver · name origAddr origMeta) with
            | .error e =>
              promoteFailed := true
              let msg := toString e
              for m in all do
                acc := { acc with cenv := { acc.cenv with
                  ungrounded := acc.cenv.ungrounded.insert m msg } }
            | .ok cenv' =>
              acc := { acc with cenv := cenv' }
          -- The ephemeral compile still stores blobs/name components and
          -- records hints (Rust `store_string`/`compile_name`/`def_hints`
          -- are unconditional; only const/Named stores are aux-gated).
          acc := { acc with
            cenv := { acc.cenv with
              blobs := cache.blockBlobs.fold (fun m k v => m.insert k v)
                acc.cenv.blobs }
            blockNames := cache.blockNames.fold (fun m k v => m.insert k v)
              acc.blockNames
            defHints := cache.defHints.fold (fun m k v => m.insert k v)
              acc.defHints }
      if !auxIncomplete then
        -- Promote remaining names from auxNameToAddr (env.rs:757-789).
        acc := (promoteRemaining acc all).1
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
        -- inside `compile_const`).
        match checkBlockClaims acc.cenv (primaryClaims lo result) cache plans brecPlans belowPlans with
        | .error e => acc := fail acc e
        | .ok () => acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans

    -- Release dependents: block members plus drained pending-aux names
    -- (env.rs:838-870).
    let pendingDrained := acc.pending
    acc := { acc with pending := #[] }
    let mut releaseNames : Array Name := #[]
    for n in all do
      releaseNames := releaseNames.push n
    releaseNames := releaseNames ++ pendingDrained
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

Wave-based parallel version of `compileEnvAux`, mirroring the plain
`compileEnvParallel` architecture: each wave snapshots the accumulated
`CompileEnv`, workers compute a pure per-block outcome against the
snapshot, and the main thread applies the same merges as the sequential
driver. Blocks within a wave are dependency-independent, and every merge
is per-name-disjoint or content-keyed: two blocks of one wave that claim
one name at different addresses (or one plan key with different plans)
are refused by the merge-time check (`checkBlockClaims`) against the live
state, as Rust's insert-once claims refuse them. Which of the two blocks
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
      subset (non-aux case); `incompleteMsg` the aux-incomplete failure;
      `noAux` the original-form compile for `Named.original` grafting;
      `noAuxFailMsg` its failure. The promote-remaining loop runs at
      merge time against the live env. -/
  | promoted
      (crossScc : Option (Name × BlockResult × BlockState
        × Std.HashMap Name CallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan))
      (crossNames : Array Name)
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
    let mut incompleteMsg := none
    if !unresolvedNames.isEmpty then
      if anyAuxGen then
        let missing := ", ".intercalate (unresolvedNames.toList.map (·.pretty))
        incompleteMsg := some s!"aux_gen precompile incomplete for \
{lo.pretty}; missing canonical aliases: {missing}"
      else
        let crossAll : Set Name :=
          unresolvedNames.foldl (fun s n => s.insert n) {}
        -- A7 (D9): named by its canonical key, as in the sequential driver.
        let clo := canonicalKey lo unresolvedNames
        match runBlockWithAux cenv crossAll clo with
        | .error _ => pure ()
        | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
          crossScc := some (clo, result, cache,
            plans, brecPlans, belowPlans)
          crossNames := unresolvedNames
    let mut noAux := none
    let mut noAuxFailMsg := none
    if anyAuxGen && incompleteMsg.isNone then
      match Ix.PhaseTimers.withPhase .noAux cenv (compileConstNoAuxPure · lo all) with
      | .error e => noAuxFailMsg := some (toString e)
      | .ok out => noAux := some out
    return .promoted crossScc crossNames incompleteMsg noAux noAuxFailMsg
  else
    match runBlockWithAux cenv all lo with
    | .error e => return .failed (toString e)
    | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
      return .compiled result cache plans brecPlans belowPlans

/-- Apply a worker outcome to the live driver state. Returns the names
    newly REGISTERED by this block (for rustRef fail-fast comparison), and
    whether the block failed at merge time: a conflicting claim
    (`checkBlockClaims`) fails the block like a compile error, so the wave
    loop must release its dependents as failed. -/
def applyAuxBlockOutcome (acc : DriverAcc) (lo : Name) (all : Set Name)
    (outcome : AuxBlockOutcome) : DriverAcc × Array Name × Bool := Id.run do
  let mut acc := acc
  let mut newNames : Array Name := #[]
  let recordFailure (acc : DriverAcc) (msg : String) : DriverAcc := Id.run do
    let mut acc := acc
    for m in all do
      acc := { acc with cenv := { acc.cenv with
        ungrounded := acc.cenv.ungrounded.insert m msg } }
    return acc
  match outcome with
  | .compiled result cache plans brecPlans belowPlans =>
    match checkBlockClaims acc.cenv (primaryClaims lo result) cache plans brecPlans belowPlans with
    | .error e => return (recordFailure acc (toString e), #[], true)
    | .ok () => acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans
    if result.projections.isEmpty then
      newNames := newNames.push lo
    else
      for (name, _, _) in result.projections do
        newNames := newNames.push name
    for (n, _) in cache.auxNamed do
      newNames := newNames.push n
  | .failed msg =>
    acc := recordFailure acc msg
  | .promoted crossScc crossNames incompleteMsg noAux noAuxFailMsg =>
    if let some (clo, result, cache, plans, brecPlans, belowPlans) := crossScc then
      -- A conflicting claim is a compile failure of the cross-SCC subset,
      -- as in the sequential driver: nothing is registered.
      match checkBlockClaims acc.cenv (primaryClaims clo result) cache plans brecPlans belowPlans with
      | .error _ => pure ()
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
    match incompleteMsg with
    | some msg =>
      acc := recordFailure acc msg
    | none =>
      match noAuxFailMsg with
      | some msg =>
        acc := recordFailure acc msg
      | none =>
        if let some (result, cache) := noAux then
          let promotions : Array (Name × Address × Ixon.ConstantMeta) :=
            if result.projections.isEmpty then
              #[(lo, result.blockAddr, result.blockMeta)]
            else
              result.projections.map fun (name, proj, constMeta) =>
                (name, Address.blake3 (Ixon.ser proj), constMeta)
          let mut promoteFailed := false
          for (name, origAddr, origMeta) in promotions do
            if promoteFailed then continue
            match Ix.PhaseTimers.withPhase .noAux acc.cenv
              (promoteAuxDriver · name origAddr origMeta) with
            | .error e =>
              promoteFailed := true
              acc := recordFailure acc (toString e)
            | .ok cenv' =>
              acc := { acc with cenv := cenv' }
          acc := { acc with
            cenv := { acc.cenv with
              blobs := cache.blockBlobs.fold (fun m k v => m.insert k v)
                acc.cenv.blobs }
            blockNames := cache.blockNames.fold (fun m k v => m.insert k v)
              acc.blockNames
            defHints := cache.defHints.fold (fun m k v => m.insert k v)
              acc.defHints }
      -- Promote remaining names from auxNameToAddr (env.rs:757-789) —
      -- against the LIVE env; also counts as registration for rustRef.
      let (acc', promoted) := promoteRemaining acc all
      acc := acc'
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

/-- Parallel aux-aware environment compile. Same output as
    `compileEnvAux` (see the module docstring for the intra-wave
    order-independence argument); wave-based workers mirror the plain
    `compileEnvParallel`.

    `rustRef` enables fail-fast address comparison: after each block's
    merge, every name it registered is checked against the reference
    map; the first divergence aborts with the offending name. -/
def compileEnvParallelAux (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (nameByHash : Std.HashMap Address Name := {})
    (pass3? : Option Bool := none)
    (schedulingSource? : Option SchedulingSource := none)
    : IO (Except String (Ixon.Env × Nat × CompileEnv)) := do
  let totalBlocks := blocks.blocks.size
  -- The `IX_SHARING_LIMITS` override (`ix compile-lean --sharing-limits`).
  let sharingLimits ← match ← compilerSharingLimitsFromEnv with
    | .ok l => pure l
    | .error e => return .error e

  let tPre ← IO.monoMsNow
  -- Pass 3, the faithful rewrite (`IX_PASS3=images`); off by default.
  let pass3 ← match pass3? with
    | some b => pure b
    | none => pure (Ix.Compile.Pass.switchOn (← IO.getEnv Ix.Compile.Pass.switchVar))
  if pass3 then
    if let some msg := pass3ReservedInput? blocks then return .error msg
  -- Pass 3: the changed-clique hook's scheduling edges (`Ix.Compile.Pass.Cliques`)
  let (blocks, p3Cliques, p3CliqueRoots) :=
    if pass3 then Ix.Compile.Pass.scheduleCliques env blocks else (blocks, {}, {})
  let blocks := if pass3 then prepareSizeOfScheduling env blocks schedulingSource? else blocks
  let p3BlockRefs := if pass3 then canonicalBlockRefs blocks else {}
  let cenv0 : CompileEnv :=
    { CompileEnv.new env with nameByHash, sharingLimits, pass3, p3BlockRefs, p3Cliques, p3CliqueRoots }
  let mut acc : DriverAcc := { cenv := cenv0 }
  -- A7 (D2b): the aux-gen seeds are scheduling dependencies, not a pre-pass.
  let schedDeps := scheduleDeps blocks pass3
  let tWaves ← IO.monoMsNow
  Ix.PhaseTimers.wall " (compile) scheduling dependencies" (tWaves - tPre)

  let workChan ← Std.CloseableChannel.Sync.new (α := AuxWorkItem)
  let resultChan ← Std.CloseableChannel.Sync.new
    (α := Name × Set Name × AuxBlockOutcome)

  -- IX_LOG_BLOCKS=1: per-block BEGIN/END trace (with duration and RSS at
  -- END), gated to the tail of the run (snapshot > 600k constants) where
  -- the whole-Mathlib memory spike lives — identifies which block a
  -- worker is inside when RSS blows up.
  let logBlocks := (← IO.getEnv "IX_LOG_BLOCKS").isSome
  -- IX_LOG_SLOW=<ms>: BEGIN for every block and END for the blocks slower
  -- than <ms> (stderr; diagnostics only, the output is unaffected).
  let logSlow := (← IO.getEnv "IX_LOG_SLOW").bind String.toNat?
  let worker (_workerId : Nat) : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break
      | some item =>
        let logThis := logBlocks && item.cenv.constants.size > 600000
        if logThis then
          IO.println s!"  [block] BEGIN {item.lo.pretty} ({item.all.size} members)"
          (← IO.getStdout).flush
        if logSlow.isSome then
          IO.eprintln s!"[block] BEGIN {item.lo.pretty}"
        let t0 ← IO.monoMsNow
        let outcome := Ix.PhaseTimers.withPhase .blockOther item.cenv
          (auxBlockOutcome · item.lo item.all)
        let t1 ← IO.monoMsNow
        if let some ms := logSlow then
          IO.eprintln s!"[block] {if t1 - t0 ≥ ms then "SLOW" else "END"} {item.lo.pretty} {t1 - t0}ms"
        if logThis then
          let rssKb ← do
            let st ← IO.FS.readFile "/proc/self/status"
            pure <| (st.splitOn "\n").findSome? fun l =>
              if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
          IO.println s!"  [block] END {item.lo.pretty} {t1 - t0}ms \
rss{(rssKb.getD "?").trimAscii}"
          (← IO.getStdout).flush
        discard <| resultChan.send (item.lo, item.all, outcome)

  let mut workerTasks : Array (Task (Except IO.Error Unit)) := #[]
  for i in [:numWorkers] do
    let task ← IO.asTask (prio := .dedicated) (worker i)
    workerTasks := workerTasks.push task

  let mut remaining : Set Name := {}
  for (lo, _) in blocks.blocks do
    remaining := remaining.insert lo
  -- Names of failed blocks count as "released" so dependents still run
  -- (and fail with MissingConstant, recorded per member) — mirroring the
  -- Rust scheduler's release-on-failure cascade.
  let mut failedNames : Set Name := {}

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
      let deps := (schedDeps.get? lo).getD {}
      let depsOk := Id.run do
        for d in deps do
          if (resolveAddrPure snapshot d).isNone && !failedNames.contains d then
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

    -- A7 (D9): a worker compiles the block under its canonical key, never
    -- under the condensation's representative (which stays the key of
    -- `remaining` only).
    for (lo, all) in ready do
      discard <| workChan.send { lo := blockKey lo all, all, cenv := snapshot }

    for _ in [:ready.size] do
      match ← resultChan.recv with
      | none =>
        discard <| workChan.close
        return .error "Result channel closed unexpectedly"
      | some (lo, all, outcome) =>
        if let .failed _ := outcome then
          for n in all do
            failedNames := failedNames.insert n
        if let .promoted _ _ (some _) _ _ := outcome then
          for n in all do
            failedNames := failedNames.insert n
        let (acc', newNames, mergeFailed) := Ix.PhaseTimers.withPhase .merge acc
          (applyAuxBlockOutcome · lo all outcome)
        if mergeFailed then
          for n in all do
            failedNames := failedNames.insert n
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
        -- growing. Enable with `dbg` or IX_COMPILE_DBG=1.
        if dbg && compiled % 20000 == 0 then
          let rssKb ← do
            let st ← IO.FS.readFile "/proc/self/status"
            pure <| (st.splitOn "\n").findSome? fun l =>
              if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
          IO.println s!"  [compile-lean] {compiled}/{totalBlocks} blocks · \
rss{(rssKb.getD "?").trimAscii} · consts {acc.cenv.constants.size} \
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

  let tAsm ← IO.monoMsNow
  Ix.PhaseTimers.wall " (compile) block waves" (tAsm - tWaves)
  let out := assembleEnv acc
  match out with
  | (env, n, cenv) =>
    Ix.PhaseTimers.wall " (compile) assemble" ((← IO.monoMsNow) - tAsm)
    return .ok (env, n, cenv)

/-! ## The full pure-Lean pipeline

`Lean canon → ref graph → ground filter → condense → aux-aware parallel
compile → serialize` — the Lean-side mirror of Rust
`compile_env_with_options`' setup phases (env.rs:146-260) feeding the
scheduler. This is what `ix compile-lean` and `ix validate-lean`
phase 1 run.

Rust's env-level `validate_ind_groups` domain restriction is not
re-scanned here: the per-block nested-expansion path performs the same
inductive-flag validation when it matters, and the compile fails loudly
there on non-canonical flags. -/

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
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (resourceProfile : Option Ix.Resource.Profile := none)
    (pass3? : Option Bool := none)
    : IO (Except String LeanPipelineOut) := do
  let tInspect ← IO.monoMsNow
  let annotated := consts.any fun (_, source) => Ix.Compile.sourceHasSemanticContracts source
  for (name, source) in consts do
    if Ix.Compile.sourceHasAnnotations source then
      return .error s!"unresolved source binder contracts: {name}"
    match inspectSemanticSource source with
    | .error error => return .error error
    | .ok _ => pure ()
  Ix.PhaseTimers.wall "semantic-contract inspection" ((← IO.monoMsNow) - tInspect)
  -- IX_COMPILE_DBG=1 forces phase timing + the driver's periodic memory
  -- attribution trace without threading a flag through callers.
  let dbg := dbg || (← IO.getEnv "IX_COMPILE_DBG").isSome
  let tick (label : String) (t0 : Nat) : IO Nat := do
    let t1 ← IO.monoMsNow
    if dbg then
      IO.println s!"  [compile-lean] {label}: {t1 - t0}ms"
    Ix.PhaseTimers.wall label (t1 - t0)
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
  -- 4. Condense (Tarjan SCCs over the filtered graph: Pass 1's
  --    `Ix.Compile.Canon.condensation`).
  let condensed ← match Ix.CondenseM.run groundedOutRefs with
    | .ok c => pure c
    | .error e => return .error e
  -- Preserve the pipeline's historical preparation in switch-off mode too.
  -- On-mode common-driver preparation is idempotent with these same edges.
  let condensed := Ix.Compile.Pass.Opt.addSizeOfEdges codeConsts.get? groundedOutRefs condensed
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
  match ← compileEnvParallelAux ixEnv condensed rustRef numWorkers dbg
      nameByHash pass3? (some { refs := groundedOutRefs, const? := codeConsts.get? }) with
  | .error e => return .error e
  | .ok (ixonEnv, _, cenv) =>
    let t ← tick "compile" t
    if dbg && cenv.ungrounded.size > 0 then
      IO.println s!"  [compile-lean] {cenv.ungrounded.size} per-block compile failures"
      for (n, e) in cenv.ungrounded.toList.take 5 do
        IO.println s!"    failed: {n.pretty}: {e.take 200}"
    -- Semantic emission is atomic: a failed source declaration must not
    -- disappear into an otherwise successful partial artifact.
    if annotated || resourceProfile.isSome then
      if !ungrounded.isEmpty || !cenv.ungrounded.isEmpty then
        return .error "resource compilation requires the complete requested closure"
      match Ix.Resource.validate ixonEnv (resourceProfile.getD (Ix.Resource.standardProfile ixonEnv)) with
      | .error error => return .error error
      | .ok _ => pure ()
    -- 6. Serialize only after the combined validation succeeds.
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
        digests }

/-- Explicit frontend boundary: resolve occurrence contracts before
canonicalization, then validate resources and erased types before emission. -/
def compileLeanInput (input : Ix.Compile.CompileInput)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (resourceProfile : Option Ix.Resource.Profile := none)
    (pass3? : Option Bool := none) :
    IO (Except String LeanPipelineOut) := do
  let tPrep ← IO.monoMsNow
  let constants ← match input.prepare with
    | .ok constants => pure constants
    | .error error => return .error error
  Ix.PhaseTimers.wall "source-contract preparation (prepare)" ((← IO.monoMsNow) - tPrep)
  compileDecoratedConsts constants rustRef numWorkers dbg resourceProfile pass3?

/-- Compile an isolated source list, extracting its checked occurrence records. -/
def compileLeanConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (resourceProfile : Option Ix.Resource.Profile := none)
    (pass3? : Option Bool := none) :
    IO (Except String LeanPipelineOut) := do
  let input ← match Ix.Compile.CompileInput.fromAnnotations consts with
    | .ok input => pure input
    | .error error => return .error (toString error)
  compileLeanInput input rustRef numWorkers dbg resourceProfile pass3?

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

