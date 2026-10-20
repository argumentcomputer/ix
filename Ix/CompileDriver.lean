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
  - One schedule, a pure fold over waves of ready blocks applied in
    block-key order (`compileEnvFold`), instead of work-stealing threads
    and Rust's seed pre-pass (the seeds are scheduling dependencies). Output maps
    are keyed by name/address. Name claims (`nameToAddr`,
    `auxNameToAddr`) and Pass 3's records are insert-once: a second claim
    at a different address, or a different record, is the error Rust's
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
    flows through the tail into Pass 3's hook and the re-registered
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
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Driver
public import Ix.AuxGen.CompileAux
public import Ix.AuxGen.SourceService
public import Ix.AuxGen.IxcScope
public import Ix.Compile.SourceContract.Transport
public import Ix.Resource.Addressed
public section

namespace Ix.CompileM

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
    (Rust `compile_mutual`, compile.rs:3719-4144), then Pass 3's hook
    (`Ix.Compile.Pass.editBlock`), whose output the block returns.

    Between the primary compile and the tail, the members' projection
    addresses are inserted into `BlockState.blockNameToAddr` — Rust
    writes them into the global `name_to_addr` at exactly that point
    (compile.rs:3926/3946/3966), and the tail's aux compilation resolves
    sibling members through them. -/
def compileBlockWithAux (lo : Name) (all : Set Name)
    : CompileM (BlockResult × Option Ixon.AuxLayout × Ix.Compile.Pass.Published) := do
  let const ← findConst lo
  let isIndBlock := match const with
    | .inductInfo _ | .ctorInfo _ => true
    | _ => false
  if all.size == 1 && !isIndBlock then
    let result ← compileConstantInfo const
    return (result, none, {})
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
  let blockResult ← compileMutualBlock sortedClasses
  -- Alpha-collapsed standalone (single non-inductive class): Rust
  -- returns BEFORE the Muts registration and the aux tail
  -- (compile.rs:3872) — no synthetic Muts entry, no aux regeneration.
  let isMuts := match blockResult.block.info with
    | .muts _ => true
    | _ => false
  if !isMuts then
    return (blockResult, none, {})
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
  -- The kernel AuxGen asks: `Ix.Tc` over the bridge (AuxGen M0), and for a
  -- safe block's `.below` IxC Source mode through the fold's oracle (AuxGen
  -- M2b, `CompileEnv.auxOracle`). An unsafe block is outside every statement
  -- and Source mode declines unsafe inductives, so its tail keeps `Ix.Tc`.
  -- Under a measurement mode (`IX_AUXGEN_IXC`) the tail's counts are traced.
  let safe := cs.all fun
    | .indc ind => !ind.isUnsafe
    | .recr rv => !rv.isUnsafe
    | .defn d => d.safety != .unsaf
  let kernel : Ix.AuxGen.AuxKernel :=
    match if safe then cenv.auxOracle.bind (· lo) else none with
    | some oracle => .ixc maps oracle
    | none => .tc maps
  let ((auxLayout?, recs), kctx) ←
    (Ix.AuxGen.compileMutualAuxTail cs sortedClasses blockResult.blockAddr
      maps kernel).run Ix.AuxGen.AuxKernelCtx.new
  if let .ixc _ oracle := kernel then
    if oracle.trace then
      let st := { kctx.ixcStats with asked := if oracle.asked then 1 else 0 }
      dbg_trace s!"{Ix.AuxGen.IxcStats.line lo st}"
      pure ()
  -- Pass 3, hook 1: a changed block's Ix auxiliaries to their display names
  let published ← Ix.Compile.Pass.editBlock cs blockResult.classNames auxLayout?
    recs.recs recs.belowRecs
  return (blockResult, auxLayout?, published)

/-- Run `compileBlockWithAux` purely, returning the tail outputs and the
    final block state. Pass 3, hook 2 first: a block that references an
    image-kind head compiles from its members rewritten, with their
    decompile records (`Ix.Compile.Pass.prepareBlock`), whose extension
    references go into the members' metadata (`withMetaRefs`). -/
def runBlockWithAux (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError
        (BlockResult × BlockState × Option Ixon.AuxLayout × Ix.Compile.Pass.Published) := do
  let (cenv, prepared) ← Ix.Compile.Pass.prepareBlock cenv all lo
  let blockEnv : BlockEnv :=
    { all, current := lo, mutCtx := default, univCtx := [] }
  let ((result, layout?, published), cache) ←
    CompileM.run cenv blockEnv {} (compileBlockWithAux lo all)
  pure (Ix.Compile.Pass.withMetaRefs cache.p3MetaRefs lo result, cache, layout?,
    prepared ++ published)

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

/-- Compile one block: an image block (every member an image-kind head of a
    changed block, `Ix.Compile.Pass.isImageBlock`) to its images, with
    `Named.original` from Lean's own form (`Ix.Compile.Pass.runImageBlock`
    over `compileConstNoAuxPure`); any other block with its aux tail
    (`runBlockWithAux`). -/
def runBlock (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError
        (BlockResult × BlockState × Option Ixon.AuxLayout × Ix.Compile.Pass.Published) :=
  if Ix.Compile.Pass.isImageBlock cenv all then
    (fun (result, cache, published) => (result, cache, none, published)) <$>
      Ix.Compile.Pass.runImageBlock compileConstNoAuxPure cenv all lo
  else
    runBlockWithAux cenv all lo

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
    `CompileState::claim_compiled_name` and `claim_aux_name`, and Pass 3's
    insert-once records), checked against the LIVE driver state before
    anything is merged.

    Rust claims inside the block, against the shared state, in this order:
    - the primary names (`claim_compiled_name`): an `aux_name_to_addr` or a
      `name_to_addr` entry at another address is a conflict;
    - the aux tail's names (`claim_aux_name`): a `name_to_addr` entry
      (including this block's own primary names) or an earlier
      `aux_name_to_addr` claim at another address is a conflict, and an
      identical re-claim is a no-op;
    - Pass 3 (`pass3::driver::edit_changed_block`): the `_ix` display names
      a changed block's Ix auxiliaries move to, then its image-kind heads,
      its Lean block and its canonical recursors: a different entry already
      published under the name (or earlier in this block) is a conflict, an
      identical one a no-op (several components of one Lean block publish
      the same heads and block).

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
    (cache : BlockState) (published : Ix.Compile.Pass.Published)
    : Except CompileError Unit := do
  let mut compiled : Std.HashMap Ix.Compile.ExactKey.ExactName Address := {}
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
  let mut claimed : Std.HashMap Ix.Compile.ExactKey.ExactName Address := {}
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
  -- Pass 3: the display names (reserved `_ix` names) are insert-once.
  for (name, addr) in cache.auxNameToAddr do
    if Ix.Compile.Pass.hasReserved name then
      if let some existing := cenv.auxNameToAddr.get? name then
        if existing != addr then throw (nameClaimConflict name existing addr)
  -- Pass 3's records, each against the live state and the block's own
  -- earlier records.
  let mut heads : Std.HashMap Ix.Compile.ExactKey.ExactName Name := {}
  for (name, key) in published.heads do
    if let some existing := (heads.get? name).orElse fun _ => cenv.p3Heads.get? name then
      if existing != key then
        throw (.invalidMutualBlock s!"Pass 3: conflicting image-kind head '{name.pretty}'")
    heads := heads.insert name key
  let mut blocks : Std.HashMap Ix.Compile.ExactKey.ExactName (Array Name) := {}
  for (key, all) in published.blocks do
    if let some existing := (blocks.get? key).orElse fun _ => cenv.p3Blocks.get? key then
      if existing != all then
        throw (.invalidMutualBlock s!"Pass 3: conflicting Lean block '{key.pretty}'")
    blocks := blocks.insert key all
  let mut recs : Std.HashMap Ix.Compile.ExactKey.ExactName RecursorVal := {}
  for (name, rv) in published.canonRecs do
    if let some existing := (recs.get? name).orElse fun _ => cenv.p3CanonRecs.get? name then
      if existing != rv then
        throw (.invalidMutualBlock s!"Pass 3: conflicting canonical recursor '{name.pretty}'")
    recs := recs.insert name rv

/-- Validate both the block's name claims (`checkBlockClaims`) and its
    anonymous payloads (`checkBlockContent`: a reused record or blob address
    must hold the same bytes) against the live state before publishing any
    output of this block. -/
def checkCompiledBlock (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    (cache : BlockState) (published : Ix.Compile.Pass.Published)
    : Except CompileError Unit := do
  checkBlockClaims cenv (primaryClaims lo result) cache published
  checkBlockContent cenv result cache

/-- The names of a compiled block whose `Named` entry another block owns
    (`mergeCompiledBlock`, CQ2.24 b): its primary names already claimed in
    `nameToAddr`, and its aux claims already in `auxNameToAddr`. A function
    of its own: when the merge read the state inside its own loops, a second
    reference to the state stayed alive and every insert of the merge
    copied its maps (Init+Std's compile phase went from 44 s to 388 s). -/
def reclaimedNames (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    (cache : BlockState) : Std.HashSet Name := Id.run do
  let primaryNames : Array Name :=
    if result.projections.isEmpty then #[lo] else result.projections.map (·.1)
  let mut reclaimed : Std.HashSet Name := {}
  for name in primaryNames do
    if cenv.nameToAddr.contains name then
      reclaimed := reclaimed.insert name
  for (n, _) in cache.auxNamed do
    if cache.auxGenExtraNames.contains n && cache.auxNameToAddr.contains n
        && cenv.auxNameToAddr.contains n then
      reclaimed := reclaimed.insert n
  return reclaimed

/-- Merge one compiled block's outputs into the driver state, mirroring
    the Rust global-mutation order: block constant, member projections
    (primary `register_name` + `name_to_addr`, compile.rs:3902-3969),
    then the tail's aux constants, Named overrides (incl. the synthetic
    `Muts` entry and aliases), aux name→addr map, extra names, and
    Pass 3's records (`Ix.Compile.Pass.Published`).

    Every caller first checks the block against the live state
    (`checkCompiledBlock`: single ownership of its names, and its records'
    and blobs' bytes) and merges only if the check passes: a conflict is an
    error and nothing is merged. The check is a separate step, not part of
    this function, so that the merge keeps consuming the driver state
    uniquely (a merge returning `Except` would keep the old state alive for
    the error branch and copy every map it inserts into). `Named` entries
    the block owns are overrides by design (the tail re-registers
    regenerated names and the `Muts` entry), as with Rust's `register_name`;
    content-keyed tables (constants, blobs) are unioned by content, which the
    check made conflict-free.

    An identical re-claim of a name an earlier block claimed in the same
    table (a primary name already in `nameToAddr`, an aux claim already in
    `auxNameToAddr`; the check made the addresses equal) does not own the
    name: its `Named` entry is not merged, so the owner's entry, with the
    original and hints its promotion set, is kept, and which entry a name
    keeps does not depend on which block merged last (CQ2.24 b, R03-16's
    residual). Mirrors Rust `CompileState::claim_and_register_compiled` and
    `claim_and_register_aux`; a name this block claims twice is still its
    own (Rust: the claim is in the block's transaction log). -/
def mergeCompiledBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState)
    (published : Ix.Compile.Pass.Published) : DriverAcc := Id.run do
  let mut cenv := acc.cenv
  -- The names whose `Named` entry another block owns, read from the state
  -- before this merge by a function of its own, so that the merge below
  -- still consumes the driver state's maps uniquely. Do not inline it: read
  -- in this function's loops, the state stayed referenced twice and every
  -- insert below copied its maps (Init+Std's compile phase 44 s → 391 s).
  let reclaimed := reclaimedNames cenv lo result cache
  cenv := { cenv with
    totalBytes := cenv.totalBytes + result.blockBytes.size
    constants := cenv.constants.insert result.blockAddr result.blockBytes
    blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) cenv.blobs }
  -- Primary registrations.
  if result.projections.isEmpty then
    if !reclaimed.contains lo then
      cenv := { cenv with
        nameToNamed := cenv.nameToNamed.insert lo
          { addr := result.blockAddr, constMeta := result.blockMeta } }
    cenv := { cenv with nameToAddr := cenv.nameToAddr.insert lo result.blockAddr }
  else
    for (name, proj, constMeta) in result.projections do
      let projBytes := Ixon.ser proj
      let projAddr := Address.admissionHash projBytes
      cenv := { cenv with
        totalBytes := cenv.totalBytes + projBytes.size
        constants := cenv.constants.insert projAddr projBytes
        nameToAddr := cenv.nameToAddr.insert name projAddr }
      if !reclaimed.contains name then
        cenv := { cenv with
          nameToNamed := cenv.nameToNamed.insert name { addr := projAddr, constMeta } }
  -- Aux tail outputs: stored constants, Named overrides (in registration
  -- order — LAST wins per name), aux resolution map, extra names, and
  -- Pass 3's records (insert-once, made conflict-free by the check; the
  -- memo tables keep the first entry of a key).
  for (addr, c) in cache.auxConsts do
    cenv := { cenv with constants := cenv.constants.insert addr (Ixon.ser c) }
  for (n, named) in cache.auxNamed do
    if !reclaimed.contains n then
      cenv := { cenv with nameToNamed := cenv.nameToNamed.insert n named }
  cenv := { cenv with
    auxNameToAddr := cache.auxNameToAddr.fold (fun m k v => m.insert k v)
      cenv.auxNameToAddr
    auxGenExtraNames := cache.auxGenExtraNames.fold (fun s n => s.insert n)
      cenv.auxGenExtraNames
    p3Heads := published.heads.foldl (fun m (k, v) => m.insert k v) cenv.p3Heads
    p3Blocks := published.blocks.foldl (fun m (k, v) => m.insert k v) cenv.p3Blocks
    p3CanonRecs := published.canonRecs.foldl (fun m (k, v) => m.insert k v)
      cenv.p3CanonRecs
    p3Views := Ix.Compile.Pass.memoMerge cenv.p3Views published.views
    p3ImageExps := Ix.Compile.Pass.memoMerge cenv.p3ImageExps published.imageExps }
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
    `nameToNamed`, `auxGenExtraNames`, `blocks`, Pass 3's heads and
    canonical recursors, the hints) and the pending releases, and each is
    recorded as a failure with `msg`. Anonymous content and unrelated
    successful names remain available. Mirrors Rust `fail_aux_promotion`
    (env.rs) and the rollback of a failed block's Pass 3 records. -/
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
        p3Heads := acc.cenv.p3Heads.erase n
        p3CanonRecs := acc.cenv.p3CanonRecs.erase n
        ungrounded := acc.cenv.ungrounded.insert n msg }
      defHints := acc.defHints.erase n }
  return { acc with pending := acc.pending.filter (!all.contains ·) }

/-- The claim check of `promoteRemaining`, read-only: the first member, in
    canonical member order, already in `nameToAddr` with an aux claim at a
    different address. -/
def remainingClaimConflict? (cenv : CompileEnv) (all : Set Name) : Option String := Id.run do
  for name in all.toArray.qsort aliasPrecedes do
    if let some existing := cenv.nameToAddr.get? name then
      if let some claimed := cenv.auxNameToAddr.get? name then
        if claimed != existing then
          return some (toString (nameClaimConflict name existing claimed))
  return none

/-- The writes of `promoteRemaining`, after its check: each member not yet
    registered takes its resolved address. Returns the members newly
    registered. -/
def promoteRemainingWrites (acc : DriverAcc) (all : Set Name) : DriverAcc × Array Name := Id.run do
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

/-- The scheduler's promote-remaining pass over a pre-compiled block's
    members (Rust env.rs, after the original-form compile). Every claim is
    checked before any member is published: a member already in `nameToAddr`
    with an aux claim at a different address fails the whole block
    (`failAuxPromotion`, single ownership; the first conflict in canonical
    member order names it). Otherwise each member not yet registered takes
    its resolved address. Returns the members newly registered. -/
def promoteRemaining (acc : DriverAcc) (all : Set Name) : DriverAcc × Array Name :=
  match remainingClaimConflict? acc.cenv all with
  | some msg => (failAuxPromotion acc all msg, #[])
  | none => promoteRemainingWrites acc all

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

/-- The checks of `promoteAuxDriver`, read-only: the meta self-name
    coherence check and the claim (a name already compiled at another
    address than its aux address is a conflict). -/
def checkPromoteAux (cenv : CompileEnv) (name : Name) (origMeta : Ixon.ConstantMeta) :
    Except CompileError Unit := do
  if let some metaAddr := constMetaSelfName? origMeta then
    if metaAddr != name.getHash then
      throw (.invalidMutualBlock s!"promote_aux: name mismatch for \
'{name.pretty}' — compile_name address is {name.getHash} but meta name \
address is {metaAddr}")
  if let some auxAddr := cenv.auxNameToAddr.get? name then
    if let some existing := cenv.nameToAddr.get? name then
      if existing != auxAddr then throw (nameClaimConflict name existing auxAddr)

/-- The writes of `promoteAuxDriver`, after its checks: the aux address
    into the resolution map, the original `(addr, meta)` into the existing
    `Named` entry. -/
def promoteAuxWrites (cenv : CompileEnv) (name : Name)
    (origAddr : Address) (origMeta : Ixon.ConstantMeta) : CompileEnv := Id.run do
  let mut cenv := cenv
  if let some auxAddr := cenv.auxNameToAddr.get? name then
    cenv := { cenv with nameToAddr := cenv.nameToAddr.insert name auxAddr }
  if let some named := cenv.nameToNamed.get? name then
    let named' := { named with original := some (origAddr, origMeta) }
    cenv := { cenv with nameToNamed := cenv.nameToNamed.insert name named' }
  return cenv

/-- Promote an aux_gen-compiled name: copy its aux address into the
    resolution map and graft the ORIGINAL `(addr, meta)` into the
    existing (regenerated) `Named` entry. Mirrors
    `CompileState::promote_aux` (compile.rs), including the meta self-name
    coherence check and the claim: a name already compiled at another
    address is a conflict, not an overwrite. -/
def promoteAuxDriver (cenv : CompileEnv) (name : Name)
    (origAddr : Address) (origMeta : Ixon.ConstantMeta)
    : Except CompileError CompileEnv := do
  checkPromoteAux cenv name origMeta
  pure (promoteAuxWrites cenv name origAddr origMeta)

/-- The original-form promotion's members: each member's original
    `(addr, meta)`, or the lone constant's. -/
def originalPromotions (lo : Name) (result : BlockResult) :
    Array (Name × Address × Ixon.ConstantMeta) :=
  if result.projections.isEmpty then
    #[(lo, result.blockAddr, result.blockMeta)]
  else
    result.projections.map fun (name, proj, constMeta) =>
      (name, Address.admissionHash (Ixon.ser proj), constMeta)

/-- The checks of the original-form promotion, read-only: its blobs agree
    with the published ones (`checkBlobContent`), then each member's
    `promoteAuxDriver` checks in member order. A member's write changes only
    its own `nameToAddr` entry, to its aux address, so checking every member
    against the state before the writes finds the same first error as
    checking each after the writes of the members before it. -/
def checkOriginalPromotion (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    (cache : BlockState) : Except CompileError Unit := do
  checkBlobContent cenv cache
  for (name, _, origMeta) in originalPromotions lo result do
    checkPromoteAux cenv name origMeta

/-- The writes of the original-form promotion, after its checks: each
    member's `promoteAuxDriver` writes, then the ephemeral compile's blobs,
    name components and hints (Rust `store_string`, `compile_name` and
    `def_hints` are unconditional; only constant and `Named` stores are
    aux-gated). -/
def promoteOriginalWrites (acc : DriverAcc) (lo : Name) (result : BlockResult)
    (cache : BlockState) : DriverAcc := Id.run do
  let mut acc := acc
  for (name, origAddr, origMeta) in originalPromotions lo result do
    acc := { acc with cenv := promoteAuxWrites acc.cenv name origAddr origMeta }
  return { acc with
    cenv := { acc.cenv with
      blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) acc.cenv.blobs }
    blockNames := cache.blockNames.fold (fun m k v => m.insert k v) acc.blockNames
    defHints := cache.defHints.fold (fun m k v => m.insert k v) acc.defHints }

/-- The entire original-form promotion in pure state (`checkOriginalPromotion`,
    then `promoteOriginalWrites`). On error the caller keeps none of these
    writes, then withdraws the failed block's earlier auxiliary bindings. -/
def promoteOriginalBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState) : Except CompileError DriverAcc := do
  checkOriginalPromotion acc.cenv lo result cache
  pure (promoteOriginalWrites acc lo result cache)

/-- Finish a source block's promotion atomically: the original-form
    promotion (`promoteOriginalBlock`), then the remaining claims
    (`promoteRemaining`). A failure of either, or a member already recorded
    as failed (a failed cross-SCC subset), fails the whole block: the staged
    original metadata is discarded, even for members outside the scheduled
    block that the original-form compile visited, and the block is withdrawn
    (`failAuxPromotion`). Returns the members newly registered and whether
    the block failed.

    Every check reads the live state before anything is written, in the
    order of the steps: the original-form promotion's, the remaining
    claims' (which the original-form writes cannot change: they set a
    member's `nameToAddr` to its aux claim), then the members' recorded
    failures (which neither step writes). The writes then consume the
    driver state uniquely; a withdrawal that kept the state alive across
    the writes would copy every table they insert into, for every block. -/
def finishAuxPromotion (acc : DriverAcc) (lo : Name) (all : Set Name)
    (original : Option (BlockResult × BlockState)) : DriverAcc × Array Name × Bool := Id.run do
  if let some (result, cache) := original then
    if let .error e := checkOriginalPromotion acc.cenv lo result cache then
      return (failAuxPromotion acc all (toString e), #[], true)
  if let some msg := remainingClaimConflict? acc.cenv all then
    return (failAuxPromotion acc all msg, #[], true)
  for name in all.toArray.qsort aliasPrecedes do
    if let some msg := acc.cenv.ungrounded.get? name then
      return (failAuxPromotion acc all msg, #[], true)
  let acc := match original with
    | some (result, cache) => promoteOriginalWrites acc lo result cache
    | none => acc
  let (acc, names) := promoteRemainingWrites acc all
  return (acc, names, false)

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

/-! ## The aux-gen seeds -/

/-- Seed names for the aux_gen prereq closure — the exact Const refs
    aux_gen emits in generated `.below`/`.brecOn`/`.brecOn.eq` bodies,
    and `And`, which Pass 3's images use to pack Prop motives (`PProd` and
    `True` are seeds already) (Rust `aux_gen_seed_names`, env.rs:1001). -/
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
    Name.mkStr root "True",
    Name.mkStr root "And"]

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

/-- A group's members: its first member's own `all`, read through `get?`
    (a first member that is not an inductive is a group of itself, which
    its validation then refuses). -/
def groupAll (env : Ix.Environment) (first : Name) : Array Name :=
  match env.get? first with
  | some (.inductInfo v) => v.all
  | _ => #[first]

/-- The first members of the input's inductive groups (Rust
    `scan.ind_groups`, graph.rs:120), each once, ordered by
    `Ix.nameCompareExact` (by hash, ties by the name): a set, so neither the
    order `consts` is folded in nor two first members sharing a hash field
    changes it. -/
def groupHeads (env : Ix.Environment) : Std.TreeSet Name Ix.nameCompareExact :=
  env.consts.fold (init := {}) fun heads _ ci =>
    match ci with
    | .inductInfo v =>
      match v.all[0]? with
      | some first => heads.insert first
      | none => heads
    | _ => heads

/-- The inductive groups in the order the validations check them: each first
    member with its own `all` (`groupAll`), in `groupHeads`' order. Rust keeps
    the first `all` met for a first member; the two agree whenever a group's
    members agree on `all`, as in every Lean environment. -/
def orderedGroups (env : Ix.Environment) : Array (Name × Array Name) :=
  (groupHeads env).toArray.map fun first => (first, groupAll env first)

/-- Groups per task in `validateInductiveFlags`. -/
def inductiveFlagsChunk : Nat := 256

/-- The domain restriction of both drivers (Rust `validate_ind_groups`,
    env.rs:277): every input inductive group must carry the flags Lean
    computes for it (`isRec`, `isReflexive`, `numNested`;
    `Ix.AuxGen.validateIndGroup`), or the compile fails before any block is
    scheduled. The groups are checked on parallel tasks, in chunks of
    `inductiveFlagsChunk` in `orderedGroups`' order; the error reported is
    the first in that order (Rust reports one of them). -/
def validateInductiveFlags (env : Ix.Environment) : Except String Unit := Id.run do
  let groups := orderedGroups env
  -- the lookup view of `compileEnvFold`: the groups read constants only
  -- through `get?`, so a materialized and a hybrid environment check alike
  let cenv := CompileEnv.new { consts := {}, fallback? := some env.get? }
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

/-- A constant's safety as the kernels compare it within a mutual block:
    `unsafe`, `partial` (a definition's), or `safe` (theorems, quotients and
    the safe constants of the other kinds). -/
def constSafety : ConstantInfo → String
  | .axiomInfo v | .opaqueInfo v | .inductInfo v | .ctorInfo v | .recInfo v =>
    if v.isUnsafe then "unsafe" else "safe"
  | .defnInfo v =>
    match v.safety with
    | .unsafe => "unsafe"
    | .partial => "partial"
    | .safe => "safe"
  | .thmInfo _ | .quotInfo _ => "safe"

/-- Whether the members present in `env` share one safety. Members are read
    through `get?`, so a hybrid environment's theorem and opaque members
    (`fallback?`) count as in a materialized one; a single member is uniform
    without a lookup (the IO pipeline's fallback re-canonicalizes). -/
def uniformSafety (env : Ix.Environment) (members : Array Name) : Bool := Id.run do
  if members.size ≤ 1 then return true
  let mut first : Option String := none
  for m in members do
    if let some c := env.get? m then
      let s := constSafety c
      match first with
      | none => first := some s
      | some s0 => if s != s0 then return false
  return true

/-- The refusal of members that disagree on safety (`uniformSafety` false):
    the least member present in `env` (by name hash) and the least member
    whose safety differs from its. -/
def mixedSafetyMessage (env : Ix.Environment) (members : Array Name) : String := Id.run do
  let present := (members.filter fun m => (env.get? m).isSome).qsort fun a b =>
    a.getHash.cmpBytes b.getHash == .lt
  let some first := present[0]? | return "mixed safety in a mutual block"
  let s0 := (env.get? first).map constSafety |>.getD "safe"
  for m in present do
    let s := (env.get? m).map constSafety |>.getD "safe"
    if s != s0 then
      return s!"mixed safety in a mutual block: '{first.pretty}' is {s0}, '{m.pretty}' is {s}"
  return "mixed safety in a mutual block"

/-- The second domain restriction of both drivers (Rust
    `validate_mutual_safety`): the members of a mutual block share one
    safety, or the compile fails before any block is scheduled. The kernels
    reject a mixed-safety block, and the compilers' orders do not key on
    safety (C6), so such members could be alpha-collapsed into one
    representative's safety. Checked first on each inductive group (`all`,
    with each member's constructors) in the order of their first members'
    hashes, then on each condensation block in the order of its least
    member's hash; the first disagreement found is the error. Members are
    read through `get?`, so the IO pipeline's hybrid environment, whose
    theorem and opaque members come from `fallback?`, refuses exactly as a
    materialized one does. -/
def validateMutualSafety (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except String Unit := Id.run do
  let groups := orderedGroups env
  for (_, all) in groups do
    let members := all.foldl (init := #[]) fun acc n =>
      match env.get? n with
      | some (.inductInfo v) => acc.push n ++ v.ctors
      | _ => acc.push n
    unless uniformSafety env members do
      return .error (toString (CompileError.invalidMutualBlock (mixedSafetyMessage env members)))
  let least (members : Array Name) : Option Name :=
    members.foldl (init := none) fun acc n => match acc with
      | some m => if n.getHash.cmpBytes m.getHash == .lt then some n else some m
      | none => some n
  let offenders := blocks.blocks.fold (init := #[]) fun (acc : Array (Name × Array Name)) _ set =>
    let members := set.toArray
    if uniformSafety env members then acc
    else match least members with
      | some m => acc.push (m, members)
      | none => acc
  match (offenders.qsort fun a b => a.1.getHash.cmpBytes b.1.getHash == .lt)[0]? with
  | some (_, members) =>
    return .error (toString (CompileError.invalidMutualBlock (mixedSafetyMessage env members)))
  | none => return .ok ()

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

/-! ## Reserved input (D14)

`_ix` names Pass 3's auxiliaries and images, and `_ix.inline`/`_ix.inline_meta`
its placeholders and decompile records (`Ix.Compile.Pass.Names`). The IO
pipeline (`compileDecoratedConsts`) refuses, before compiling, an input
constant with a metadata key that has a reserved component, then an input
name with one, each by its least message, as the Rust compiler does
(`compile_env`): with several reserved inputs both compilers name the same
one. `Ix.Cert.compile` refuses the same input, before its fold, by the same
least messages (`Ix.Cert.reservedRefusal`, over the grounded input), so all
three name the same input (`compile-reserved-mdata`). -/

/-- Some component of the Lean name `n` is reserved
    (`Ix.Compile.Pass.hasReserved` on Lean names). -/
def leanNameHasReserved : Lean.Name → Bool
  | .anonymous => false
  | .str p s => Ix.Compile.Pass.isReservedComponent s || leanNameHasReserved p
  | .num p _ => leanNameHasReserved p

/-- Some metadata key in `e` has a reserved component. -/
def exprHasReservedMetadata (e : Lean.Expr) : Bool :=
  (e.find? fun
    | .mdata data _ => data.entries.any (leanNameHasReserved ·.1)
    | _ => false).isSome

/-- Some expression of the Lean source constant has a metadata key with a
    reserved component: the expressions the reference graph walks (Rust
    `graph::inspect_constant_references`). -/
def sourceHasReservedMetadata (source : Lean.ConstantInfo) : Bool :=
  exprHasReservedMetadata source.type ||
    match source with
    | .defnInfo v => exprHasReservedMetadata v.value
    | .thmInfo v => exprHasReservedMetadata v.value
    | .opaqueInfo v => exprHasReservedMetadata v.value
    | .recInfo v => v.rules.any (exprHasReservedMetadata ·.rhs)
    | _ => false

/-- The least of some messages, by their text. -/
def leastMessage? (msgs : Array String) : Option String :=
  msgs.foldl (init := none) fun best msg =>
    match best with
    | some b => if msg < b then some msg else some b
    | none => some msg

/-- The refusal of input constants with a reserved metadata key: the least
    message (`Ix.Compile.Pass.reservedMetadataInput`), as Rust names it. -/
def reservedMetadataRefusal? (names : Array Name) : Option String :=
  leastMessage? (names.map Ix.Compile.Pass.reservedMetadataInput)

/-- The refusal of reserved input names in a condensation: the least message
    (`Ix.Compile.Pass.reservedInput?`), as Rust names it
    (`pass3::names::reserved_input_in`), not the first in the blocks'
    iteration order. -/
def reservedInputRefusal? (blocks : Ix.CondensedBlocks) : Option String :=
  leastMessage? <| blocks.blocks.fold (init := #[]) fun (acc : Array String) _ all =>
    all.fold (init := acc) fun (acc : Array String) n =>
      match Ix.Compile.Pass.reservedInput? n with
      | some msg => acc.push msg
      | none => acc

/-! ## Per-block outcomes

The driver's step (`compileEnvFold`, below): a block's outcome is computed
against a wave's snapshot of the state (`auxBlockOutcome`, pure), and applied
to the live state (`applyAuxBlockOutcome`). Blocks within a wave are
dependency-independent, and every merge is per-name-disjoint or
content-keyed: two blocks of one wave that claim one name at different
addresses (or one Pass 3 record with different values) are refused by the
merge-time check (`checkCompiledBlock`) against the live state, as Rust's
insert-once claims refuse them; so are conflicting payloads at one record or
blob address. The fold applies a wave's outcomes in block-key order, so the
later block in that order reports the conflict (Rust reports by completion
order). -/

/-- Pure per-block outcome computed by a wave worker. -/
inductive AuxBlockOutcome where
  /-- Normal path: full block compile + aux tail. -/
  | compiled (result : BlockResult) (cache : BlockState)
      (published : Ix.Compile.Pass.Published)
  /-- Promotion path (env.rs:566-708): pre-compiled by prereqs or a
      parent's aux tail. `crossScc` carries the compiled unresolved
      subset (non-aux case), `crossFailure` its names and error when its
      compile fails; `incompleteMsg` the aux-incomplete failure;
      `noAux` the original-form compile for `Named.original` grafting;
      `noAuxFailMsg` its failure. The promote-remaining loop runs at
      merge time against the live env. -/
  | promoted
      (crossScc : Option (Name × BlockResult × BlockState × Ix.Compile.Pass.Published))
      (crossNames : Array Name)
      (crossFailure : Option (Array Name × String))
      (incompleteMsg : Option String)
      (noAux : Option (BlockResult × BlockState))
      (noAuxFailMsg : Option String)
  /-- Normal-path compile failure — soft (env.rs:727-737). -/
  | failed (msg : String)

/-- Compute a block's outcome against a wave-snapshot env. Pure; mirrors
    the per-block body of the sequential driver it replaced (kept for the
    tests as `Tests.Ix.Compile.ScheduleReference.sequential`). -/
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
        match runBlock cenv crossAll clo with
        | .error e => crossFailure := some (unresolvedNames, toString e)
        | .ok (result, cache, _, published) =>
          crossScc := some (clo, result, cache, published)
          crossNames := unresolvedNames
    let mut noAux := none
    let mut noAuxFailMsg := none
    if anyAuxGen && incompleteMsg.isNone then
      match compileConstNoAuxPure cenv lo all with
      | .error e => noAuxFailMsg := some (toString e)
      | .ok out => noAux := some out
    return .promoted crossScc crossNames crossFailure incompleteMsg noAux noAuxFailMsg
  else
    match runBlock cenv all lo with
    | .error e => return .failed (toString e)
    | .ok (result, cache, _, published) =>
      return .compiled result cache published

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
  | .compiled result cache published =>
    match checkCompiledBlock acc.cenv lo result cache published with
    | .error e => return (recordFailure acc all.toArray (toString e), #[], true)
    | .ok () => acc := mergeCompiledBlock acc lo result cache published
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
    if let some (clo, result, cache, published) := crossScc then
      -- A conflicting claim or payload is a failure of the cross-SCC subset,
      -- as in the sequential driver: nothing of it is registered.
      match checkCompiledBlock acc.cenv clo result cache published with
      | .error e =>
        acc := recordFailure acc crossNames (toString e)
      | .ok () =>
        acc := mergeCompiledBlock acc clo result cache published
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

/-! ## The wave fold: the one driver

`compileEnvFold` is the driver of both the pure compiler (`Ix.Cert.compile`)
and the IO pipeline (`compileDecoratedConsts`): the same function, so the
parallel schedule equals the pure one by definition.

**Waves.** A wave is the set of blocks not yet compiled whose scheduling
dependencies are all ready under the one readiness rule
(`auxDependencyReady`) against the state the previous wave left. Every block
of a wave computes its outcome (`auxBlockOutcome`) against that same state,
the wave's snapshot; the outcomes are applied (`applyAuxBlockOutcome`) in the
order of the blocks' canonical keys (`blockKey`, `Ix.nameCompare`), and the
wave's members settle. The fold stops when every block has settled; a wave
with no ready block is an error.

**Parallelism.** A wave's blocks, in key order, are split into at most
`width` contiguous chunks, each computed on a task of its own (`Task.spawn`,
the task pool). The value does not depend on the split or on `width`:
`(Task.spawn f).get = f ()` by definition, and the outcomes are applied in key
order whatever the chunks. `width` bounds how many blocks compile at once
(the IO pipeline passes its `--workers`, which bounds memory on whole-Mathlib
runs; `Ix.Cert.compile` takes `foldWaveTasks`, leaving the pool to balance).
Outcomes are taken in chunk order, so a chunk is applied as soon as the
chunks before it have finished, while later chunks still run.

**Readiness** is counted, not rescanned: each block counts its source-owned
dependencies not yet settled; a settling block releases the blocks waiting on
its members. A block whose count reaches zero is checked against the whole
rule (`auxDependencyReady`, which also covers dependencies no block owns:
those must resolve in the current state); one that fails the check is checked
again at the next wave. So a wave is exactly the set the rule selects: a
block with an unsettled source-owned dependency is not ready under the rule.

**The aux-gen seeds are scheduling dependencies** (`e051b559`, A7 D2b): aux
tails emit references to `auxGenSeedNames` (`PUnit`, `PProd`, `Eq`, …) that a
block's source need not contain, so every block outside the seeds' closure
depends on the seeds. Rust (and these drivers before CQ2.14) pre-compiled the
seeds' closure in a pre-pass (`precompile_aux_gen_prereqs`, env.rs:1036-1140),
moved the names into `auxNameToAddr` and re-promoted them when their blocks
came up. Each seed block is compiled by the same `runBlockWithAux` on its own
closure either way, its names end at the same addresses with the same
`Named`, and the promotion route the pre-pass forced on them registered
nothing else, so the output is the same (checked by `cert-compile-parity-init`,
the byte legs and `compile-schedule-identity`'s reference schedule, which keeps
the pre-pass). A failed seed block is now an ordinary block failure with its
cascade, instead of an error of the whole compile.

**The Source service** (AuxGen M2b; AUXGEN-IXC §3.2, `auxgen-m2.md`): the fold
runs IxC's Source-mode environment over its input **ahead of the waves**
(`Ix.AuxGen.Source.RunAhead`), read through the same lookups as the blocks
(`get?`) and at the committed bundle's evidence: from the start, level by
level of the schedule (`scheduleLevels`), it folds the declaration groups of
the blocks with a Type-level `.below`, with everything they depend on, and
publishes the run after each level. Each such block's aux tail asks
`.below`'s and `.brecOn`'s questions of IxC over its level's run
(`CompileEnv.auxOracle`, `AuxIxcOptions`: `fallback`, so IxC's answers are
the compile's wherever IxC answers; a safe block only, an unsafe block's tail
keeps `Ix.Tc`). `compileEnvFoldWithSource`
waits for the run-ahead at the end and returns what Source mode accepted
(`Ix.AuxGen.Source.Report`). -/

/-- The aux-gen seeds the condensation holds. -/
def auxGenSeeds (blocks : Ix.CondensedBlocks) : Array Name :=
  auxGenSeedNames.filter blocks.lowLinks.contains

/-- The representatives of the blocks the seeds reach: their own blocks and,
    transitively, every block those reference (the closure Rust pre-compiles,
    env.rs:1063-1097). -/
def auxGenSeedClosure (blocks : Ix.CondensedBlocks) : Set Name := Id.run do
  let mut visited : Set Name := {}
  let mut stack : Array Name := (auxGenSeeds blocks).filterMap (blocks.lowLinks.get? ·)
  repeat
    match stack.back? with
    | none => break
    | some rep =>
      stack := stack.pop
      if visited.contains rep then continue
      visited := visited.insert rep
      if let some outRefs := blocks.blockRefs.get? rep then
        for referenced in outRefs do
          if let some depRep := blocks.lowLinks.get? referenced then
            if !visited.contains depRep then
              stack := stack.push depRep
  return visited

/-- Each block's scheduling dependencies, by representative: its
    condensation references, plus every seed for a block outside the seeds'
    closure. No cycle: nothing in the closure references a block outside it. -/
def scheduleDeps (blocks : Ix.CondensedBlocks) : Std.HashMap Name (Set Name) := Id.run do
  let seeds := auxGenSeeds blocks
  let closure := auxGenSeedClosure blocks
  let mut out : Std.HashMap Name (Set Name) := {}
  for (rep, _) in blocks.blocks do
    let refs := (blocks.blockRefs.get? rep).getD {}
    out := out.insert rep (if closure.contains rep then refs else seeds.foldl (·.insert ·) refs)
  return out

/-- The fold's schedule, fixed before the first wave. -/
structure FoldSchedule where
  /-- Each block's scheduling dependencies (`scheduleDeps`), by representative. -/
  deps : Std.HashMap Name (Set Name)
  /-- For each source-owned name, the blocks (representatives) depending on it. -/
  waiters : Std.HashMap Name (Array Name)
  /-- Each block's number of source-owned scheduling dependencies. -/
  sourceDeps : Std.HashMap Name Nat

/-- The schedule of a condensation. The waiter lists are built by taking each
    list out of the map before pushing to it, so that it is never copied
    (PERF P4: `insert d ((getD d #[]).push lo)` copied the list every time). -/
def FoldSchedule.of (blocks : Ix.CondensedBlocks) : FoldSchedule := Id.run do
  let deps := scheduleDeps blocks
  let mut waiters : Std.HashMap Name (Array Name) := {}
  let mut sourceDeps : Std.HashMap Name Nat := {}
  for (rep, ds) in deps do
    let mut k := 0
    for d in ds do
      if blocks.lowLinks.contains d then
        k := k + 1
        let ws := waiters.getD d #[]
        waiters := waiters.erase d
        waiters := waiters.insert d (ws.push rep)
    sourceDeps := sourceDeps.insert rep k
  return { deps, waiters, sourceDeps }

/-- The fold's state between waves. -/
structure FoldState where
  /-- The accumulated driver state. -/
  acc : DriverAcc
  /-- The members of every block that has completed, successfully or not
      (`auxDependencyReady`'s `settled`). -/
  settled : Set Name := {}
  /-- Per block not yet ready-checked: its source-owned dependencies not yet
      settled (absent once zero). -/
  unmet : Std.HashMap Name Nat := {}
  /-- The blocks to check at the next wave: every source-owned dependency
      settled, not yet compiled. -/
  candidates : Array Name := #[]
  /-- Blocks not yet compiled. -/
  remaining : Nat := 0
  /-- Waves so far. -/
  waves : Nat := 0

/-- The state before the first wave. The compile environment learns each
    block's references, by block key (`CompileEnv.p3BlockRefs`, Pass 3's
    cheap test before it walks a block's terms). -/
def FoldState.init (cenv : CompileEnv) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) : FoldState := Id.run do
  let mut unmet : Std.HashMap Name Nat := {}
  let mut candidates : Array Name := #[]
  let mut blockRefs : Std.HashMap Name (Set Name) := {}
  for (rep, all) in blocks.blocks do
    let k := (sched.sourceDeps.get? rep).getD 0
    if k == 0 then candidates := candidates.push rep else unmet := unmet.insert rep k
    if let some refs := blocks.blockRefs.get? rep then
      blockRefs := blockRefs.insert (blockKey rep all) refs
  return { acc := { cenv := { cenv with p3BlockRefs := blockRefs } }, unmet, candidates,
           remaining := blocks.blocks.size }

/-- The default `width` (`Ix.Cert.compile`'s): at most this many tasks per
    wave. The value of the fold does not depend on it; it bounds the tasks a
    wave spawns while leaving the task pool (`LEAN_NUM_THREADS`, else one
    worker per core) enough of them to balance blocks of very different
    sizes. -/
def foldWaveTasks : Nat := 256

/-- A wave's outcomes, as at most `width` tasks over contiguous chunks of
    `ready` (in key order), each block compiled under its canonical key
    against `snapshot`. Flattened, the chunks' values are `ready.map` of
    `auxBlockOutcome`, whatever `width`. -/
def waveTasks (width : Nat) (snapshot : CompileEnv) (ready : Array (Name × Name × Set Name)) :
    Array (Task (Array (Name × Set Name × AuxBlockOutcome))) :=
  let n := ready.size
  let width := max 1 width
  let size := (n + width - 1) / width
  let chunks := if size == 0 then 0 else (n + size - 1) / size
  (Array.range chunks).map fun c => Task.spawn fun _ =>
    (ready.extract (c * size) ((c + 1) * size)).map fun (key, _, all) =>
      (key, all, auxBlockOutcome snapshot key all)

/-- One wave. -/
def foldWave (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat)
    (dbg : Bool) (st : FoldState) : Except String FoldState := Id.run do
  let { acc, settled, unmet, candidates, remaining, waves } := st
  let sourceOwned := blocks.lowLinks.contains
  -- 1. The ready blocks: the candidates the one readiness rule admits.
  let mut ready : Array (Name × Name × Set Name) := #[]
  let mut parked : Array Name := #[]
  for rep in candidates do
    let some all := blocks.blocks.get? rep
      | return .error s!"wave driver: block {rep.pretty} is not in the condensation"
    let deps := (sched.deps.get? rep).getD {}
    let depsOk := Id.run do
      for d in deps do
        if !auxDependencyReady sourceOwned acc.cenv settled d then return false
      return true
    if depsOk then ready := ready.push (blockKey rep all, rep, all)
    else parked := parked.push rep
  if ready.isEmpty then
    return .error s!"Circular dependency detected: {remaining} blocks remaining but none ready"
  ready := ready.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt
  if dbg then
    dbg_trace s!"  [Lean CompileAux] Wave {waves + 1}: {ready.size} blocks ready, \
{remaining - ready.size} after it"
    pure ()
  -- 2. The outcomes against the wave's snapshot, on tasks; 3. applied in key
  -- order, each chunk as soon as the chunks before it are done.
  let tasks := waveTasks width acc.cenv ready
  let mut acc := acc
  for t in tasks do
    for (key, all, outcome) in t.get do
      acc := (applyAuxBlockOutcome acc key all outcome).1
  -- 4. The wave's members settle; the blocks waiting on them are released.
  let mut settled := settled
  let mut unmet := unmet
  let mut next := parked
  for (_, _, all) in ready do
    for m in all do
      settled := settled.insert m
  for (_, _, all) in ready do
    for m in all do
      for w in (sched.waiters.get? m).getD #[] do
        match unmet.get? w with
        | some 1 =>
          unmet := unmet.erase w
          next := next.push w
        | some k => unmet := unmet.insert w (k - 1)
        | none => pure ()
  return .ok { acc, settled, unmet, candidates := next,
               remaining := remaining - ready.size, waves := waves + 1 }

/-- The waves, at most `fuel` of them (every wave compiles at least one block). -/
def foldWaves (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (width : Nat)
    (dbg : Bool) : Nat → FoldState → Except String FoldState
  | 0, st =>
    if st.remaining == 0 then .ok st
    else .error s!"Only compiled {blocks.blocks.size - st.remaining}/{blocks.blocks.size} \
blocks - circular dependency?"
  | fuel + 1, st =>
    if st.remaining == 0 then .ok st
    else match foldWave blocks sched width dbg st with
      | .error e => .error e
      | .ok st' => foldWaves blocks sched width dbg fuel st'

/-- The fold's schedule as levels: the blocks with no source-owned
dependency, then the blocks whose source-owned dependencies are all in
earlier levels, and so on (the waves of a fold in which every block is ready
as soon as its dependencies settle); `(canonical key, representative,
members)`, in key order within a level. A block in a dependency cycle is
in no level. The Source service's run-ahead asks in this order. -/
def scheduleLevels (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) :
    Array (Array (Name × Name × Set Name)) := Id.run do
  let mut unmet : Std.HashMap Name Nat := {}
  let mut current : Array Name := #[]
  for (rep, _) in blocks.blocks do
    let k := (sched.sourceDeps.get? rep).getD 0
    if k == 0 then current := current.push rep else unmet := unmet.insert rep k
  let mut out : Array (Array (Name × Name × Set Name)) := #[]
  for _ in [0:blocks.blocks.size + 1] do
    if current.isEmpty then break
    let level := current.map fun rep =>
      let all := (blocks.blocks.get? rep).getD {}
      (blockKey rep all, rep, all)
    out := out.push (level.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt)
    let mut next : Array Name := #[]
    for rep in current do
      for m in (blocks.blocks.get? rep).getD {} do
        for w in (sched.waiters.get? m).getD #[] do
          match unmet.get? w with
          | some 1 =>
            unmet := unmet.erase w
            next := next.push w
          | some k => unmet := unmet.insert w (k - 1)
          | none => pure ()
    current := next
  return out

/-- **The literal support a selected closure lacks**, for the Source service
only (AuxGen M3; `Ix.AuxGen.literalSupportFor`): its constants by name and
their condensation. Generation side only: nothing compiled or certified
reads it. -/
structure ServiceSupport where
  get? : Name → Option ConstantInfo
  blocks : Ix.CondensedBlocks

instance : Inhabited ServiceSupport := ⟨{ get? := fun _ => none, blocks := default }⟩

/-- The support constants canonicalized and condensed, as the IO pipeline
canonicalizes and condenses its input. -/
def ServiceSupport.of (consts : List (Lean.Name × Lean.ConstantInfo)) : ServiceSupport := Id.run do
  let mut state : Ix.CanonM.CanonState := {}
  let mut map : Std.HashMap Name ConstantInfo := {}
  let mut refs : Ix.Map Name (Set Name) := {}
  for (_, lci) in consts do
    let (ci, state') := StateT.run (Ix.CanonM.canonConst lci) state
    state := state'
    let (r, _) := Ix.GraphM.run { consts := {} } .init (Ix.graphConst ci)
    map := map.insert ci.getCnst.name ci
    refs := refs.insert ci.getCnst.name r
  return { get? := map.get?, blocks := Ix.CondenseM.run refs }

/-- **How the fold's aux tails ask IxC** (AuxGen M2). The defaults are
production's: `fallback` (IxC's answers to `.below`'s and `.brecOn`'s questions
are the compile's wherever IxC answers; `Ix.Tc` answers behind a refusal,
which a selected closure without what Source mode needs can meet; lazy since
AuxGen M3), no trace, and the
Source service asks only for the blocks with a Type-level `.below`
(`Asks.below`, lever P2). Other settings are AuxGen's measurement modes (the
CLI's `IX_AUXGEN_IXC`, which also traces each tail's counts): `shadow`
(`Ix.Tc`'s answers, compared), `failClosed`, `fallbackEager` (M2b's
production: both kernels asked), the asks of every block that holds an
inductive, and `measureOnly` (the service's work timed alone,
`Ix.AuxGen.Source.measure`; the pipeline then compiles nothing). Whatever the
setting, an unsafe block's tail asks `Ix.Tc` (`compileBlockWithAux`). -/
structure AuxIxcOptions where
  mode : Ix.AuxGen.IxcMode := .fallback
  asks : Ix.AuxGen.Source.Asks := .below
  trace : Bool := false
  measureOnly : Bool := false
  /-- the literal support the input lacks (`ServiceSupport`); the IO pipeline
  sets it from `DriverOptions.serviceSupport` -/
  support : Option ServiceSupport := none
  /-- AuxGen M4a: the recursor generator and the elimination decision ask IxC
  (a measurement; production keeps `Ix.Tc` there) -/
  recursors : Bool := false
  deriving Inhabited

/-- **A block's IxC oracle** over the run-ahead `ra`, by the block's canonical
key, in `aux`'s setting (`Ix.AuxGen.Ixc.oracleOfRun`): with AuxGen M4a's
facts: whether the recursor generator asks IxC (`recursors`, the
measurement modes only), whether the run-ahead asked for the block, and the
input's declarations (`get?`) for the lazy scopes' fast paths. -/
def AuxIxcOptions.oracleFor (aux : AuxIxcOptions) (ra : Ix.AuxGen.Source.RunAhead)
    (get? : Name → Option ConstantInfo) (key : Name) : Option Ix.AuxGen.AuxOracle :=
  (ra.runFor key).map fun t =>
    let members := ra.membersFor key
    let facts : Ix.AuxGen.Ixc.OracleFacts :=
      { recursors := aux.recursors
        -- read by the trace only, so computed only when tracing
        asked := !aux.trace || (Ix.AuxGen.Source.holdsInductive get? members
          && aux.asks.selects get? members)
        lookup := get? }
    Ix.AuxGen.Ixc.oracleOfRun aux.mode aux.trace (fun _ => t.get) members facts

/-- **The Source service's input**: the fold's lookups and condensation, with
the literal support beside them when the input lacks it (generation side
only: the fold itself reads `get?` and `blocks` alone). -/
def AuxIxcOptions.serviceInput (aux : AuxIxcOptions) (get? : Name → Option ConstantInfo)
    (blocks : Ix.CondensedBlocks) : (Name → Option ConstantInfo) × Ix.CondensedBlocks :=
  match aux.support with
  | none => (get?, blocks)
  | some s =>
    let union {α} (a b : Ix.Map Name α) : Ix.Map Name α := b.fold (init := a) fun m k v => m.insert k v
    (fun n => (get? n).orElse fun _ => s.get? n,
      { lowLinks := union blocks.lowLinks s.blocks.lowLinks
        blocks := union blocks.blocks s.blocks.blocks
        blockRefs := union blocks.blockRefs s.blocks.blockRefs })

/-- **The driver.** Compile an environment's condensation with the full
    production semantics (per-block aux tails, Pass 3's hooks and image blocks, the
    promotion route with the original-form compile into `Named.original`, the
    cross-SCC subsets, claims and fail-closed promotion), as a fold over waves
    (see the section docstring). Per-block failures are recorded per member in
    `ungrounded`, and dependents cascade into `MissingConstant` failures,
    mirroring env.rs:727-737. The compile itself fails on a condensation
    block without references, on an input inductive group with non-canonical
    flags, on a mutual block of mixed safety, and on a schedule that cannot
    finish.

    The fold reads constants only through `Ix.Environment.get?`: it runs over
    a lookup view of `env` whose map is empty, so a materialized environment
    and a hybrid one with the same lookups (the IO pipeline's, whose theorem
    and opaque bodies come from `fallback?`) compile alike. `unmaterialized`
    counts the input constants `env.consts` does not hold; the view carries
    `env.consts.size + unmaterialized`, so the source-claim walk's bound is
    the same either way. The returned `CompileEnv` holds `env` and
    `unmaterialized` again.

    With the compiled environment it returns what the Source service said of
    the blocks it was asked for (AuxGen M2b, see the section docstring). The
    service reads the input through the same view's `get?`. `aux` is the
    production setting by default (`fallback`, the `.below` asks); other
    settings are AuxGen's measurement modes (`IX_AUXGEN_IXC`). -/
def compileEnvFoldWithSource (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (unmaterialized : Nat := 0)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks)
    (aux : AuxIxcOptions := {})
    : Except String ((Ixon.Env × Nat × CompileEnv) × Ix.AuxGen.Source.Report) := do
  if let some msg := missingBlockRefs? blocks then throw msg
  validateInductiveFlags env
  validateMutualSafety env blocks
  let sched := FoldSchedule.of blocks
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  let (serviceGet?, serviceBlocks) := aux.serviceInput view.get? blocks
  let ra := Ix.AuxGen.Source.RunAhead.start serviceGet? serviceBlocks (scheduleLevels blocks sched)
    aux.asks
  let oracle : Name → Option Ix.AuxGen.AuxOracle := aux.oracleFor ra serviceGet?
  let cenv₀ := { CompileEnv.new view with
    unmaterialized := env.consts.size + unmaterialized, sharingLimits, auxOracle := some oracle }
  let st ← foldWaves blocks sched width dbg (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched)
  let (ixe, bytes, cenv) := assembleEnv st.acc
  return ((ixe, bytes, { cenv with env, unmaterialized, auxOracle := none }), ra.report)

/-- **The driver**: `compileEnvFoldWithSource`'s compiled environment. -/
def compileEnvFold (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (unmaterialized : Nat := 0)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks)
    : Except String (Ixon.Env × Nat × CompileEnv) :=
  Prod.fst <$> compileEnvFoldWithSource env blocks dbg unmaterialized sharingLimits width

/-- The first name, in `Ix.nameCompare` order, whose published address
    differs from a reference's (the wave driver's fail-fast `rustRef` check,
    now made after the fold). -/
def rustRefMismatch? (rust : Std.HashMap Name Address) (cenv : CompileEnv) : Option String :=
  let bad := cenv.nameToNamed.fold (init := (#[] : Array (Name × Address × Address)))
    fun acc n named =>
      match rust.get? n with
      | some r => if named.addr != r then acc.push (n, named.addr, r) else acc
      | none => acc
  match (bad.qsort fun a b => Ix.nameCompare a.1 b.1 == .lt)[0]? with
  | some (n, l, r) => some s!"rustRef mismatch at {n.pretty}: lean={l} rust={r}"
  | none => none

instance : Inhabited AuxBlockOutcome where
  default := .failed "uninitialized"

/-- The options of the Lean compile drivers. The drivers read no environment
    variable and no `/proc` file: the CLI parses these (`ix compile-lean`:
    `--sharing-limits` and `IX_SHARING_LIMITS`,
    `IX_COMPILE_DBG`) and passes them in. -/
structure DriverOptions where
  /-- Resource limits of the canonical sharing construction. -/
  sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits
  /-- Phase timings, and the fold's per-wave trace. -/
  dbg : Bool := false
  /-- A memory reading for the trace after the compile phase, supplied by the
      caller (the CLI reads the process's resident set size); `none` prints
      none. -/
  memory : Option (IO String) := none
  /-- AuxGen's measurement modes (`AuxIxcOptions`; the CLI's
      `IX_AUXGEN_IXC`); `none`, production's setting, by default. -/
  auxIxc : Option AuxIxcOptions := none
  /-- The literal support the input lacks, from the Lean environment it was
      taken from (`Ix.AuxGen.literalSupportFor`; the CLI sets it). For the
      Source service only (`AuxIxcOptions.support`): generation side, never
      compiled or certified. -/
  serviceSupport : List (Lean.Name × Lean.ConstantInfo) := []


/-! ## The full pure-Lean pipeline

`Lean canon → ref graph → ground filter → condense → the wave fold →
serialize` — the Lean-side mirror of Rust
`compile_env_with_options`' setup phases (env.rs:146-260) feeding the
scheduler. This is what `ix compile-lean` and `ix validate-lean`
phase 1 run.

The driver applies Rust's env-level domain restriction
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
  /-- What the driver's Source service said of the inductive blocks (AuxGen
      M1; `compileEnvFoldWithSource`). -/
  source : Ix.AuxGen.Source.Report := {}

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
  --     map (Ix name → pinned Lean constant), and the THIN ground-check env — ground
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
  let mut thinConsts : Ix.Map Ix.Name Ix.ConstantInfo := {}
  let mut ixArr : Array (Ix.Name × Lean.ConstantInfo) := #[]
  for (ln, lci) in constArr do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    leanByIx := leanByIx.insert ixn (ln, lci)
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
          × Option Ix.ConstantInfo × Bool) := #[]
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
        out := out.push (ixn, refs, groundErr?, hash ci, keep?,
          sourceHasReservedMetadata lci)
      out
  let mut outRefs : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  let mut immediate : Ix.Map Ix.Name Ix.GroundError := {}
  let mut digests : Std.HashMap Ix.Name UInt64 := {}
  let mut codeConsts : Ix.Map Ix.Name Ix.ConstantInfo := {}
  let mut reservedMetadata : Array Ix.Name := #[]
  for task in tasks do
    for (n, refs, gerr?, dig, keep?, reserved) in task.get do
      if reserved then reservedMetadata := reservedMetadata.push n
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
  -- 4b. Reserved input (D14): a grounded input constant with a reserved
  --     metadata key, then a grounded input name with a reserved component,
  --     is refused before compiling, as Rust's `compile_env` refuses it.
  let groundedReserved := reservedMetadata.filter (!ungrounded.contains ·)
  if let some msg := reservedMetadataRefusal? groundedReserved then
    return .error msg
  if let some msg := reservedInputRefusal? condensed then
    return .error msg
  -- 5. The driver (`compileEnvFold`, the same function as `Ix.Cert.compile`'s)
  --    against the HYBRID environment: code kinds are the materialized
  --    (shared) map; proof bodies canonicalize on demand from the pinned
  --    Lean constants and are dropped when their block's `CompileM.run`
  --    returns. Each wave is split into `4 * numWorkers` tasks (`width`; the
  --    value does not depend on it): chunks that small let the task pool
  --    (`LEAN_NUM_THREADS`, else one thread per core) balance blocks of very
  --    different sizes, where `numWorkers` chunks left the wave waiting on its
  --    slowest chunk (Mathlib's compile phase 505.5 s at width 32, 414.1 s at
  --    128; the queue driver took 458.1 s). At most `min width pool` blocks
  --    compile at once. The fold's Source service (AuxGen M1) reads the same
  --    lookups; its report is printed under `dbg` and returned.
  let fallback : Ix.Name → Option Ix.ConstantInfo := fun n =>
    (leanByIx.get? n).bind fun (ln, lci) =>
      ((Ix.CanonM.canonChunk #[(ln, lci)])[0]?).map (·.2)
  let ixEnv : Ix.Environment :=
    { consts := codeConsts, fallback? := some fallback }
  if dbg then
    IO.println s!"  [Lean CompileAux] {condensed.blocks.size} blocks, {4 * numWorkers} tasks per wave"
  -- AuxGen's measurement modes (`opts.auxIxc`, the CLI's `IX_AUXGEN_IXC`;
  -- `none` is production's setting): the service's work timed alone, or the
  -- fold under another setting (`AuxIxcOptions`).
  if let some aux := opts.auxIxc then
    if aux.measureOnly then
      let view : Ix.Environment := { consts := {}, fallback? := some ixEnv.get? }
      let levels := scheduleLevels condensed (FoldSchedule.of condensed)
      for line in ← Ix.AuxGen.Source.measure view.get? condensed levels do IO.println line
      return .error "AuxGen M2a: service measured (IX_AUXGEN_IXC=measure); nothing compiled"
  let folded ← IO.lazyPure fun _ =>
    compileEnvFoldWithSource ixEnv condensed (dbg := dbg)
      (unmaterialized := leanByIx.size - codeConsts.size)
      (sharingLimits := opts.sharingLimits) (width := 4 * numWorkers)
      (aux := { opts.auxIxc.getD {} with
        support := if opts.serviceSupport.isEmpty then none
          else some (ServiceSupport.of opts.serviceSupport) })
  match folded with
  | .error e => return .error e
  | .ok ((ixonEnv, _, cenv), source) =>
    let t ← tick "compile" t
    if dbg then
      IO.println s!"  [compile-lean] source service: {source.summary}"
      IO.println s!"  [compile-lean] pass 3: {cenv.p3Blocks.size} changed blocks, \
{cenv.p3Heads.size} image-kind heads"
      for (k, why) in source.notAccepted.extract 0 8 do
        IO.println s!"    source service, block not accepted: {k.pretty}: {why.take 160}"
      for (g, why) in source.refused.extract 0 8 do
        IO.println s!"    source service, group refused: {g}: {why.take 160}"
    if dbg then
      if let some read := opts.memory then
        IO.println s!"  [compile-lean] rss after the compile phase: {← read}"
    if let some rust := rustRef then
      if let some msg := rustRefMismatch? rust cenv then return .error msg
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
        annotated
        source }

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



