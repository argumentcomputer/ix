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
    are keyed by name/address and every merge is insert-once or
    last-wins-per-name in dependency order, so scheduling order does not
    affect the result (Rust relies on the same property for its
    nondeterministic work-stealing order).
  - The parallel driver's output is defined by a wave schedule (every
    block compiled against the state after all earlier waves), not by
    live global state; it runs blocks ahead of their wave speculatively
    and validates or recomputes them. See "The aux-aware parallel
    driver" below for which snapshot reads make this necessary.
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
public section

namespace Ix.CompileM

open Ix.AuxGen (CallSitePlan BRecOnCallSitePlan)

/-- Pure `stt.resolve_addr` over the merged driver state
    (compile.rs:261-274): `name_to_addr` then `aux_name_to_addr`. -/
def resolveAddrPure (cenv : CompileEnv) (name : Name) : Option Address :=
  match cenv.nameToAddr.get? name with
  | some a => some a
  | none => cenv.auxNameToAddr.get? name

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
  -- Collect the Lean `.all` names from any constant in the SCC
  -- (compile.rs:3283-3299).
  let mut leanAll : Array Name := #[]
  for n in all do
    match getConst n with
    | some (.inductInfo v) => leanAll := v.all; break
    | some (.recInfo v) => leanAll := v.all; break
    | some (.defnInfo v) => leanAll := v.all; break
    | some (.thmInfo v) => leanAll := v.all; break
    | _ => continue
  -- Determine phase from the first aux_gen constant (compile.rs:3302-3334).
  let mut phase? : Option NoAuxPhase := none
  for n in all do
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
      { all := target, current := lo, mutCtx := default, univCtx := [] }
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
    for n in all do
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

/-- Merge one compiled block's outputs into the driver state, mirroring
    the Rust global-mutation order: block constant, member projections
    (primary `register_name` + `name_to_addr`, compile.rs:3902-3969),
    then the tail's aux constants, Named overrides (incl. the synthetic
    `Muts` entry and aliases), aux name→addr map, extra names, and
    call-site plans.

    `acc` is destructured before any update: projecting `acc.cenv` while
    `acc` stays live would share every map with the old state and copy
    its bucket array on the first insert. -/
def mergeCompiledBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState)
    (plans : Std.HashMap Name CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Name BRecOnCallSitePlan) : DriverAcc := Id.run do
  let ⟨cenv₀, blockNames, defHints, pending₀⟩ := acc
  let mut cenv := cenv₀
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
  -- Class-ordering registry (Rust `stt.blocks`, compile.rs:4048-4057):
  -- one entry per member, all pointing at the block's full ordering.
  if !result.classNames.isEmpty then
    for cls in result.classNames do
      for n in cls do
        cenv := { cenv with blocks := cenv.blocks.insert n result.classNames }
  let mut pending := pending₀
  for (n, _) in cache.auxNameToAddr do
    pending := pending.push n
  return ⟨cenv, cache.blockNames.fold (fun m k v => m.insert k v) blockNames,
    cache.defHints.fold (fun m k v => m.insert k v) defHints, pending⟩

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

/-- The coherence check of `promoteAuxDriver` alone (it reads no state). -/
def promoteAuxCheck (name : Name) (origMeta : Ixon.ConstantMeta) :
    Option CompileError :=
  match constMetaSelfName? origMeta with
  | some metaAddr =>
    if metaAddr != name.getHash then
      some (.invalidMutualBlock s!"promote_aux: name mismatch for \
'{name.pretty}' — compile_name address is {name.getHash} but meta name \
address is {metaAddr}")
    else none
  | none => none

/-- The promotion of `promoteAuxDriver` alone, for a name that passed
    `promoteAuxCheck`. -/
def promoteAuxApply (cenv : CompileEnv) (name : Name) (origAddr : Address)
    (origMeta : Ixon.ConstantMeta) : CompileEnv := Id.run do
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
    `CompileState::promote_aux` (compile.rs:309-350), including the
    meta self-name coherence check. -/
def promoteAuxDriver (cenv : CompileEnv) (name : Name)
    (origAddr : Address) (origMeta : Ixon.ConstantMeta)
    : Except CompileError CompileEnv := do
  if let some e := promoteAuxCheck name origMeta then
    throw e
  pure (promoteAuxApply cenv name origAddr origMeta)

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
  for rep in order do
    if acc.cenv.auxNameToAddr.contains rep then
      continue
    let some all := blocks.blocks.get? rep | continue
    match runBlockWithAux acc.cenv all rep with
    | .error e =>
      return .error s!"aux_gen prereq pre-compile failed for SCC \
'{rep.pretty}' ({all.size} members): {e}. The SCC closure is traversed \
in reverse-topological order starting from the aux_gen seed names, so \
all transitive deps should be compiled before this — if you're hitting \
this, a dep relationship isn't captured in the ref graph, or the source \
env is inconsistent."
    | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
      acc := mergeCompiledBlock acc rep result cache plans brecPlans belowPlans
      -- Move compiled names → auxNameToAddr (env.rs:1119-1137). At this
      -- stage `nameToAddr` contains exactly the prereq registrations.
      let moved := acc.cenv.nameToAddr
      acc := { acc with cenv := { acc.cenv with
        nameToAddr := {}
        auxNameToAddr := moved.fold (fun m k v => m.insert k v)
          acc.cenv.auxNameToAddr } }
  return .ok acc

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
        let addrMap := addrMap.insert named.addr name
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

/-! ## The aux-aware sequential driver -/

/-- Compile an entire environment with the FULL production pipeline
    semantics: aux-gen prereq pre-compilation, per-block aux tails
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
    : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
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
  let mut readyQueue : Array (Name × Set Name) := #[]
  for (lo, (all, depCount)) in blockInfo do
    if depCount == 0 then
      readyQueue := readyQueue.push (lo, all)

  let mut blocksCompleted : Nat := 0
  let mut lastPct : Nat := 0
  -- Deps already satisfied (released) — HashSet-style idempotent release
  -- mirrors Rust's `remaining.remove` (env.rs:838-856): a name can be
  -- released at most once per dependent.
  let mut released : Set Name := {}

  while !readyQueue.isEmpty do
    let (lo, all) := readyQueue.back!
    readyQueue := readyQueue.pop

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
          match runBlockWithAux acc.cenv crossAll unresolvedNames[0]! with
          | .error _ =>
            -- Rust logs and does NOT register failed names — dependents
            -- will get MissingConstant rather than broken data.
            pure ()
          | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
            acc := mergeCompiledBlock acc unresolvedNames[0]! result cache
              plans brecPlans belowPlans
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
            match promoteAuxDriver acc.cenv name origAddr origMeta with
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
        -- Promote remaining names from auxNameToAddr (env.rs:697-707).
        for name in all do
          if !acc.cenv.nameToAddr.contains name then
            if let some addr := resolveAddrPure acc.cenv name then
              acc := { acc with cenv := { acc.cenv with
                nameToAddr := acc.cenv.nameToAddr.insert name addr } }
    else
      -- Normal path: compile the block with the aux tail.
      match runBlockWithAux acc.cenv all lo with
      | .error e =>
        -- Soft failure (env.rs:727-737): record per member; the
        -- scheduler keeps running and dependents cascade.
        let msg := toString e
        for m in all do
          acc := { acc with cenv := { acc.cenv with
            ungrounded := acc.cenv.ungrounded.insert m msg } }
      | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
        acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans

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
              readyQueue := readyQueue.push (dependentLo, depAll)

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

### Reference semantics: waves

The output is defined by the wave schedule. Wave 1 is the set of blocks
all of whose dependencies (`blockRefs`) resolve (`resolveAddrPure`) after
the prereq pre-compilation; wave `w + 1` is the set of remaining blocks
all of whose dependencies resolve, or are members of a failed block
(`AuxBlockOutcome.failsMembers`), in `W≤w`, the state after merging the
outcomes of waves `1..w`. A block of wave `w` has the outcome
`auxBlockOutcome W<w lo all`, a pure function of that snapshot. Merges
within one wave are per-name disjoint or content-keyed (the property the
sequential driver and Rust's scheduler rely on), so `W≤w` does not depend
on the order in which a wave's outcomes are merged; this driver merges
them in block-index order, which also fixes the iteration order of the
merged maps.

### What a block reads from its snapshot

Readiness alone does not determine an outcome, because a block reads more
than the addresses of its dependencies:

1. The promotion decision and the unresolved subset (`auxBlockOutcome`):
   `resolveAddrPure lo`, and `nameToAddr`, `auxNameToAddr`,
   `auxGenExtraNames` for the block's own members.
2. `lookupConstAddr` / `resolveAddr?` (`nameToAddr`, `auxNameToAddr`) for
   every constant the block references, and, in the aux tail and the
   promotion path, for aux names registered by other blocks (alias
   targets and sources, `all0.rec_N` claims).
3. The call-site plan maps: per head (`planHeadArity?`,
   `compileAppSpine`, the tail's collision checks), and as a whole:
   `CompileEnv.surgeryFree` (all three maps empty) selects the ordinary or
   the surgery expression compiler and gates `auditPlanHeadArities`.
4. `nameToNamed`: `compilingIsAuxRegen` (the compiled name's `original`),
   `lookupNamed?` (alias registration clones the target's entry), the
   `.below` / `.brecOn` presence checks, and `Ix.AuxGen.nameForAddr`, a
   linear scan that returns the first entry with a given address, so its
   result depends on which aliases of that address are present and on
   the map's iteration order.
5. `blocks` (class orderings of spec members for evaporation claims).
6. Immutable: `env`, `nameByHash`, `sharingLimits`. Never read by a
   block's compile: `constants`, `blobs`, `totalBytes`, `ungrounded`.

Items 1, 2 restricted to dependencies, and 3 per head are fixed once the
block's dependencies have resolved, provided resolution is write-once and
a plan is written no later than the name it keys first resolves — the
invariants the aux generator's ownership rules and collision checks aim
at. Item 3 as a whole, item 4's scan, and the cross-block reads of the aux
tail are not: they can observe blocks the reader does not depend on, so
the same block started at another time can produce another outcome (for
`nameForAddr`, whether `getLevel`'s fault-in finds the referenced
spelling; for the plan maps, which expression compiler runs). Rust's
work-stealing scheduler reads all of them from live global state; the
wave schedule fixes them. Dispatching each block as soon as its
dependencies resolve would therefore not preserve the output.

### Speculate, validate against the waves

The driver keeps two states.

* `V` (authoritative) merges outcomes in wave order and is the result.
  An outcome enters `V` only if it equals `auxBlockOutcome W<w lo all`:
  either it was computed against the snapshot of `V` taken when `V`
  reached the block's wave (an exact run), or the block is plain and its
  speculative run read exactly the facts that `W<w` holds (below).
  Otherwise the block is recomputed exactly when `V` reaches its wave.
* `L` (speculative) merges every outcome as it arrives. A block whose
  dependencies resolve in `L` is started against a recent snapshot of `L`
  before its wave opens, so a straggler delays only its own dependents
  and the rest of the work flows around it. Nothing from `L` reaches the
  output; a wrong speculation costs a recomputation, never a different
  result.

Wave membership is computed on `V` with the wave rule above, so the
waves, every snapshot `W<w`, every outcome, the merge order and the
result are the wave schedule's, whatever the worker count, completion
order or priorities. Errors follow: per-block failures are outcomes
(`ungrounded`); a missing dependency surfaces as "Circular dependency
detected" when a wave closes with no successor, with the same count of
remaining blocks; `rustRef` mismatches are checked as blocks merge into
`V`, so the first one reported is the first in (wave, block-index)
order.

**Plain blocks.** A block is plain when it is a single constant that is
not an inductive, constructor or recursor and whose name is not an aux
name (`Ix.AuxGen.classifyAuxGen`). Its compile goes through
`compileConstantInfo` without the aux tail, and if `lo` does not resolve
it reads only: `resolveAddrPure` of the names that `.const` heads and
`.proj` type names in its type and value spell (exactly its `blockRefs`,
by the definition of the reference graph in `Ix.GraphM`), the plan maps
at those heads, and `surgeryFree`; `compilingIsAuxRegen` returns `false`
without reading anything because the name is not an aux name. So if two
snapshots agree on `PlainFacts` (whether `lo` resolves, `surgeryFree`,
and for every dependency its resolution and whether any plan map has
it), and no dependency has a plan (no surgery runs), the outcomes are
equal. The speculative run records these facts; when `V` reaches the
block's wave they are recomputed on `W<w` and compared. The outcome must
also have the plain shape (a compiled singleton without projections or
aux registrations) and every address in its reference table must be a
recorded dependency resolution or a blob of the block, which guards the
reference-graph argument. Any mismatch leads to an exact recomputation.

**Dispatch.** Jobs go in order of block height (the longest chain of
dependent blocks), so long chains start early whatever their wave;
exact runs compete on the same priority, with `exactShare` reserving a
share of the workers for them. `V` can therefore lag behind `L`, most
of all while a straggler holds its wave open, and close several waves at
once when it completes; what is left at the end is a chain of at most
one recomputation per remaining wave.

**Bounds.** At most `numWorkers` jobs are in flight and each holds one
snapshot. `L` is republished at most every `publishMs` (when work that
is not ready in the current snapshot has a higher priority than the work
that is) and `V` once per wave; each publication costs one copy of the
shared maps' bucket arrays on the next merge. Snapshots handed to workers
omit `constants`, `blobs`, `totalBytes` and `ungrounded`, which only the
scheduling thread reads, so those maps are never shared or copied. Workers
return outcomes stripped to the fields merges read
(`AuxBlockOutcome.forMerge`), so expression caches die in the worker.
Outcomes are retained from completion until `V` reaches their wave. -/

/-- Pure per-block outcome computed by a worker. -/
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
      merge time against the merged state. -/
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

instance : Inhabited AuxBlockOutcome where
  default := .failed "uninitialized"

/-- Compute a block's outcome against a snapshot. Pure; mirrors the
    per-block body of `compileEnvAux`. -/
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
        match runBlockWithAux cenv crossAll unresolvedNames[0]! with
        | .error _ => pure ()
        | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
          crossScc := some (unresolvedNames[0]!, result, cache,
            plans, brecPlans, belowPlans)
          crossNames := unresolvedNames
    let mut noAux := none
    let mut noAuxFailMsg := none
    if anyAuxGen && incompleteMsg.isNone then
      match compileConstNoAuxPure cenv lo all with
      | .error e => noAuxFailMsg := some (toString e)
      | .ok out => noAux := some out
    return .promoted crossScc crossNames incompleteMsg noAux noAuxFailMsg
  else
    match runBlockWithAux cenv all lo with
    | .error e => return .failed (toString e)
    | .ok (result, cache, _, plans, brecPlans, belowPlans) =>
      return .compiled result cache plans brecPlans belowPlans

/-- Record `msg` for every member (soft failure, env.rs:727-737). -/
def DriverAcc.markUngrounded (acc : DriverAcc) (all : Set Name)
    (msg : String) : DriverAcc :=
  let ⟨cenv, blockNames, defHints, pending⟩ := acc
  ⟨{ cenv with ungrounded := all.fold (fun m n => m.insert n msg) cenv.ungrounded },
    blockNames, defHints, pending⟩

/-- Apply a worker outcome to a driver state. Returns the names newly
    REGISTERED by this block (for the `rustRef` comparison). The state is
    destructured before it is updated, so every map is updated in place
    when the state is not shared. -/
def applyAuxBlockOutcome (acc : DriverAcc) (lo : Name) (all : Set Name)
    (outcome : AuxBlockOutcome) : DriverAcc × Array Name := Id.run do
  match outcome with
  | .compiled result cache plans brecPlans belowPlans =>
    let mut newNames : Array Name := #[]
    if result.projections.isEmpty then
      newNames := newNames.push lo
    else
      for (name, _, _) in result.projections do
        newNames := newNames.push name
    for (n, _) in cache.auxNamed do
      newNames := newNames.push n
    return (mergeCompiledBlock acc lo result cache plans brecPlans belowPlans,
      newNames)
  | .failed msg => return (acc.markUngrounded all msg, #[])
  | .promoted crossScc crossNames incompleteMsg noAux noAuxFailMsg =>
    let mut acc := acc
    let mut newNames : Array Name := #[]
    if let some (clo, result, cache, plans, brecPlans, belowPlans) := crossScc then
      if result.projections.isEmpty then
        newNames := newNames.push clo
      else
        for (name, _, _) in result.projections do
          newNames := newNames.push name
      for (n, _) in cache.auxNamed do
        newNames := newNames.push n
      acc := mergeCompiledBlock acc clo result cache plans brecPlans belowPlans
    let ⟨cenv₀, blockNames₀, defHints₀, pending⟩ := acc
    let mut cenv := cenv₀
    let mut blockNames := blockNames₀
    let mut defHints := defHints₀
    if !crossNames.isEmpty then
      cenv := { cenv with
        auxGenExtraNames := crossNames.foldl (·.insert ·) cenv.auxGenExtraNames }
    match incompleteMsg with
    | some msg =>
      cenv := { cenv with
        ungrounded := all.fold (fun m n => m.insert n msg) cenv.ungrounded }
    | none =>
      match noAuxFailMsg with
      | some msg =>
        cenv := { cenv with
          ungrounded := all.fold (fun m n => m.insert n msg) cenv.ungrounded }
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
            match promoteAuxCheck name origMeta with
            | some e =>
              promoteFailed := true
              let msg := toString e
              cenv := { cenv with
                ungrounded := all.fold (fun m n => m.insert n msg) cenv.ungrounded }
            | none =>
              cenv := promoteAuxApply cenv name origAddr origMeta
          cenv := { cenv with
            blobs := cache.blockBlobs.fold (fun m k v => m.insert k v) cenv.blobs }
          blockNames := cache.blockNames.fold (fun m k v => m.insert k v) blockNames
          defHints := cache.defHints.fold (fun m k v => m.insert k v) defHints
      -- Promote remaining names from auxNameToAddr (env.rs:697-707) —
      -- against the merged state; also counts as registration for rustRef.
      for name in all do
        if !cenv.nameToAddr.contains name then
          if let some addr := resolveAddrPure cenv name then
            cenv := { cenv with nameToAddr := cenv.nameToAddr.insert name addr }
            newNames := newNames.push name
    return (⟨cenv, blockNames, defHints, pending⟩, newNames)

/-! ### Scheduler support -/

/-- The fields of `BlockState` that merges read. The rest (expression,
    universe and comparison caches, tables, arena) is dropped in the
    worker, so it neither crosses threads nor is freed by the scheduling
    thread. -/
def BlockState.forMerge (s : BlockState) : BlockState :=
  { blockBlobs := s.blockBlobs, blockNames := s.blockNames
    defHints := s.defHints, auxConsts := s.auxConsts, auxNamed := s.auxNamed
    auxNameToAddr := s.auxNameToAddr, auxGenExtraNames := s.auxGenExtraNames }

/-- `applyAuxBlockOutcome` reads only the `forMerge` fields of the block
    states it receives, so this is merge-equivalent. -/
def AuxBlockOutcome.forMerge : AuxBlockOutcome → AuxBlockOutcome
  | .compiled r c p b w => .compiled r c.forMerge p b w
  | .promoted cross names inc noAux fail =>
    .promoted (cross.map fun (clo, r, c, p, b, w) => (clo, r, c.forMerge, p, b, w))
      names inc (noAux.map fun (r, c) => (r, c.forMerge)) fail
  | .failed m => .failed m

/-- The outcome as the speculative state needs it: what only the output
    reads (blobs, name components, hints, serialized aux constants) is
    dropped, so the speculative merge skips that work. -/
def AuxBlockOutcome.forLive : AuxBlockOutcome → AuxBlockOutcome
  | .compiled r c p b w => .compiled r (live c) p b w
  | .promoted cross names inc noAux fail =>
    .promoted (cross.map fun (clo, r, c, p, b, w) => (clo, r, live c, p, b, w))
      names inc (noAux.map fun (r, c) => (r, live c)) fail
  | .failed m => .failed m
where
  live (s : BlockState) : BlockState :=
    { s with blockBlobs := {}, blockNames := {}, defHints := {}, auxConsts := #[] }

/-- Whether the wave rule counts the block's members as failed, which
    releases their dependents. -/
def AuxBlockOutcome.failsMembers : AuxBlockOutcome → Bool
  | .failed _ => true
  | .promoted _ _ (some _) _ _ => true
  | _ => false

/-- Every name whose `resolveAddrPure` a merge of this outcome can change:
    `applyAuxBlockOutcome` inserts into `nameToAddr` only the block's own
    registrations (`lo` or projection names, the cross-SCC subset) and
    promotions of names that already resolve, and into `auxNameToAddr`
    only aux-tail registrations. Failures mark members. -/
def AuxBlockOutcome.touchedNames (all : Set Name) : AuxBlockOutcome → Array Name
  | .compiled result cache .. => Id.run do
    let mut out := all.toArray
    for (n, _, _) in result.projections do out := out.push n
    for (n, _) in cache.auxNameToAddr do out := out.push n
    return out
  | .promoted cross crossNames .. => Id.run do
    let mut out := all.toArray ++ crossNames
    if let some (clo, result, cache, _) := cross then
      out := out.push clo
      for (n, _, _) in result.projections do out := out.push n
      for (n, _) in cache.auxNameToAddr do out := out.push n
    return out
  | .failed _ => all.toArray

private def hashMapSame [BEq α] [Hashable α] [BEq β] (a b : Std.HashMap α β) : Bool :=
  a.size == b.size && a.fold (fun ok k v => ok && b.get? k == some v) true

private def hashSetSame [BEq α] [Hashable α] (a b : Std.HashSet α) : Bool :=
  a.size == b.size && a.fold (fun ok k => ok && b.contains k) true

private def BlockResult.same (a b : BlockResult) : Bool :=
  a.block == b.block && a.blockBytes == b.blockBytes && a.blockAddr == b.blockAddr
    && a.blockMeta == b.blockMeta && a.projections == b.projections
    && a.classNames == b.classNames

private def BlockState.sameForMerge (a b : BlockState) : Bool :=
  hashMapSame a.blockBlobs b.blockBlobs && hashMapSame a.blockNames b.blockNames
    && hashMapSame a.defHints b.defHints && a.auxConsts == b.auxConsts
    && a.auxNamed == b.auxNamed && hashMapSame a.auxNameToAddr b.auxNameToAddr
    && hashSetSame a.auxGenExtraNames b.auxGenExtraNames

/-- Merge-relevant equality of two outcomes (test aid). -/
def AuxBlockOutcome.same : AuxBlockOutcome → AuxBlockOutcome → Bool
  | .compiled r c p b w, .compiled r' c' p' b' w' =>
    r.same r' && c.sameForMerge c' && hashMapSame p p' && hashMapSame b b'
      && hashMapSame w w'
  | .promoted x n i a f, .promoted x' n' i' a' f' =>
    (match x, x' with
      | some (l, r, c, p, b, w), some (l', r', c', p', b', w') =>
        l == l' && r.same r' && c.sameForMerge c' && hashMapSame p p'
          && hashMapSame b b' && hashMapSame w w'
      | none, none => true
      | _, _ => false)
    && n == n' && i == i' && f == f'
    && (match a, a' with
      | some (r, c), some (r', c') => r.same r' && c.sameForMerge c'
      | none, none => true
      | _, _ => false)
  | .failed m, .failed m' => m == m'
  | _, _ => false

/-- The view of a state handed to workers: the fields no block compile
    reads are emptied, so the scheduling thread's copies of them are never
    shared. -/
def CompileEnv.workerView (c : CompileEnv) : CompileEnv :=
  { c with constants := {}, blobs := {}, totalBytes := 0, ungrounded := {} }

/-- A single non-inductive, non-recursor constant whose name is not an
    aux name. Constants absent from the materialized map are the theorem
    and opaque bodies `compileDecoratedConsts` canonicalizes on demand
    (or missing, and then the block fails, and failures are never
    accepted speculatively). -/
def plainCandidate (env : Ix.Environment) (lo : Name) (all : Set Name) : Bool :=
  all.size == 1 && all.contains lo && (Ix.AuxGen.classifyAuxGen lo).isNone &&
    match env.consts.get? lo with
    | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) => false
    | _ => true

/-- Everything a plain block's compile reads from its snapshot. -/
structure PlainFacts where
  loResolved : Bool
  plansEmpty : Bool
  anyPlan : Bool
  resolved : Array (Option Address)
  deriving BEq, Inhabited

def plainFacts (cenv : CompileEnv) (lo : Name) (deps : Array Name) : PlainFacts :=
  let hasPlan (n : Name) : Bool :=
    cenv.callSitePlans.contains n || cenv.belowCallSitePlans.contains n
      || cenv.brecOnCallSitePlans.contains n
  { loResolved := (resolveAddrPure cenv lo).isSome
    plansEmpty := cenv.surgeryFree
    anyPlan := hasPlan lo || deps.any hasPlan
    resolved := deps.map (resolveAddrPure cenv) }

/-- The plain-path shape (a compiled singleton, no projections, no aux
    registrations or plans) and a reference table made only of recorded
    dependency resolutions and the block's own blobs. -/
def PlainFacts.explains (f : PlainFacts) : AuxBlockOutcome → Bool
  | .compiled result cache plans brecPlans belowPlans =>
    result.projections.isEmpty && result.classNames.isEmpty
      && cache.auxConsts.isEmpty && cache.auxNamed.isEmpty
      && cache.auxNameToAddr.isEmpty && cache.auxGenExtraNames.isEmpty
      && plans.isEmpty && brecPlans.isEmpty && belowPlans.isEmpty
      && (let known : Std.HashSet Address := f.resolved.foldl (init := {})
            fun s a? => match a? with
              | some a => s.insert a
              | none => s
          result.block.refs.all fun a => known.contains a || cache.blockBlobs.contains a)
  | _ => false

/-- Whether a speculative outcome may enter `V` without recomputation:
    the block is plain, its run took the plain path without surgery, and
    `cenv` (the snapshot `W<w` of its wave) holds the facts it read. -/
def acceptSpeculative (cenv : CompileEnv) (isPlain : Bool) (lo : Name)
    (deps : Array Name) (outcome : AuxBlockOutcome) (facts? : Option PlainFacts) :
    Bool :=
  match facts? with
  | some f =>
    isPlain && !f.loResolved && !f.anyPlan && f.explains outcome
      && plainFacts cenv lo deps == f
  | none => false

/-- Per-block scheduling state. `spec`/`exact`: 0 none, 1 queued,
    2 running, 3 done. -/
structure SchedBlock where
  spec : UInt8 := 0
  exact : UInt8 := 0
  final : Bool := false
  inFront : Bool := false
  ms : Nat := 0
  deriving Inhabited

/-- Max-priority queue over small integer priorities (block heights).
    Entries are removed lazily: the caller skips stale ones. -/
structure BucketQ where
  buckets : Array (Array Nat) := #[]
  top : Nat := 0
  deriving Inhabited

namespace BucketQ

def push (q : BucketQ) (prio idx : Nat) : BucketQ :=
  let ⟨buckets, top⟩ := q
  let buckets := if prio < buckets.size then buckets
    else buckets ++ Array.replicate (prio + 1 - buckets.size) #[]
  ⟨buckets.modify prio (·.push idx), max top prio⟩

/-- Drop stale entries from the top and return the top `(prio, idx)`. An
    entry is live when its block is queued for this kind of run (`exact`
    or speculative) and, for speculative runs, its wave has not opened. -/
partial def peek (q : BucketQ) (st : Array SchedBlock) (exact : Bool) :
    Option (Nat × Nat) × BucketQ :=
  let ⟨buckets, top⟩ := q
  match buckets[top]? with
  | none => (none, ⟨buckets, 0⟩)
  | some b =>
    match b.back? with
    | none => if top == 0 then (none, ⟨buckets, 0⟩) else peek ⟨buckets, top - 1⟩ st exact
    | some i =>
      let s := st[i]!
      let live := if exact then s.exact == 1 else s.spec == 1 && !s.inFront && !s.final
      if live then (some (top, i), ⟨buckets, top⟩)
      else peek ⟨buckets.modify top (·.pop), top⟩ st exact

/-- Remove the top entry (after `peek` returned it). -/
def popTop (q : BucketQ) : BucketQ :=
  let ⟨buckets, top⟩ := q
  ⟨buckets.modify top (·.pop), top⟩

def append (q r : BucketQ) : BucketQ := Id.run do
  let mut q := q
  for h : p in [:r.buckets.size] do
    for i in r.buckets[p] do
      q := q.push p i
  return q

end BucketQ

/-- Scheduler configuration of `compileEnvParallelAuxWith`. -/
structure AuxSchedConfig where
  numWorkers : Nat := 32
  /-- Start blocks ahead of their wave against the speculative state;
      `false` runs the plain wave schedule. Both give the same output. -/
  speculate : Bool := true
  /-- Minimum interval between republications of the speculative state. -/
  publishMs : Nat := 100
  /-- Percentage of the workers that exact runs (blocks whose wave is open)
      may occupy ahead of speculative runs of higher priority; beyond it
      the higher block height goes first. -/
  exactShare : Nat := 0
  /-- Recompute every speculative outcome against its wave snapshot and
      compare (test aid: checks the plain-block validation and measures
      how often speculation agrees with the waves). -/
  verify : Bool := false
  /-- Nonzero: dispatch priorities and per-job start delays derive from
      this seed instead of block heights (test aid: other completion
      orders). -/
  seed : Nat := 0
  /-- Upper bound of the seeded per-job start delay, in milliseconds. -/
  jitterMs : Nat := 0
  /-- Write one line per wave (wave, blocks, slowest accepted run and its
      block, sum of accepted runs) to this file. -/
  waveLog : Option String := none
  dbg : Bool := false
  deriving Inhabited

/-- `AuxSchedConfig` from the environment: `IX_COMPILE_SCHEDULE=waves`
    disables speculation; `IX_COMPILE_VERIFY=1`, `IX_COMPILE_SEED=<n>`,
    `IX_COMPILE_JITTER_MS=<n>`, `IX_COMPILE_PUBLISH_MS=<n>` and
    `IX_COMPILE_WAVE_LOG=<path>` set the corresponding fields. -/
def AuxSchedConfig.fromEnv (numWorkers : Nat) (dbg : Bool) : IO AuxSchedConfig := do
  let nat (var : String) (dflt : Nat) : IO Nat := do
    return ((← IO.getEnv var).bind (·.toNat?)).getD dflt
  let schedule ← IO.getEnv "IX_COMPILE_SCHEDULE"
  return {
    numWorkers
    speculate := schedule != some "waves"
    publishMs := ← nat "IX_COMPILE_PUBLISH_MS" 100
    exactShare := ← nat "IX_COMPILE_EXACT_SHARE" 0
    verify := (← IO.getEnv "IX_COMPILE_VERIFY").isSome
    seed := ← nat "IX_COMPILE_SEED" 0
    jitterMs := ← nat "IX_COMPILE_JITTER_MS" 0
    waveLog := ← IO.getEnv "IX_COMPILE_WAVE_LOG"
    dbg }

/-- One block compile handed to a worker. -/
structure SchedJob where
  idx : Nat
  exact : Bool
  lo : Name
  all : Set Name
  cenv : CompileEnv
  /-- Dependencies whose facts the worker records (plain speculative runs). -/
  factsOf : Option (Array Name)
  delayMs : Nat
  /-- `IX_LOG_BLOCKS` trace for this job. -/
  log : Bool

instance : Inhabited SchedJob where
  default := ⟨0, true, default, {}, default, none, 0, false⟩

structure SchedResult where
  idx : Nat
  exact : Bool
  outcome : AuxBlockOutcome
  facts : Option PlainFacts
  ms : Nat
  deriving Inhabited

/-- The job's pure work, kept out of line so that it runs between the
    worker's clock reads. -/
@[noinline] def runSchedJob (job : SchedJob) :
    BaseIO (AuxBlockOutcome × Option PlainFacts) :=
  pure ((auxBlockOutcome job.cenv job.lo job.all).forMerge,
    job.factsOf.map (plainFacts job.cenv job.lo))

/-- Parallel aux-aware environment compile with an explicit scheduler
    configuration. The output does not depend on `cfg` (see the section
    docstring). `rustRef` enables fail-fast address comparison as blocks
    merge into the authoritative state: the first divergence, in (wave,
    block-index) order, aborts with the offending name. -/
def compileEnvParallelAuxWith (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (cfg : AuxSchedConfig)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (nameByHash : Std.HashMap Address Name := {})
    : IO (Except String (Ixon.Env × Nat × CompileEnv)) := do
  -- The `IX_SHARING_LIMITS` override (`ix compile-lean --sharing-limits`).
  let sharingLimits ← match ← compilerSharingLimitsFromEnv with
    | .ok l => pure l
    | .error e => return .error e
  let mut vAcc : DriverAcc :=
    { cenv := { CompileEnv.new env with nameByHash, sharingLimits } }
  match precompileAuxGenPrereqs blocks vAcc with
  | .error e => return .error e
  | .ok a => vAcc := a
  let tStart ← IO.monoMsNow
  let numWorkers := max 1 cfg.numWorkers
  -- Block table, indexed in `blocks.blocks` order.
  let mut los : Array Name := #[]
  let mut alls : Array (Set Name) := #[]
  let mut idxOf : Std.HashMap Name Nat := {}
  for (lo, all) in blocks.blocks do
    idxOf := idxOf.insert lo los.size
    los := los.push lo
    alls := alls.push all
  let n := los.size
  let deps : Array (Array Name) := los.map fun lo =>
    match blocks.blockRefs.get? lo with
    | some d => d.toArray
    | none => #[]
  let plain : Array Bool := (los.zip alls).map fun (lo, all) => plainCandidate env lo all
  -- Readiness index shared by `V` and `L`: unresolved dependency → blocks.
  let mut dependents : Std.HashMap Name (Array Nat) := {}
  let mut vCnt : Array Nat := Array.replicate n 0
  for i in [:n] do
    for d in deps[i]! do
      if (resolveAddrPure vAcc.cenv d).isNone then
        dependents := dependents.alter d fun
          | some a => some (a.push i)
          | none => some #[i]
        vCnt := vCnt.modify i (· + 1)
  let mut lCnt := vCnt
  -- Priorities: length of the longest chain of dependent blocks.
  let height : Array Nat := Id.run do
    let mut succs : Array (Array Nat) := Array.replicate n #[]
    let mut indeg : Array Nat := Array.replicate n 0
    for j in [:n] do
      for d in deps[j]! do
        if let some dlo := blocks.lowLinks.get? d then
          if let some i := idxOf.get? dlo then
            if i != j then
              succs := succs.modify i (·.push j)
              indeg := indeg.modify j (· + 1)
    let mut order : Array Nat := #[]
    for i in [:n] do
      if indeg[i]! == 0 then order := order.push i
    let mut k := 0
    while k < order.size do
      let i := order[k]!
      k := k + 1
      for j in succs[i]! do
        indeg := indeg.modify j (· - 1)
        if indeg[j]! == 0 then order := order.push j
    let mut hts : Array Nat := Array.replicate n 1
    for r in [:order.size] do
      let i := order[order.size - 1 - r]!
      let mut m := 0
      for j in succs[i]! do
        m := max m hts[j]!
      hts := hts.set! i (m + 1)
    return hts
  let prio (i : Nat) : Nat :=
    if cfg.seed == 0 then height[i]! else (hash (cfg.seed, i)).toNat % 4096
  let delayOf (i : Nat) (exact : Bool) : Nat :=
    if cfg.jitterMs == 0 then 0
    else (hash (cfg.seed, i, exact)).toNat % (cfg.jitterMs + 1)
  let mkJob (i : Nat) (exact : Bool) (cenv : CompileEnv)
      (factsOf : Option (Array Name)) (log : Bool) : SchedJob :=
    { idx := i, exact, lo := los[i]!, all := alls[i]!, cenv, factsOf,
      delayMs := delayOf i exact, log }

  let workChan ← Std.CloseableChannel.Sync.new (α := SchedJob)
  let resultChan ← Std.CloseableChannel.Sync.new (α := SchedResult)
  -- IX_LOG_BLOCKS=1: per-block BEGIN/END trace (with duration and RSS at
  -- END), gated to the tail of the run (more than 600k merged constants)
  -- where the whole-Mathlib memory spike lives.
  let logBlocks := (← IO.getEnv "IX_LOG_BLOCKS").isSome
  let worker : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break
      | some job =>
        if job.delayMs > 0 then IO.sleep job.delayMs.toUInt32
        if job.log then
          IO.println s!"  [block] BEGIN {job.lo.pretty} ({job.all.size} members)"
          (← IO.getStdout).flush
        let t0 ← IO.monoMsNow
        let (outcome, facts) ← runSchedJob job
        let t1 ← IO.monoMsNow
        if job.log then
          let rssKb ← do
            let s ← IO.FS.readFile "/proc/self/status"
            pure <| (s.splitOn "\n").findSome? fun l =>
              if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
          IO.println s!"  [block] END {job.lo.pretty} {t1 - t0}ms \
rss{(rssKb.getD "?").trimAscii}"
          (← IO.getStdout).flush
        discard <| resultChan.send
          { idx := job.idx, exact := job.exact, outcome, facts, ms := t1 - t0 }
  for _ in [:numWorkers] do
    discard <| IO.asTask (prio := .dedicated) worker

  if cfg.dbg then
    IO.println s!"  [Lean CompileAux] {n} blocks, {numWorkers} workers, \
{if cfg.speculate then "speculative" else "wave"} schedule\
{if cfg.verify then ", verify" else ""}{if cfg.seed != 0 then s!", seed {cfg.seed}" else ""}"

  let mut st : Array SchedBlock := Array.replicate n {}
  let mut specOut : Array (Option (AuxBlockOutcome × Option PlainFacts)) :=
    Array.replicate n none
  let mut finalOut : Array (Option AuxBlockOutcome) := Array.replicate n none
  -- `V`: wave state.
  let mut vSat : Std.HashSet Name := {}
  let mut vFailed : Std.HashSet Name := {}
  let mut frontier : Array Nat := #[]
  let mut frontLeft := 0
  let mut wave := 0
  let mut merged := 0
  let mut vSnap := vAcc.cenv.workerView
  -- `L`: speculative state.
  let mut lAcc : DriverAcc := vAcc
  let mut lSat : Std.HashSet Name := {}
  let mut lFailed : Std.HashSet Name := {}
  let mut lSnap := lAcc.cenv.workerView
  let mut lastPub ← IO.monoMsNow
  -- Queues.
  let mut exactQ : BucketQ := {}
  let mut specCur : BucketQ := {}
  let mut specNext : BucketQ := {}
  let mut inFlight := 0
  let mut exactInFlight := 0
  let mut errorMsg : Option String := none
  let mut done := false
  -- Statistics.
  let mut nExact := 0
  let mut nSpec := 0
  let mut nAccepted := 0
  let mut nRedundant := 0
  let mut nRejected := 0
  let mut nPub := 0
  let mut nVerifyDiff := 0
  let mut nVerifyViolation := 0
  let mut workMs := 0
  let mut schedMs := 0
  let mut tWave := 0
  let mut tPub := 0
  let mut tLMerge := 0
  let mut tDisp := 0
  let mut lastPct := 0
  let mut waveLines : Array String := #[]
  -- Wave 1.
  let mut nextFront : Array Nat := #[]
  for i in [:n] do
    if vCnt[i]! == 0 then nextFront := nextFront.push i
  let mut opening := true

  repeat
    let tc0 ← IO.monoMsNow
    -- Close finished waves and open their successors.
    while errorMsg.isNone && !done && frontLeft == 0 do
      if !opening then
        -- Merge the finished wave into `V` in block-index order.
        let sorted := frontier.qsort (· < ·)
        let mut maxMs := 0
        let mut maxLo : Name := default
        let mut sumMs := 0
        for i in sorted do
          let o := (finalOut[i]!).getD default
          finalOut := finalOut.set! i none
          specOut := specOut.set! i none
          let b := st[i]!
          sumMs := sumMs + b.ms
          if b.ms >= maxMs then
            maxMs := b.ms
            maxLo := los[i]!
          if o.failsMembers then
            vFailed := alls[i]!.fold (·.insert ·) vFailed
          let touched := o.touchedNames alls[i]!
          let (acc', newNames) := applyAuxBlockOutcome vAcc los[i]! alls[i]! o
          vAcc := acc'
          merged := merged + 1
          if let some rust := rustRef then
            for name in newNames do
              if errorMsg.isNone then
                if let some rustAddr := rust.get? name then
                  if let some named := vAcc.cenv.nameToNamed.get? name then
                    if named.addr != rustAddr then
                      errorMsg := some s!"rustRef mismatch at {name.pretty}: \
lean={named.addr} rust={rustAddr} (block {los[i]!.pretty})"
          if errorMsg.isSome then break
          for nm in touched do
            if !vSat.contains nm &&
                ((resolveAddrPure vAcc.cenv nm).isSome || vFailed.contains nm) then
              vSat := vSat.insert nm
              if let some ds := dependents.get? nm then
                for j in ds do
                  vCnt := vCnt.modify j (· - 1)
                  if vCnt[j]! == 0 then nextFront := nextFront.push j
        if errorMsg.isSome then break
        if cfg.waveLog.isSome then
          waveLines := waveLines.push
            s!"{wave}\t{sorted.size}\t{maxMs}\t{sumMs}\t{maxLo.pretty}"
        if cfg.dbg then
          let pct := (merged * 100) / (max n 1)
          if pct >= lastPct + 10 then
            lastPct := pct
            let rssKb ← do
              let s ← IO.FS.readFile "/proc/self/status"
              pure <| (s.splitOn "\n").findSome? fun l =>
                if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
            let c := vAcc.cenv
            IO.println s!"  [Lean CompileAux] wave {wave}: {merged}/{n} blocks \
merged ({pct}%) · {(← IO.monoMsNow) - tStart}ms · \
rss{(rssKb.getD "?").trimAscii} · consts {c.constants.size} \
({c.totalBytes} B ser) · named {c.nameToNamed.size} · blobs {c.blobs.size} · \
plans {c.callSitePlans.size}/{c.brecOnCallSitePlans.size}/\
{c.belowCallSitePlans.size} · auxNames {c.auxNameToAddr.size}"
            (← IO.getStdout).flush
      opening := false
      -- Open the next wave.
      if nextFront.isEmpty then
        if merged < n then
          errorMsg := some s!"Circular dependency detected: {n - merged} \
blocks remaining but none ready"
        else
          done := true
        break
      wave := wave + 1
      frontier := nextFront.qsort (· < ·)
      nextFront := #[]
      vSnap := vAcc.cenv.workerView
      for i in frontier do
        let b := st[i]!
        let mut b := { b with inFront := true }
        frontLeft := frontLeft + 1
        if b.spec == 3 then
          let ok := match specOut[i]! with
            | some (o, f) => acceptSpeculative vAcc.cenv plain[i]! los[i]! deps[i]! o f
            | none => false
          if ok && !cfg.verify then
            finalOut := finalOut.set! i ((specOut[i]!).map (·.1))
            b := { b with final := true }
            nAccepted := nAccepted + 1
            frontLeft := frontLeft - 1
          else
            if plain[i]! && !ok then nRejected := nRejected + 1
            b := { b with exact := 1 }
            exactQ := exactQ.push (prio i) i
        else if b.spec == 2 && plain[i]! && !cfg.verify then
          pure ()  -- validate when the speculative run returns
        else
          b := { b with exact := 1, spec := if b.spec == 1 then 0 else b.spec }
          exactQ := exactQ.push (prio i) i
        st := st.set! i b
    let tc0d ← IO.monoMsNow
    tWave := tWave + (tc0d - tc0)
    if errorMsg.isSome || done then
      schedMs := schedMs + ((← IO.monoMsNow) - tc0)
      break

    let td0 ← IO.monoMsNow
    -- Dispatch.
    while inFlight < numWorkers do
      let (eTop, eq') := exactQ.peek st true
      exactQ := eq'
      let (cTop, cq') := specCur.peek st false
      specCur := cq'
      let (nTop, nq') := specNext.peek st false
      specNext := nq'
      -- Republish `L` when it exposes better work.
      if let some (np, _) := nTop then
        let curBest := cTop.map (·.1)
        let now ← IO.monoMsNow
        let better := match curBest with
          | none => true
          | some cp => np > cp && now - lastPub >= cfg.publishMs
        if better then
          let tp0 ← IO.monoMsNow
          lSnap := lAcc.cenv.workerView
          lastPub := now
          nPub := nPub + 1
          specCur := specCur.append specNext
          specNext := {}
          tPub := tPub + ((← IO.monoMsNow) - tp0)
          continue
      match eTop, cTop with
      | none, none => break
      | some (ep, i), cTop =>
        if exactInFlight * 100 < cfg.exactShare * numWorkers
            || cTop.all (fun (cp, _) => ep >= cp) then
          exactQ := exactQ.popTop
          st := st.modify i fun b => { b with exact := 2 }
          discard <| workChan.send (mkJob i true vSnap none
            (logBlocks && vAcc.cenv.constants.size > 600000))
          inFlight := inFlight + 1
          nExact := nExact + 1
          exactInFlight := exactInFlight + 1
          continue
        let some (_, j) := cTop | break
        specCur := specCur.popTop
        st := st.modify j fun b => { b with spec := 2 }
        discard <| workChan.send (mkJob j false lSnap
          (if plain[j]! then some deps[j]! else none)
          (logBlocks && vAcc.cenv.constants.size > 600000))
        inFlight := inFlight + 1
        nSpec := nSpec + 1
      | none, some (_, j) =>
        specCur := specCur.popTop
        st := st.modify j fun b => { b with spec := 2 }
        discard <| workChan.send (mkJob j false lSnap
          (if plain[j]! then some deps[j]! else none)
          (logBlocks && vAcc.cenv.constants.size > 600000))
        inFlight := inFlight + 1
        nSpec := nSpec + 1
    tDisp := tDisp + ((← IO.monoMsNow) - td0)
    schedMs := schedMs + ((← IO.monoMsNow) - tc0)

    if inFlight == 0 then
      errorMsg := some s!"scheduler stalled at wave {wave} with {n - merged} \
blocks unmerged"
      break
    -- Receive one result.
    let some r ← resultChan.recv
      | errorMsg := some "Result channel closed unexpectedly"
        break
    let tc1 ← IO.monoMsNow
    inFlight := inFlight - 1
    if r.exact then exactInFlight := exactInFlight - 1
    workMs := workMs + r.ms
    let i := r.idx
    let b := st[i]!
    if b.final then
      nRedundant := nRedundant + 1
      st := st.set! i (if r.exact then { b with exact := 3 } else { b with spec := 3 })
    else
      let o := r.outcome
      -- Speculative merge into `L` (any run that may still be needed).
      let tl0 ← IO.monoMsNow
      if cfg.speculate then
        if o.failsMembers then
          lFailed := alls[i]!.fold (·.insert ·) lFailed
        let touched := o.touchedNames alls[i]!
        let (acc', _) := applyAuxBlockOutcome lAcc los[i]! alls[i]! o.forLive
        let ⟨lc, _, _, _⟩ := acc'
        lAcc := { cenv := lc.workerView }
        for nm in touched do
          if !lSat.contains nm &&
              ((resolveAddrPure lAcc.cenv nm).isSome || lFailed.contains nm) then
            lSat := lSat.insert nm
            if let some ds := dependents.get? nm then
              for j in ds do
                lCnt := lCnt.modify j (· - 1)
                if lCnt[j]! == 0 then
                  let bj := st[j]!
                  if !bj.inFront && !bj.final && bj.spec == 0 && bj.exact == 0 then
                    st := st.set! j { bj with spec := 1 }
                    specNext := specNext.push (prio j) j
      tLMerge := tLMerge + ((← IO.monoMsNow) - tl0)
      let b := st[i]!
      if r.exact then
        if cfg.verify && b.spec == 3 then
          if let some (so, sf) := specOut[i]! then
            -- `V` still holds `W<w` of this block's (open) wave.
            let would := acceptSpeculative vAcc.cenv plain[i]! los[i]! deps[i]! so sf
            if would then nAccepted := nAccepted + 1
            if !so.same o then
              nVerifyDiff := nVerifyDiff + 1
              if would then
                nVerifyViolation := nVerifyViolation + 1
                IO.eprintln s!"  [Lean CompileAux] VERIFY: speculative outcome \
of {los[i]!.pretty} passed validation but differs from its wave outcome"
              else if cfg.dbg then
                IO.println s!"  [Lean CompileAux] verify: speculative outcome of \
{los[i]!.pretty} ({if plain[i]! then "plain" else "not plain"}) differs from \
its wave outcome; validation rejected it"
        finalOut := finalOut.set! i (some o)
        st := st.set! i { b with exact := 3, final := true, ms := r.ms }
        frontLeft := frontLeft - 1
      else
        let mut b := { b with spec := 3, ms := r.ms }
        if plain[i]! || cfg.verify then
          specOut := specOut.set! i (some (o, r.facts))
        if b.inFront && b.exact == 0 then
          let ok := acceptSpeculative vAcc.cenv plain[i]! los[i]! deps[i]! o r.facts
          if ok && !cfg.verify then
            finalOut := finalOut.set! i (some o)
            b := { b with final := true }
            nAccepted := nAccepted + 1
            frontLeft := frontLeft - 1
          else
            if plain[i]! && !ok then nRejected := nRejected + 1
            b := { b with exact := 1 }
            exactQ := exactQ.push (prio i) i
        st := st.set! i b
    schedMs := schedMs + ((← IO.monoMsNow) - tc1)

  discard <| workChan.close
  if let some e := errorMsg then
    return .error e
  -- Let in-flight redundant runs finish before returning.
  while inFlight > 0 do
    match ← resultChan.recv with
    | some r =>
      workMs := workMs + r.ms
      nRedundant := nRedundant + 1
      inFlight := inFlight - 1
    | none => inFlight := 0
  if let some path := cfg.waveLog then
    IO.FS.writeFile path ("\n".intercalate waveLines.toList ++ "\n")
  if cfg.dbg then
    let wall := (← IO.monoMsNow) - tStart
    let w := max wall 1
    IO.println s!"  [Lean CompileAux] {n} blocks in {wave} waves, {wall}ms: \
{nExact} exact runs, {nSpec} speculative ({nAccepted} accepted, {nRejected} plain ones rejected, \
{nRedundant} redundant), {nPub} publications; worker compute {workMs}ms \
(avg {workMs / w}.{(workMs * 10 / w) % 10} busy), scheduling thread {schedMs}ms (waves {tWave}, dispatch {tDisp}, L merges {tLMerge}, publications {tPub})\
{if cfg.verify then s!"; verify: {nVerifyDiff} speculative outcomes differ from \
the wave outcome, {nVerifyViolation} of them passed validation" else ""}"
  if cfg.verify && nVerifyViolation > 0 then
    return .error s!"speculative validation accepted {nVerifyViolation} \
outcome(s) that differ from their wave outcome"
  return .ok (assembleEnv vAcc)

/-- Parallel aux-aware environment compile. Same output as
    `compileEnvAux` and as the wave schedule (see the section docstring);
    the schedule knobs come from the environment
    (`AuxSchedConfig.fromEnv`).

    `rustRef` enables fail-fast address comparison: as each block merges
    into the authoritative state, every name it registered is checked
    against the reference map; the first divergence, in (wave,
    block-index) order, aborts with the offending name. -/
def compileEnvParallelAux (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (nameByHash : Std.HashMap Address Name := {})
    : IO (Except String (Ixon.Env × Nat × CompileEnv)) := do
  let cfg ← AuxSchedConfig.fromEnv numWorkers dbg
  compileEnvParallelAuxWith env blocks cfg rustRef nameByHash

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
    : IO (Except String LeanPipelineOut) := do
  let annotated := consts.any fun (_, source) => Ix.Compile.sourceHasSemanticContracts source
  for (name, source) in consts do
    if Ix.Compile.sourceHasAnnotations source then
      return .error s!"unresolved source binder contracts: {name}"
    match inspectSemanticSource source with
    | .error error => return .error error
    | .ok _ => pure ()
  -- IX_COMPILE_DBG=1 forces phase timing + the driver's periodic memory
  -- attribution trace without threading a flag through callers.
  let dbg := dbg || (← IO.getEnv "IX_COMPILE_DBG").isSome
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
  match ← compileEnvParallelAux ixEnv condensed rustRef numWorkers dbg
      nameByHash with
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
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  let constants ← match input.prepare with
    | .ok constants => pure constants
    | .error error => return .error error
  compileDecoratedConsts constants rustRef numWorkers dbg resourceProfile

/-- Compile an isolated source list, extracting its checked occurrence records. -/
def compileLeanConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    (resourceProfile : Option Ix.Resource.Profile := none) :
    IO (Except String LeanPipelineOut) := do
  let input ← match Ix.Compile.CompileInput.fromAnnotations consts with
    | .ok input => pure input
    | .error error => return .error (toString error)
  compileLeanInput input rustRef numWorkers dbg resourceProfile

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



