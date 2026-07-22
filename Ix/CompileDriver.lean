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
  - A fresh `AuxKernelCtx` per block instead of Rust's per-worker
    `KernelCtx` reused across blocks (cleared every `KENV_CLEAR_EVERY`).
    The kernel env is content-addressed, so reuse is a cache, not an
    input — the A2–A7 dump gates verified byte-identical aux output
    under fresh-per-block contexts.
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
  let getConst (n : Name) : Option ConstantInfo := cenv.env.consts.get? n
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
    call-site plans. -/
def mergeCompiledBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState)
    (plans : Std.HashMap Name CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Name BRecOnCallSitePlan) : DriverAcc := Id.run do
  let mut cenv := acc.cenv
  cenv := { cenv with
    totalBytes := cenv.totalBytes + result.blockBytes.size
    constants := cenv.constants.insert result.blockAddr result.block
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
        constants := cenv.constants.insert projAddr proj
        nameToNamed := cenv.nameToNamed.insert name { addr := projAddr, constMeta }
        nameToAddr := cenv.nameToAddr.insert name projAddr }
  -- Aux tail outputs: stored constants, Named overrides (in registration
  -- order — LAST wins per name), aux resolution map, extra names, plans.
  for (addr, c) in cache.auxConsts do
    cenv := { cenv with constants := cenv.constants.insert addr c }
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
  let mut pending := acc.pending
  for (n, _) in cache.auxNameToAddr do
    pending := pending.push n
  return { acc with
    cenv
    blockNames := cache.blockNames.fold (fun m k v => m.insert k v) acc.blockNames
    defHints := cache.defHints.fold (fun m k v => m.insert k v) acc.defHints
    pending }

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
      fun m a c => m.insert a (Ixon.LazyConstant.ofConstant c)
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
    (dbg : Bool := false) : Except String (Ixon.Env × Nat × CompileEnv) := Id.run do
  let mut acc : DriverAcc := { cenv := CompileEnv.new env }
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

Wave-based parallel version of `compileEnvAux`, mirroring the plain
`compileEnvParallel` architecture: each wave snapshots the accumulated
`CompileEnv`, workers compute a pure per-block outcome against the
snapshot, and the main thread applies the same merges as the sequential
driver. Blocks within a wave are dependency-independent, and every merge
is per-name-disjoint or content-keyed, so intra-wave completion order
cannot affect the output — the same property Rust's work-stealing
scheduler relies on. -/

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

/-- Apply a worker outcome to the live driver state. Returns the names
    newly REGISTERED by this block (for rustRef fail-fast comparison). -/
def applyAuxBlockOutcome (acc : DriverAcc) (lo : Name) (all : Set Name)
    (outcome : AuxBlockOutcome) : DriverAcc × Array Name := Id.run do
  let mut acc := acc
  let mut newNames : Array Name := #[]
  match outcome with
  | .compiled result cache plans brecPlans belowPlans =>
    acc := mergeCompiledBlock acc lo result cache plans brecPlans belowPlans
    if result.projections.isEmpty then
      newNames := newNames.push lo
    else
      for (name, _, _) in result.projections do
        newNames := newNames.push name
    for (n, _) in cache.auxNamed do
      newNames := newNames.push n
  | .failed msg =>
    for m in all do
      acc := { acc with cenv := { acc.cenv with
        ungrounded := acc.cenv.ungrounded.insert m msg } }
  | .promoted crossScc crossNames incompleteMsg noAux noAuxFailMsg =>
    if let some (clo, result, cache, plans, brecPlans, belowPlans) := crossScc then
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
      for m in all do
        acc := { acc with cenv := { acc.cenv with
          ungrounded := acc.cenv.ungrounded.insert m msg } }
    | none =>
      match noAuxFailMsg with
      | some msg =>
        for m in all do
          acc := { acc with cenv := { acc.cenv with
            ungrounded := acc.cenv.ungrounded.insert m msg } }
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
            match promoteAuxDriver acc.cenv name origAddr origMeta with
            | .error e =>
              promoteFailed := true
              let msg := toString e
              for m in all do
                acc := { acc with cenv := { acc.cenv with
                  ungrounded := acc.cenv.ungrounded.insert m msg } }
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
      -- Promote remaining names from auxNameToAddr (env.rs:697-707) —
      -- against the LIVE env; also counts as registration for rustRef.
      if incompleteMsg.isNone then
        for name in all do
          if !acc.cenv.nameToAddr.contains name then
            if let some addr := resolveAddrPure acc.cenv name then
              acc := { acc with cenv := { acc.cenv with
                nameToAddr := acc.cenv.nameToAddr.insert name addr } }
              newNames := newNames.push name
  return (acc, newNames)

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
    : IO (Except String (Ixon.Env × Nat × CompileEnv)) := do
  let totalBlocks := blocks.blocks.size

  let mut acc : DriverAcc := { cenv := CompileEnv.new env }
  match precompileAuxGenPrereqs blocks acc with
  | .error e => return .error e
  | .ok a => acc := a

  let workChan ← Std.CloseableChannel.Sync.new (α := AuxWorkItem)
  let resultChan ← Std.CloseableChannel.Sync.new
    (α := Name × Set Name × AuxBlockOutcome)

  let worker (_workerId : Nat) : IO Unit := do
    while true do
      match ← workChan.recv with
      | none => break
      | some item =>
        let outcome := auxBlockOutcome item.cenv item.lo item.all
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
      let all := blocks.blocks.get! lo
      let deps := match blocks.blockRefs.get? lo with
        | some d => d
        | none => {}
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

    for (lo, all) in ready do
      discard <| workChan.send { lo, all, cenv := snapshot }

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
        let (acc', newNames) := applyAuxBlockOutcome acc lo all outcome
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

/-- Run the full pure-Lean compile pipeline over a constant list.
    See the section docstring; phase timings print when `dbg` is set. -/
def compileLeanConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (dbg : Bool := false)
    : IO (Except String LeanPipelineOut) := do
  let tick (label : String) (t0 : Nat) : IO Nat := do
    let t1 ← IO.monoMsNow
    if dbg then
      IO.println s!"  [compile-lean] {label}: {t1 - t0}ms"
    pure t1
  let t0 ← IO.monoMsNow
  -- 1. Canonicalize (Lean → Ix, content-addressed hashing) — chunked
  --    task-parallel, mirroring `Ix.CanonM.canonEnvParallel`.
  let constArr := consts.toArray
  let chunkSize := max 1 ((constArr.size + numWorkers - 1) / numWorkers)
  let chunkArr := Ix.CanonM.chunks constArr chunkSize
  let tasks := chunkArr.map fun chunk =>
    Task.spawn fun _ => Ix.CanonM.canonChunk chunk
  let mut ixConsts : Ix.Map Ix.Name Ix.ConstantInfo := {}
  for task in tasks do
    for (name, const) in task.get do
      ixConsts := ixConsts.insert name const
  let ixEnv : Ix.Environment := { consts := ixConsts }
  let t ← tick s!"canon ({ixConsts.size} consts)" t0
  -- 2. Reference graph (out-refs).
  let outRefs := Ix.GraphM.envParallel ixEnv
  let t ← tick s!"graph ({outRefs.size} nodes)" t
  -- 3. Groundedness: immediate per-constant scan, reverse-ref
  --    proliferation, graph filter (env.rs:160-227 / setup_scan).
  let mut immediate : Ix.Map Ix.Name Ix.GroundError := {}
  for (n, ci) in ixEnv.consts do
    if let .error e := Ix.groundConstCheck ci ixEnv then
      immediate := immediate.insert n e
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
  -- 5. Aux-aware parallel compile.
  match ← compileEnvParallelAux ixEnv condensed rustRef numWorkers dbg with
  | .error e => return .error e
  | .ok (ixonEnv, _, cenv) =>
    let t ← tick "compile" t
    if dbg && cenv.ungrounded.size > 0 then
      IO.println s!"  [compile-lean] {cenv.ungrounded.size} per-block compile failures"
      for (n, e) in cenv.ungrounded.toList.take 5 do
        IO.println s!"    failed: {n.pretty}: {e.take 200}"
    -- 6. Serialize.
    match Ixon.serEnv ixonEnv with
    | .error e => return .error s!"serEnv failed: {e}"
    | .ok bytes =>
      let _ ← tick s!"serialize ({bytes.size} bytes)" t
      return .ok {
        bytes
        env := ixonEnv
        cenv
        ungroundedCount := ungrounded.size
        blockCount := condensed.blocks.size }

end Ix.CompileM
