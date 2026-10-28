/-
  Ix.CompileDriver: the compile-env driver.

  Port of the production scheduler semantics of
  `crates/compile/src/compile/env.rs` (`compile_env_with_options`) and the
  per-block dispatch of `compile_const` (compile.rs), on top of the pure
  block compiler (`Ix.CompileM`). Lean's declarations compile as given: each
  block of the condensation is compiled once, in Lean's order, and Lean's own
  auxiliaries (`rec`, `casesOn`, `below`, …) are blocks of their own.

  Deliberate deviations from Rust, none output-visible:
  - One schedule, a pure fold over waves of ready blocks applied in
    block-key order (`compileEnvFold`), instead of work-stealing threads.
    Output maps are keyed by name/address. Name claims (`nameToAddr`) are
    insert-once: a second claim at a different address is the error Rust's
    insert-once claims raise (`checkBlockClaims`, single ownership).
    `Named` entries are last-wins overrides within one block's
    registrations, and constants and blobs are content-keyed. So
    scheduling order does not affect the result (Rust relies on the same
    property for its nondeterministic work-stealing order).
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
public import Ix.Compile.WorkerContext
import all Ix.CompileM
import all Ix.Compile.WorkerContext
import Std.Data.HashSet.Lemmas
public import Ix.IndFlags
public import Ix.Compile.Publication
public import Ix.Compile.SourceContract.Transport
public import Ix.Compile.SourceGraph.Prepass
public import Ix.Compile.SourceInput
public import Ix.Resource.Addressed
public section

namespace Ix.CompileM

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

/-- Register the synthetic `Muts` named entry of a mutual block (Rust
    `compile_mutual`): the block's address under `Ix.<hex>.<first member>`
    (`Address.mutsName`), with each class's member name hashes. Kernel
    ingress discovers a mutual block through this entry. The entry goes to
    `BlockState.mutsNamed`, which the driver merges after the members'
    entries. -/
def registerMutsEntry (sortedClasses : List (List MutConst)) (blockAddr : Address) :
    CompileM Unit := do
  let some firstClass := sortedClasses.head?
    | throw (.invalidMutualBlock "registerMutsEntry: block without a class")
  let some first := firstClass.head?
    | throw (.invalidMutualBlock "registerMutsEntry: class without a member")
  let mutsAll : Array (Array Address) := sortedClasses.toArray.map fun cls =>
    cls.toArray.map fun c => c.name.getHash
  let mutsName := blockAddr.mutsName first.name
  compileName mutsName
  modifyBlockState fun st =>
    { st with mutsNamed := st.mutsNamed.push (mutsName,
        { addr := blockAddr, constMeta := Ixon.ConstantMeta.new (.muts mutsAll none) }) }

/-- Compile one block of the condensation. Mirrors `compile_const_inner`
    (compile.rs): singleton non-inductive constants take the plain
    single-constant path; mutual blocks and inductives (of any size) go
    through `compileMutualBlock` in Lean's order (`sourceClasses`) and
    register their synthetic `Muts` entry (Rust `compile_mutual`).

    The members' projection addresses are inserted into
    `BlockState.blockNameToAddr`, where Rust writes them into the global
    `name_to_addr` (compile.rs). -/
def compileBlock (lo : Name) (all : Set Name) : CompileM BlockResult := do
  let const ← findConst lo
  let isIndBlock := match const with
    | .inductInfo _ | .ctorInfo _ => true
    | _ => false
  if all.size == 1 && !isIndBlock then
    let result ← compileConstantInfo const
    return result
  let mut cs : Array MutConst := #[]
  for n in all do
    match ← findConst n with
    | .inductInfo val => cs := cs.push (← MutConst.mkIndc val)
    | .defnInfo val => cs := cs.push (MutConst.fromDefinitionVal val)
    | .opaqueInfo val => cs := cs.push (MutConst.fromOpaqueVal val)
    | .thmInfo val => cs := cs.push (MutConst.fromTheoremVal val)
    | .recInfo val => cs := cs.push (.recr val)
    | _ => continue
  -- Lean's order (`sourceClasses`): the order of a block is the source's.
  let sortedClasses := sourceClasses cs
  let blockResult ← compileMutualBlock sortedClasses
  -- A standalone constant (a single non-inductive member): Rust returns
  -- before the Muts registration (compile.rs) — no synthetic Muts entry.
  let isMuts := match blockResult.block.info with
    | .muts _ => true
    | _ => false
  if !isMuts then
    return blockResult
  -- Primary member registrations (compile.rs).
  for (name, proj, _) in blockResult.projections do
    let projAddr := Address.admissionHash (Ixon.ser proj)
    modifyBlockState fun st =>
      { st with blockNameToAddr := st.blockNameToAddr.insert name projAddr }
  -- Class ordering for `CompileEnv.blocks` (Rust `stt.blocks`).
  let blockResult := { blockResult with
    classNames := sortedClasses.toArray.map fun cls =>
      cls.toArray.map (·.name) }
  registerMutsEntry sortedClasses blockResult.blockAddr
  return blockResult

/-- Compile one block (`compileBlock`) purely, from the empty block state,
    returning its result and the final block state. -/
def runBlock (cenv : CompileEnv) (all : Set Name) (lo : Name)
    : Except CompileError (BlockResult × BlockState) := do
  let blockEnv : BlockEnv :=
    { all, current := lo, mutCtx := default, univCtx := [] }
  CompileM.run cenv blockEnv {} (compileBlock lo all)

/-! ## Driver state and merges -/

/-- Accumulated driver-level side maps that live OUTSIDE `CompileEnv`
    (the per-name hints and the name-component index). -/
structure DriverAcc where
  cenv : CompileEnv
  blockNames : Std.HashMap Address Ix.Name := {}
  defHints : Std.HashMap Name Lean.ReducibilityHints := {}

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
    `CompileState::claim_compiled_name`), checked against the LIVE driver
    state before anything is merged: a `name_to_addr` entry at another
    address, by an earlier block or earlier in this block, is a conflict, and
    an identical re-claim is a no-op.

    The Lean block computes against a snapshot and the driver merges
    afterwards, so the same check runs here, in the same order, with the
    same messages. In the sequential driver the snapshot is the live state;
    in the wave driver this check is what catches two blocks of one wave
    claiming one name. A refused block merges nothing; the driver records
    the error for every member, like any other block failure. -/
def checkBlockClaims (cenv : CompileEnv) (primary : Array (Name × Address))
    : Except CompileError Unit := do
  let mut compiled : Std.HashMap Ix.Compile.ExactKey.ExactName Address := {}
  for (name, addr) in primary do
    -- A second compiled claim at another address, by an earlier block or
    -- earlier in this block, is a conflict: an overwrite would make the
    -- address a name keeps depend on which block merged last. An identical
    -- re-claim is a no-op, so valid input (where no name is compiled twice)
    -- merges the same values.
    if let some existing := (compiled.get? name).orElse fun _ => cenv.nameToAddr.get? name then
      if existing != addr then throw (nameClaimConflict name existing addr)
    compiled := compiled.insert name addr

/-- Validate both the block's name claims (`checkBlockClaims`) and its
    anonymous payloads (`checkBlockContent`: a reused record or blob address
    must hold the same bytes) against the live state before publishing any
    output of this block. -/
def checkCompiledBlock (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    (cache : BlockState) : Except CompileError Unit := do
  checkBlockClaims cenv (primaryClaims lo result)
  checkBlockContent cenv result cache

/-- The names of a compiled block whose `Named` entry another block owns
    (`mergeCompiledBlock`): its primary names already claimed in
    `nameToAddr`. A function of its own: when the merge read the state
    inside its own loops, a second reference to the state stayed alive and
    every insert of the merge copied its maps (Init+Std's compile phase went
    from 44 s to 388 s). -/
def reclaimedNames (cenv : CompileEnv) (lo : Name) (result : BlockResult)
    : Std.HashSet Name := Id.run do
  let primaryNames : Array Name :=
    if result.projections.isEmpty then #[lo] else result.projections.map (·.1)
  let mut reclaimed : Std.HashSet Name := {}
  for name in primaryNames do
    if cenv.nameToAddr.contains name then
      reclaimed := reclaimed.insert name
  return reclaimed

/-- Merge one compiled block's outputs into the driver state, mirroring
    the Rust global-mutation order: block constant, member projections
    (primary `register_name` + `name_to_addr`, compile.rs), then the block's
    `Muts` entry.

    Every caller first checks the block against the live state
    (`checkCompiledBlock`: single ownership of its names, and its records'
    and blobs' bytes) and merges only if the check passes: a conflict is an
    error and nothing is merged. The check is a separate step, not part of
    this function, so that the merge keeps consuming the driver state
    uniquely (a merge returning `Except` would keep the old state alive for
    the error branch and copy every map it inserts into). Content-keyed
    tables (constants, blobs) are unioned by content, which the check made
    conflict-free.

    An identical re-claim of a name an earlier block claimed (a primary name
    already in `nameToAddr`; the check made the addresses equal) does not own
    the name: its `Named` entry is not merged, so the owner's entry, with its
    hints, is kept, and which entry a name keeps does not depend on which
    block merged last. Mirrors Rust
    `CompileState::claim_and_register_compiled`; a name this block claims
    twice is still its own (Rust: the claim is in the block's transaction
    log). -/
def mergeCompiledBlock (acc : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState) : DriverAcc := Id.run do
  let mut cenv := acc.cenv
  -- The names whose `Named` entry another block owns, read from the state
  -- before this merge by a function of its own, so that the merge below
  -- still consumes the driver state's maps uniquely. Do not inline it: read
  -- in this function's loops, the state stayed referenced twice and every
  -- insert below copied its maps (Init+Std's compile phase 44 s → 391 s).
  let reclaimed := reclaimedNames cenv lo result
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
  -- The block's `Muts` entry (in registration order; LAST wins per name).
  for (n, named) in cache.mutsNamed do
    if !reclaimed.contains n then
      cenv := { cenv with nameToNamed := cenv.nameToNamed.insert n named }
  -- Class-ordering registry (Rust `stt.blocks`, compile.rs):
  -- one entry per member, all pointing at the block's full ordering.
  if !result.classNames.isEmpty then
    for cls in result.classNames do
      for n in cls do
        cenv := { cenv with blocks := cenv.blocks.insert n result.classNames }
  return { acc with
    cenv
    blockNames := cache.blockNames.fold (fun m k v => m.insert k v) acc.blockNames
    defHints := cache.defHints.fold (fun m k v => m.insert k v) acc.defHints }

/-- The one readiness rule of the driver: a source name (a member of a
    condensation block, `sourceOwned`) is ready only when its own block has
    completed, successfully or not (`settled`); a name without a source block
    is ready once it resolves. Failed blocks settle too, so their dependents
    run and report their missing reads. -/
def auxDependencyReady (sourceOwned : Name → Bool) (cenv : CompileEnv)
    (settled : Set Name) (name : Name) : Bool :=
  settled.contains name || (!sourceOwned name && (cenv.nameToAddr.get? name).isSome)

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
  -- The stored blobs are inserted last, so at an address both hold, the payload the
  -- compile stored (and checked, `checkBlobContent`) wins over a name component's.
  let allBlobs := cenv.blobs.fold (fun m k v => m.insert k v) nameBlobs
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

/-- Assemble the final environment (`assembleEnv`). -/
def finalizeEnv (acc : DriverAcc) : Except String (Ixon.Env × Nat × CompileEnv) :=
  pure (assembleEnv acc)

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
    `Ix.IndFlags.validateIndGroup`), or the compile fails before any block is
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
      if let .error e := CompileM.run cenv blockEnv {} (Ix.IndFlags.validateIndGroup all) then
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

/-! ## Per-block outcomes

The driver's step (`compileEnvFold`, below): a block's outcome is computed
against a wave's snapshot of the state (`auxBlockOutcome`, pure), and applied
to the live state (`applyAuxBlockOutcome`). Blocks within a wave are
dependency-independent, and every merge is per-name-disjoint or
content-keyed: two blocks of one wave that claim one name at different
addresses are refused by the merge-time check (`checkCompiledBlock`) against
the live state, as Rust's insert-once claims refuse them; so are conflicting
payloads at one record or blob address. The fold applies a wave's outcomes in
block-key order, so the later block in that order reports the conflict (Rust
reports by completion order). -/

/-- Pure per-block outcome computed by a wave worker. -/
inductive AuxBlockOutcome where
  /-- The block compiled (`runBlock`): its result and final block state. -/
  | compiled (result : BlockResult) (cache : BlockState)
  /-- The block's compile failed — soft (env.rs). -/
  | failed (msg : String)

/-- Compute a block's outcome against a wave-snapshot env: its compile
    (`runBlock`) under its canonical key. Pure. -/
def auxBlockOutcome (cenv : CompileEnv) (lo : Name) (all : Set Name) :
    AuxBlockOutcome :=
  match runBlock cenv all lo with
  | .error e => .failed (toString e)
  | .ok (result, cache) => .compiled result cache

/-- Apply a worker outcome to the live driver state. Returns the names
    newly REGISTERED by this block (for rustRef fail-fast comparison), and
    whether the block failed at merge time: a conflicting claim or payload
    (`checkCompiledBlock`). The wave loop settles every completed block's
    members, failed or not (`auxDependencyReady`). -/
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
  | .compiled result cache =>
    match checkCompiledBlock acc.cenv lo result cache with
    | .error e => return (recordFailure acc all.toArray (toString e), #[], true)
    | .ok () => acc := mergeCompiledBlock acc lo result cache
    if result.projections.isEmpty then
      newNames := newNames.push lo
    else
      for (name, _, _) in result.projections do
        newNames := newNames.push name
    for (n, _) in cache.mutsNamed do
      newNames := newNames.push n
  | .failed msg =>
    acc := recordFailure acc all.toArray msg
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

**Dependencies.** A block's scheduling dependencies are its condensation
references (`Ix.CondensedBlocks.blockRefs`): a block compiles Lean's own
declarations, which reference nothing outside them. -/

/-- The fold's schedule, fixed before the first wave. -/
structure FoldSchedule where
  /-- Each block's scheduling dependencies (its condensation references), by
      representative. -/
  deps : Std.HashMap Name (Set Name)
  /-- For each source-owned name, the blocks (representatives) depending on it. -/
  waiters : Std.HashMap Name (Array Name)
  /-- Each block's number of source-owned scheduling dependencies. -/
  sourceDeps : Std.HashMap Name Nat

/-- The schedule of a condensation: each block depends on its condensation
    references. The waiter lists are built by taking each list out of the
    map before pushing to it, so that it is never copied (`insert d ((getD d
    #[]).push lo)` copied the list every time). -/
def FoldSchedule.of (blocks : Ix.CondensedBlocks) : FoldSchedule := Id.run do
  let mut deps : Std.HashMap Name (Set Name) := {}
  let mut waiters : Std.HashMap Name (Array Name) := {}
  let mut sourceDeps : Std.HashMap Name Nat := {}
  for (rep, _) in blocks.blocks do
    let ds := (blocks.blockRefs.get? rep).getD {}
    deps := deps.insert rep ds
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

/-- The state before the first wave. -/
def FoldState.init (cenv : CompileEnv) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) : FoldState := Id.run do
  let mut unmet : Std.HashMap Name Nat := {}
  let mut candidates : Array Name := #[]
  for (rep, _) in blocks.blocks do
    let k := (sched.sourceDeps.get? rep).getD 0
    if k == 0 then candidates := candidates.push rep else unmet := unmet.insert rep k
  return { acc := { cenv }, unmet, candidates,
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

namespace WorkerSnapshot

open Ix.Compile.WorkerContext
open scoped Ix.Compile.WorkerContext

theorem Stable.forIn_set (items : Ix.Set Ix.Name) (initial : α)
    (body : Ix.Name → α → CompileM (ForInStep α)) (stable : ∀ item acc, Stable (body item acc)) :
    Stable (forIn items initial body) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact Stable.forIn_list items.toList initial body stable

theorem registerMutsEntry_stable (classes : List (List Ix.MutConst)) (address : Address) :
    Stable (registerMutsEntry classes address) := by
  unfold registerMutsEntry
  finish_steps

theorem compileBlock_stable (name : Ix.Name) (all : Ix.Set Ix.Name) : Stable (compileBlock name all) := by
  unfold compileBlock
  with_reducible repeat' first
    | exact compileConstantInfo_stable _
    | exact compileMutualBlock_stable _
    | exact registerMutsEntry_stable _ _
    | exact mkIndc_stable _
    | refine Stable.forIn_set _ _ _ (fun _ _ => ?_)
    | finish_step

/-- A block's successful result or complete refusal depends only on its four
global inputs, independently of the driver's accumulated output maps. -/
theorem runBlock_same (left right : CompileEnv) (same : SameReads left right)
    (all : Ix.Set Ix.Name) (name : Ix.Name) : runBlock left all name = runBlock right all name := by
  have runs := compileBlock_stable name all left right same
    { all, current := name, mutCtx := default, univCtx := [] } {}
  have run_eq (action : CompileM BlockResult) (env : CompileEnv) (block : BlockEnv) (state : BlockState) :
      CompileM.run env block state action =
        match Ix.Compile.WorkerContext.run action (env, block) state with
        | (.ok value, after) => .ok (value, after)
        | (.error error, _) => .error error := by
    simp only [CompileM.run, Ix.Compile.WorkerContext.run, ReaderT.run, ExceptT.run, StateT.run]
    cases action (env, block) state with
    | mk outcome after => cases outcome <;> rfl
  unfold runBlock
  rw [run_eq, run_eq, runs]

theorem outcome_projected (snapshot : CompileEnv) (name : Ix.Name) (all : Ix.Set Ix.Name) :
    auxBlockOutcome (project snapshot) name all = auxBlockOutcome snapshot name all := by
  unfold auxBlockOutcome
  rw [← runBlock_same snapshot (project snapshot) (project_same snapshot)]

end WorkerSnapshot

/-- Project the snapshot before spawning any task. Workers keep their exact
input fields while output-only maps stay outside every task closure. Chunk
partitioning and the scheduler's application order are unchanged. -/
@[expose] def waveTasksProjected (width : Nat) (snapshot : CompileEnv)
    (ready : Array (Name × Name × Set Name)) :
    Array (Task (Array (Name × Set Name × AuxBlockOutcome))) :=
  let snapshot := Ix.Compile.WorkerContext.project snapshot
  let n := ready.size
  let width := max 1 width
  let size := (n + width - 1) / width
  let chunks := if size == 0 then 0 else (n + size - 1) / size
  (Array.range chunks).map fun c => Task.spawn fun _ =>
    (ready.extract (c * size) ((c + 1) * size)).map fun (key, _, all) =>
      (key, all, auxBlockOutcome snapshot key all)

@[csimp] theorem waveTasks_eq_projected : @waveTasks = @waveTasksProjected := by
  funext width snapshot ready
  simp only [waveTasks, waveTasksProjected, WorkerSnapshot.outcome_projected]

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
    dbg_trace s!"  [compile-lean] wave {waves + 1}: {ready.size} blocks ready, \
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

/-- **The driver.** Compile an environment's condensation, as a fold over
    waves (see the section docstring). Per-block failures are recorded per
    member in `ungrounded`, and dependents cascade into `MissingConstant`
    failures, mirroring env.rs. The compile itself fails on a condensation
    block without references, on an input inductive group with non-canonical
    flags, on a mutual block of mixed safety, and on a schedule that cannot
    finish.

    The fold reads constants only through `Ix.Environment.get?`: it runs over
    a lookup view of `env` whose map is empty, so a materialized environment
    and a hybrid one with the same lookups (the IO pipeline's, whose theorem
    and opaque bodies come from `fallback?`) compile alike. The returned
    `CompileEnv` holds `env` again. -/
def compileEnvFold (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool := false)
    (sharingLimits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks)
    : Except String (Ixon.Env × Nat × CompileEnv) := do
  if let some msg := missingBlockRefs? blocks then throw msg
  validateInductiveFlags env
  validateMutualSafety env blocks
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  let sched := FoldSchedule.of blocks
  let cenv₀ := { CompileEnv.new view with sharingLimits }
  let st ← foldWaves blocks sched width dbg (blocks.blocks.size + 1) (FoldState.init cenv₀ blocks sched)
  let (ixe, bytes, cenv) ← finalizeEnv st.acc
  return (ixe, bytes, { cenv with env })

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
  /-- The condensation the driver compiled (the declaration groups and their
      references). -/
  blocks : Ix.CondensedBlocks := default
  /-- Complete original-input dependency facts, before grounding; no acceptance
      verdict. `none` is unavailable, while `some {}` is an empty input. -/
  sourceNodes? : Option (Ix.Map Name Ix.Compile.SourceGraph.Node) := none
  /-- Original prepared-input winners, shared with the lazy compiler fallback.
      Production always supplies this; manually fabricated outputs may omit it. -/
  originalSource? : Option Ix.Compile.SourceInput.Carrier := none

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

/-- **The checks of a prepared source list** (`Ix.Compile.CompileInput.prepare`'s
output), made before it is canonicalized: no binder contract is left
unresolved, and every semantic contract inspects (`inspectSemanticSource`).
The result says whether the list carries semantic contracts; such a list's
output is emitted only after resource validation. -/
def checkPreparedSource (consts : List (Lean.Name × Lean.ConstantInfo)) : Except String Bool := do
  for (name, source) in consts do
    if Ix.Compile.sourceHasAnnotations source then
      throw s!"unresolved source binder contracts: {name}"
    inspectSemanticSource source
  return consts.any fun (_, source) => Ix.Compile.sourceHasSemanticContracts source

def compileDecoratedConsts (consts : List (Lean.Name × Lean.ConstantInfo))
    (rustRef : Option (Std.HashMap Name Address) := none)
    (numWorkers : Nat := 32) (opts : DriverOptions := {})
    : IO (Except String LeanPipelineOut) := do
  let annotated ← match checkPreparedSource consts with
    | .ok annotated => pure annotated
    | .error error => return .error error
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
  let ⟨leanByIx, thinConsts, ixArr⟩ ← IO.lazyPure fun _ =>
    Ix.Compile.SourceGraph.Prepass.run constArr
  let t ← tick s!"canon names ({ixArr.size} consts)" t0
  -- 1b/2/3a. Streamed canon (chunk-parallel): canonicalize, take refs +
  --     immediate ground error + digest. PROOF bodies (`thmInfo` /
  --     `opaqueInfo` — the bulk of a Mathlib-scale env, and never read
  --     by dependents' compiles) are dropped after extraction and
  --     re-canonicalized on demand for their own block only. CODE kinds
  --     (definitions, inductive families, recursors — what the flags check and
  --     kernel ingress read from dependents, repeatedly and with
  --     retention) are KEPT and materialized as the shared `consts`
  --     map: one shared structure instead of a fresh unshared copy per
  --     on-demand read.
  -- Destructure immediately: fallback retains only leanByIx; temporary thin,
  -- label and task storage must not escape through a captured aggregate.
  let ⟨⟨sourceNodes, codeConsts⟩, outRefs, immediate, digests⟩ ←
    IO.lazyPure fun _ => Ix.Compile.SourceGraph.Stream.runLabelled
      { consts := thinConsts } ixArr numWorkers
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
  --    compile at once.
  let originalSource : Ix.Compile.SourceInput.Carrier := ⟨leanByIx⟩
  let fallback : Ix.Name → Option Ix.ConstantInfo := originalSource.lookup?
  let ixEnv : Ix.Environment :=
    { consts := codeConsts, fallback? := some fallback }
  if dbg then
    IO.println s!"  [compile-lean] {condensed.blocks.size} blocks, {4 * numWorkers} tasks per wave"
  let folded ← IO.lazyPure fun _ =>
    compileEnvFold ixEnv condensed (dbg := dbg)
      (sharingLimits := opts.sharingLimits) (width := 4 * numWorkers)
  match folded with
  | .error e => return .error e
  | .ok (ixonEnv, _, cenv) =>
    let t ← tick "compile" t
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
        blocks := condensed
        sourceNodes? := some sourceNodes
        originalSource? := some originalSource }

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



