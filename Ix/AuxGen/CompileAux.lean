/-
  Ix.AuxGen.CompileAux: compilation of aux_gen-generated constants into
  Ixon blocks.

  Port of `crates/compile/src/compile/mutual.rs`:

  1. `compileAuxBlock` / `compileAuxBlockWithRename` (mutual.rs:60/:103):
     sort aux `MutConst`s into equivalence classes, compile each class
     representative, emit either a standalone constant (singleton
     non-inductive) or a `Muts` block with per-member projections, and
     register the results.
  2. `generateAndCompileAuxRecursors` (mutual.rs:511): the full aux_gen
     pipeline — generate patches, then compile recursors, `.casesOn`,
     `.recOn`, `.below`, `.below.rec`, and `.brecOn` (3 batches).

  State model: Rust mutates the global `CompileState`
  (`stt.env.store_const` / `stt.env.register_name` /
  `stt.aux_name_to_addr` / `stt.aux_gen_extra_names`); the pure model
  collects the same events into the current block's `BlockState`
  (`auxConsts` / `auxNamed` / `auxNameToAddr` / `auxGenExtraNames`) for
  the driver to merge. Within-block phase ordering still works like
  Rust's global DashMap because `Ix.CompileM.lookupConstAddr` falls back
  to `blockState.auxNameToAddr`. Rust's `stt.aux_gen_pending` queue is
  scheduler machinery and is NOT modeled here (next milestone); its push
  sites are marked with comments.

  Cache model: Rust's `compile_aux_block` creates a fresh
  `BlockCache::default()` per call (mutual.rs:114). Here that means
  saving, clearing, and afterwards restoring the cache-like `BlockState`
  fields (`exprCache`/`univCache`/`cmpCache`/`refs`/`refsIndex`/`univs`/
  `univsIndex`/`arena`) around each `compileAuxBlockWithRename` call —
  the same precedent as `sortAuxByPartitionRefinement` in
  `Ix.AuxGen.Nested`. The stt-like fields (`blockBlobs`/`blockNames`/
  `defHints` and the `aux*` fields) accumulate across phases, mirroring
  Rust's global state.

  NOTE on addressing: Rust resolves addresses LIVE through
  `stt.resolve_addr` inside `ensure_in_kenv`; the Lean `AddrMaps` is a
  snapshot of closures, so kenv keying may use provisional (name-hash)
  addresses for constants compiled after the snapshot was taken.
  Provisional addresses are internally consistent within one bridge kenv
  (see `Ix.AuxGen.Kernel`), which is all the kernel needs. The
  output-visible resolution paths (`registerAuxAliases`, the
  available-alias filter, and all expression compilation) go through the
  live CompileM chain instead.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Mutual
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.Nested
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.Recursor
public import Ix.AuxGen.Patches
public import Ix.AuxGen.Surgery
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError getBlockState modifyBlockState
  getCompileEnv compileName withMutCtx preseedExprTables
  mutConstPreseedExprs compileMutConsts sortConsts buildConstantWithSharing)

/-! ## State-model helpers (Rust `CompileState` mutations) -/

/-- `u64::MAX` — the "no key entry" sentinel of the class-order reorder
    (mutual.rs:136) and of `class_order_key` (mutual.rs:713). Numerically
    identical to `PERM_OUT_OF_SCC`. -/
def u64Max : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Content-addressed hash of a Constant. Mirrors Rust `content_address`
    (mutual.rs:487).

    (Defined before its callers instead of at its Rust source position
    after `register_aux_aliases`; no semantic difference.) -/
def contentAddress (constant : Ixon.Constant) : Address :=
  Address.blake3 (Ixon.ser constant)

/-- Model of Rust `stt.env.store_const(addr, constant)` for aux blocks:
    append to the current block's `auxConsts`. -/
def auxStoreConst (addr : Address) (constant : Ixon.Constant) : CompileM Unit :=
  modifyBlockState fun st =>
    { st with auxConsts := st.auxConsts.push (addr, constant) }

/-- Model of Rust `stt.env.register_name(name, named)` for aux blocks:
    append to `auxNamed` (later entries for a name override earlier —
    DashMap insert semantics). -/
def auxRegisterName (name : Name) (named : Ixon.Named) : CompileM Unit :=
  modifyBlockState fun st =>
    { st with auxNamed := st.auxNamed.push (name, named) }

/-- Model of Rust `stt.aux_name_to_addr.insert(name, addr)`. -/
def auxInsertNameToAddr (name : Name) (addr : Address) : CompileM Unit :=
  modifyBlockState fun st =>
    { st with auxNameToAddr := st.auxNameToAddr.insert name addr }

/-- Model of Rust `stt.aux_gen_extra_names.insert(name)`. -/
def auxInsertExtraName (name : Name) : CompileM Unit :=
  modifyBlockState fun st =>
    { st with auxGenExtraNames := st.auxGenExtraNames.insert name }

/-- Non-throwing `stt.resolve_addr` (compile.rs:261-274): compiled names
    (the current block's primary registrations, then the driver-merged
    map), then the current block's aux registrations, then previously
    merged aux names. The total sibling of `Ix.CompileM.lookupConstAddr`. -/
def resolveAddr? (name : Name) : CompileM (Option Address) := do
  let env ← getCompileEnv
  let bstate ← getBlockState
  match bstate.blockNameToAddr.get? name with
  | some addr => pure (some addr)
  | none =>
  match env.nameToAddr.get? name with
  | some addr => pure (some addr)
  | none =>
    match bstate.auxNameToAddr.get? name with
    | some addr => pure (some addr)
    | none => pure (env.auxNameToAddr.get? name)

/-- Model of Rust `stt.env.lookup_name(name)`: the current block's aux
    registrations override (LAST entry wins, matching DashMap overwrite),
    then previously merged Named entries. Linear over `auxNamed` — the
    per-block aux registration list is small. -/
def lookupNamed? (name : Name) : CompileM (Option Ixon.Named) := do
  let bs ← getBlockState
  let mut found : Option Ixon.Named := none
  for (n, named) in bs.auxNamed do
    if n == name then
      found := some named
  match found with
  | some named => pure (some named)
  | none => pure ((← getCompileEnv).nameToNamed.get? name)

/-- Last string component of a name, if any. Mirrors Rust
    `Name::last_str` (consumed by `brecOnToMutConst` / `breconBatch`,
    mutual.rs:989/:1041). -/
def nameLastStr? : Name → Option String
  | .str _ s _ => some s
  | _ => none

/-! ## compileAuxBlock (mutual.rs:46-414) -/

/-- Body of `compile_aux_block_with_rename` (mutual.rs:111-413), run
    against already-cleared block caches (the wrapper handles the fresh
    `BlockCache` model). -/
private def compileAuxBlockCore (auxConsts : Array MutConst)
    (maps : AddrMaps) (nameRename : Option (Std.HashMap Name Name))
    (classOrderKey : Option (MutConst → UInt64)) : KBridgeM Unit := do
  -- Helper: canonical name → source name under the optional rename
  -- (mutual.rs:118-122).
  let resolveName : Name → Name := fun canon =>
    match nameRename with
    | some m => (m.get? canon).getD canon
    | none => canon

  -- Sort into equivalence classes (same algorithm as compile_mutual)
  -- (mutual.rs:125-126).
  let sortedClasses0 ← liftM (sortConsts auxConsts.toList : CompileM _)

  -- Optional class reorder (mutual.rs:134-138): sort classes by the
  -- minimum key over the class; Rust `sort_by_key` is stable, so ties
  -- keep the `sort_consts` relative order — modeled by the
  -- original-position tiebreak.
  let sortedClasses : List (List MutConst) :=
    match classOrderKey with
    | some keyFn =>
      let decorated := sortedClasses0.toArray.zipIdx.map fun (cls, i) =>
        (cls.foldl (fun acc c => min acc (keyFn c)) u64Max, i, cls)
      let sorted := decorated.qsort fun a b =>
        a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
      (sorted.map fun t => t.2.2).toList
    | none => sortedClasses0

  let mutCtx := MutConst.ctx sortedClasses

  -- Preseed exprs collected in INPUT order (mutual.rs:142-146); the
  -- tables are canonically re-sorted by `preseedExprTables`.
  let preseedExprs : Array (Expr × List Name) :=
    auxConsts.foldl (init := #[]) fun acc c => acc ++ mutConstPreseedExprs c

  -- Compile each representative per class (mutual.rs:149-187).
  -- `compileMutConsts` is the exact loop: per class, compile EVERY
  -- member (collecting metas, incl. ctor metas), push only the first
  -- representative's data/exprs. Runs under the block's mutCtx like
  -- Rust's explicit `&mut_ctx` threading.
  let (mutConsts, allExprs, allMetas, blockRefs, blockUnivs) ←
    liftM (withMutCtx mutCtx (do
      preseedExprTables preseedExprs
      let (dat, exprs, metas) ← compileMutConsts sortedClasses
      let st ← getBlockState
      pure (dat, exprs, metas, st.refs, st.univs)) : CompileM _)

  -- `all_metas` name → meta view (Rust FxHashMap; keys are unique).
  let metaMap : Std.HashMap Name Ixon.ConstantMeta :=
    allMetas.foldl (init := {}) fun m (n, cm) => m.insert n cm

  -- `name_str` (mutual.rs:192) feeds Rust's sharing debug stats only —
  -- not modeled.

  -- Singleton non-inductive aux blocks: standalone `Defn`/`Recr`
  -- Constant instead of `Muts([one])` (mutual.rs:199-247).
  if mutConsts.size == 1 && !(mutConsts[0]! matches .indc _) then
    let info : Ixon.ConstantInfo :=
      match mutConsts[0]! with
      | .defn d => .defn d
      | .recr r => .recr r
      | .indc _ => unreachable!
    -- `apply_sharing_to_{definition,recursor}_with_stats`
    -- (mutual.rs:208-218): `buildConstantWithSharing` dispatches on the
    -- info variant; `allExprs` holds exactly the single representative's
    -- root exprs ([typ, value] / [typ, rule rhss…]).
    let constant := buildConstantWithSharing info allExprs blockRefs blockUnivs
    let standaloneAddr := contentAddress constant
    liftM <| show CompileM Unit from do
      auxStoreConst standaloneAddr constant
      -- Register every class member at the standalone address
      -- (mutual.rs:222-233).
      for cnst in sortedClasses.head! do
        let canonN := cnst.name
        let n := resolveName canonN
        let cm := (metaMap.get? canonN).getD .empty
        auxRegisterName n { addr := standaloneAddr, constMeta := cm }
        auxInsertNameToAddr n standaloneAddr
        auxInsertExtraName n
        -- Rust pushes `n` onto `stt.aux_gen_pending` here
        -- (mutual.rs:232-235) — scheduler machinery, next milestone.
    -- Ingress all registered aux constants into the kernel environment
    -- (mutual.rs:238-245).
    for cnst in auxConsts do
      ensureInKenvOf cnst.name maps
    return ()

  -- Compile the mutual block (mutual.rs:249-256).
  let block := buildConstantWithSharing (.muts mutConsts) allExprs
    blockRefs blockUnivs
  let blockBytes := Ixon.ser block
  let blockAddr := Address.blake3 blockBytes
  liftM (auxStoreConst blockAddr block : CompileM _)

  -- Register projections for every member, even when the block
  -- alpha-collapses to a single non-inductive class (mutual.rs:258-343;
  -- see the Rust comment on structural uniformity for anon ingress).
  liftM <| show CompileM Unit from do
    for (cls, idxNat) in sortedClasses.zipIdx do
      let idx := UInt64.ofNat idxNat
      for cnst in cls do
        let canonN := cnst.name
        let n := resolveName canonN
        let cm := (metaMap.get? canonN).getD .empty
        match cnst with
        | .indc ind =>
          -- Inductive projection (mutual.rs:283-293).
          let indcProj : Ixon.Constant := ⟨.iPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩
          let projAddr := contentAddress indcProj
          auxStoreConst projAddr indcProj
          auxRegisterName n { addr := projAddr, constMeta := cm }
          auxInsertNameToAddr n projAddr
          auxInsertExtraName n
          -- Rust pushes `n` onto `stt.aux_gen_pending` (mutual.rs:293).
          -- Constructor projections: ctor names pass through the rename
          -- unchanged (mutual.rs:295-316).
          for (ctor, cidxNat) in ind.ctors.zipIdx do
            let ctorMeta := (metaMap.get? ctor.cnst.name).getD .empty
            let ctorProj : Ixon.Constant :=
              ⟨.cPrj ⟨idx, UInt64.ofNat cidxNat, blockAddr⟩, #[], #[], #[]⟩
            let ctorAddr := contentAddress ctorProj
            auxStoreConst ctorAddr ctorProj
            auxRegisterName ctor.cnst.name
              { addr := ctorAddr, constMeta := ctorMeta }
            auxInsertNameToAddr ctor.cnst.name ctorAddr
            auxInsertExtraName ctor.cnst.name
            -- Rust pushes the ctor name onto `stt.aux_gen_pending`
            -- (mutual.rs:315).
        | .recr _ =>
          -- Recursor projection (mutual.rs:318-328).
          let proj : Ixon.Constant := ⟨.rPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩
          let projAddr := contentAddress proj
          auxStoreConst projAddr proj
          auxRegisterName n { addr := projAddr, constMeta := cm }
          auxInsertNameToAddr n projAddr
          auxInsertExtraName n
          -- Rust pushes `n` onto `stt.aux_gen_pending` (mutual.rs:327).
        | .defn _ =>
          -- Definition projection (mutual.rs:329-339).
          let proj : Ixon.Constant := ⟨.dPrj ⟨idx, blockAddr⟩, #[], #[], #[]⟩
          let projAddr := contentAddress proj
          auxStoreConst projAddr proj
          auxRegisterName n { addr := projAddr, constMeta := cm }
          auxInsertNameToAddr n projAddr
          auxInsertExtraName n
          -- Rust pushes `n` onto `stt.aux_gen_pending` (mutual.rs:338).

  -- Register the synthetic Muts named entry (mutual.rs:345-396). Rust
  -- `.expect`s the first class/member (invariant: aux_consts nonempty).
  let firstNameCanonical := sortedClasses.head!.head!.name
  let firstName := resolveName firstNameCanonical
  -- `muts_all` uses SOURCE names (after rename): kernel ingress resolves
  -- each class's primary name hash against the Named entries registered
  -- above (mutual.rs:361-377).
  let mutsAll : Array (Array Address) := sortedClasses.toArray.map fun cls =>
    cls.toArray.map fun c => (resolveName c.name).getHash
  let mutsName := blockAddr.mutsName firstName
  liftM <| show CompileM Unit from do
    compileName mutsName
    -- aux_layout is NOT attached here: derivative blocks (rec, below,
    -- brecOn, …) inherit layout via the primary inductive's Muts meta
    -- (mutual.rs:380-386).
    auxRegisterName mutsName
      { addr := blockAddr
        constMeta := Ixon.ConstantMeta.new (.muts mutsAll none) }

  -- Rust batch-pushes `pending_names` onto `stt.aux_gen_pending` here
  -- (mutual.rs:398-401) — scheduler machinery, next milestone.

  -- Ingress all registered aux constants into the kernel environment
  -- (mutual.rs:403-411).
  for cnst in auxConsts do
    ensureInKenvOf cnst.name maps

/-- Like `compileAuxBlock`, but applies an optional canonical→source
    name-rename when registering named entries, and an optional
    `classOrderKey` reordering the `sortConsts` classes before block
    layout (stable, min-over-class, `u64::MAX` tail). Mirrors Rust
    `compile_aux_block_with_rename` (mutual.rs:103) — see the Rust doc
    for the rename/key rationale.

    Creates a fresh per-call block cache (Rust `BlockCache::default()`,
    mutual.rs:114): the cache-like `BlockState` fields are saved,
    cleared, and restored around the body; the stt-like fields
    accumulate. -/
def compileAuxBlockWithRename (auxConsts : Array MutConst)
    (maps : AddrMaps) (nameRename : Option (Std.HashMap Name Name))
    (classOrderKey : Option (MutConst → UInt64)) : KBridgeM Unit := do
  if auxConsts.isEmpty then
    return ()
  -- Fresh BlockCache: save + clear the cache fields.
  let saved ← liftM (getBlockState : CompileM _)
  liftM (modifyBlockState (fun c => { c with
    exprCache := {}, univCache := {}, cmpCache := {},
    refs := #[], refsIndex := {}, univs := #[], univsIndex := {},
    arena := {} }) : CompileM _)
  compileAuxBlockCore auxConsts maps nameRename classOrderKey
  -- Drop the local cache (restore the caller's cache fields; the aux
  -- registrations and blob/name/hint accumulators persist).
  liftM (modifyBlockState (fun c => { c with
    exprCache := saved.exprCache, univCache := saved.univCache,
    cmpCache := saved.cmpCache, refs := saved.refs,
    refsIndex := saved.refsIndex, univs := saved.univs,
    univsIndex := saved.univsIndex, arena := saved.arena }) : CompileM _)

/-- Compile a set of aux_gen-produced constants into an Ixon mutual
    block: the aux_gen analogue of `compile_mutual`. Compiled constants
    register into the block's `auxNameToAddr` (not the primary name map)
    so they don't interfere with scheduler dependency tracking. Mirrors
    Rust `compile_aux_block` (mutual.rs:60). -/
def compileAuxBlock (auxConsts : Array MutConst) (maps : AddrMaps)
    : KBridgeM Unit :=
  compileAuxBlockWithRename auxConsts maps none none

/-! ## Alias registration (mutual.rs:420) -/

/-- Register Lean-source aux names as aliases of already-compiled
    canonical aux_gen patches (one compiled constant per canonical class;
    every real Lean-exported aux name still resolves). Mirrors Rust
    `register_aux_aliases` (mutual.rs:420). -/
def registerAuxAliases (aliases : Std.HashMap Name Name) : CompileM Unit := do
  if aliases.isEmpty then
    return ()

  -- Deterministic order (mutual.rs:428-432).
  let entries := aliases.toList.toArray.qsort fun a b =>
    match compare a.1.pretty b.1.pretty with
    | .lt => true
    | .gt => false
    | .eq => compare a.2.pretty b.2.pretty == .lt

  for (source, target) in entries do
    if source == target then
      continue

    let some targetAddr ← resolveAddr? target
      | throw (.invalidMutualBlock
          s!"aux_gen alias target '{target.pretty}' for '{source.pretty}' \
has not been compiled")

    match ← resolveAddr? source with
    | some existingAddr =>
      -- Already-resolves consistency check (mutual.rs:450-463).
      if existingAddr != targetAddr then
        throw (.invalidMutualBlock
          s!"aux_gen alias '{source.pretty}' already resolves to \
{(toString existingAddr).take 12}, expected {(toString targetAddr).take 12} \
via '{target.pretty}'")
      -- Consistent — skip (Rust `continue`).
    | none =>
      -- Clone the target's Named, overriding the address
      -- (mutual.rs:465-471).
      let targetNamed := (← lookupNamed? target).getD { addr := targetAddr }
      let aliasNamed := { targetNamed with addr := targetAddr }
      compileName source
      auxRegisterName source aliasNamed
      auxInsertNameToAddr source targetAddr
      auxInsertExtraName source
      -- Rust pushes `source` onto `stt.aux_gen_pending`
      -- (mutual.rs:476-481) — scheduler machinery, next milestone.

/-! ## Helpers (mutual.rs:910-1046)

    (Defined before `generateAndCompileAuxRecursors` — their only
    caller — instead of at their Rust source positions after it; no
    semantic difference.) -/

/-- Map an `isUnsafe` flag to a `DefinitionSafety`. Mirrors Rust
    `def_safety` (mutual.rs:1031). -/
def defSafety (isUnsafe : Bool) : Ix.DefinitionSafety :=
  if isUnsafe then .unsaf else .safe

/-- Which batch a `.brecOn` definition belongs to: 0 `.go` (compiled
    first), 1 main, 2 `.eq` (references `.brecOn`). Mirrors Rust
    `brecon_batch` (mutual.rs:1040). -/
def breconBatch (name : Name) : UInt8 :=
  match nameLastStr? name with
  | some "go" => 0
  | some "eq" => 2
  | _ => 1

/-- Convert a `BelowIndc` (aux_gen output) to a `MutConst.indc`.
    `allBelowNames` lists all `.below` inductives in the mutual block
    (the `all` field lets `.below.rec` see the full mutual structure).
    Mirrors Rust `below_indc_to_mut_const` (mutual.rs:917), including
    the safety/reflexivity propagation from the parent. -/
def belowIndcToMutConst (bi : BelowIndc) (allBelowNames : Array Name)
    : MutConst :=
  let ctorVals : Array ConstructorVal := bi.ctors.zipIdx.map fun (c, ci) =>
    { cnst := { name := c.name, levelParams := bi.levelParams, type := c.typ }
      induct := bi.name
      cidx := ci
      numParams := c.nParams
      numFields := c.nFields
      -- A `.below` constructor inherits the parent inductive's safety.
      isUnsafe := bi.isUnsafe }
  .indc {
    name := bi.name
    levelParams := bi.levelParams
    type := bi.typ
    numParams := bi.nParams
    -- .below has original indices + 1 (the major premise), already in
    -- `bi.nIndices`.
    numIndices := bi.nIndices
    all := allBelowNames
    ctors := ctorVals
    numNested := 0
    isRec := true
    -- Safety and reflexivity mirror the parent's (mutual.rs:953-963).
    isReflexive := bi.isReflexive
    isUnsafe := bi.isUnsafe }

/-- Convert a `BRecOnDef` to a `MutConst.defn`, replicating Lean's
    per-kind decisions (`Lean/Meta/Constructions/BRecOn.lean` /
    `mkThmOrUnsafeDef`):

    | Shape                 | Kind    | Hints    |
    |-----------------------|---------|----------|
    | `.brecOn` (Prop)      | `.thm`* | default  |
    | `.brecOn` (Type)      | `.defn` | `.abbrev`|
    | `.brecOn.go`          | `.defn` | `.abbrev`|
    | `.brecOn.eq` (safe)   | `.thm`  | default  |
    | `.brecOn.eq` (unsafe) | `.defn` | `.opaque`|

    (* unsafe flips `.thm` to `.defn`.) Mirrors Rust
    `brecon_to_mut_const` (mutual.rs:988). Rust also computes an unused
    `is_go` (`let _ = is_go`) — the kind decision doesn't differentiate
    go from plain brecOn; not reproduced. -/
def brecOnToMutConst (d : BRecOnDef) : MutConst :=
  let isEq := nameLastStr? d.name == some "eq"

  -- Determine kind (mutual.rs:993-1003).
  let kind : Ix.DefKind :=
    if isEq then
      if d.isUnsafe then .defn else .thm
    else if d.isProp then
      -- Unsafe Prop inductives are effectively impossible, but honor the
      -- flag anyway.
      if d.isUnsafe then .defn else .thm
    else
      .defn

  -- Hints (mutual.rs:1009-1013): `.abbrev` for reducible aux
  -- definitions; `.opaque` for the unsafe-eq case; theorems use the
  -- opaque default.
  let hints : Lean.ReducibilityHints :=
    if (isEq && d.isUnsafe) || kind == .thm then .opaque else .abbrev

  .defn {
    name := d.name
    levelParams := d.levelParams
    type := d.typ
    kind
    value := d.value
    hints
    safety := defSafety d.isUnsafe
    all := #[] }

/-- Compile `.below.rec` recursors for Prop-level `.below` inductives:
    build an overlay env with the `.below` inductives + ctors (they don't
    exist in the original environment), generate canonical recursors for
    ALL `.below` inductives as ONE mutual block (one class each), and
    compile them. Mirrors Rust `compile_below_recursors`
    (mutual.rs:1053).

    (Defined before `generateAndCompileAuxRecursors` — its only caller —
    instead of at its Rust source position after it; no semantic
    difference.) -/
def compileBelowRecursors (belowIndcs : Array MutConst) (maps : AddrMaps)
    : KBridgeM Unit := do
  -- Overlay with just the .below inductives + ctors (mutual.rs:1063-1077).
  let mut overlay : Std.HashMap Name ConstantInfo := {}
  for c in belowIndcs do
    if let .indc ind := c then
      let indVal : InductiveVal :=
        { cnst := { name := ind.name, levelParams := ind.levelParams,
                    type := ind.type }
          numParams := ind.numParams
          numIndices := ind.numIndices
          all := ind.all
          ctors := ind.ctors.map (·.cnst.name)
          numNested := ind.numNested
          isRec := ind.isRec
          isUnsafe := ind.isUnsafe
          isReflexive := ind.isReflexive }
      overlay := overlay.insert ind.name (.inductInfo indVal)
      for ctor in ind.ctors do
        overlay := overlay.insert ctor.cnst.name (.ctorInfo ctor)

  -- One class per .below inductive (mutual.rs:1082-1088). Class ORDER
  -- is semantic: the joint generation bakes it into the motive layout
  -- and rule concatenation of every recursor in the block. `belowIndcs`
  -- arrives in canonical (sortConsts) order from the Phase-3 collection,
  -- which is what makes the emitted bytes alpha-canonical.
  let classes : Array (Array Name) := belowIndcs.filterMap fun c =>
    match c with
    | .indc ind => some #[ind.name]
    | _ => none

  if classes.isEmpty then
    return ()

  let (recs, _) ← generateCanonicalRecursorsWithOverlay classes
    (some overlay) none maps
  let mut belowRecs : Array MutConst := #[]
  for (_, rv) in recs do
    belowRecs := belowRecs.push (.recr rv)

  if !belowRecs.isEmpty then
    compileAuxBlock belowRecs maps

/-! ## generateAndCompileAuxRecursors (mutual.rs:511) -/

/-- Generate and compile auxiliary constants for an alpha-collapsed
    inductive block. Called from the compile_mutual mirror after
    projections are registered. Runs the full aux_gen pipeline:

    1. Generate patches (recursors, `.below`, `.brecOn`)
    2. Compile recursors (class-ordered against the inductive block's
       flat layout)
    3. Compile `.casesOn` / `.recOn` wrappers
    4. Compile `.below` inductives (Prop) or definitions (Type)
    5. Compile `.below.rec` (for Prop `.below` inductives)
    6. Compile `.brecOn` in batched order (`.go`, main, `.eq`)

    Only runs for inductive blocks; returns the `AuxLayout` (perm +
    source ctor counts) when the block has nested auxiliaries. Mirrors
    Rust `generate_and_compile_aux_recursors` (mutual.rs:511). Rust's
    `IX_TIMING` instrumentation is not ported. -/
def generateAndCompileAuxRecursors (cs : Array MutConst)
    (classNames : Array (Array Name)) (maps : AddrMaps)
    : KBridgeM (Option Ixon.AuxLayout) := do
  -- Guard: aux_gen canonical generation only runs for blocks containing
  -- inductives (mutual.rs:521-524).
  let isInductiveBlock := cs.any fun c => c matches .indc _
  if !isInductiveBlock then
    return none

  -- `block_label` (mutual.rs:527-531) feeds timing output only — not
  -- modeled.

  -- Lean's source-walk `all` list from the first inductive
  -- (mutual.rs:537-546).
  let sourceAll : Array Name :=
    (cs.findSome? fun c =>
      match c with
      | .indc ind => some ind.all
      | _ => none).getD #[]
  if sourceAll.isEmpty then
    return none

  -- Intersect the SCC classes with `.all` (mutual.rs:548-570): extra
  -- SCC inductives from ordinary dependency cycles must not become
  -- primary recursor motives for this source declaration.
  let sourceAllSet : Std.HashSet Name :=
    sourceAll.foldl (init := {}) fun s n => s.insert n
  let mut auxClassNames : Array (Array Name) := #[]
  for cls in classNames do
    let names := cls.filter (sourceAllSet.contains ·)
    if !names.isEmpty then
      auxClassNames := auxClassNames.push names
  if auxClassNames.isEmpty then
    return none

  -- Phase 1: Generate patches (mutual.rs:572-587). Errors propagate —
  -- they indicate an aux_gen bug, not a user error.
  let auxOut ← generateAuxPatches auxClassNames sourceAll maps
  let patches := auxOut.patches
  if patches.isEmpty then
    return none

  -- Record the nested-aux permutation + per-source ctor counts
  -- (mutual.rs:590-643). Fail closed on missing ctor metadata: silently
  -- dropping `perm` would make call-site surgery fall back to identity
  -- exactly for the cases that need the permutation.
  let originalAll : Array Name := sourceAll
  let mut auxLayout : Option Ixon.AuxLayout := none
  if !originalAll.isEmpty then
    if let some perm := auxOut.perm then
      if !perm.isEmpty then
        let srcOrder ← liftM (sourceAuxOrder originalAll : CompileM _)
        let mut sourceCtorCounts : Array Nat := #[]
        for (head, _) in srcOrder do
          match ← liftM (lookupConst? head : CompileM _) with
          | some (.inductInfo v) =>
            sourceCtorCounts := sourceCtorCounts.push v.ctors.size
          | _ =>
            throw (.missingConstant
              s!"{head.pretty} (compile_aux_block(aux_layout.source_ctor_counts))")
        if sourceCtorCounts.size != perm.size then
          throw (.invalidMutualBlock
            s!"aux layout mismatch: {sourceCtorCounts.size} source aux \
ctor counts for {perm.size} permutation entries")
        auxLayout := some {
          perm := perm.map UInt64.ofNat
          sourceCtorCounts := sourceCtorCounts.map UInt64.ofNat }

  -- Historically a canonical→source rename map was built here; aux_gen
  -- now emits source-indexed names directly, so the empty map makes
  -- `resolveName` the identity (mutual.rs:645-652).
  let auxNameRename : Std.HashMap Name Name := {}

  -- Phase 2: Compile canonical recursors (mutual.rs:654-723). The
  -- recursor block's storage order must align with the inductive block's
  -- flat layout ([originals in class order, aux in canonical order]) so
  -- the kernel's `populate_recursor_rules_from_block` can match
  -- positionally — hence the name → canonical-position class-order key.
  let recConsts : Array MutConst := Id.run do
    let mut out : Array MutConst := #[]
    for (_, p) in patches do
      if let .recr r := p then
        out := out.push (.recr r)
    return out
  if !recConsts.isEmpty then
    let mut nameToPos : Std.HashMap Name UInt64 := {}
    let nOriginalsInBlock := auxClassNames.size
    for (cls, pos) in auxClassNames.zipIdx do
      for memberName in cls do
        let recName := Name.mkStr memberName "rec"
        nameToPos := nameToPos.insert recName (UInt64.ofNat pos)
    -- Nested ifs: Rust `if let Some(perm) = … && !perm.is_empty()`.
    if let some perm := auxOut.perm then
      if !perm.isEmpty then
        let nCanon := auxOut.nCanonicalAux
        -- `source_of_canonical[canon_i]` = min source_j mapping to that
        -- canonical aux (usize::MAX = PERM_OUT_OF_SCC seed).
        let mut sourceOfCanonical : Array Nat :=
          Array.replicate nCanon PERM_OUT_OF_SCC
        for (canonI, srcJ) in perm.zipIdx do
          if canonI < nCanon
              && sourceOfCanonical[canonI]! == PERM_OUT_OF_SCC then
            sourceOfCanonical := sourceOfCanonical.set! canonI srcJ
        for (sourceJ, canonicalI) in sourceOfCanonical.zipIdx do
          if sourceJ != PERM_OUT_OF_SCC then
            let auxRecName :=
              Name.mkStr originalAll[0]! s!"rec_{sourceJ + 1}"
            nameToPos := nameToPos.insert auxRecName
              (UInt64.ofNat (nOriginalsInBlock + canonicalI))
    let keyMap := nameToPos
    let classOrderKey : MutConst → UInt64 := fun c =>
      (keyMap.get? c.name).getD u64Max
    compileAuxBlockWithRename recConsts maps (some auxNameRename)
      (some classOrderKey)

  -- Register every alias whose target was compiled by the recursor
  -- phase; the rest register after their phases (mutual.rs:724-734).
  let mut availableRecAliases : Std.HashMap Name Name := {}
  for (source, target) in auxOut.aliases do
    if (← liftM (resolveAddr? target : CompileM _)).isSome then
      availableRecAliases := availableRecAliases.insert source target
  liftM (registerAuxAliases availableRecAliases : CompileM _)

  -- Phase 2b: Compile .casesOn definitions (mutual.rs:736-759) — after
  -- .rec, before .brecOn (`.brecOn.eq` references casesOn).
  let casesOnDefs : Array MutConst := Id.run do
    let mut out : Array MutConst := #[]
    for (_, p) in patches do
      if let .casesOnDef d := p then
        out := out.push (.defn {
          name := d.name
          levelParams := d.levelParams
          type := d.typ
          kind := .defn
          value := d.value
          hints := .abbrev
          safety := defSafety d.isUnsafe
          all := #[] })
    return out
  if !casesOnDefs.isEmpty then
    compileAuxBlock casesOnDefs maps

  -- Phase 2c: Compile .recOn definitions (arg-reordered .rec wrapper),
  -- after .rec (mutual.rs:761-783).
  let recOnDefs : Array MutConst := Id.run do
    let mut out : Array MutConst := #[]
    for (_, p) in patches do
      if let .recOnDef d := p then
        out := out.push (.defn {
          name := d.name
          levelParams := d.levelParams
          type := d.typ
          kind := .defn
          value := d.value
          hints := .abbrev
          safety := defSafety d.isUnsafe
          all := #[] })
    return out
  if !recOnDefs.isEmpty then
    compileAuxBlock recOnDefs maps

  -- Phase 3: Compile .below inductives (Prop-level); all .below names
  -- first for the mutual `all` field (mutual.rs:784-816).
  --
  -- CANONICAL ORDER (mirrors the mutual.rs Phase-3 collection): the
  -- collection is sorted by the below inductives' own sortConsts
  -- partition-refinement order — their canonical member order in the
  -- Phase-3 block (≡ ascending anon projection index). Iterating
  -- `patches` directly would leak Std.HashMap iteration order into
  -- (1) the JOINT `.below.rec` generation in Phase 5, which bakes class
  -- order (motive order + rule concatenation) into the recursor bytes,
  -- and (2) the `all` field, which flows verbatim into per-name
  -- metadata — a canonicity violation (alpha-identical families would
  -- compile to name-dependent bytes; see the ZFA clone fixtures).
  -- sortConsts only reads anon content and `all` is metadata, so
  -- sorting preliminary MutConsts built with the unsorted name list is
  -- sound; the final MutConsts are rebuilt in canonical order.
  let belowRaw : Array BelowIndc := Id.run do
    let mut out : Array BelowIndc := #[]
    for (_, p) in patches do
      if let .belowIndc bi := p then
        out := out.push bi
    return out
  let belowRaw ←
    if belowRaw.size ≤ 1 then pure belowRaw else do
      let prelimNames := belowRaw.map (·.name)
      let prelim := belowRaw.map (belowIndcToMutConst · prelimNames)
      -- Fresh-cache sort, mirroring Rust's `BlockCache::default()`
      -- (same save/clear/restore as compileAuxBlockWithRename).
      let saved ← liftM (getBlockState : CompileM _)
      liftM (modifyBlockState (fun c => { c with
        exprCache := {}, univCache := {}, cmpCache := {},
        refs := #[], refsIndex := {}, univs := #[], univsIndex := {},
        arena := {} }) : CompileM _)
      let sorted ← liftM (sortConsts prelim.toList : CompileM _)
      liftM (modifyBlockState (fun c => { c with
        exprCache := saved.exprCache, univCache := saved.univCache,
        cmpCache := saved.cmpCache, refs := saved.refs,
        refsIndex := saved.refsIndex, univs := saved.univs,
        univsIndex := saved.univsIndex, arena := saved.arena }) : CompileM _)
      let canonical : Array Name :=
        sorted.toArray.flatMap fun cls => (cls.map (·.name)).toArray
      pure <| belowRaw.qsort fun a b =>
        ((canonical.findIdx? (· == a.name)).getD canonical.size)
          < ((canonical.findIdx? (· == b.name)).getD canonical.size)
  let allBelowNames : Array Name := belowRaw.map (·.name)
  let belowIndcs : Array MutConst :=
    belowRaw.map (belowIndcToMutConst · allBelowNames)
  if !belowIndcs.isEmpty then
    compileAuxBlockWithRename belowIndcs maps (some auxNameRename) none
    -- Note: constructor names are already correctly set by
    -- rename_below_indc during alias patching;
    -- register_below_ctor_aliases was removed because it created
    -- spurious cross-aliases (mutual.rs:812-815).

  -- Phase 4: Compile .below definitions (Type-level)
  -- (mutual.rs:818-844).
  let belowDefs : Array MutConst := Id.run do
    let mut out : Array MutConst := #[]
    for (_, p) in patches do
      if let .belowDef d := p then
        out := out.push (.defn {
          name := d.name
          levelParams := d.levelParams
          type := d.typ
          kind := .defn
          value := d.value
          hints := .abbrev
          safety := defSafety d.isUnsafe
          all := #[] })
    return out
  if !belowDefs.isEmpty then
    compileAuxBlockWithRename belowDefs maps (some auxNameRename) none

  -- Phase 5: Compile .below.rec for Prop-level .below inductives
  -- (mutual.rs:847-852).
  if !belowIndcs.isEmpty then
    compileBelowRecursors belowIndcs maps

  -- Phase 6: Compile .brecOn in 3 batches: .go, main, .eq
  -- (mutual.rs:854-877).
  for batch in #[(0 : UInt8), 1, 2] do
    let defs : Array MutConst := Id.run do
      let mut out : Array MutConst := #[]
      for (_, p) in patches do
        if let .brecOnDef d := p then
          if breconBatch d.name == batch then
            out := out.push (brecOnToMutConst d)
      return out
    if !defs.isEmpty then
      compileAuxBlockWithRename defs maps (some auxNameRename) none

  liftM (registerAuxAliases auxOut.aliases : CompileM _)

  -- Note: `.noConfusion`, `.noConfusionType`, `.ctorIdx`, `.ctor.inj*`,
  -- `._sizeOf_*`, etc. are NOT regenerated: their bodies only invoke
  -- `.casesOn` (never `.rec`), whose public binder arity is invariant
  -- under alpha collapse — the original Lean values compile to correct
  -- Ixon as-is (mutual.rs:881-889).

  -- Rust's IX_TIMING report (mutual.rs:891-906) is not ported.
  return auxLayout

/-- The aux tail of `compile_mutual` (compile.rs:3986-4144): register the
    primary block's synthetic `Muts` named entry, run the aux pipeline,
    re-register the entry with the returned `AuxLayout`, and compute
    call-site surgery plans. Returns `(auxLayout, plans, brecOnPlans,
    belowPlans)` — the driver stores them (next milestone); the plans gate
    dumps them. Lives here rather than in `Ix.CompileM.compileMutualBlock`
    because CompileM cannot import AuxGen (dependency direction). -/
def compileMutualAuxTail (cs : Array MutConst)
    (sortedClasses : List (List MutConst)) (blockAddr : Address)
    (maps : AddrMaps)
    : KBridgeM (Option Ixon.AuxLayout
        × Std.HashMap Name CallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan
        × Std.HashMap Name BRecOnCallSitePlan) := do
  -- Primary `Muts` named entry (compile.rs:3986-4013); registered on the
  -- aux path only — the no-aux promotion pass reuses these entries.
  let firstName := sortedClasses.head!.head!.name
  let mutsAll : Array (Array Address) := sortedClasses.toArray.map fun cls =>
    cls.toArray.map fun c => c.name.getHash
  let mutsName := blockAddr.mutsName firstName
  liftM <| show CompileM Unit from do
    Ix.CompileM.compileName mutsName
    auxRegisterName mutsName
      { addr := blockAddr
        constMeta := Ixon.ConstantMeta.new (.muts mutsAll none) }

  -- Regenerate + compile auxiliaries (compile.rs:4018-4029).
  let classNames : Array (Array Name) :=
    sortedClasses.toArray.map fun cls => cls.toArray.map (·.name)
  let auxLayout ← generateAndCompileAuxRecursors cs classNames maps

  -- Original inductive `all` + the plan class filtering (compile.rs:4031-4056).
  let originalAll : Array Name := Id.run do
    for c in cs do
      if let .indc ind := c then
        return ind.all
    return #[]
  let planClassNames : Array (Array Name) :=
    if originalAll.isEmpty then #[]
    else Id.run do
      let lookup : Std.HashSet Name :=
        originalAll.foldl (init := {}) (·.insert ·)
      let mut out : Array (Array Name) := #[]
      for cls in classNames do
        let names := cls.filter lookup.contains
        if !names.isEmpty then
          out := out.push names
      return out

  -- Patch the Muts entry with the layout (compile.rs:4058-4094; the
  -- re-registration overrides — `auxNamed` keeps later entries last).
  if let some layout := auxLayout then
    liftM <| show CompileM Unit from
      auxRegisterName mutsName
        { addr := blockAddr
          constMeta := Ixon.ConstantMeta.new (.muts mutsAll (some layout)) }

  -- Change detection (compile.rs:4096-4108).
  let userLayoutChanged : Bool := !originalAll.isEmpty
    && (planClassNames.size < originalAll.size
      || (planClassNames.size == originalAll.size
        && (planClassNames.zip originalAll).any
            (fun (cls, orig) => cls[0]! != orig)))
  let auxLayoutChanged : Bool := match auxLayout with
    | some layout =>
      layout.perm.zipIdx.any fun (canonicalI, sourceJ) =>
        canonicalI.toNat != PERM_OUT_OF_SCC && canonicalI.toNat != sourceJ
    | none => false

  let mut plans : Std.HashMap Name CallSitePlan := {}
  let mut brecPlans : Std.HashMap Name BRecOnCallSitePlan := {}
  let mut belowPlans : Std.HashMap Name BRecOnCallSitePlan := {}
  if userLayoutChanged || auxLayoutChanged then
    plans ← liftM
      (computeCallSitePlans planClassNames originalAll auxLayout : CompileM _)
    -- Head-rewritten (evaporated-aux) recursors get NO derived
    -- brecOn/below plans (compile.rs:4117-4140).
    for (name, plan) in plans do
      if plan.headRewrite.isNone then
        if let some breconName := recNameToBreconName name then
          if (← liftM (lookupConst? breconName : CompileM _)).isSome then
            brecPlans := brecPlans.insert breconName
              (BRecOnCallSitePlan.fromRecPlan plan)
        if let some belowName := recNameToBelowName name then
          if (← liftM (lookupConst? belowName : CompileM _)).isSome then
            belowPlans := belowPlans.insert belowName
              (BRecOnCallSitePlan.fromRecPlan plan)

  return (auxLayout, plans, brecPlans, belowPlans)

end Ix.AuxGen
