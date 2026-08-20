/-
  Ix.AuxGen.Nested: nested-inductive expansion and the canonical aux order.

  Port of `crates/compile/src/compile/aux_gen/nested.rs` (the compiler-side
  canonicity core). An inductive with nested occurrences (`Array (Part α)`)
  is expanded into a flat mutual block whose auxiliary members
  (`<all0>._nested.Array_1 …`) share the block's params/levels — mirroring
  the C++ kernel's `elim_nested_inductive`. The aux tail is then sorted
  STRUCTURALLY (each aux carrying a synthetic trailing `_nested_id`
  identity-marker ctor, ordered by the ordinary content-addressed
  `sortConsts`) so the canonical layout is independent of Lean's
  source-walk discovery order; `computeAuxPerm` maps Lean's source
  numbering (`X.rec_N`) onto the canonical positions.

  The auxiliaries are EPHEMERAL: they exist only during recursor
  generation and are restored to nested applications before emission —
  only regenerated recursors/below/brecOn persist, plus the
  `AuxLayout {perm, sourceCtorCounts}` metadata.

  The kernel re-derives this order via blake3 `AUX_INDC_VIEW` /
  `AUX_MARKER_VIEW` seed addresses (`Ix/Tc/Inductive.lean:canonicalAuxOrder`,
  `crates/kernel/src/inductive.rs:canonical_aux_order`) — those seed
  strings are the CONSUMER's reconstruction and must not appear here: the
  compile side orders purely by marker ctor + `sortConsts`.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Mutual
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError findConst getBlockState modifyBlockState)

/-! ## Expanded block (expand/restore model) -/

/-- A constructor in the expanded block.
    Mirrors Rust `ExpandedCtor` (nested.rs:105). -/
structure ExpandedCtor where
  /-- Constructor name: for auxiliaries, prefixed with the aux name. -/
  name : Name
  /-- Constructor type with nested refs replaced by aux const applications.
      Shape: `∀ (block_params…) (fields…) → Member block_params indices`. -/
  typ : Expr
  /-- Number of fields (constructor arguments past params). -/
  nFields : Nat
  deriving Repr, Nonempty, Inhabited

/-- A member of the expanded block (original or auxiliary). All members
    share the same `levelParams` and `nParams` — auxiliaries take the
    block's parameters, not the external inductive's own.
    Mirrors Rust `ExpandedMember` (nested.rs:86). -/
structure ExpandedMember where
  /-- Original name for originals, `<all0>._nested.<Ext>_N` for auxes. -/
  name : Name
  /-- Original source member whose constructor walk first discovered this
      member (auxes inherit it through the discovery queue). -/
  sourceOwner : Name
  /-- Inductive type: `∀ (block_params…) (indices…) → Sort s`. -/
  typ : Expr
  /-- Constructors with types already rewritten (nested refs → aux consts). -/
  ctors : Array ExpandedCtor
  /-- Number of block parameters (same for all members). -/
  nParams : Nat
  /-- Number of indices (from the external inductive's metadata). -/
  nIndices : Nat
  deriving Repr, Nonempty, Inhabited

/-- An expanded mutual block: originals first, then auxiliaries.
    Mirrors Rust `ExpandedBlock` (nested.rs:55). -/
structure ExpandedBlock where
  types : Array ExpandedMember
  /-- `auxName → nested expr` (the original nested application with block
      param FVars free) — the aux's semantic identity, used by restore. -/
  auxToNested : Std.HashMap Name Expr
  /-- `auxCtorName → (originalCtorName, auxInductiveName)`. -/
  auxCtorMap : Std.HashMap Name (Name × Name)
  /-- Block parameters as FVars (shared across all members). -/
  blockParamFvars : Array Expr
  /-- Number of original (non-auxiliary) types. -/
  nOriginals : Nat
  /-- Block-level universe parameters (from the first original inductive). -/
  levelParams : Array Name
  deriving Inhabited

/-- Sentinel: "this source aux position has no canonical match in the
    current SCC block" — its spec_params reference inductives from another
    SCC, handled by that block's compilation. Numeric value is Rust's
    `usize::MAX` (nested.rs:1033); it also lands in the serialized
    `AuxLayout.perm`, so the value itself is wire-relevant. -/
def PERM_OUT_OF_SCC : Nat := 18446744073709551615

/-! ## Name and FVar rewriting helpers (nested.rs-local) -/

/-- Strip `oldPrefix` from the front of `name`, returning the suffix
    components root-first, or `none` when `name` doesn't extend it.
    Support for `nameReplacePrefix` (Rust `Name::strip_prefix`). -/
partial def stripPrefixComponents (name oldPrefix : Name)
    : Option (List (String ⊕ Nat)) :=
  if name == oldPrefix then some []
  else
    match name with
    | .str parent s _ =>
      (stripPrefixComponents parent oldPrefix).map (· ++ [.inl s])
    | .num parent i _ =>
      (stripPrefixComponents parent oldPrefix).map (· ++ [.inr i])
    | .anonymous _ => none

/-- Replace `oldPrefix` in a Name with `newPrefix`
    (`A.B.mk`, `A.B` → `X.Y` gives `X.Y.mk`); names not extending
    `oldPrefix` pass through unchanged.
    Mirrors Rust `name_replace_prefix` (nested.rs:1458). -/
def nameReplacePrefix (name oldPrefix newPrefix : Name) : Name :=
  match stripPrefixComponents name oldPrefix with
  | some suffix =>
    suffix.foldl (init := newPrefix) fun acc c =>
      match c with
      | .inl s => Name.mkStr acc s
      | .inr i => Name.mkNat acc i
  | none => name

/-- Substitute FVars by name. Mirrors Rust `replace_fvars` (nested.rs:1493). -/
partial def replaceFVarsMap (e : Expr) (fvarMap : Std.HashMap Name Expr) : Expr :=
  match e with
  | .fvar n _ => (fvarMap.get? n).getD e
  | .app f a _ =>
    Expr.mkApp (replaceFVarsMap f fvarMap) (replaceFVarsMap a fvarMap)
  | .lam n t b bi _ =>
    Expr.mkLam n (replaceFVarsMap t fvarMap) (replaceFVarsMap b fvarMap) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (replaceFVarsMap t fvarMap) (replaceFVarsMap b fvarMap) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (replaceFVarsMap t fvarMap) (replaceFVarsMap v fvarMap)
      (replaceFVarsMap b fvarMap) nd
  | .proj n i s _ => Expr.mkProj n i (replaceFVarsMap s fvarMap)
  | .mdata md inner _ => Expr.mkMData md (replaceFVarsMap inner fvarMap)
  | _ => e

/-- Convert an expression from constructor-local param FVars (`asFvars`)
    to block param FVars. Matches C++ `replace_params`: abstract over
    `As`, instantiate with block params.
    Mirrors Rust `replace_params_expr` (nested.rs:1474). -/
def replaceParamsExpr (e : Expr) (asFvars blockParamFvars : Array Expr) : Expr :=
  if asFvars.isEmpty then e
  else Id.run do
    let mut fvarMap : Std.HashMap Name Expr := {}
    for (localFv, blockFv) in asFvars.zip blockParamFvars do
      if let .fvar n _ := localFv then
        fvarMap := fvarMap.insert n blockFv
    return replaceFVarsMap e fvarMap

/-- Rewrite Const names via `nameMap`, cached. UNLIKE
    `replaceConstNamesCached`, `Proj` type names are deliberately NOT
    rewritten — Rust's `canonicalize_const_names` (nested.rs:1401) keeps
    them, and the two walkers must not be conflated. -/
partial def canonicalizeConstNames (e : Expr)
    (nameMap : Std.HashMap Name Name) : StateM ExprCache Expr := do
  if let some cached := (← get).get? e then
    return cached
  let result ← match e with
    | .const name levels _ =>
      match nameMap.get? name with
      | some newName => pure (Expr.mkConst newName levels)
      | none => pure e
    | .app f a _ =>
      pure (Expr.mkApp (← canonicalizeConstNames f nameMap)
        (← canonicalizeConstNames a nameMap))
    | .lam n t b bi _ =>
      pure (Expr.mkLam n (← canonicalizeConstNames t nameMap)
        (← canonicalizeConstNames b nameMap) bi)
    | .forallE n t b bi _ =>
      pure (Expr.mkForallE n (← canonicalizeConstNames t nameMap)
        (← canonicalizeConstNames b nameMap) bi)
    | .letE n t v b nd _ =>
      pure (Expr.mkLetE n (← canonicalizeConstNames t nameMap)
        (← canonicalizeConstNames v nameMap)
        (← canonicalizeConstNames b nameMap) nd)
    | .proj n i s _ =>
      pure (Expr.mkProj n i (← canonicalizeConstNames s nameMap))
    | .mdata md inner _ =>
      pure (Expr.mkMData md (← canonicalizeConstNames inner nameMap))
    | _ => pure e
  modify (·.insert e result)
  return result

/-- Rewrite the final result of an auxiliary constructor from
    `J spec_params indices` to `aux_name block_params indices`.
    Mirrors Rust `replace_ctor_result_head_with_aux` (nested.rs:1542). -/
partial def replaceCtorResultHeadWithAux (e : Expr) (originalInd auxName : Name)
    (originalNParams : Nat) (blockLevels : Array Level)
    (blockParamFvars : Array Expr) : Expr :=
  match e with
  | .forallE n t b bi _ =>
    Expr.mkForallE n t
      (replaceCtorResultHeadWithAux b originalInd auxName originalNParams
        blockLevels blockParamFvars) bi
  | .mdata md inner _ =>
    Expr.mkMData md
      (replaceCtorResultHeadWithAux inner originalInd auxName originalNParams
        blockLevels blockParamFvars)
  | _ => Id.run do
    let (head, args) := decomposeApps e
    let .const headName _ _ := head | return e
    if headName != originalInd || args.size < originalNParams then
      return e
    let mut result := Expr.mkConst auxName blockLevels
    for param in blockParamFvars do
      result := Expr.mkApp result param
    for idxArg in args.toList.drop originalNParams do
      result := Expr.mkApp result idxArg
    return result

/-- Check whether an expression contains any invalid reference for a
    spec_param: a free BVar (domain-local) or an FVar outside the block
    param set (field-local). Mirrors Rust `has_invalid_spec_ref`
    (nested.rs:1659). -/
def hasInvalidSpecRef (expr : Expr) (paramFvarNames : Array Name) : Bool := Id.run do
  let mut stack : Array (Expr × Nat) := #[(expr, 0)]
  while !stack.isEmpty do
    let (e, depth) := stack.back!
    stack := stack.pop
    match e with
    | .bvar idx _ =>
      if idx ≥ depth then return true
    | .fvar n _ =>
      if !paramFvarNames.contains n then return true
    | .app f a _ =>
      stack := stack.push (f, depth) |>.push (a, depth)
    | .lam _ t b _ _ | .forallE _ t b _ _ =>
      stack := stack.push (t, depth) |>.push (b, depth + 1)
    | .letE _ t v b _ _ =>
      stack := stack.push (t, depth) |>.push (v, depth) |>.push (b, depth + 1)
    | .proj _ _ s _ => stack := stack.push (s, depth)
    | .mdata _ inner _ => stack := stack.push (inner, depth)
    | _ => pure ()
  return false

/-- Memoized "mentions any of these inductive names" check. NOTE: unlike
    `exprMentionsAnyName`, `Proj` TYPE names are NOT consulted — only the
    projected value is walked (Rust `has_ind_occ`, nested.rs:2227). -/
partial def hasIndOcc (e : Expr) (names : Std.HashSet Name)
    : StateM (Std.HashMap Expr Bool) Bool := do
  if let some cached := (← get).get? e then
    return cached
  let result ← match e with
    | .const name _ _ => pure (names.contains name)
    | .app f a _ => do
      -- Rust `||` short-circuits; mirror with early-exit style.
      if (← hasIndOcc f names) then pure true else hasIndOcc a names
    | .lam _ t b _ _ | .forallE _ t b _ _ => do
      if (← hasIndOcc t names) then pure true else hasIndOcc b names
    | .letE _ t v b _ _ => do
      if (← hasIndOcc t names) then pure true
      else if (← hasIndOcc v names) then pure true
      else hasIndOcc b names
    | .proj _ _ s _ => hasIndOcc s names
    | .mdata _ inner _ => hasIndOcc inner names
    | _ => pure false
  modify (·.insert e result)
  return result

/-- Memoized "contains a Const that is an original mutual member NOT in
    the current SCC" check. Mirrors Rust `has_out_of_scc_const`
    (nested.rs:1352). -/
partial def hasOutOfSccConst (e : Expr) (inSccNames : Std.HashMap Name Name)
    (originalNames : Std.HashSet Name)
    : StateM (Std.HashMap Expr Bool) Bool := do
  if let some cached := (← get).get? e then
    return cached
  let result ← match e with
    | .const name _ _ =>
      pure (originalNames.contains name && !inSccNames.contains name)
    | .app f a _ => do
      if (← hasOutOfSccConst f inSccNames originalNames) then pure true
      else hasOutOfSccConst a inSccNames originalNames
    | .lam _ t b _ _ | .forallE _ t b _ _ => do
      if (← hasOutOfSccConst t inSccNames originalNames) then pure true
      else hasOutOfSccConst b inSccNames originalNames
    | .letE _ t v b _ _ => do
      if (← hasOutOfSccConst t inSccNames originalNames) then pure true
      else if (← hasOutOfSccConst v inSccNames originalNames) then pure true
      else hasOutOfSccConst b inSccNames originalNames
    | .proj _ _ s _ => hasOutOfSccConst s inSccNames originalNames
    | .mdata _ inner _ => hasOutOfSccConst inner inSccNames originalNames
    | _ => pure false
  modify (·.insert e result)
  return result

/-! ## Level alpha-equivalence (congruence.rs port, nested-scope) -/

/-- Normalize a level bottom-up via the smart max/imax constructors.
    Idempotent; `succ` left raw. Mirrors Rust `normalize_level`
    (congruence.rs:47). -/
partial def normalizeLevel (l : Level) : Level :=
  match l with
  | .zero _ | .param _ _ | .mvar _ _ => l
  | .succ inner _ => Level.mkSucc (normalizeLevel inner)
  | .max x y _ => levelMaxSmart (normalizeLevel x) (normalizeLevel y)
  | .imax x y _ => levelImaxSmart (normalizeLevel x) (normalizeLevel y)

/-- Strict structural equivalence on already-normalized levels; params
    compare positionally-lenient (both sides share the block's param
    order, so accept any param-param pair). Mirrors Rust
    `level_alpha_eq_struct` (congruence.rs:66); the `Result` error channel
    collapses to `Bool` — nested.rs consults only `is_ok()`. -/
partial def levelAlphaEqStruct (a b : Level) : Bool :=
  match a, b with
  | .zero _, .zero _ => true
  | .succ a1 _, .succ b1 _ => levelAlphaEqStruct a1 b1
  | .max a1 a2 _, .max b1 b2 _ =>
    levelAlphaEqStruct a1 b1 && levelAlphaEqStruct a2 b2
  | .imax a1 a2 _, .imax b1 b2 _ =>
    levelAlphaEqStruct a1 b1 && levelAlphaEqStruct a2 b2
  | .param _ _, .param _ _ => true
  | _, _ => false

/-- Alpha-equivalence of levels after smart-constructor normalization.
    Mirrors Rust `level_alpha_eq` (congruence.rs:41). -/
def levelAlphaEq (a b : Level) : Bool :=
  levelAlphaEqStruct (normalizeLevel a) (normalizeLevel b)

/-- Strip `mdata` wrappers. Mirrors Rust `congruence::strip_mdata`
    (congruence.rs:337). -/
partial def stripMdata (e : Expr) : Expr :=
  match e with
  | .mdata _ inner _ => stripMdata inner
  | _ => e

/-- Semantic equality for nested-aux spec parameters: constants equal by
    name OR by resolved compiled address; fvars matched through the
    source→canonical block-param map; levels via `levelAlphaEq`; mdata
    ignored. Mirrors Rust `aux_spec_eq` (nested.rs:1259).

    `strictNames` overrides the address fallback: constants in this set
    compare by NAME only. Callers put the original mutual members that
    are out of the matching SCC here — those act as external constants
    inside specs, but address-equating them would let an alpha-twin
    member of a DIFFERENT SCC match this SCC's canonical specs, making
    two SCCs claim one source position
    (plans/aux-recursor-alias-collision.md §2/§13.4). Genuine external
    types (never mutual members) keep the address fallback: their
    alpha-twins legitimately dedup many-to-one. -/
partial def auxSpecEq (canon src : Expr)
    (resolveAddr : Name → Option Address)
    (sourceToCanonFvar : Std.HashMap Name Name)
    (strictNames : Std.HashSet Name)
    : StateM (Std.HashMap (Expr × Expr) Bool) Bool := do
  let canon := stripMdata canon
  let src := stripMdata src
  let key := (canon, src)
  if let some cached := (← get).get? key then
    return cached
  let result ← do
    match canon, src with
    | .bvar a _, .bvar b _ => pure (a == b)
    | .fvar a _, .fvar b _ =>
      pure (match sourceToCanonFvar.get? b with
        | some expected => a == expected
        | none => a == b)
    | .sort a _, .sort b _ => pure (levelAlphaEq a b)
    | .const aName aLvls _, .const bName bLvls _ =>
      if aLvls.size != bLvls.size
          || (aLvls.zip bLvls).any (fun (x, y) => !levelAlphaEq x y) then
        pure false
      else if aName == bName then
        pure true
      else if strictNames.contains aName || strictNames.contains bName then
        pure false
      else
        pure (match resolveAddr aName, resolveAddr bName with
          | some aAddr, some bAddr => aAddr == bAddr
          | _, _ => false)
    | .app aF aArg _, .app bF bArg _ => do
      if !(← auxSpecEq aF bF resolveAddr sourceToCanonFvar strictNames) then
        pure false
      else auxSpecEq aArg bArg resolveAddr sourceToCanonFvar strictNames
    | .lam _ aT aB _ _, .lam _ bT bB _ _ => do
      if !(← auxSpecEq aT bT resolveAddr sourceToCanonFvar strictNames) then
        pure false
      else auxSpecEq aB bB resolveAddr sourceToCanonFvar strictNames
    | .forallE _ aT aB _ _, .forallE _ bT bB _ _ => do
      if !(← auxSpecEq aT bT resolveAddr sourceToCanonFvar strictNames) then
        pure false
      else auxSpecEq aB bB resolveAddr sourceToCanonFvar strictNames
    | .letE _ aT aV aB _ _, .letE _ bT bV bB _ _ => do
      if !(← auxSpecEq aT bT resolveAddr sourceToCanonFvar strictNames) then
        pure false
      else if !(← auxSpecEq aV bV resolveAddr sourceToCanonFvar strictNames) then
        pure false
      else auxSpecEq aB bB resolveAddr sourceToCanonFvar strictNames
    | .proj aName aIdx aVal _, .proj bName bIdx bVal _ => do
      let namesOk := aName == bName
        || (!strictNames.contains aName
          && !strictNames.contains bName
          && (match resolveAddr aName, resolveAddr bName with
            | some aAddr, some bAddr => aAddr == bAddr
            | _, _ => false))
      if aIdx != bIdx || !namesOk then pure false
      else auxSpecEq aVal bVal resolveAddr sourceToCanonFvar strictNames
    | .lit a _, .lit b _ => pure (a == b)
    | _, _ => pure false
  modify (·.insert key result)
  return result

/-- Collect every `Const` reference to an original mutual-block member
    inside `expr` into the returned set. DAG-memoized via the visited
    set (same rationale as `hasOutOfSccConst`). Mirrors Rust
    `collect_member_refs` (nested.rs). -/
partial def collectMemberRefs (expr : Expr)
    (originalNames : Std.HashSet Name)
    : StateM (Std.HashSet Expr × Std.HashSet Name) Unit := do
  if (← get).1.contains expr then
    return ()
  modify fun (seen, out) => (seen.insert expr, out)
  match expr with
  | .const name _ _ =>
    if originalNames.contains name then
      modify fun (seen, out) => (seen, out.insert name)
  | .app f a _ => do
    collectMemberRefs f originalNames
    collectMemberRefs a originalNames
  | .lam _ t b _ _ | .forallE _ t b _ _ => do
    collectMemberRefs t originalNames
    collectMemberRefs b originalNames
  | .letE _ t v b _ _ => do
    collectMemberRefs t originalNames
    collectMemberRefs v originalNames
    collectMemberRefs b originalNames
  | .proj name _ val _ => do
    if originalNames.contains name then
      modify fun (seen, out) => (seen, out.insert name)
    collectMemberRefs val originalNames
  | .mdata _ inner _ => collectMemberRefs inner originalNames
  | _ => return ()

/-! ## Expand: create auxiliary types for nested occurrences -/

/-- Mutable state for the nested expansion walk.
    Mirrors Rust `ExpandCtx` (nested.rs:120); `walkCache` is the per-ctor
    memo Rust threads separately (reset per constructor — rewrites depend
    on `asFvars`/`sourceOwner`, so entries don't transfer between ctors). -/
structure ExpandSt where
  types : Array ExpandedMember := #[]
  /-- Incremental mirror of `types[*].name` for O(1) membership. -/
  typeNameSet : Std.HashSet Name := {}
  auxToNested : Std.HashMap Name Expr := {}
  auxCtorMap : Std.HashMap Name (Name × Name) := {}
  /-- Dedup: nested-app (`IAs`) → aux name (hash-keyed Expr map mirrors
      Rust's `FxHashMap<Hash, Name>`). -/
  auxSeen : Std.HashMap Expr Name := {}
  nextAuxIdx : Nat := 1
  all0 : Name := default
  blockLevels : Array Level := #[]
  blockParamFvars : Array Expr := #[]
  blockParamDecls : Array LocalDecl := #[]
  blockParamFvarNames : Array Name := #[]
  nParams : Nat := 0
  walkCache : ExprCache := {}
  deriving Inhabited

abbrev ExpandM := StateT ExpandSt CompileM

/-- Push a member keeping `typeNameSet` in sync (Rust `push_type`,
    nested.rs:148). All pushes must go through here. -/
def ExpandM.pushType (member : ExpandedMember) : ExpandM Unit :=
  modify fun st => { st with
    typeNameSet := st.typeNameSet.insert member.name
    types := st.types.push member }

/-- Non-throwing constant lookup (Rust `lean_env.get`; sees the
    streaming fallback). -/
def lookupConst? (name : Name) : CompileM (Option ConstantInfo) := do
  pure ((← Ix.CompileM.getCompileEnv).env.get? name)

/-- Check if `e` is a nested inductive application; if so, create auxiliary
    types for the external inductive's whole mutual group and return the
    replacement expression. Mirrors Rust `ExpandCtx::replace_if_nested`
    (nested.rs:229), itself the C++ `replace_if_nested`
    (inductive.cpp:963-1027). -/
def replaceIfNested (e : Expr) (asFvars : Array Expr) (sourceOwner : Name)
    : ExpandM (Option Expr) := do
  let (head, args) := decomposeApps e
  let .const headName headLevels _ := head | return none

  -- Head in the block = direct recursion, not nested.
  if (← get).typeNameSet.contains headName then
    return none

  -- Head must be an external inductive.
  let some (.inductInfo extInd) ← lookupConst? headName | return none
  let extNParams := extInd.numParams
  if args.size < extNParams then
    return none

  -- Some parameter arg must mention a block member.
  let st ← get
  if !(args.toList.take extNParams).any
      (fun a => exprMentionsAnyName a st.typeNameSet) then
    return none

  -- Extract spec_params normalized to block-param FVars.
  let specParams : Array Expr :=
    (args.toList.take extNParams).toArray.map
      (fun sp => replaceParamsExpr sp asFvars st.blockParamFvars)
  for sp in specParams do
    if hasInvalidSpecRef sp st.blockParamFvarNames then
      return none

  -- `IAs = I.{lvls} spec_params` in block-param space.
  let iAs := mkAppN (Expr.mkConst headName headLevels) specParams

  -- Dedup by nested-app identity.
  if let some auxName := st.auxSeen.get? iAs then
    let mut result := Expr.mkConst auxName st.blockLevels
    for af in asFvars do
      result := Expr.mkApp result af
    for idxArg in args.toList.drop extNParams do
      result := Expr.mkApp result idxArg
    return some result

  -- New occurrence — create auxiliaries for the whole external group.
  let extAll := extInd.all
  let mut result : Option Expr := none

  for jName in extAll do
    let some (.inductInfo jInfo) ← lookupConst? jName | continue

    -- `<all0>._nested.<Ext>_N`
    let auxIdx := (← get).nextAuxIdx
    let auxName := Name.mkStr (Name.mkStr (← get).all0 "_nested")
      s!"{jName.pretty.replace "." "_"}_{auxIdx}"
    modify fun s => { s with nextAuxIdx := s.nextAuxIdx + 1 }

    -- aux → `J.{I_lvls} spec_params` (semantic identity).
    let jAs := mkAppN (Expr.mkConst jName headLevels) specParams
    modify fun s => { s with auxToNested := s.auxToNested.insert auxName jAs }
    -- Only the FIRST group member (the head) registers under this
    -- occurrence hash; the rest are reached via the queue walk.
    modify fun s =>
      if s.auxSeen.contains iAs then s
      else { s with auxSeen := s.auxSeen.insert iAs auxName }

    -- Aux type: substLevels → instantiatePiParams → block-param space →
    -- re-abstract block params.
    let jTypeInst := substLevels jInfo.cnst.type jInfo.cnst.levelParams headLevels
    let jTypePeeled := instantiatePiParams jTypeInst extNParams specParams
    let jTypeBlock := replaceParamsExpr jTypePeeled asFvars (← get).blockParamFvars
    let auxType := mkForall jTypeBlock (← get).blockParamDecls

    -- Aux constructors.
    let mut auxCtors : Array ExpandedCtor := #[]
    for jCtorName in jInfo.ctors do
      let some (.ctorInfo jCtor) ← lookupConst? jCtorName | continue
      let auxCtorName := nameReplacePrefix jCtorName jName auxName
      let ctorTypeInst :=
        substLevels jCtor.cnst.type jInfo.cnst.levelParams headLevels
      let ctorTypePeeled := instantiatePiParams ctorTypeInst extNParams specParams
      let ctorTypeBlock :=
        replaceParamsExpr ctorTypePeeled asFvars (← get).blockParamFvars
      let ctorTypeBlock := replaceCtorResultHeadWithAux ctorTypeBlock jName
        auxName extNParams (← get).blockLevels (← get).blockParamFvars
      let auxCtorType := mkForall ctorTypeBlock (← get).blockParamDecls
      modify fun s => { s with
        auxCtorMap := s.auxCtorMap.insert auxCtorName (jCtorName, auxName) }
      auxCtors := auxCtors.push
        { name := auxCtorName, typ := auxCtorType, nFields := jCtor.numFields }

    -- The head inductive supplies the replacement expression.
    if jName == headName then
      let mut r := Expr.mkConst auxName (← get).blockLevels
      for af in asFvars do
        r := Expr.mkApp r af
      for idxArg in args.toList.drop extNParams do
        r := Expr.mkApp r idxArg
      result := some r

    ExpandM.pushType
      { name := auxName
        sourceOwner
        typ := auxType
        nParams := (← get).nParams
        nIndices := jInfo.numIndices
        ctors := auxCtors }

  return result

/-- Recursively replace all nested occurrences (top-down, memoized per
    constructor via `walkCache`). Mirrors Rust
    `ExpandCtx::replace_all_nested` (nested.rs:168) / C++
    `replace_all_nested` (inductive.cpp:1031). -/
partial def replaceAllNested (e : Expr) (asFvars : Array Expr)
    (sourceOwner : Name) : ExpandM Expr := do
  if let some cached := (← get).walkCache.get? e then
    return cached

  -- Top-level replacement first.
  if let some replaced ← replaceIfNested e asFvars sourceOwner then
    modify fun s => { s with walkCache := s.walkCache.insert e replaced }
    return replaced

  -- No match — recurse into sub-expressions.
  let result ← match e with
    | .app f a _ =>
      pure (Expr.mkApp (← replaceAllNested f asFvars sourceOwner)
        (← replaceAllNested a asFvars sourceOwner))
    | .lam n t b bi _ =>
      pure (Expr.mkLam n (← replaceAllNested t asFvars sourceOwner)
        (← replaceAllNested b asFvars sourceOwner) bi)
    | .forallE n t b bi _ =>
      pure (Expr.mkForallE n (← replaceAllNested t asFvars sourceOwner)
        (← replaceAllNested b asFvars sourceOwner) bi)
    | .letE n t v b nd _ =>
      pure (Expr.mkLetE n (← replaceAllNested t asFvars sourceOwner)
        (← replaceAllNested v asFvars sourceOwner)
        (← replaceAllNested b asFvars sourceOwner) nd)
    | .proj n i s _ =>
      pure (Expr.mkProj n i (← replaceAllNested s asFvars sourceOwner))
    | .mdata md inner _ =>
      pure (Expr.mkMData md (← replaceAllNested inner asFvars sourceOwner))
    | _ => pure e
  modify fun s => { s with walkCache := s.walkCache.insert e result }
  return result

/-- Build an expanded mutual block: replace nested inductive occurrences
    with auxiliary types sharing the block's params and levels.
    Mirrors Rust `expand_nested_block` (nested.rs:428) / C++
    `elim_nested_inductive_fn::operator()` (inductive.cpp:1045-1077). -/
def expandNestedBlock (orderedOriginals : Array Name)
    (aliasToRep : Std.HashMap Name Name) : CompileM ExpandedBlock := do
  let some firstName := orderedOriginals[0]?
    | throw (.invalidMutualBlock "expand_nested_block: empty ordered_originals")
  let some (.inductInfo firstInd) ← lookupConst? firstName
    | throw (.missingConstant
        s!"{firstName} (expand_nested_block: first original not an inductive)")

  let nParams := firstInd.numParams
  let levelParams := firstInd.cnst.levelParams
  let blockLevels : Array Level := levelParams.map Level.mkParam

  let (blockParamFvars, blockParamDecls, _) :=
    forallTelescope firstInd.cnst.type nParams "bp" 0
  let blockParamFvarNames : Array Name := blockParamDecls.map (·.fvarName)

  let all0 := firstInd.all[0]?.getD firstName

  let init : ExpandSt := {
    all0, blockLevels
    blockParamFvars, blockParamDecls, blockParamFvarNames
    nParams
  }

  let build : ExpandM ExpandedBlock := do
    -- Seed with the original inductives.
    for name in orderedOriginals do
      let some (.inductInfo ind) ← lookupConst? name
        | throw (.missingConstant
            s!"{name} (expand_nested_block: original not an inductive)")
      let mut ctors : Array ExpandedCtor := #[]
      for cn in ind.ctors do
        if let some (.ctorInfo c) ← lookupConst? cn then
          ctors := ctors.push
            { name := c.cnst.name, typ := c.cnst.type, nFields := c.numFields }
      ExpandM.pushType
        { name
          sourceOwner := name
          typ := ind.cnst.type
          nParams
          nIndices := ind.numIndices
          ctors }

    let nOriginals := (← get).types.size

    -- Canonicalize alias references to representatives (prevents false
    -- nested detection of aliases the block only holds via reps). One
    -- shared cache across the whole block (same `aliasToRep` everywhere).
    if !aliasToRep.isEmpty then
      let mut aliasCache : ExprCache := {}
      let types := (← get).types
      let mut newTypes : Array ExpandedMember := #[]
      for mem in types do
        let mut ctors : Array ExpandedCtor := #[]
        for ctor in mem.ctors do
          let (typ', cache') :=
            (canonicalizeConstNames ctor.typ aliasToRep).run aliasCache
          aliasCache := cache'
          ctors := ctors.push { ctor with typ := typ' }
        let (memTyp', cache') :=
          (canonicalizeConstNames mem.typ aliasToRep).run aliasCache
        aliasCache := cache'
        newTypes := newTypes.push { mem with typ := memTyp', ctors }
      modify fun s => { s with types := newTypes }

    -- Queue-based scan over every member's constructors. Fresh walk
    -- cache per constructor (rewrites depend on asFvars/sourceOwner).
    let mut qi := 0
    while qi < (← get).types.size do
      let nCtors := ((← get).types[qi]!).ctors.size
      let sourceOwner := ((← get).types[qi]!).sourceOwner
      for ci in [0:nCtors] do
        let ctorType := (((← get).types[qi]!).ctors[ci]!).typ
        let (asFvars, asDecls, peeled) :=
          forallTelescope ctorType nParams "cp" (qi * 100 + ci)
        modify fun s => { s with walkCache := {} }
        let replaced ← replaceAllNested peeled asFvars sourceOwner
        let newCtorType := mkForall replaced asDecls
        modify fun s => { s with
          types := s.types.modify qi fun mem =>
            { mem with ctors := mem.ctors.modify ci fun c =>
                { c with typ := newCtorType } } }
      qi := qi + 1

    let st ← get
    return {
      types := st.types
      auxToNested := st.auxToNested
      auxCtorMap := st.auxCtorMap
      blockParamFvars
      nOriginals
      levelParams
    }

  Prod.fst <$> build.run init

/-! ## Canonical structural sort of the aux section -/

/-- Reorder the aux tail of an `ExpandedBlock` structurally so the
    canonical order is independent of Lean's source-walk discovery order,
    returning the updated block and `perm[oldJ] = canonicalJ`.

    Each aux member gets a synthetic trailing `_nested_id` identity-marker
    ctor whose type is its `auxToNested` entry with block-param FVars
    abstracted to loose BVars by position — two occurrences of the same
    external inductive can be alpha-identical when the distinguishing spec
    param is phantom; the marker orders them by spec-param content. The
    aux tail is then sorted by the ordinary `sortConsts` (fresh comparison
    cache, mirroring Rust's fresh `BlockCache`), and the renaming
    (`<all0>._nested.<Ext>_<newJ+1>`) cascades through `auxCtorMap`,
    `auxToNested`, and every member/ctor type.
    Mirrors Rust `sort_aux_by_partition_refinement` (nested.rs:616).
    (Rust's `IX_RECURSOR_DUMP` debug block is not ported.) -/
def sortAuxByPartitionRefinement (expanded : ExpandedBlock)
    : CompileM (ExpandedBlock × Array Nat) := do
  let nOriginals := expanded.nOriginals
  let nTotal := expanded.types.size
  if nTotal ≤ nOriginals then
    return (expanded, #[])
  let nAux := nTotal - nOriginals

  let levelParams := expanded.levelParams
  let blockParamBvars : Array Expr :=
    (Array.range expanded.blockParamFvars.size).map Expr.mkBVar

  -- Synthetic MutConst::Indc views for all members; aux members carry the
  -- trailing identity marker (nested.rs:656-725).
  let mut allMutConsts : Array MutConst := #[]
  for _h : mi in [0:expanded.types.size] do
    let mem := expanded.types[mi]!
    let mut ctorNames : Array Name := mem.ctors.map (·.name)
    let mut ctors : Array ConstructorVal := #[]
    for _h2 : ci in [0:mem.ctors.size] do
      let c := mem.ctors[ci]!
      ctors := ctors.push {
        cnst := { name := c.name, levelParams, type := c.typ }
        induct := mem.name
        cidx := ci
        numParams := mem.nParams
        numFields := c.nFields
        isUnsafe := false
      }
    if mi ≥ nOriginals then
      if let some nested := expanded.auxToNested.get? mem.name then
        let markerTyp :=
          replaceParamsExpr nested expanded.blockParamFvars blockParamBvars
        let markerName := Name.mkStr mem.name "_nested_id"
        ctors := ctors.push {
          cnst := { name := markerName, levelParams, type := markerTyp }
          induct := mem.name
          cidx := ctors.size
          numParams := mem.nParams
          numFields := 0
          isUnsafe := false
        }
        ctorNames := ctorNames.push markerName
    allMutConsts := allMutConsts.push (.indc {
      name := mem.name
      levelParams
      type := mem.typ
      numParams := mem.nParams
      numIndices := mem.nIndices
      all := #[]
      ctors
      numNested := 0
      isRec := false
      isReflexive := false
      isUnsafe := false
    })

  let auxConsts := allMutConsts.toList.drop nOriginals

  -- Fresh comparison cache (Rust: `BlockCache::default()`), restored after.
  let savedCmp := (← getBlockState).cmpCache
  modifyBlockState fun c => { c with cmpCache := {} }
  let sortedClasses ← Ix.CompileM.sortConsts auxConsts
  modifyBlockState fun c => { c with cmpCache := savedCmp }

  let nCanon := sortedClasses.length

  -- Build oldJ → canonicalJ; equivalence classes map many-to-one.
  let auxTailNames : Array Name :=
    (expanded.types.toList.drop nOriginals).toArray.map (·.name)
  let mut perm : Array Nat := Array.replicate nAux PERM_OUT_OF_SCC
  let mut sortedOrder : Array Nat := #[]
  for (cls, canonicalJ) in sortedClasses.zipIdx do
    for (member, memberJ) in cls.zipIdx do
      let some oldJ := auxTailNames.findIdx? (· == member.name)
        | throw (.invalidMutualBlock
            s!"aux sort returned unknown member {member.name.pretty}")
      perm := perm.set! oldJ canonicalJ
      if memberJ == 0 then
        sortedOrder := sortedOrder.push oldJ
  if perm.contains PERM_OUT_OF_SCC then
    throw (.invalidMutualBlock
      "aux sort did not assign every auxiliary member")

  -- Already canonical?
  if nCanon == nAux && (perm.zipIdx.all fun (p, i) => p == i) then
    return (expanded, perm)

  -- `<all0>._nested` prefix from the first aux name.
  let firstAuxName := (expanded.types[nOriginals]!).name
  let nestedPrefix ← match firstAuxName with
    | .str prefix_ _ _ => pure prefix_
    | _ => throw (.invalidMutualBlock
        s!"nested aux name is not a string name: {firstAuxName.pretty}")

  -- New canonical names `<all0>._nested.<Ext>_<newJ+1>` (Ext recovered by
  -- stripping the trailing `_<N>` from the OLD suffix).
  let mut newAuxNames : Array Name := #[]
  for newJ in [0:nCanon] do
    let oldJ := sortedOrder[newJ]!
    let oldName := (expanded.types[nOriginals + oldJ]!).name
    let ext ← match oldName with
      | .str _ suffix _ =>
        let parts := suffix.splitOn "_"
        pure (if parts.length > 1 then
          String.intercalate "_" parts.dropLast
        else suffix)
      | _ => throw (.invalidMutualBlock
          s!"nested aux name is not a string name: {oldName.pretty}")
    newAuxNames := newAuxNames.push
      (Name.mkStr nestedPrefix s!"{ext}_{newJ + 1}")

  let mut nameRename : Std.HashMap Name Name := {}
  for (canonicalJ, oldJ) in perm.zipIdx.map (fun (p, i) => (p, i)) do
    let oldName := (expanded.types[nOriginals + oldJ]!).name
    nameRename := nameRename.insert oldName newAuxNames[canonicalJ]!

  -- Cascade 1: auxCtorMap (keys are prefix-renamed; first insert wins).
  let mut newAuxCtorMap : Std.HashMap Name (Name × Name) := {}
  for (oldCtorName, origCtorName, oldAuxInd) in expanded.auxCtorMap do
    let newAuxInd := (nameRename.get? oldAuxInd).getD oldAuxInd
    let newCtorName := nameReplacePrefix oldCtorName oldAuxInd newAuxInd
    if !newAuxCtorMap.contains newCtorName then
      newAuxCtorMap := newAuxCtorMap.insert newCtorName (origCtorName, newAuxInd)

  -- Cascade 2: auxToNested keys (values are name-independent).
  let mut newAuxToNested : Std.HashMap Name Expr := {}
  for (oldName, nestedExpr) in expanded.auxToNested do
    let newName := (nameRename.get? oldName).getD oldName
    if !newAuxToNested.contains newName then
      newAuxToNested := newAuxToNested.insert newName nestedExpr

  -- Cascade 3: every member/ctor type (sibling auxes reference each other
  -- via Const nodes); shared rewrite cache. NOTE: this deliberately uses
  -- `replaceConstNamesCached` (proj type names renamed too), matching the
  -- Rust call to `expr_utils::replace_const_names_cached` — NOT
  -- `canonicalizeConstNames`.
  let mut renameCache : ExprCache := {}
  let mut renamedTypes : Array ExpandedMember := #[]
  for mem in expanded.types do
    let (memTyp, cache1) :=
      (replaceConstNamesCached mem.typ nameRename).run renameCache
    renameCache := cache1
    let mut ctors : Array ExpandedCtor := #[]
    for ctor in mem.ctors do
      let (ctorTyp, cache2) :=
        (replaceConstNamesCached ctor.typ nameRename).run renameCache
      renameCache := cache2
      ctors := ctors.push { ctor with typ := ctorTyp }
    renamedTypes := renamedTypes.push { mem with typ := memTyp, ctors }

  -- Reorder the aux tail into canonical positions and apply own-name +
  -- ctor-prefix renames.
  let auxTail : Array ExpandedMember :=
    (renamedTypes.toList.drop nOriginals).toArray
  let mut reordered : Array ExpandedMember := #[]
  for newJ in [0:nCanon] do
    let oldJ := sortedOrder[newJ]!
    let mem := auxTail[oldJ]!
    let oldName := mem.name
    let newName := newAuxNames[newJ]!
    let ctors := mem.ctors.map fun ctor =>
      { ctor with name := nameReplacePrefix ctor.name oldName newName }
    reordered := reordered.push { mem with name := newName, ctors }
  let finalTypes :=
    (renamedTypes.toList.take nOriginals).toArray ++ reordered

  return ({ expanded with
    types := finalTypes
    auxToNested := newAuxToNested
    auxCtorMap := newAuxCtorMap }, perm)

/-! ## Source-walk order and the source→canonical permutation -/

/-- Per-aux `(sourceOwner, extHead, headLevels, specParams)` in discovery
    order. Mirrors Rust `source_aux_order_from_expanded` (nested.rs:1006). -/
def sourceAuxOrderFromExpanded (expanded : ExpandedBlock)
    : Array (Name × Name × Array Level × Array Expr) := Id.run do
  let mut out : Array (Name × Name × Array Level × Array Expr) := #[]
  for mem in expanded.types.toList.drop expanded.nOriginals do
    let some nestedExpr := expanded.auxToNested.get? mem.name | continue
    let (head, args) := decomposeApps nestedExpr
    let .const headName headLevels _ := head | continue
    out := out.push (mem.sourceOwner, headName, headLevels, args)
  return out

/-- Source-walk discovery order with owners: a fresh expansion of the
    SOURCE-order originals (no alias rewriting, no canonical sort) —
    structurally mirrors Lean's `inductive.cpp:1045` walk, so the order
    matches Lean's `X.rec_N` numbering. Mirrors Rust
    `source_aux_order_with_owner` (nested.rs:997). -/
def sourceAuxOrderWithOwner (originalAll : Array Name)
    : CompileM (Array (Name × Name × Array Expr)) := do
  let expanded ← expandNestedBlock originalAll {}
  return sourceAuxOrderFromExpanded expanded |>.map
    fun (o, h, _, s) => (o, h, s)

/-- `sourceAuxOrderWithOwner` without the owner column
    (Rust `source_aux_order`, nested.rs:983). -/
def sourceAuxOrder (originalAll : Array Name)
    : CompileM (Array (Name × Array Expr)) := do
  return (← sourceAuxOrderWithOwner originalAll).map fun (_, h, s) => (h, s)

/-- Extract `(headName, headLevels, specParams)` for each auxiliary
    member of an expanded block (positions `[nOriginals..]`), in the
    block's aux order. Mirrors Rust `aux_signatures_of_expanded`. -/
def auxSignaturesOfExpanded (expanded : ExpandedBlock)
    : Array (Name × Array Level × Array Expr) := Id.run do
  let mut out : Array (Name × Array Level × Array Expr) := #[]
  for mem in expanded.types.toList.drop expanded.nOriginals do
    let some nestedExpr := expanded.auxToNested.get? mem.name | continue
    let (head, args) := decomposeApps nestedExpr
    let .const headName headLevels _ := head | continue
    out := out.push (headName, headLevels, args)
  return out

/-- Head-name buckets over aux signatures (matching becomes
    ≈O(nSource) instead of O(nSource × nCanon)). Mirrors Rust
    `signatures_by_head`. -/
def signaturesByHead (signatures : Array (Name × Array Level × Array Expr))
    : Std.HashMap Name (Array Nat) := Id.run do
  let mut byHead : Std.HashMap Name (Array Nat) := {}
  for ((head, _, _), i) in signatures.zipIdx do
    byHead := byHead.insert head ((byHead.get? head).getD #[] |>.push i)
  return byHead

/-- Match one source-walk aux signature against a canonical signature
    set: pass A requires the head's universe instantiation to match
    exactly; pass B falls back level-insensitively (alpha-collapse can
    rename the block's universe parameters). Threads the spec-equality
    cache explicitly. Mirrors Rust `match_aux_signature`. -/
def matchAuxSignature (srcHead : Name) (srcLevels : Array Level)
    (normalized : Array Expr)
    (signatures : Array (Name × Array Level × Array Expr))
    (byHead : Std.HashMap Name (Array Nat))
    (resolveAddr : Name → Option Address)
    (sourceToCanonFvar : Std.HashMap Name Name)
    (strictNames : Std.HashSet Name)
    (specEqCache : Std.HashMap (Expr × Expr) Bool)
    : Option Nat × Std.HashMap (Expr × Expr) Bool := Id.run do
  let candidates := (byHead.get? srcHead).getD #[]
  let mut cache := specEqCache
  -- Pass A: exact universe instantiation + spec equality.
  for i in candidates do
    let (_, canonLevels, canonSpecs) := signatures[i]!
    if canonLevels == srcLevels && canonSpecs.size == normalized.size then
      let mut allEq := true
      for (canonSp, srcSp) in canonSpecs.zip normalized do
        if allEq then
          let (eq, cache') := (auxSpecEq canonSp srcSp resolveAddr
            sourceToCanonFvar strictNames).run cache
          cache := cache'
          if !eq then allEq := false
      if allEq then return (some i, cache)
  -- Pass B: level-insensitive fallback.
  for i in candidates do
    let (_, _, canonSpecs) := signatures[i]!
    if canonSpecs.size == normalized.size then
      let mut allEq := true
      for (canonSp, srcSp) in canonSpecs.zip normalized do
        if allEq then
          let (eq, cache') := (auxSpecEq canonSp srcSp resolveAddr
            sourceToCanonFvar strictNames).run cache
          cache := cache'
          if !eq then allEq := false
      if allEq then return (some i, cache)
  return (none, cache)

/-- Per-spec-SCC signature context memoized by
    `positionClaimedBySpecScc` across the out-of-SCC positions of one
    block. Mirrors Rust `SccClaimCtx`. -/
structure SccClaimCtx where
  signatures : Array (Name × Array Level × Array Expr)
  byHead : Std.HashMap Name (Array Nat)
  origToCanon : Std.HashMap Name Name
  strictNames : Std.HashSet Name
  /-- Source (full-block) param FVars → the spec SCC's expansion param
      FVars, zipped positionally (a split mutual's members share one
      uniform param telescope, so positions correspond). -/
  fvarMap : Std.HashMap Name Name
  specEqCache : Std.HashMap (Expr × Expr) Bool := {}
  normalizeCache : ExprCache := {}
  deriving Inhabited

/-- Build the claim context for one spec-member SCC from its recorded
    class ordering. Mirrors Rust `build_scc_claim_ctx` (incl. the
    `aux_class_names`-style intersection with `originalAll` — a
    scheduler SCC can contain extra members through ordinary dependency
    cycles). -/
def buildSccClaimCtx (memberClasses : Array (Array Name))
    (sourceExpanded : ExpandedBlock) (originalAll : Array Name)
    : CompileM SccClaimCtx := do
  let originalLookup : Std.HashSet Name :=
    originalAll.foldl (init := {}) (·.insert ·)
  let mut filtered : Array (Array Name) := #[]
  for cls in memberClasses do
    let names := cls.filter originalLookup.contains
    if !names.isEmpty then
      filtered := filtered.push names
  let reps : Array Name := filtered.map (·[0]!)
  let mut aliasToRep : Std.HashMap Name Name := {}
  for cls in filtered do
    for aliasName in cls.toList.drop 1 do
      aliasToRep := aliasToRep.insert aliasName cls[0]!
  let expanded ← expandNestedBlock reps aliasToRep
  let signatures := auxSignaturesOfExpanded expanded
  let byHead := signaturesByHead signatures
  let mut origToCanon : Std.HashMap Name Name := {}
  for cls in filtered do
    for n in cls do
      origToCanon := origToCanon.insert n cls[0]!
  let mut strictNames : Std.HashSet Name := {}
  for n in originalAll do
    if !origToCanon.contains n then
      strictNames := strictNames.insert n
  let mut fvarMap : Std.HashMap Name Name := {}
  for (src, canon) in
      sourceExpanded.blockParamFvars.zip expanded.blockParamFvars do
    if let (.fvar srcName _, .fvar canonName _) := (src, canon) then
      fvarMap := fvarMap.insert srcName canonName
  return { signatures, byHead, origToCanon, strictNames, fvarMap }

/-- The global half of the evaporation decision: does the SCC owning an
    out-of-SCC position's spec members canonically discover the same
    aux? If yes, the `all0.{rec,below,brecOn}_N` name family for that
    position belongs to THAT SCC's canonical block (registered as its
    patches/aliases when it compiled — always before this block, since
    the discovering constructor's reference forces the scheduler edge),
    and the owner's SCC must register neither an evaporation alias nor a
    head-rewrite plan for it. Only when NO SCC discovers the position
    may it evaporate to the external head's generic recursor
    (plans/aux-recursor-alias-collision.md §2). Mirrors Rust
    `position_claimed_by_spec_scc`; the per-SCC context cache (keyed by
    the SCC's recorded representative) threads through the return. -/
def positionClaimedBySpecScc (sourceExpanded : ExpandedBlock)
    (srcHead : Name) (srcLevels : Array Level) (srcSpecs : Array Expr)
    (originalAll : Array Name)
    (resolveAddr : Name → Option Address)
    (sccCtxCache : Std.HashMap Name SccClaimCtx)
    : CompileM (Bool × Std.HashMap Name SccClaimCtx) := do
  let originalNames : Std.HashSet Name :=
    originalAll.foldl (init := {}) (·.insert ·)
  let mut seen : Std.HashSet Expr := {}
  let mut memberRefs : Std.HashSet Name := {}
  for sp in srcSpecs do
    let ((), (seen', out')) :=
      (collectMemberRefs sp originalNames).run (seen, memberRefs)
    seen := seen'
    memberRefs := out'
  if memberRefs.isEmpty then
    return (false, sccCtxCache)

  -- Dedup candidate SCCs by their recorded class representative;
  -- deterministic probe order for deterministic error attribution.
  let cenv ← Ix.CompileM.getCompileEnv
  let mut sccCtxCache := sccCtxCache
  let mut candidateReps : Array Name := #[]
  for member in memberRefs do
    let some classes := cenv.blocks.get? member
      | throw (.invalidMutualBlock
          s!"evaporation disposition: spec member '{member.pretty}' has \
no compiled block — scheduler ordering should have compiled it before \
its dependents")
    let some rep := classes[0]?.bind (·[0]?)
      | continue
    if !candidateReps.contains rep then
      candidateReps := candidateReps.push rep
      if !sccCtxCache.contains rep then
        let ctx ← buildSccClaimCtx classes sourceExpanded originalAll
        sccCtxCache := sccCtxCache.insert rep ctx
  candidateReps := candidateReps.qsort (·.pretty < ·.pretty)

  let mut claimant : Option Name := none
  for rep in candidateReps do
    let some ctx := sccCtxCache.get? rep
      | throw (.invalidMutualBlock
          "evaporation disposition: claim context missing after insert")
    let mut normalizeCache := ctx.normalizeCache
    let mut normalized : Array Expr := #[]
    for sp in srcSpecs do
      let (sp', cache') :=
        (replaceConstNamesCached sp ctx.origToCanon).run normalizeCache
      normalizeCache := cache'
      normalized := normalized.push sp'
    let (matched, specEqCache) := matchAuxSignature srcHead srcLevels
      normalized ctx.signatures ctx.byHead resolveAddr ctx.fvarMap
      ctx.strictNames ctx.specEqCache
    sccCtxCache := sccCtxCache.insert rep
      { ctx with normalizeCache, specEqCache }
    if matched.isSome then
      if let some prev := claimant then
        -- Two SCCs discovering one occurrence requires a mutual
        -- dependency cycle between them, which contradicts them being
        -- distinct SCCs — a modeling gap if it ever fires.
        throw (.invalidMutualBlock
          s!"evaporation disposition: position (head={srcHead.pretty}) \
canonically claimed by two SCCs: '{prev.pretty}' and '{rep.pretty}'")
      claimant := some rep
  return (claimant.isSome, sccCtxCache)

/-- Compute `perm[sourceJ] = canonicalI` mapping Lean's source aux-walk
    positions onto canonical aux positions (`PERM_OUT_OF_SCC` for source
    auxes whose spec_params reference out-of-SCC inductives; many-to-one
    under alpha-collapse). Mirrors Rust `compute_aux_perm`
    (nested.rs:1067). `resolveAddr` mirrors `stt.resolve_addr`
    (name→addr with aux fallback). -/
def computeAuxPerm (expanded : ExpandedBlock) (originalAll : Array Name)
    (origToCanonNames : Std.HashMap Name Name)
    (resolveAddr : Name → Option Address) : CompileM (Array Nat) := do
  let nOriginals := expanded.nOriginals
  let canonicalAux := (expanded.types.toList.drop nOriginals).toArray
  let nCanon := canonicalAux.size

  let sourceExpanded ← expandNestedBlock originalAll {}
  let sourceOrder := sourceAuxOrderFromExpanded sourceExpanded
  let nSource := sourceOrder.size

  -- Source→canonical block-param FVar correspondence.
  let mut sourceToCanonFvar : Std.HashMap Name Name := {}
  for (src, canon) in sourceExpanded.blockParamFvars.zip expanded.blockParamFvars do
    if let (.fvar srcName _, .fvar canonName _) := (src, canon) then
      sourceToCanonFvar := sourceToCanonFvar.insert srcName canonName

  -- Canonical `(head, headLevels, specParams)` signatures (semantic
  -- identities). Not keyed by raw hash: alpha-collapse can express the
  -- same aux via different source names that resolve to one address.
  let canonicalSignatures := auxSignaturesOfExpanded expanded
  if canonicalSignatures.size != nCanon then
    throw (.invalidMutualBlock
      "compute_aux_perm: canonical aux missing nested_expr entries")

  -- Head-name buckets.
  let canonByHead := signaturesByHead canonicalSignatures

  let originalNames : Std.HashSet Name :=
    originalAll.foldl (init := {}) (·.insert ·)

  -- Original members OUTSIDE this SCC compare name-strictly during
  -- matching (see `auxSpecEq`): they behave as external constants in
  -- specs, but address-equating them would let an alpha-twin member of
  -- a different SCC spuriously match, making two SCCs claim one source
  -- position's `all0.rec_N` name family.
  let mut strictNamesM : Std.HashSet Name := {}
  for n in originalAll do
    if !origToCanonNames.contains n then
      strictNamesM := strictNamesM.insert n
  let strictNames := strictNamesM

  let mut perm : Array Nat := Array.replicate nSource PERM_OUT_OF_SCC
  let mut specEqCache : Std.HashMap (Expr × Expr) Bool := {}
  let mut outOfSccCache : Std.HashMap Expr Bool := {}
  let mut normalizeCache : ExprCache := {}

  for ((srcOwner, srcHead, srcLevels, srcSpecs), j) in sourceOrder.zipIdx do
    -- Normalize source spec_params to the canonical walk's view. In-SCC
    -- alpha-collapse aliases rewrite to their representatives;
    -- everything else (genuine external types AND other-SCC original
    -- members) stays as spelled.
    let mut normalized : Array Expr := #[]
    for sp in srcSpecs do
      let (sp', cache') :=
        (replaceConstNamesCached sp origToCanonNames).run normalizeCache
      normalizeCache := cache'
      normalized := normalized.push sp'

    -- Match FIRST, then classify misses. A position whose specs mention
    -- other-SCC members can still be canonical HERE when this SCC's own
    -- constructors mention the same occurrence — e.g.
    -- `S.mk : List (S × T) → S` with `T` split into its own SCC: the
    -- canonical expansion of {S} carries the `T`-spelling verbatim, so
    -- strict-name matching identifies exactly the discovered-here
    -- occurrences (fixture `AuxOwnership.SplitSpecs`; the old
    -- out-of-SCC pre-filter skipped these and then failed the
    -- covered-check below with "canonical aux has no source mapping").
    let (canonIdx, specEqCache') := matchAuxSignature srcHead srcLevels
      normalized canonicalSignatures canonByHead resolveAddr
      sourceToCanonFvar strictNames specEqCache
    specEqCache := specEqCache'

    match canonIdx with
    | some ci => perm := perm.set! j ci
    | none =>
      -- No canonical match here. A position whose specs reference
      -- out-of-SCC original members is another block's business:
      -- canonical in the SCC that discovers it, or evaporated by the
      -- owner's SCC — the disposition pass in `generateAuxPatches`
      -- decides. Other constants are ordinary external parameters.
      let mut referencesOut := false
      for sp in srcSpecs do
        let (bad, cache') :=
          (hasOutOfSccConst sp origToCanonNames originalNames).run
            outOfSccCache
        outOfSccCache := cache'
        if bad then referencesOut := true
      if referencesOut then
        continue
      -- Discovered from a different split SCC's ctor walk → skip; an
      -- in-SCC owner with no match is a construction bug.
      if !origToCanonNames.contains srcOwner then
        continue
      let srcSig := ", ".intercalate
        (normalized.toList.map (fun e => toString e.getHash))
      let canonSigs := " · ".intercalate (canonicalSignatures.toList.map
        fun (head, levels, specs) =>
          s!"{head.pretty}.\{{", ".intercalate (levels.toList.map (toString ·.getHash))}}[{", ".intercalate (specs.toList.map (toString ·.getHash))}]")
      throw (.invalidMutualBlock
        s!"compute_aux_perm: no canonical match for in-SCC source aux #{j} \
owned by {srcOwner.pretty} (head={srcHead.pretty}); normalized source \
specs: [{srcSig}]; canonical signatures: {canonSigs}")

  -- Coverage: every canonical aux needs at least one source mapping.
  let mut covered : Array Bool := Array.replicate nCanon false
  for p in perm do
    if p != PERM_OUT_OF_SCC && p < nCanon then
      covered := covered.set! p true
  for (c, i) in covered.zipIdx do
    if !c then
      throw (.invalidMutualBlock
        s!"compute_aux_perm: canonical aux #{i} has no source mapping \
(canonical produced an aux that source walk missed)")

  return perm

/-! ## Lean-faithful inductive flags -/

/-- Block-wide `isRec` / `isReflexive` / `numNested`.
    Mirrors Rust `LeanIndFlags` (nested.rs:2120). -/
structure LeanIndFlags where
  isRec : Bool
  isReflexive : Bool
  numNested : Nat
  deriving Repr, Inhabited

/-- Recompute Lean's block-wide flags for the original mutual group
    (used wherever an `InductiveVal` must be reconstructed without a Lean
    env — Ixon doesn't store these). Mirrors Rust `compute_lean_ind_flags`
    (nested.rs:2131). -/
def computeLeanIndFlags (all : Array Name) : CompileM LeanIndFlags := do
  let expanded ← expandNestedBlock all {}
  let numNested := expanded.types.size - expanded.nOriginals
  let blockNames : Std.HashSet Name :=
    expanded.types.foldl (init := {}) fun s m => s.insert m.name

  let mut occCache : Std.HashMap Expr Bool := {}
  let mut isRec := false
  let mut isReflexive := false
  for member in expanded.types do
    for ctor in member.ctors do
      let mut ty := ctor.typ
      let mut go := true
      while go do
        match ty with
        | .forallE _ dom body _ _ =>
          let (occ, cache') := (hasIndOcc dom blockNames).run occCache
          occCache := cache'
          if occ then
            isRec := true
            if let .forallE .. := dom then
              isReflexive := true
          ty := body
        | _ => go := false
  return { isRec, isReflexive, numNested }

/-- Validate that every inductive group carries exactly the recomputed
    flags. Groups with missing members/ctors are skipped (Rust returns Ok
    for them). Mirrors Rust `validate_ind_groups` (nested.rs:2176),
    sequentially (Rust uses par_iter; ordering of error discovery is the
    only difference, and each group's verdict is independent). -/
def validateIndGroups (groups : Std.HashMap Name (Array Name))
    : CompileM Unit := do
  for (_, all) in groups do
    -- Skip groups whose members/ctors aren't all resolvable inductives.
    let mut skip := false
    for member in all do
      match ← lookupConst? member with
      | some (.inductInfo v) =>
        for cn in v.ctors do
          match ← lookupConst? cn with
          | some (.ctorInfo _) => pure ()
          | _ => skip := true
      | _ => skip := true
    if skip then
      continue
    let flags ← computeLeanIndFlags all
    for member in all do
      let some (.inductInfo v) ← lookupConst? member | continue
      if v.isRec != flags.isRec || v.isReflexive != flags.isReflexive
          || v.numNested != flags.numNested then
        throw (.invalidMutualBlock
          s!"non-canonical inductive flags for '{member.pretty}': stored \
isRec={v.isRec} isReflexive={v.isReflexive} numNested={v.numNested}, \
computed isRec={flags.isRec} isReflexive={flags.isReflexive} \
numNested={flags.numNested}")

end Ix.AuxGen
