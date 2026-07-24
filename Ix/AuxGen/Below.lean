/-
  Ix.AuxGen.Below: canonical `.below` generation for inductive blocks.

  Port of the generator half of `crates/compile/src/compile/aux_gen/below.rs`
  (lines 1-1309): `generate_below_constants` and everything reachable from
  it. For Type-level inductives, `.below` is a reducible definition:

    `A.below {motives} t := A.rec (λ _, Sort rlvl) (λ fields ih, motive x ×' ih) t`

  For Prop-level inductives, `.below` is an inductive type with constructors
  mirroring the parent's structure (see `IndPredBelow.lean`).

  Follows `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:59-108`.

  NOT here (already ported, reused):
  - the data model `BelowDef`/`BelowCtor`/`BelowIndc`/`BelowConstant`
    (below.rs:41-95) lives in `Ix.AuxGen.Types`;
  - the pure level suite (below.rs:1311-1788: `mk_level_succ`,
    `level_max`, `level_normalize`, `mk_pprod`, `punit_const`,
    `mk_pprod_mk`, `mk_punit_unit`, `replace_result_sort_with_prop`) lives
    in `Ix.AuxGen.Levels`;
  - `kuniv_to_level` (below.rs:1689) lives in `Ix.AuxGen.Kernel`;
  - `count_foralls_expr` (below.rs:579) is byte-identical in behavior to
    ExprUtils' `countForalls` (expr_utils.rs:1521) — the Rust duplicate
    exists only to dodge a module-path collision, so the port reuses
    `countForalls`.

  Environment access: Rust threads `lean_env: &LeanEnv` and
  `stt: &CompileState`; the Lean port reads the base compile environment
  via `lookupConst?` / `getCompileEnv` (CompileM under KBridgeM), the same
  view `generate_aux_patches` hands the Rust generator.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkParam`,
  ...) so the embedded blake3 hashes stay bit-identical with the Rust
  compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.CompileM
public import Ix.AuxGen.Types
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.Nested
public import Ix.AuxGen.Kernel
public import Ix.AuxGen.CasesOn
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-- Mirrors Rust `aux_rec_suffix_idx` (aux_gen/below.rs:31).

    Extract the 1-based suffix index from an auxiliary recursor name of
    shape `<head>.rec_N`. Returns `none` if the last component isn't a
    `rec_<n>` string.

    Used by `generateBelowConstants` and `generateBreconConstants`
    to derive source-indexed `below_N` / `brecOn_N` suffixes from the
    (already source-indexed) aux rec names produced by
    `generateAuxPatches`. -/
def auxRecSuffixIdx (auxRecName : Name) : Option Nat :=
  match auxRecName with
  | .str _ s _ =>
    if s.startsWith "rec_" then (s.drop 4).toNat? else none
  | _ => none

/-- Mirrors Rust `extract_major_head_ind` (aux_gen/below.rs:392).

    Extract the `InductiveVal` from a recursor's major premise.

    The major premise is the last binder in the recursor type:
    `∀ params motives minors indices (t : ExtInd ...), motive ...`.
    Returns the `InductiveVal` for the head constant of the major's
    domain. -/
def extractMajorHeadInd (recVal : RecursorVal)
    : KBridgeM (Option InductiveVal) := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices
  let total := nParams + nMotives + nMinors + nIndices + 1

  -- Peel all binders to get the major premise's domain.
  let mut cur := recVal.cnst.type
  for _ in [0:total - 1] do
    if let .forallE _ _ body _ _ := cur then
      cur := body
  -- cur is now `∀ (t : MajorDom), ReturnType`
  let majorDom ← match cur with
    | .forallE _ dom _ _ _ => pure dom
    | _ => return none
  let (head, _) := decomposeApps majorDom
  match head with
  | .const name _ _ =>
    match ← lookupConst? name with
    | some (.inductInfo v) => return some v
    | _ => return none
  | _ => return none

/-- Mirrors Rust `build_below_type` (aux_gen/below.rs:433).

    Build the `.below` type from the recursor type.

    Takes the recursor type `∀ params motives minors indices major,
    motive major` and produces `∀ params motives indices major, Sort rlvl`
    (drops minors, replaces return with Sort rlvl).

    Uses FVar-based construction: opens all rec type binders into FVars,
    discards minor FVars, and re-closes with `mkForall` which handles all
    BVar computation automatically. -/
def buildBelowType (recVal : RecursorVal) (rlvl : Level) : Expr :=
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices

  -- Open all rec type binders into FVars.
  let (_, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "btp" 0
  let (_, motiveDecls, afterMotives) :=
    forallTelescope afterParams nMotives "btm" 0
  -- Open minors (we'll discard these decls)
  let (_, _minorDecls, afterMinors) :=
    forallTelescope afterMotives nMinors "btx" 0
  let (_, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "bti" 0
  -- Open major
  let (_, majorDecl, _afterMajor) :=
    forallTelescope afterIndices 1 "btj" 0

  -- Build: ∀ params motives indices major, Sort rlvl
  -- The decls already have correct FVar-based domains (instantiate1
  -- resolved cross-references). mkForall abstracts all FVars into BVars.
  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ indexDecls ++ majorDecl

  mkForall (Expr.mkSort rlvl) allDecls

/-- Mirrors Rust `detect_rec_target_class` (aux_gen/below.rs:1125).

    Detect if a field domain targets an inductive in the block. Returns
    the class index if found.

    Works on both BVar-based and FVar-based domains — checks for Const
    heads. -/
def detectRecTargetClass (dom : Expr) (allIndNames : Array (Name × Nat))
    : Option Nat := Id.run do
  let mut ty := dom
  repeat
    match ty with
    | .forallE _ _ body _ _ => ty := body
    | _ =>
      let (head, _) := decomposeApps ty
      if let .const name _ _ := head then
        for (indName, classIdx) in allIndNames do
          if name == indName then
            return some classIdx
      return none
  return none -- unreachable: the non-forall arm always returns

/-- Mirrors Rust `transform_to_below_fvar` (aux_gen/below.rs:1025).

    Transform a recursive field type `∀ ys, I_j args` (FVar-based) to the
    corresponding `.below` IH type
    `∀ ys, I_j.below params motives args (h ys)`.

    For a first-order recursive field `h : I_j args`, `innerFvars` is
    empty and the result is `I_j.below params motives args h`.

    For a higher-order recursive field `h : ∀ y₁ .. yₙ, I_j args`, the
    result is `∀ y₁ .. yₙ, I_j.below params motives args (h y₁ .. yₙ)`.
    The inner binders are re-closed with `mkForall`.

    Matches `ihTypeToBelowType` at
    `refs/lean4/src/Lean/Meta/IndPredBelow.lean:71-75`: the motive fvar in
    the minor-premise IH type is replaced by the `.below` constant applied
    to params+motives, while the rest of the application spine (indices
    plus the applied field) is preserved. -/
def transformToBelowFvar (fieldDom : Expr) (targetJ : Nat)
    (paramFvars motiveFvars : Array Expr) (belowNames : Array Name)
    (levelParams : Array Name) (majorFvar : Expr) : Expr := Id.run do
  -- Open any inner foralls (for higher-order recursive fields like
  -- `∀ a, I_j (f a)`)
  let nInner := countForalls fieldDom
  let (innerFvars, innerDecls, leaf) :=
    forallTelescope fieldDom nInner "bict" 0

  -- Decompose leaf: should be `I_j args...` (Const or FVar head)
  let (_head, args) := decomposeApps leaf

  -- Build: I_j.below params motives indices (majorFvar innerFvars)
  let belowConst := mkConst belowNames[targetJ]!
    (levelParams.map Level.mkParam)
  let mut result := belowConst
  result := mkAppN result paramFvars
  result := mkAppN result motiveFvars
  -- Apply original index args (skip the leading params)
  let nParams := paramFvars.size
  for a in args[nParams:] do
    result := Expr.mkApp result a
  -- The `.below` major premise is the FIELD value, applied to the inner
  -- binders if the field is higher-order.
  let mut majorApplied := majorFvar
  if !innerFvars.isEmpty then
    majorApplied := mkAppN majorApplied innerFvars
  result := Expr.mkApp result majorApplied

  -- Re-close inner foralls if present
  if !innerDecls.isEmpty then
    result := mkForall result innerDecls
  return result

/-- Mirrors Rust `replace_head_with_fvar` (aux_gen/below.rs:1087).

    Replace the head constant in a recursive field domain with a motive
    FVar.

    For a first-order field `h : I_j params indices`, builds
    `motiveFvar indices h`.

    For a higher-order field `h : ∀ y₁ .. yₙ, I_j params indices`, builds
    `∀ y₁ .. yₙ, motiveFvar indices (h y₁ .. yₙ)`. The major is the FIELD
    value applied to the inner binders, not the inner binders spliced onto
    the motive's spine.

    `numParams` is the parent inductive's parameter count — the leaf's
    application spine is `[params..., indices...]`, so we skip the first
    `numParams` to retain only the indices. -/
def replaceHeadWithFvar (fieldDom : Expr) (motiveFvar : Expr)
    (majorFvar : Expr) (numParams : Nat) : Expr := Id.run do
  let nInner := countForalls fieldDom
  let (innerFvars, innerDecls, leaf) :=
    forallTelescope fieldDom nInner "bicr" 0

  let (_head, args) := decomposeApps leaf

  -- Build: motiveFvar indices... (majorFvar innerFvars)
  let mut result := motiveFvar
  for a in args[numParams:] do
    result := Expr.mkApp result a
  -- The motive's major premise is `h` applied to the inner binders (or
  -- just `h` itself if the field is first-order).
  let mut majorApplied := majorFvar
  if !innerFvars.isEmpty then
    majorApplied := mkAppN majorApplied innerFvars
  result := Expr.mkApp result majorApplied

  if !innerDecls.isEmpty then
    result := mkForall result innerDecls
  return result

/-- Per-field classification for `buildBelowMinor`. Mirrors the local
    `struct FieldInfo` in Rust `build_below_minor`
    (aux_gen/below.rs:1193-1205). -/
structure BelowMinorField where
  decl : LocalDecl
  fvar : Expr
  isIh : Bool
  /-- For higher-order IH: inner forall binders and leaf motive
      application. Empty for simple IH or non-IH fields. -/
  innerDecls : Array LocalDecl
  innerFvars : Array Expr
  /-- The leaf motive application (after peeling inner foralls). For
      simple IH: same as `decl.domain`. For higher-order IH: the innermost
      `motiveFvar args` after stripping foralls. -/
  leafMotiveApp : Option Expr

/-- Mirrors Rust `build_below_minor` (aux_gen/below.rs:1168).

    Build a minor premise argument for `.below`.

    `minorDom` is the minor's type from the rec type, in FVar form (params
    and motives already substituted with FVars). e.g.:
      `∀ (x : B) (x_ih : _bvm_1 x), _bvm_0 (A.a x)`
    where `_bvm_0`, `_bvm_1` are motive FVars.

    For each field:
    - Non-IH field (head is NOT a motive FVar) → keep as lambda param
    - Simple IH field (domain = `motive args`) → replace domain with
      `Sort rlvl`, collect PProd entry: `motive_app ×' ih_field`
    - Higher-order IH field (domain = `∀ a₁..aₙ, motive args`) → replace
      domain with `∀ a₁..aₙ, Sort rlvl`, collect PProd entry:
      `∀ a₁..aₙ, PProd (motive args) (ih_field a₁..aₙ)`

    The result is a lambda taking all fields (with IH types replaced),
    returning a PProd chain of entries, ending with PUnit.

    Matches Lean's `buildBelowMinorPremise` in
    `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:33-48`.

    (The Rust `tc_scope: &mut TcScope` becomes pass-in/return of
    `TcScopeSt`; the kernel state itself lives in KBridgeM.) -/
def buildBelowMinor (minorDom : Expr) (rlvl : Level)
    (motiveFvars : Array Expr) (tcScope : TcScopeSt)
    : KBridgeM (Expr × TcScopeSt) := do
  -- Open all field binders with forallTelescope. After this, field
  -- domains reference motive FVars directly (no BVar arithmetic needed).
  --
  -- Head-reduce each field's domain to match the shape Lean stores. When
  -- the parent inductive uses lambda-valued parameters (e.g.
  -- `β := λ_:α. Json` for `Internal.Impl α β`), a field like
  -- `v : (λ_:α. Json) k` is stored in Lean's .below value as `v : Json`.
  -- This is an empirical difference: the recursor's stored TYPE preserves
  -- the lambda redex, but the downstream `mkBelowFromRec` path reduces
  -- field binder types. Reducing here matches Lean's stored form exactly.
  let nFields := countForalls minorDom
  let (fieldFvars, fieldDecls0, _returnType) :=
    forallTelescope minorDom nFields "bwf" 0
  let fieldDecls := fieldDecls0.map fun d =>
    { d with domain := betaReduce d.domain }

  -- Classify fields: IH (head is motive FVar) vs non-IH. For IH fields,
  -- also open inner foralls to detect higher-order pattern.
  let fields : Array BelowMinorField :=
    (fieldDecls.zip fieldFvars).map fun (decl, fvar) =>
      let isIh := (findMotiveFVar decl.domain motiveFvars).isSome
      if isIh then
        let nInner := countForalls decl.domain
        let (innerFvars, innerDecls, leaf) :=
          forallTelescope decl.domain nInner "bwi" 0
        { decl, fvar, isIh, innerDecls, innerFvars,
          leafMotiveApp := some leaf }
      else
        { decl, fvar, isIh, innerDecls := #[], innerFvars := #[],
          leafMotiveApp := none }

  -- Build lambda binders FIRST (before PProd construction): for IH
  -- fields, replace domain with `Sort rlvl`. We need these pushed into
  -- the TcScope before inferring PProd levels.
  let lamDecls : Array LocalDecl := fields.map fun f =>
    if f.isIh then
      let newDomain :=
        if f.innerDecls.isEmpty then Expr.mkSort rlvl
        else mkForall (Expr.mkSort rlvl) f.innerDecls
      { f.decl with domain := newDomain }
    else
      f.decl

  -- Push field decls (with replaced IH domains) into the TcScope so that
  -- getLevel can resolve the FVars in PProd operands.
  let mut scope ← tcScope.pushLocals lamDecls

  -- Build PProd entries from IH fields. Infer each PProd operand's level
  -- via TC — matches Lean's `mkPProd` (PProdN.lean:37-38), which calls
  -- `getLevel` on each operand.
  let mut ihEntries : Array Expr := #[]
  for field in fields do
    if field.isIh then
      if let some leaf := field.leafMotiveApp then
        if field.innerDecls.isEmpty then
          -- Simple IH: PProd(motive_app, ih_fvar).
          let lvl1 ← scope.getLevel leaf
          let lvl2 ← scope.getLevel field.fvar
          ihEntries := ihEntries.push (mkPProd lvl1 lvl2 leaf field.fvar)
        else
          -- Higher-order IH: ∀ (a₁..aₙ), PProd(leaf, ih_fvar a₁..aₙ).
          scope ← scope.pushLocals field.innerDecls
          let ihApplied := mkAppN field.fvar field.innerFvars
          let lvl1 ← scope.getLevel leaf
          let lvl2 ← scope.getLevel ihApplied
          scope ← scope.popLocals field.innerDecls
          let pprod := mkPProd lvl1 lvl2 leaf ihApplied
          ihEntries := ihEntries.push (mkForall pprod field.innerDecls)

  -- Pack IH entries following Lean's PProdN.pack convention. Lean's
  -- genMk calls mkPProd per-pair, which infers levels from each operand.
  let mut body := punitConst rlvl
  if !ihEntries.isEmpty then
    let mut acc := ihEntries.back!
    let rest := ihEntries.pop
    for entry in rest.reverse do
      let lvl1 ← scope.getLevel entry
      let lvl2 ← scope.getLevel acc
      acc := mkPProd lvl1 lvl2 entry acc
    body := acc

  -- Pop field decls from the TcScope.
  scope ← scope.popLocals lamDecls

  return (mkLambda body lamDecls, scope)

/-- Mirrors Rust `build_below_value` (aux_gen/below.rs:471).

    Build the `.below` value (lambda body).

    Uses FVar-based construction: opens the rec type into FVars, builds
    the rec application with motive/minor replacements using FVar
    references, then closes with `mkLambda` over the non-minor binders. -/
def buildBelowValue (recVal : RecursorVal) (_ind : InductiveVal)
    (rlvl : Level) (_nClasses : Nat)
    (_canonicalRecs : Array (Name × RecursorVal)) (maps : AddrMaps)
    : KBridgeM Expr := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices

  -- Open all rec type binders into FVars.
  let (paramFvars, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "bvp" 0
  let (motiveFvars, motiveDecls, afterMotives) :=
    forallTelescope afterParams nMotives "bvm" 0
  -- Open minors — we need their domains (now FVar-based) for building
  -- the minor replacement args, but we discard the minor decls from the
  -- output binder list.
  let mut minorDoms : Array Expr := #[]
  let mut afterMinors := afterMotives
  for _ in [0:nMinors] do
    if let .forallE _ dom body _ _ := afterMinors then
      minorDoms := minorDoms.push dom
      -- Instantiate with a dummy FVar so subsequent minors see correct
      -- context (Rust indexes with the post-push length: 1-based).
      let (_, dummyFv) := freshFVar "bvx" minorDoms.size
      afterMinors := instantiate1 body dummyFv
  let (indexFvars, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "bvi" 0
  let (majorFvars, majorDecls, _) :=
    forallTelescope afterIndices 1 "bvj" 0

  -- Universe args for the rec application: [succ(rlvl), ind_lvls...]
  -- Use `Level.mkSucc` directly (not `mkLevelSucc`) to match Lean's
  -- elaborator, which does NOT distribute Succ over Max for recursor
  -- elimination levels.
  --
  -- Derive the inductive-level params from the recursor's own level
  -- params, not from `ind`. The recursor's level params are
  -- [elim_level, ind_params...], so [1..] gives the inductive-level
  -- params. This is correct for both the main .below (where ind = block
  -- inductive) and below_N (where ind = external inductive, whose level
  -- params may differ from the auxiliary recursor's).
  let mut recUnivs : Array Level := #[Level.mkSucc rlvl]
  for lp in recVal.cnst.levelParams[1:] do
    recUnivs := recUnivs.push (Level.mkParam lp)

  -- Build rec application using FVars:
  --   I.rec.{succ(rlvl), lvls...} params motives' minors' indices major
  let mut app := mkConst recVal.cnst.name recUnivs

  -- Apply params (FVars)
  app := mkAppN app paramFvars

  -- Apply modified motives: for each motive, build
  -- λ (motive_args...), Sort rlvl. The motive domains are in FVar form
  -- (param FVars already substituted), so we can use forallTelescope on
  -- them directly.
  for decl in motiveDecls do
    let motiveType := decl.domain -- ∀ (indices) (major), Sort u
    let nMotiveArgs := countForalls motiveType
    let (_, motiveArgDecls, _) :=
      forallTelescope motiveType nMotiveArgs "bvma" 0
    let motiveReplacement := mkLambda (Expr.mkSort rlvl) motiveArgDecls
    app := Expr.mkApp app motiveReplacement

  -- Apply modified minors: for each minor, build the PProd chain. The
  -- minor domains are in FVar form (params + motives substituted), so
  -- field IH detection uses findMotiveFVar instead of BVar range checks.
  --
  -- Create a TcScope for PProd level inference (matching Lean's mkPProd
  -- which calls getLevel on each operand). The outer context is
  -- paramDecls + motiveDecls; per-minor field decls are pushed inside.
  let recLevelParams := recVal.cnst.levelParams
  let outerCtx : Array LocalDecl := paramDecls ++ motiveDecls
  let mut tcScope ← TcScopeSt.new outerCtx recLevelParams maps

  for minorDom in minorDoms do
    let (minorArg, tcScope') ←
      buildBelowMinor minorDom rlvl motiveFvars tcScope
    tcScope := tcScope'
    app := Expr.mkApp app minorArg

  -- Apply indices and major (FVars)
  app := mkAppN app indexFvars
  app := mkAppN app majorFvars

  -- Wrap in lambdas over [params, motives, indices, major] (no minors)
  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ indexDecls ++ majorDecls

  return mkLambda app allDecls

/-- Mirrors Rust `build_below_def` (aux_gen/below.rs:272).

    Build a single `.below` definition for a Type-level inductive.

    The `.below` definition's value is:
    ```text
    λ {params} {motives} (indices) (major),
      I.rec.{succ(rlvl), lvls...} params
        (λ (indices) (major), Sort rlvl)     -- for each motive
        (buildMinor rlvl motives minorType)  -- for each minor
        indices major
    ```

    (Deviation: Rust dumps the full recursor type to stderr before
    propagating a telescope-arity error — CompileM has no IO channel, so
    only the error itself is surfaced; its message text is identical.) -/
def buildBelowDef (belowName : Name) (recVal : RecursorVal)
    (ind : InductiveVal) (nClasses : Nat)
    (canonicalRecs : Array (Name × RecursorVal)) (maps : AddrMaps)
    : KBridgeM BelowDef := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := recVal.numIndices
  let recLevelParams := recVal.cnst.levelParams
  let _indLevelParams := ind.cnst.levelParams

  -- The elimination level is the first level param (for large
  -- eliminators).
  let elimLevel := Level.mkParam recLevelParams[0]!

  -- ilvl: the universe level of the inductive's type former.
  --
  -- Lean (BRecOn.lean:78-80):
  --   let majorTypeType ← inferType (← inferType major)
  --   let ilvl ← typeFormerTypeLevel majorTypeType
  --
  -- We use TcScope.getLevel(major_domain) which does exactly this:
  -- infers the type of the major's domain expression (getting Sort ilvl),
  -- then extracts ilvl. This matches Lean's approach of delegating to
  -- inferType rather than manually decomposing level trees.
  let ilvl ← do
    let total := nParams + nMotives + nMinors + nIndices + 1
    let ctx := s!"build_below_def({recVal.cnst.name.pretty})"
    let what := s!"n_params({nParams}) + n_motives({nMotives}) + \
n_minors({nMinors}) + n_indices({nIndices}) + 1 major"
    let (_fvars, decls, _) ←
      match forallTelescopeExact recVal.cnst.type total "blv" 0 ctx what with
      | .ok t => pure t
      | .error (.unsupportedExpr desc) =>
        throw (CompileError.unsupportedExpr desc)
    let majorDomain := decls[total - 1]!.domain

    let ctxDecls : Array LocalDecl := decls.extract 0 (total - 1)
    let tc ← TcScopeSt.new ctxDecls recLevelParams maps
    tc.getLevel majorDomain

  -- rlvl = mkLevelMax(ilvl, elim_level), matching Lean's BRecOn.lean:83:
  --   `let rlvl : Level := mkLevelMax ilvl lvl`
  -- mkLevelMax only eliminates zeros — no subsumption, no
  -- right-association (RAW `Level.mkMax`).
  let rlvl :=
    if ilvl matches .zero _ then elimLevel
    else if elimLevel matches .zero _ then ilvl
    else Level.mkMax ilvl elimLevel

  -- .below level params = same as .rec level params
  let belowLevelParams := recLevelParams

  -- Build the type: ∀ {params} {motives} (indices) (major : I params
  -- indices), Sort rlvl. This is the recursor type WITHOUT minors and
  -- with Sort rlvl as return.
  let belowType := buildBelowType recVal rlvl

  -- Build the value: λ {params} {motives} (indices) (major),
  --   I.rec.{succ(rlvl), lvls...} params motives' minors' indices major
  let belowValue ← buildBelowValue recVal ind rlvl nClasses canonicalRecs maps

  return {
    name := belowName
    levelParams := belowLevelParams
    typ := belowType
    value := belowValue
    -- `.below` (Type-level) references the `.rec` it was built from, so
    -- `mkDefinitionValInferringUnsafe` propagates that recursor's safety.
    -- For originals `recVal.isUnsafe` matches the class rep; for nested
    -- aux members `ind` is the external inductive (whose own safety is
    -- unrelated — think `List` in `_nested.List_1`), so we can't read the
    -- flag off `ind`. The canonical recursor was generated with the
    -- block-wide `isUnsafe` (see `Ix.AuxGen.Recursor`), which is what
    -- Lean's `mkBelowFromRec` sees during elaboration.
    isUnsafe := recVal.isUnsafe
  }

/-- Mirrors Rust `build_below_indc_type` (aux_gen/below.rs:713).

    Build the type of a Prop-level `.below` inductive.

    Type: `∀ {params} {motives} (indices) (major : I params indices), Prop`

    Uses FVar-based construction: opens all rec type binders, skips
    minors, adjusts motive domains to target Prop, re-closes with
    `mkForall`. -/
def buildBelowIndcType (recVal : RecursorVal) (ind : InductiveVal) : Expr :=
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let nMinors := recVal.numMinors
  let nIndices := ind.numIndices

  -- Open all rec type binders into FVars.
  let (_, paramDecls, afterParams) :=
    forallTelescope recVal.cnst.type nParams "bitp" 0
  let (_, motiveDecls, afterMotives) :=
    forallTelescope afterParams nMotives "bitm" 0
  let (_, _minorDecls, afterMinors) :=
    forallTelescope afterMotives nMinors "bitx" 0
  let (_, indexDecls, afterIndices) :=
    forallTelescope afterMinors nIndices "biti" 0
  let (_, majorDecls, _) := forallTelescope afterIndices 1 "bitj" 0

  -- Match Lean's `toImplicit` (IndPredBelow.lean:77-80): make index
  -- binders implicit while keeping the major (last binder) explicit.
  let indexDecls : Array LocalDecl := indexDecls.map fun d =>
    { d with info := .implicit }

  -- Adjust motive domains: replace result Sort with Prop, make implicit.
  -- Prop .below motives always target Prop, even with large elimination
  -- (drec).
  let motiveDecls : Array LocalDecl := motiveDecls.map fun d =>
    { d with domain := replaceResultSortWithProp d.domain,
             info := .implicit }

  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ indexDecls ++ majorDecls

  mkForall (Expr.mkSort Level.mkZero) allDecls

/-- Field classification for `buildBelowIndcCtor`. Mirrors the local
    `struct FieldEntry` in Rust `build_below_indc_ctor`
    (aux_gen/below.rs:884-888). -/
structure BelowFieldEntry where
  decl : LocalDecl
  fvar : Expr
  recTarget : Option Nat

/-- Mirrors Rust `build_below_indc_ctor` (aux_gen/below.rs:778).

    Build a constructor for a Prop-level `.below` inductive.

    For parent ctor `C : ∀ params fields, I params`: the `.below` ctor
    has `∀ params motives (expanded_fields), I.below motives (C params
    orig_fields)`.

    For each field in the parent ctor:
    - Non-recursive field: keep as-is
    - Recursive field (head is inductive in block): expand to TWO extra
      fields:
      1. `ih : Target_j.below motives args` (below proof)
      2. `f_ih : motive_j args` (motive proof)

    Uses FVar-based construction: opens all binders into FVars, builds
    domains using FVar references, closes with `mkForall`.

    (Deviation: Rust returns `BelowCtor` directly; the Lean port is
    monadic only for the `lookupConst?` env reads — it never throws. The
    Rust `MissingConstant.caller` context strings have no slot in
    `CompileError.missingConstant`.) -/
def buildBelowIndcCtor (belowName : Name) (ctorName : Name)
    (ctor : ConstructorVal) (recVal : RecursorVal) (ind : InductiveVal)
    (_ci : Nat) (nParams nMotives nClasses : Nat) (belowNames : Array Name)
    (sortedClasses : Array (Array Name)) : KBridgeM BelowCtor := do
  let ctorSuffix :=
    (nameStripPrefix ctorName ind.cnst.name).getD (nameComponents ctorName)
  let belowCtorName := nameAppendComponents belowName ctorSuffix

  let nCtorParams := ctor.numParams
  let nCtorFields := ctor.numFields
  let indLevelParams := ind.cnst.levelParams

  -- Extract original field binder names from the Lean-generated `.below`
  -- ctor for faithful roundtrip of hygiene names.
  let origBelowCtorName := nameAppendComponents belowName ctorSuffix
  let origFieldNames : Array Name :=
    match ← lookupConst? origBelowCtorName with
    | some (.ctorInfo cv) => Id.run do
      let mut names : Array Name := #[]
      let mut ty := cv.cnst.type
      let skip := cv.numParams
      for _ in [0:skip] do
        if let .forallE _ _ body _ _ := ty then
          ty := body
      repeat
        match ty with
        | .forallE name _ body _ _ =>
          names := names.push name
          ty := body
        | _ => break
      return names
    | _ => #[]
  -- Rust consumes `orig_field_names` through an iterator shared by Pass 1
  -- and Pass 2; the port tracks the cursor explicitly.
  let mut origNameIdx := 0

  -- --- Phase 1: Open ctor type into FVars ---

  -- Open params from ctor type
  let (paramFvars, paramDecls, afterParams) :=
    forallTelescope ctor.cnst.type nCtorParams "bicp" 0

  -- Open fields from ctor type (after params). Domains now reference
  -- param FVars. ctorReturn is the constructor's return type (e.g.,
  -- `I params indices`) in FVar form.
  let (fieldFvars, fieldDecls, ctorReturn) :=
    forallTelescope afterParams nCtorFields "bicf" 0

  -- --- Phase 2: Create motive FVars from rec type ---
  -- Peel rec type params by substituting with the ctor's param FVars
  -- (bicp_*). This ensures motive domains reference the same FVars as
  -- paramDecls, so mkForall can abstract them correctly.
  let mut recAfterParams := recVal.cnst.type
  for pf in paramFvars do
    if let .forallE _ _ body _ _ := recAfterParams then
      recAfterParams := instantiate1 body pf
  let mut motiveFvars : Array Expr := #[]
  let mut motiveDecls : Array LocalDecl := #[]
  let mut recCur := recAfterParams
  for mi in [0:nMotives] do
    if let .forallE name dom body _ _ := recCur then
      let dom := replaceResultSortWithProp dom
      let (fvName, fv) := freshFVar "bicm" mi
      motiveDecls := motiveDecls.push
        { fvarName := fvName, binderName := name, domain := dom,
          info := .implicit }
      motiveFvars := motiveFvars.push fv
      recCur := instantiate1 body fv

  -- --- Phase 3: Detect recursive fields and build expanded binders ---

  -- Maps from inductive name → class index for recursive field
  -- detection. (Rust filter_map: names whose env lookup fails are
  -- skipped; non-inductive entries keep their own name.)
  let mut allIndNames : Array (Name × Nat) := #[]
  for j in [0:nClasses] do
    for name in sortedClasses[j]! do
      match ← lookupConst? name with
      | some (.inductInfo v) => allIndNames := allIndNames.push (v.cnst.name, j)
      | some _ => allIndNames := allIndNames.push (name, j)
      | none => pure ()

  -- Classify fields as recursive or not. Field domains are in FVar form
  -- (param FVars substituted), so detectRecTargetClass works on Const
  -- heads.
  let fields : Array BelowFieldEntry :=
    (fieldDecls.zip fieldFvars).map fun (decl, fvar) =>
      let recTarget := detectRecTargetClass decl.domain allIndNames
      { decl, fvar, recTarget }

  -- Build the expanded binder list following Lean's IndPredBelow ordering
  -- (IndPredBelow.lean:99-113).
  --
  -- Lean processes the recursor MINOR premise, which places ALL
  -- constructor fields first, then ALL IH fields. IndPredBelow iterates
  -- the minor args in order: non-IH args (constructor fields) are pushed
  -- as-is, then IH args (motive-typed) get (below, motive) pairs
  -- inserted.
  --
  -- Since we work from the constructor (not the minor), we replicate
  -- this with two passes:
  --   Pass 1: push ALL original fields
  --   Pass 2: for each recursive field, push (ih_below, motive_proof)
  let mut expandedDecls : Array LocalDecl := #[]
  let mut origFieldFvars : Array Expr := #[] -- FVars for original fields

  -- Pass 1: Push all original fields
  for field in fields do
    let origName := origFieldNames[origNameIdx]?.getD field.decl.binderName
    origNameIdx := origNameIdx + 1
    expandedDecls := expandedDecls.push
      { field.decl with binderName := origName }
    origFieldFvars := origFieldFvars.push field.fvar

  -- Pass 2: For each recursive field, push (ih_below, motive_proof)
  for field in fields do
    if let some targetJ := field.recTarget then
      -- ih: Target_j.below params motives field_fvar
      -- The field domain is `I_j args` in FVar form. We need to build
      -- `I_j.below params motives args field_fvar`.
      let ihDom := transformToBelowFvar field.decl.domain targetJ paramFvars
        motiveFvars belowNames indLevelParams field.fvar
      let ihName :=
        origFieldNames[origNameIdx]?.getD (Name.mkStr .mkAnon "ih")
      origNameIdx := origNameIdx + 1
      let (ihFvName, _ihFv) := freshFVar "bici" expandedDecls.size
      expandedDecls := expandedDecls.push
        { fvarName := ihFvName, binderName := ihName, domain := ihDom,
          info := .default }

      -- f_ih: motive_j indices... field_fvar
      -- Replace inductive head with motive FVar, skip params, apply
      -- indices + field_fvar
      let fihDom := replaceHeadWithFvar field.decl.domain
        motiveFvars[targetJ]! field.fvar nParams
      let fihName := origFieldNames[origNameIdx]?.getD field.decl.binderName
      origNameIdx := origNameIdx + 1
      let (fihFvName, _fihFv) := freshFVar "bicih" expandedDecls.size
      expandedDecls := expandedDecls.push
        { fvarName := fihFvName, binderName := fihName, domain := fihDom,
          info := .default }

  -- --- Phase 4: Build return type using FVars ---
  -- Return type: below_name params motives indices... (ctor params
  -- orig_fields) where indices are extracted from the constructor's
  -- return type `I params indices`.
  let univs : Array Level := indLevelParams.map Level.mkParam
  let ctorApp := mkAppN (mkConst ctorName univs)
    (paramFvars ++ origFieldFvars)

  -- Extract index arguments from the ctor's return type. ctorReturn is
  -- e.g. `Nat.le n (Nat.succ m)` in FVar form; args after nParams are
  -- the index expressions.
  let (_retHead, retArgs) := decomposeApps ctorReturn
  let indexArgs := retArgs.extract nParams retArgs.size

  let mut ret := mkConst belowName univs
  ret := mkAppN ret paramFvars
  ret := mkAppN ret motiveFvars
  for idxArg in indexArgs do
    ret := Expr.mkApp ret idxArg
  ret := Expr.mkApp ret ctorApp

  -- --- Phase 5: Close with mkForall ---
  let allDecls : Array LocalDecl :=
    paramDecls ++ motiveDecls ++ expandedDecls

  let nFieldsTotal := allDecls.size - nParams - nMotives
  let typ := mkForall ret allDecls

  return {
    name := belowCtorName
    typ
    nParams := nParams + nMotives
    nFields := nFieldsTotal
  }

/-- Mirrors Rust `build_below_indc` (aux_gen/below.rs:602).

    Build a Prop-level `.below` inductive.

    For a Prop inductive `I_i` with constructor
    `C : ∀ params fields, I_i params`, the `.below` inductive has:
    - Type: `∀ {params} {motives} (major : I_i params), Prop`
    - One ctor per parent ctor, with IH fields expanded to include
      `.below` proofs.

    Follows `IndPredBelow.lean:83-120`.

    (Deviation: the Rust `try_nat_to_usize(&rec_val.num_minors)` checked
    conversion has no Lean counterpart — `RecursorVal` counts are native
    `Nat`s. `CompileError.missingConstant` carries no `caller` slot for
    the Rust context strings.) -/
def buildBelowIndc (ci : Nat) (belowName : Name) (recVal : RecursorVal)
    (ind : InductiveVal) (nClasses : Nat)
    (sortedClasses : Array (Array Name))
    (_canonicalRecs : Array (Name × RecursorVal)) : KBridgeM BelowIndc := do
  let nParams := recVal.numParams
  let nMotives := recVal.numMotives
  let _nMinors := recVal.numMinors
  let nIndices := ind.numIndices
  let belowNParams := nParams + nMotives
  let indLevelParams := ind.cnst.levelParams

  -- Build .below names for all classes (needed for ihTypeToBelowType)
  let belowNames : Array Name := (Array.range nClasses).map fun j =>
    Name.mkStr sortedClasses[j]![0]! "below"

  -- .below type: ∀ {params} {motives} (major : I_i params indices), Prop
  -- Build from the recursor type: take params + motives, skip minors,
  -- take indices + major, return Prop.
  let belowType := buildBelowIndcType recVal ind

  -- Build constructors: one per parent ctor for class ci

  -- Walk rec type to find the minors for this class. The minors in the
  -- rec type correspond to constructors. We need to identify which
  -- minors belong to class ci.
  let mut ctors : Array BelowCtor := #[]
  let mut _globalMinorIdx := 0
  for classIdx in [0:nClasses] do
    let classRep := sortedClasses[classIdx]![0]!
    let classInd ←
      match ← lookupConst? classRep with
      | some (.inductInfo v) => pure v
      | _ =>
        -- Rust: MissingConstant { caller: "build_below_indc: class
        -- {class_idx} rep not an inductive" }
        throw (CompileError.missingConstant classRep.pretty)

    for ctorName in classInd.ctors do
      if classIdx == ci then
        -- This ctor belongs to our class — build a .below ctor for it
        let ctor ←
          match ← lookupConst? ctorName with
          | some (.ctorInfo c) => pure c
          | _ =>
            -- Rust: MissingConstant { caller: "build_below_indc:
            -- constructor not found" }
            throw (CompileError.missingConstant ctorName.pretty)

        let belowCtor ← buildBelowIndcCtor belowName ctorName ctor recVal
          ind ci nParams nMotives nClasses belowNames sortedClasses
        ctors := ctors.push belowCtor
      _globalMinorIdx := _globalMinorIdx + 1

  return {
    name := belowName
    -- .below has same level params as parent (no elim level for Prop)
    levelParams := indLevelParams
    nParams := belowNParams
    nIndices := nIndices + 1 -- original indices + major premise
    -- `.below` inherits reflexivity from the parent: any higher-order
    -- recursive field in the parent (the defining trait of a reflexive
    -- inductive) produces a higher-order `.below` IH field.
    isReflexive := ind.isReflexive
    -- Prop-level `.below` is an inductive whose constructors mirror the
    -- parent's. Lean's `IndPredBelow` inherits the parent inductive's
    -- safety (`env.hasUnsafe` fires via the parent's ctor types).
    isUnsafe := ind.isUnsafe
    typ := belowType
    ctors
  }

/-- Mirrors Rust `generate_below_constants` (aux_gen/below.rs:110).

    Generate `.below` constants for all classes in a block.

    For Type-level inductives: generates a `BelowDef` (reducible
    definition). For Prop-level inductives: generates a `BelowIndc`
    (inductive type).

    `canonicalRecs` are the recursors generated by Phase 1. `isProp`
    indicates whether the inductive block is in Prop (Sort 0). This
    determines the generation strategy — matching Lean's split between
    `BRecOn.lean` (Type-level → definition) and `IndPredBelow.lean`
    (Prop → inductive).

    Note: `isProp` is distinct from `is_large`. A Prop inductive with
    single constructors and all-Prop fields gets large elimination
    (`drec`), but Lean still generates `.below` as an inductive via
    `IndPredBelow`. -/
def generateBelowConstants (sortedClasses : Array (Array Name))
    (canonicalRecs : Array (Name × RecursorVal)) (isProp : Bool)
    (maps : AddrMaps) : KBridgeM (Array BelowConstant) := do
  let nClasses := sortedClasses.size
  if nClasses == 0 || canonicalRecs.isEmpty then
    return #[]

  let mut results : Array BelowConstant := #[]

  -- Rust: `for ci in 0..n_classes.min(canonical_recs.len())` — the
  -- extract+zipIdx form walks the same index range (`(Name ×
  -- RecursorVal)` has no `Inhabited`, so `[ci]!` indexing is
  -- unavailable).
  for (pair, ci) in
      (canonicalRecs.extract 0 (min nClasses canonicalRecs.size)).zipIdx do
    let (_, recVal) := pair
    let classRep := sortedClasses[ci]![0]!

    let ind ←
      match ← lookupConst? classRep with
      | some (.inductInfo v) => pure v
      | _ =>
        -- Rust: MissingConstant { caller: "generate_below_constants:
        -- class rep not an inductive" }
        throw (CompileError.missingConstant classRep.pretty)

    let belowName := Name.mkStr ind.cnst.name "below"

    if !isProp then
      -- Type-level: generate definition (BRecOn.lean path)
      let d ← buildBelowDef belowName recVal ind nClasses canonicalRecs maps
      results := results.push (.defn d)
    else
      -- Prop-level: generate .below inductive (IndPredBelow.lean path)
      let indc ← buildBelowIndc ci belowName recVal ind nClasses
        sortedClasses canonicalRecs
      results := results.push (.indc indc)

  -- Generate .below_N for nested auxiliary members (Type-level only).
  -- Lean generates these via mkBelowFromRec for each nested auxiliary
  -- recursor (BRecOn.lean:125-129). They're always definitions, even for
  -- Prop-level blocks, but we only implement Type-level for now.
  --
  -- The auxiliary recursors are at canonicalRecs[nClasses..]. Each gets
  -- a 1-based suffix: .below_1, .below_2, etc., hanging off the first
  -- inductive in the block.
  if !isProp then
    let nAux := canonicalRecs.size - nClasses
    if nAux > 0 then
      let firstClassName := sortedClasses[0]![0]!
      let firstInd ←
        match ← lookupConst? firstClassName with
        | some (.inductInfo v) => pure v
        | _ =>
          -- Rust: MissingConstant { caller: "generate_below_constants:
          -- first class rep not an inductive" }
          throw (CompileError.missingConstant firstClassName.pretty)
      -- Lean hangs _N suffixed names off all[0] (first in source order),
      -- not the canonical class representative.
      let all0 := firstInd.all[0]!
      -- Rust: `for j in 0..n_aux { &canonical_recs[n_classes + j] }`.
      for (pair, j) in
          (canonicalRecs.extract nClasses canonicalRecs.size).zipIdx do
        let (auxRecName, auxRecVal) := pair

        -- The aux rec's suffix is already Lean-source-indexed by
        -- `generateAuxPatches` (it renames `_nested.X.rec` →
        -- `<all0>.rec_{source_j+1}` via `canonRepr`). So `below_N`'s N
        -- matches the aux rec's N — just swap the leading `rec` with
        -- `below`. This keeps below and rec in lockstep with Lean's
        -- source naming.
        let some idx := auxRecSuffixIdx auxRecName
          | throw (CompileError.invalidMutualBlock
              s!"below aux recursor '{auxRecName.pretty}' is not \
source-indexed; refusing to synthesize below_{j + 1}")
        let belowName := Name.mkStr all0 s!"below_{idx}"

        -- Only generate if this constant exists in the source
        -- environment. Check lean_env (original Lean env during
        -- compilation) OR stt.env.named (Ixon compile state — has all
        -- constants during decompilation where lean_env is the
        -- incrementally-built work_env and won't contain the constant
        -- we're about to generate).
        let cenv ← Ix.CompileM.getCompileEnv
        let existsInEnv := (← lookupConst? belowName).isSome
          || cenv.nameToNamed.contains belowName
        if existsInEnv then
          -- Extract the actual external inductive from the auxiliary
          -- recursor's major premise. The major is the last binder in
          -- the rec type: `∀ ... (t : ExtInd spec_params indices), ...`.
          -- We need the external ind for the ilvl fallback path in
          -- buildBelowDef, which uses ind.cnst.type to extract the sort.
          let some extInd ← extractMajorHeadInd auxRecVal
            | throw (CompileError.unsupportedExpr
                s!"below_{idx}: cannot extract head inductive from \
auxiliary recursor major premise")

          let d ← buildBelowDef belowName auxRecVal extInd nClasses
            canonicalRecs maps
          results := results.push (.defn d)

  return results

end Ix.AuxGen

end
