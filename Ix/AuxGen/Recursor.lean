/-
  Ix.AuxGen.Recursor: canonical recursor generation for alpha-collapsed
  inductive blocks.

  Port of `crates/compile/src/compile/aux_gen/recursor.rs` (the
  recursor-regeneration core), plus the kernel-backed
  `decompose_inductive_type` from `aux_gen/expr_utils.rs:121` (deliberately
  left out of the pure `Ix.AuxGen.ExprUtils` — it belongs with the recursor
  machinery), plus `CompileFlatMember` / `build_compile_flat_block(_with_overlay)`
  from `aux_gen/nested.rs:37/:1723` (the flat-block discovery that
  `generate_canonical_recursors_with_layout` falls back to when no pre-built
  flat block is supplied; `Ix.AuxGen.Nested` predates this milestone and is
  frozen, so those pieces live here).

  Regenerates a `RecursorVal` from canonical class structure, producing
  identical output regardless of source declaration order. Closely follows
  `refs/lean4/src/kernel/inductive.cpp:589-776` (`mk_rec_infos`,
  `mk_rec_rules`, `declare_recursors`); like the Rust, all intermediate
  computation is FVar-based (see `Ix.AuxGen.ExprUtils`) and abstracted back
  into de Bruijn binder chains at the end.

  Monad discipline: pure helpers stay pure; everything that touches the
  kernel bridge (TcScope WHNF, kenv ingress, `is_large_eliminator`) runs in
  `KBridgeM` (`Ix.AuxGen.Kernel`). Rust's `lean_env` parameter becomes the
  CompileM environment (`lookupConst?`); `overlay: Option<&LeanEnv>` becomes
  `Option (Std.HashMap Name ConstantInfo)`; `stt`'s name→address views
  become `AddrMaps`; `kctx: &mut KernelCtx` is the KBridgeM state.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Level.mkParam`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
-/
module
public import Ix.AuxGen.Kernel
public section

namespace Ix.AuxGen

open Ix.CompileM (CompileM CompileError)

/-! ## Environment view (overlay + base env)

Rust threads `lean_env: &LeanEnv` and `overlay: Option<&LeanEnv>` and looks
constants up via the `env_get` closure (recursor.rs:479-483, :955-959).
The Lean port reads the base env from CompileM (`lookupConst?`) and takes
the overlay as an explicit map. -/

/-- Mirrors the Rust `env_get` closure (recursor.rs:479): check the overlay
    first, then the base compile environment. -/
def envGet (overlay : Option (Std.HashMap Name ConstantInfo)) (name : Name) :
    CompileM (Option ConstantInfo) := do
  match overlay.bind (·.get? name) with
  | some ci => return some ci
  | none => lookupConst? name

/-! ## Inductive recursor-structural decomposition (kernel-backed) -/

/-- Mirrors Rust `decompose_inductive_type` (aux_gen/expr_utils.rs:121).

    Decompose an inductive's stored type into its recursor-structural
    pieces (`IndRecInfo`), peeling params (using the caller-supplied
    `paramFvars` LocalDecls) then all remaining leading `Pi`s as indices,
    with kernel WHNF between steps. Mirrors `mk_rec_infos` in
    `refs/lean4/src/kernel/inductive.cpp:588-618`.

    Syntactic-first peeling: WHNF is only invoked when the current head
    is not already a forall (to expose hidden Pis behind reducible-alias
    targets like `Set σ := σ → Prop`) — unconditional WHNF would drift
    the regenerated binders away from the source-shape form and risk
    alpha-twin display-name aliasing through the kernel cache.

    Errors (`CompileError.invalidMutualBlock`, matching Rust):
    - fewer Pi binders than `paramFvars.size` (even after WHNF);
    - the final body isn't a `Sort` after peeling every leading Pi. -/
def decomposeInductiveType (ind : InductiveVal) (indUnivs : Array Level)
    (paramFvars : Array LocalDecl) (maps : AddrMaps) : KBridgeM IndRecInfo := do
  let nParams := paramFvars.size
  let ty := substLevels ind.cnst.type ind.cnst.levelParams indUnivs

  -- TcScope pre-populated with the caller's param FVars. As we peel
  -- indices, each is pushed into the scope so subsequent `whnfLean` calls
  -- see them as locals.
  let mut scope ← TcScopeSt.new paramFvars ind.cnst.levelParams maps

  let mut cur := ty
  if !(cur matches .forallE ..) then
    cur ← scope.whnfLean cur

  -- Instantiate `nParams` leading Pi's with the caller's param FVars.
  -- No WHNF between substitutions unless a post-substitution head is
  -- non-Pi (targeted delta-unfold).
  for p in [0:nParams] do
    match cur with
    | .forallE _ _ body _ _ =>
      let paramFv := Expr.mkFVar paramFvars[p]!.fvarName
      cur := instantiate1 body paramFv
      if !(cur matches .forallE ..) then
        cur ← scope.whnfLean cur
    | _ =>
      throw (.invalidMutualBlock
        s!"decompose_inductive_type({ind.cnst.name.pretty}): fewer than \
{nParams} param foralls in stored type (peeled {p} before hitting non-Pi)")

  -- Peel all remaining leading Pi's as indices (no imposed count; the
  -- stored `numIndices` is informational). Same syntactic-first /
  -- WHNF-on-stuck pattern as above.
  let mut indices : Array LocalDecl := #[]
  let mut idxI : Nat := 0
  repeat
    if !(cur matches .forallE ..) then
      let after ← scope.whnfLean cur
      if !(after matches .forallE ..) then
        cur := after
        break
      cur := after
    match cur with
    | .forallE name dom body bi _ =>
      let (fvName, fv) := freshFVar "idx" idxI
      let decl : LocalDecl :=
        { fvarName := fvName, binderName := name, domain := dom, info := bi }
      scope ← scope.pushLocals #[decl]
      indices := indices.push decl
      cur := instantiate1 body fv
      idxI := idxI + 1
    | _ => break

  -- Target sort.
  if !(cur matches .sort ..) then
    throw (.invalidMutualBlock
      s!"decompose_inductive_type({ind.cnst.name.pretty}): peeled {nParams} \
params + {indices.size} indices; expected remaining body to be a Sort, got \
something else")

  -- Major domain: `I params indices`, all FVars.
  let mut majorDom := mkConst ind.cnst.name indUnivs
  for p in paramFvars do
    majorDom := Expr.mkApp majorDom (Expr.mkFVar p.fvarName)
  for ix in indices do
    majorDom := Expr.mkApp majorDom (Expr.mkFVar ix.fvarName)

  let (majorFvName, _) := freshFVar "major" (nParams + indices.size)
  let major : LocalDecl :=
    { fvarName := majorFvName
      binderName := Name.mkStr .mkAnon "t"
      domain := majorDom
      info := .default }

  return { indices, major }

/-! ## Flat block construction (aux_gen/nested.rs:37, :1696-2117)

`Ix.AuxGen.Nested` covers the expand/restore model but not the legacy
flat-block detector that `generate_canonical_recursors_with_layout` falls
back to when `preFlat` is `none` (used by `compile_below_recursors` and
the no-nested standard path). Ported here since Nested.lean is frozen. -/

/-- Mirrors Rust `CompileFlatMember` (aux_gen/nested.rs:37).

    A member of the flat block (original inductive or nested auxiliary).
    Spec_params use BVars relative to the block's parameter context:
    `BVar(0)` = innermost (last) param, `BVar(nParams-1)` = outermost. -/
structure CompileFlatMember where
  name : Name
  specParams : Array Expr
  occurrenceLevelArgs : Array Level
  ownParams : Nat
  nIndices : Nat
  deriving Repr, Nonempty, Inhabited

/-- Mirrors Rust `FvarFlatMember` (aux_gen/nested.rs:1702).
    Internal flat member during detection — spec_params in FVar form. -/
structure FvarFlatMember where
  name : Name
  /-- Spec_params as FVar expressions referencing block param FVars. -/
  specParams : Array Expr
  occurrenceLevelArgs : Array Level
  ownParams : Nat
  nIndices : Nat
  deriving Repr, Nonempty, Inhabited

/-- Mirrors Rust `abstract_spec_params_to_bvars` (aux_gen/nested.rs:1920).

    Convert spec_params from FVar form (referencing block-param FVars) back
    to BVar form using batch abstraction: outermost param `_bp_0` ends up
    at `BVar(nParams - 1)`, innermost at `BVar(0)`. -/
def abstractSpecParamsToBVars (specParams : Array Expr)
    (blockParamDecls : Array LocalDecl) : Array Expr :=
  let n := blockParamDecls.size
  if n == 0 then specParams
  else
    let fvarMap : Std.HashMap Name Nat :=
      blockParamDecls.zipIdx.foldl (init := {}) fun m (d, i) =>
        m.insert d.fvarName i
    specParams.map fun sp => batchAbstract sp fvarMap n 0

/-- Mirrors Rust `level_max_raw` (aux_gen/nested.rs:1989, local fn inside
    `maximize_occurrence_levels`): `max(a, b)` with only zero elimination,
    matching Lean's `mkLevelMax` behavior. -/
def levelMaxRaw (a b : Level) : Level :=
  if a == b then a
  else if a matches .zero _ then b
  else if b matches .zero _ then a
  else Level.mkMax a b

/-- Mirrors Rust `maximize_occurrence_levels` (aux_gen/nested.rs:1958).

    Maximize occurrence levels across all auxiliaries sharing the same
    external inductive name: pointwise `levelMaxRaw` of
    `occurrenceLevelArgs` across all auxiliaries with the same `name`,
    then apply the merged levels to all of them. -/
def maximizeOccurrenceLevels (flat : Array FvarFlatMember) (nOriginals : Nat) :
    Array FvarFlatMember := Id.run do
  -- Group auxiliary members by external inductive name.
  let mut maxLevels : Std.HashMap Name (Array Level) := {}
  for entry in flat.extract nOriginals flat.size do
    -- Rust `entry().or_insert_with(occ)` then pointwise max when lengths
    -- match; on the fresh insert the max is `max(x, x) = x`.
    let merged := (maxLevels.get? entry.name).getD entry.occurrenceLevelArgs
    let merged :=
      if merged.size == entry.occurrenceLevelArgs.size then
        (merged.zip entry.occurrenceLevelArgs).map fun (m, e) => levelMaxRaw m e
      else merged
    maxLevels := maxLevels.insert entry.name merged
  -- Apply the maximized levels to all auxiliaries.
  let mut out : Array FvarFlatMember := #[]
  for (entry, i) in flat.zipIdx do
    if i < nOriginals then
      out := out.push entry
    else
      match maxLevels.get? entry.name with
      | some merged =>
        if merged.size == entry.occurrenceLevelArgs.size then
          out := out.push { entry with occurrenceLevelArgs := merged }
        else
          out := out.push entry
      | none => out := out.push entry
  return out

/-- Mirrors Rust `try_detect_nested_fvar` (aux_gen/nested.rs:2003).

    Check if a field domain contains a nested inductive occurrence and, if
    so, add an auxiliary entry to the flat block. A nested occurrence is:
    after peeling foralls, the result is `ExtInd args` where `ExtInd` is a
    previously-declared inductive (not in our block) and some parameter arg
    mentions an original block inductive. Rust mutates `flat`/`aux_seen`
    in place; here they are passed and returned. -/
def tryDetectNestedFVar (dom : Expr) (blockNames : Std.HashSet Name)
    (flat : Array FvarFlatMember) (auxSeen : Array (Name × Array Address))
    (overlay : Option (Std.HashMap Name ConstantInfo))
    (blockParamFvarNames : Array Name) :
    CompileM (Array FvarFlatMember × Array (Name × Array Address)) := do
  -- Peel foralls structurally to get to the result type. Note: NOT
  -- forallTelescope — peeled binders introduce BVars in the body, which
  -- `hasInvalidSpecRef` flags if they leak into a spec_param.
  let mut cur := dom
  repeat
    match cur with
    | .forallE _ _ body _ _ => cur := body
    | _ => break

  let (head, args) := decomposeApps cur
  let .const headName headLevels _ := head | return (flat, auxSeen)

  -- Skip if head is in the original block (direct recursive, not nested).
  if blockNames.contains headName then
    return (flat, auxSeen)
  -- Skip if head is already a non-auxiliary flat member.
  if flat.any (fun m => m.name == headName && blockNames.contains m.name) then
    return (flat, auxSeen)

  -- Verify head is an external inductive.
  let (extNParams, extNIndices) ← match ← envGet overlay headName with
    | some (.inductInfo v) => pure (v.numParams, v.numIndices)
    | _ => return (flat, auxSeen)

  -- Must have at least extNParams applied args.
  if args.size < extNParams then
    return (flat, auxSeen)

  -- Some parameter arg must mention an *original* block inductive
  -- (deliberately NOT extended with flat-stored aux names — see the Rust
  -- comment about the `Aesop.RappData` false positive).
  let hasNestedRef :=
    (args.extract 0 extNParams).any (exprMentionsAnyName · blockNames)
  if !hasNestedRef then
    return (flat, auxSeen)

  -- Extract spec_params (first extNParams args) and reject invalid refs
  -- (free BVars from domain-local foralls, non-param FVars).
  let specParams : Array Expr := args.extract 0 extNParams
  for sp in specParams do
    if hasInvalidSpecRef sp blockParamFvarNames then
      return (flat, auxSeen)

  -- Dedup by (ext ind name, spec_param content hashes). FVar naming is
  -- deterministic (_bp_0, _bp_1, ...) so hashing in FVar form is stable.
  let specHashes : Array Address := specParams.map (·.getHash)
  if auxSeen.any (fun (name, hashes) =>
      name == headName && hashes.size == specHashes.size
        && (hashes.zip specHashes).all fun (a, b) => a == b) then
    return (flat, auxSeen)
  let auxSeen := auxSeen.push (headName, specHashes)

  -- Use the raw levels from the Const node in the constructor type.
  let flat := flat.push
    { name := headName
      specParams
      occurrenceLevelArgs := headLevels
      ownParams := extNParams
      nIndices := extNIndices }
  return (flat, auxSeen)

/-- Mirrors Rust `build_compile_flat_block_with_overlay`
    (aux_gen/nested.rs:1734).

    Build a flat block from an ordered list of original inductives:
    originals (in order) followed by auxiliary entries for nested
    occurrences discovered during the queue-based ctor scan. Works in FVar
    space during detection; spec_params are abstracted back to BVar form
    for the returned `CompileFlatMember`s. -/
def buildCompileFlatBlockWithOverlay (orderedOriginals : Array Name)
    (overlay : Option (Std.HashMap Name ConstantInfo)) :
    CompileM (Array CompileFlatMember) := do
  let some firstName := orderedOriginals[0]?
    | throw (.invalidMutualBlock "build_compile_flat_block: empty ordered_originals")
  let firstInd ← match ← envGet overlay firstName with
    | some (.inductInfo v) => pure v
    | _ => throw (.missingConstant
        s!"{firstName.pretty} (build_compile_flat_block: first original not \
an inductive)")
  let nParams := firstInd.numParams

  -- Canonical block-parameter FVars from the first inductive's type.
  let (blockParamFvars, blockParamDecls, _) :=
    forallTelescope firstInd.cnst.type nParams "bp" 0
  let blockParamFvarNames : Array Name := blockParamDecls.map (·.fvarName)

  let mut flat : Array FvarFlatMember := #[]
  let mut auxSeen : Array (Name × Array Address) := #[]

  let blockNameSet : Std.HashSet Name :=
    orderedOriginals.foldl (init := {}) (·.insert ·)

  -- Seed with original block inductives (identity specialization).
  for name in orderedOriginals do
    let ind ← match ← envGet overlay name with
      | some (.inductInfo v) => pure v
      | _ => throw (.missingConstant
          s!"{name.pretty} (build_compile_flat_block: original not an \
inductive)")
    flat := flat.push
      { name
        specParams := blockParamFvars
        occurrenceLevelArgs := ind.cnst.levelParams.map Level.mkParam
        ownParams := ind.numParams
        nIndices := ind.numIndices }

  -- Queue-based processing: scan each member's constructors for nested
  -- occurrences; new auxiliary entries are appended and processed later.
  let mut qi := 0
  while qi < flat.size do
    let member := flat[qi]!
    qi := qi + 1

    let (ctorNames, levelParams) ← match ← envGet overlay member.name with
      | some (.inductInfo v) => pure (v.ctors, v.cnst.levelParams)
      | _ => continue

    for ctorName in ctorNames do
      let (ctorNFields, ctorTyp) ← match ← envGet overlay ctorName with
        | some (.ctorInfo c) => pure (c.numFields, c.cnst.type)
        | _ => continue

      -- Substitute the external inductive's level params with the concrete
      -- universe args from the occurrence.
      let ctorTyInst := substLevels ctorTyp levelParams member.occurrenceLevelArgs

      -- Peel ownParams foralls, substituting with FVar-form spec_params.
      let mut cur := ctorTyInst
      for j in [0:member.ownParams] do
        match cur with
        | .forallE _ _ body _ _ =>
          if j < member.specParams.size then
            cur := instantiate1 body member.specParams[j]!
          else
            continue -- Shouldn't happen for well-formed types.
        | _ => break

      -- Open field foralls into FVars; each field domain is now in FVar
      -- space (block-param FVars + earlier-field FVars).
      let (_, fieldDecls, _) := forallTelescope cur ctorNFields "nf" 0

      for decl in fieldDecls do
        let (flat', auxSeen') ← tryDetectNestedFVar decl.domain blockNameSet
          flat auxSeen overlay blockParamFvarNames
        flat := flat'
        auxSeen := auxSeen'

  -- Maximize occurrence levels per external inductive name.
  flat := maximizeOccurrenceLevels flat orderedOriginals.size

  -- Convert FVar-form spec_params back to BVar form for the output.
  return flat.map fun entry =>
    { name := entry.name
      specParams := abstractSpecParamsToBVars entry.specParams blockParamDecls
      occurrenceLevelArgs := entry.occurrenceLevelArgs
      ownParams := entry.ownParams
      nIndices := entry.nIndices }

/-- Mirrors Rust `build_compile_flat_block` (aux_gen/nested.rs:1723). -/
def buildCompileFlatBlock (orderedOriginals : Array Name) :
    CompileM (Array CompileFlatMember) :=
  buildCompileFlatBlockWithOverlay orderedOriginals none

/-! ## Flat-block info for recursor generation -/

/-- Mirrors Rust `FlatInfo` (recursor.rs:253).
    Info about one member of the flat block (original or auxiliary). -/
structure FlatInfo where
  /-- Name of the inductive (originals: the class rep; aux: external ind). -/
  name : Name
  /-- `InductiveVal` from the (overlay-first) environment. -/
  ind : InductiveVal
  /-- Constructors from the (overlay-first) environment. -/
  ctors : Array ConstructorVal
  /-- All inductive names in the equivalence class (for rec target
      detection). For auxiliaries: just the external inductive name. -/
  allNames : Array Name
  /-- True if this is an auxiliary member (nested occurrence). -/
  isAux : Bool
  /-- Specialized parameter expressions (empty for originals, concrete
      args like `[Syntax]` for auxiliaries). -/
  specParams : Array Expr
  /-- Concrete universe level args from the nested occurrence. Empty for
      originals (use `indUnivs` instead). -/
  occurrenceLevelArgs : Array Level
  /-- Number of params for this member's inductive (may differ from block
      params for auxiliaries). -/
  ownParams : Nat
  /-- Number of indices for this member's inductive. -/
  nIndices : Nat

/-- Manual instance (`InductiveVal`/`ConstructorVal` don't derive
    `Inhabited`); needed for panicking `classes[i]!` indexing, which
    mirrors Rust's panicking `classes[i]`. -/
instance : Inhabited FlatInfo where
  default :=
    { name := default
      ind :=
        { cnst := { name := default, levelParams := #[], type := default }
          numParams := 0
          numIndices := 0
          all := #[]
          ctors := #[]
          numNested := 0
          isRec := false
          isUnsafe := false
          isReflexive := false }
      ctors := #[]
      allNames := #[]
      isAux := false
      specParams := #[]
      occurrenceLevelArgs := #[]
      ownParams := 0
      nIndices := 0 }

/-- Manual instance for panicking `ctors[0]!` indexing in
    `computeIsLargeAndK` (mirrors Rust's panicking index). -/
instance : Inhabited ConstructorVal where
  default :=
    { cnst := { name := default, levelParams := #[], type := default }
      induct := default
      cidx := 0
      numParams := 0
      numFields := 0
      isUnsafe := false }

/-- Mirrors Rust `NestedRewriteCtx` (recursor.rs:213).

    Shared state for rewriting nested-aux Const level args across every
    ctor and recursor rule in a block. `auxInfo`/`blockNames` depend only
    on the block's classes, so a single `walkCache` amortises the DAG walk
    across every rewrite site (`rewriteNestedConstLevelsCached`). -/
structure NestedRewriteCtx where
  auxInfo : Std.HashMap Name (Nat × Array Level)
  blockNames : Std.HashSet Name
  walkCache : ExprCache

namespace NestedRewriteCtx

/-- Mirrors Rust `NestedRewriteCtx::new` (recursor.rs:220).

    `none` signals "nothing to rewrite" — either the block has no aux
    members or every member is an aux; both imply the
    `rewrite_nested_const_levels` gate is false at every caller. -/
def new (classes : Array FlatInfo) (nClasses : Nat) : Option NestedRewriteCtx :=
  let hasAux := classes.any (·.isAux)
  let hasUser := (classes.extract 0 nClasses).any (fun c => !c.isAux)
  if !hasAux || !hasUser then
    none
  else
    some
      { blockNames := (classes.extract 0 nClasses).foldl (init := {})
          fun s c => s.insert c.name
        auxInfo := classes.foldl (init := {}) fun m c =>
          if c.isAux then m.insert c.name (c.ownParams, c.occurrenceLevelArgs)
          else m
        walkCache := {} }

/-- Mirrors Rust `NestedRewriteCtx::rewrite` (recursor.rs:242).
    Rust mutates the ctx's `walk_cache` through `&mut self`; here the
    updated ctx is returned alongside the result. -/
def rewrite (ctx : NestedRewriteCtx) (expr : Expr) : Expr × NestedRewriteCtx :=
  let (result, cache) :=
    (rewriteNestedConstLevelsCached expr ctx.auxInfo ctx.blockNames).run
      ctx.walkCache
  (result, { ctx with walkCache := cache })

end NestedRewriteCtx

/-! ## Binder info collected from types (recursor.rs:876) -/

/-- Mirrors Rust `Binder` (recursor.rs:885).
    A binder extracted from a forall chain. `name` and `domain` are
    retained for parity (dead in Rust too — only `info` is consumed). -/
structure Binder where
  name : Name
  domain : Expr
  info : Lean.BinderInfo
  deriving Nonempty, Inhabited

/-- Mirrors Rust `collect_binders` (recursor.rs:894).
    Collect the first `n` forall binders from an expression, stripping
    outParam/semiOutParam/optParam/autoParam wrappers from domains
    (Lean's `consume_type_annotations` in `mk_local_decl`,
    inductive.cpp:179). -/
def collectBinders (expr : Expr) (n : Nat) : Array Binder := Id.run do
  let mut binders : Array Binder := #[]
  let mut cur := expr
  for _ in [0:n] do
    match cur with
    | .forallE name dom body bi _ =>
      let cleanDom := consumeTypeAnnotations dom
      binders := binders.push { name, domain := cleanDom, info := bi }
      cur := body
    | _ => break
  return binders

/-! ## Name helpers (recursor.rs:2001) -/

/-- Mirrors Rust `has_deeper_str` (recursor.rs:2039).
    Check if a Name has any `Str` component deeper in its structure. -/
partial def hasDeeperStr (n : Name) : Bool :=
  match n with
  | .anonymous _ => false
  | .str _ _ _ => true
  | .num parent _ _ => hasDeeperStr parent

/-- Mirrors Rust `name_append_after` (recursor.rs:2021).

    Lean's `appendAfter`: append a suffix to the DEEPEST string component
    of a Name, recursing through `Num`/`Str` wrappers (matches Lean 4.26's
    kernel behavior on hygienic names like
    `Num(Str(Str(Str(Str(Anon,"a"),"_@"),"_internal"),"_hyg"),0)`). -/
partial def nameAppendAfter (n : Name) (suffix : String) : Name :=
  match n with
  | .anonymous _ => Name.mkStr n suffix
  | .str parent s _ =>
    if hasDeeperStr parent then
      Name.mkStr (nameAppendAfter parent suffix) s
    else
      -- This is the deepest Str — append suffix to its string.
      Name.mkStr parent (s ++ suffix)
  | .num parent num _ =>
    Name.mkNat (nameAppendAfter parent suffix) num

/-! ## inferImplicit (recursor.rs:2200) -/

/-- Mirrors Rust `expr_has_loose_bvar` (recursor.rs:2290).
    Check if `BVar(target)` appears anywhere in `e`. -/
partial def exprHasLooseBVar (e : Expr) (target : Nat) : Bool :=
  match e with
  | .bvar idx _ => idx == target
  | .app f a _ => exprHasLooseBVar f target || exprHasLooseBVar a target
  | .lam _ t b _ _ | .forallE _ t b _ _ =>
    exprHasLooseBVar t target || exprHasLooseBVar b (target + 1)
  | .letE _ t v b _ _ =>
    exprHasLooseBVar t target || exprHasLooseBVar v target
      || exprHasLooseBVar b (target + 1)
  | .proj _ _ e' _ | .mdata _ e' _ => exprHasLooseBVar e' target
  | _ => false

/-- Mirrors Rust `has_loose_bvar_in_explicit_domain` (recursor.rs:2241).

    Check if `BVar(target)` appears free in an explicit binder domain
    within `e`. `strict = true`: only domains count; `strict = false`:
    the range counts too. Includes the C++ kernel's transitivity rule for
    implicit-binder chains (`refs/lean4/src/kernel/expr.cpp:480-500`). -/
partial def hasLooseBVarInExplicitDomain (e : Expr) (target : Nat)
    (strict : Bool) : Bool :=
  match e with
  | .bvar idx _ =>
    if strict then
      false -- In strict mode, bare BVars in the range don't count.
    else
      idx == target
  | .forallE _ dom body bi _ => Id.run do
    -- Check if target appears in this binder's domain (any binder info).
    if exprHasLooseBVar dom target then
      if bi matches .default then
        -- Explicit domain contains target — mark as implicit.
        return true
      else if hasLooseBVarInExplicitDomain body 0 strict then
        -- Transitivity: target appears in an implicit binder's domain and
        -- that binder's own variable feeds an explicit domain downstream.
        return true
    -- Continue searching in the body with shifted target.
    return hasLooseBVarInExplicitDomain body (target + 1) strict
  | .app f a _ =>
    if strict then
      false -- In strict mode, apps in the range don't count.
    else
      exprHasLooseBVar f target || exprHasLooseBVar a target
  | _ =>
    if strict then false
    else exprHasLooseBVar e target

/-- Mirrors Rust `infer_implicit` (recursor.rs:2208).

    Port of Lean's `inferImplicit(ty, numParams, strict=false)`
    (`refs/lean4/src/Lean/Expr.lean:1362-1368`): marks explicit binders
    implicit when the binder's own BVar appears in an explicit domain
    downstream. -/
partial def inferImplicit (ty : Expr) (numParams : Nat) : Expr :=
  if numParams == 0 then ty
  else match ty with
  | .forallE name dom body bi _ =>
    let newBody := inferImplicit body (numParams - 1)
    let newBi :=
      if (bi matches .default)
          && hasLooseBVarInExplicitDomain newBody 0 true then
        Lean.BinderInfo.implicit
      else bi
    Expr.mkForallE name dom newBody newBi
  | _ => ty

/-! ## Recursive-target detection (recursor.rs:2047) -/

/-- Mirrors Rust `match_classes_against_app` (recursor.rs:2160).

    Match an `App`-spine against the block's classes by source name.
    If the head is a `Const` in some `class.allNames`, validate the
    param/spec_param slots against the recursor's outer params and return
    the class index. -/
def matchClassesAgainstApp (ty : Expr) (classes : Array FlatInfo)
    (paramFvars : Array Expr) (nParams : Nat) : Option Nat := Id.run do
  let (head, args) := decomposeApps ty
  let .const name _ _ := head | return none
  for (class_, ci) in classes.zipIdx do
    if !class_.allNames.any (· == name) then
      continue
    if !class_.isAux then
      if args.size >= nParams
          && ((args.extract 0 nParams).zip paramFvars).all
            (fun (a, p) => a.getHash == p.getHash) then
        return some ci
      continue
    let spFvars := instantiateSpecWithFVars class_.specParams paramFvars
    let nPar := class_.ownParams
    if args.size >= nPar && spFvars.size == nPar
        && ((args.extract 0 nPar).zip spFvars).all
          (fun (a, sp) => a.getHash == sp.getHash) then
      return some ci
  return none

/-- Mirrors Rust `find_rec_target` (recursor.rs:2093).

    Detect whether a constructor field's type targets one of the block's
    inductives (returning its class index). Two-phase strategy: Phase 1
    peels foralls syntactically and matches the source-name head directly
    (immune to WHNF-cache display-name aliasing under alpha-collapse);
    Phase 2 (kernel WHNF) only runs when Phase 1 finds nothing — the
    reducible-alias-head case. A warming `whnfLean dom` runs even on a
    Phase 1 hit so downstream `buildIhTypeFVar`/`buildRuleIhFVar` WHNFs
    are cache-hot. The scope is left balanced. Mirrors
    `kernel/inductive.cpp::is_rec_argument`. -/
def findRecTarget (dom : Expr) (classes : Array FlatInfo)
    (paramFvars : Array Expr) (nParams : Nat) (scope : TcScopeSt) :
    KBridgeM (Option Nat × TcScopeSt) := do
  let mut scope := scope
  -- Phase 1: syntactic peel + match.
  let mut ty := dom
  let mut phase1Match : Option Nat := none
  repeat
    if let some ci := matchClassesAgainstApp ty classes paramFvars nParams then
      phase1Match := some ci
      break
    match ty with
    | .forallE _ _ body _ _ =>
      let (_, fv) := freshFVar "frt_syn" 0
      ty := instantiate1 body fv
    | _ => break

  -- Pre-warm the kernel cache for `dom` (result discarded; see Rust doc).
  discard <| scope.whnfLean dom

  if let some ci := phase1Match then
    return (some ci, scope)

  -- Phase 2: WHNF fallback for reducible-alias heads.
  let mut ty2 ← scope.whnfLean dom
  let mut pushed : Array LocalDecl := #[]
  repeat
    match ty2 with
    | .forallE name d body bi _ =>
      let (fvName, fv) := freshFVar "frt" pushed.size
      let decl : LocalDecl :=
        { fvarName := fvName, binderName := name, domain := d, info := bi }
      scope ← scope.pushLocals #[decl]
      pushed := pushed.push decl
      ty2 ← scope.whnfLean (instantiate1 body fv)
    | _ => break
  scope ← scope.popLocals pushed
  return (matchClassesAgainstApp ty2 classes paramFvars nParams, scope)

/-! ## Motive types (recursor.rs:1194) -/

/-- Mirrors Rust `build_motive_type` (recursor.rs:1207).

    `∀ (indices...) (t : I params indices), Sort elimLevel` from a
    pre-computed `IndRecInfo` (cf. `mk_C` in inductive.cpp:609-615). The
    result contains param FVars free; the caller abstracts them. -/
def buildMotiveType (indInfo : IndRecInfo) (elimLevel : Level) : Expr :=
  let sort := Expr.mkSort elimLevel
  let decls : Array LocalDecl := indInfo.indices.push indInfo.major
  mkForall sort decls

/-- Mirrors Rust `build_motive_type_aux` (recursor.rs:1226).

    Motive type for an auxiliary (nested) flat member: for a nested
    occurrence `J Ds` the motive type is
    `∀ (indices...) (t : J Ds indices), Sort u`, with `Ds` the FVar-form
    spec_params. Uses FVar-based index peeling so dependent index domains
    are correctly instantiated. -/
def buildMotiveTypeAux (member : FlatInfo) (_nParams : Nat) (elimLevel : Level)
    (_indUnivs : Array Level) (overlay : Option (Std.HashMap Name ConstantInfo))
    (paramFvars : Array Expr) : CompileM Expr := do
  -- Look up the external inductive (overlay first for expanded aux types).
  let ind ← match ← envGet overlay member.name with
    | some (.inductInfo v) => pure v
    | _ => return Expr.mkSort Level.mkZero -- fallback
  let nExtParams := member.ownParams
  let nExtIndices := member.nIndices

  -- Substitute levels with the concrete occurrence levels.
  let ty :=
    if !member.occurrenceLevelArgs.isEmpty then
      substLevels ind.cnst.type ind.cnst.levelParams member.occurrenceLevelArgs
    else
      ind.cnst.type

  -- Skip params, substituting with spec_params in FVar form.
  let specFvars := instantiateSpecWithFVars member.specParams paramFvars
  let mut cur := ty
  for p in [0:nExtParams] do
    if let .forallE _ _ body _ _ := cur then
      if p < specFvars.size then
        cur := instantiate1 body specFvars[p]!
      else
        cur := instantiate1 body (Expr.mkSort Level.mkZero) -- placeholder
  -- Beta-reduce after spec_param instantiation (lambda-valued spec_params
  -- create unreduced redexes that may obstruct the telescope below).
  cur := betaReduce cur
  -- Peel index binders using FVars.
  let (indexFvars, indexDecls, _) := forallTelescope cur nExtIndices "ma_idx" 0

  -- Major type: `J.{occurrence_us} spec_params index_fvars`.
  let majorUnivs :=
    if !member.occurrenceLevelArgs.isEmpty then
      member.occurrenceLevelArgs
    else
      -- Fallback: identity-mapped level params (shouldn't be reached for
      -- proper aux members).
      ind.cnst.levelParams.map Level.mkParam
  let mut majorTy := mkConst member.name majorUnivs
  for sp in specFvars do
    majorTy := Expr.mkApp majorTy sp
  for idxFv in indexFvars do
    majorTy := Expr.mkApp majorTy idxFv

  -- `∀ (indices...) (major : majorTy), Sort elimLevel`.
  let sort := Expr.mkSort elimLevel
  let majorDecl : LocalDecl :=
    { fvarName := Name.mkStr .mkAnon "_ma_major_0"
      binderName := Name.mkStr .mkAnon "t"
      domain := majorTy
      info := .default }
  let mut allDecls : Array LocalDecl := #[]
  allDecls := allDecls ++ indexDecls
  allDecls := allDecls.push majorDecl
  return mkForall sort allDecls

/-! ## IH types (recursor.rs:1536) -/

/-- Mirrors Rust `build_ih_type_fvar` (recursor.rs:1550).

    IH type for a recursive field, with kernel WHNF between binder peels
    (so reducible-alias heads unfold — `kernel/inductive.cpp::is_rec_argument`
    behavior): `∀ (xs...), motive[target] idx_args (field xs)`. The scope
    is borrowed across fields of one constructor (Rust `&mut`); here the
    updated scope is returned. -/
def buildIhTypeFVar (fieldFvar fieldDom : Expr) (targetCi : Nat)
    (_nParams : Nat) (_paramFvars : Array Expr) (motiveFvars : Array Expr)
    (classes : Array FlatInfo) (scope : TcScopeSt) :
    KBridgeM (Expr × TcScopeSt) := do
  let mut scope := scope
  let mut xsFvars : Array Expr := #[]
  let mut xsDecls : Array LocalDecl := #[]
  let mut cur ← scope.whnfLean fieldDom

  repeat
    match cur with
    | .forallE name dom body bi _ =>
      -- Check if the expression head is an inductive in the block — stop
      -- if so. (Ported verbatim from Rust; a forall head can never be a
      -- Const so this guard cannot fire, but omitting it would be a
      -- silent divergence.)
      let (h, _) := decomposeApps cur
      let mut isBlockHead := false
      if let .const cname _ _ := h then
        if classes.any (fun c => c.allNames.any (· == cname)) then
          isBlockHead := true
      if isBlockHead then
        break
      let (fvName, fv) := freshFVar "ih_xs" xsFvars.size
      let decl : LocalDecl :=
        { fvarName := fvName, binderName := name, domain := dom, info := bi }
      scope ← scope.pushLocals #[decl]
      xsDecls := xsDecls.push decl
      xsFvars := xsFvars.push fv
      cur ← scope.whnfLean (instantiate1 body fv)
    | _ => break

  -- Pop the xs decls so the scope stays balanced for the next field.
  scope ← scope.popLocals xsDecls

  -- `cur` is now the fully FVar-instantiated inner: I params idx_args.
  let (_, innerArgs) := decomposeApps cur
  let nTargetParams := classes[targetCi]!.ind.numParams
  let idxArgs : Array Expr := innerArgs.extract nTargetParams innerArgs.size

  -- IH body: motive[target](idx_args, field xs_fvars).
  let mut ihBody := motiveFvars[targetCi]!
  for idx in idxArgs do
    ihBody := Expr.mkApp ihBody idx
  let mut fieldApp := fieldFvar
  for fv in xsFvars do
    fieldApp := Expr.mkApp fieldApp fv
  ihBody := Expr.mkApp ihBody fieldApp

  -- Abstract xs FVars back into foralls, preserving binder names.
  return (mkForall ihBody xsDecls, scope)

/-! ## Minor premise types (recursor.rs:1325) -/

/-- Mirrors Rust `build_minor_type` (recursor.rs:1342).

    Minor premise type for a constructor using FVars:
    `∀ (fields...) (ihs...), motive[classIdx] ret_indices (C params fields)`.
    A single TcScope is built here (seeded with the recursor's shared
    params) and pushed as fields peel, so `findRecTarget` /
    `buildIhTypeFVar` can delta-unfold definition heads in field domains
    (`reduceCtorParam.rec` regression). `nestedRewrite` is the caller-owned
    block-wide rewrite scratch (Rust `Option<&mut NestedRewriteCtx>`),
    threaded through the return value. -/
def buildMinorType (classIdx : Nat) (ctor : ConstructorVal)
    (classes : Array FlatInfo) (nParams : Nat) (_nClasses : Nat)
    (paramFvars : Array Expr) (paramDecls : Array LocalDecl)
    (motiveFvars : Array Expr) (indUnivs : Array Level)
    (recLevelParams : Array Name) (maps : AddrMaps)
    (nestedRewrite : Option NestedRewriteCtx) :
    KBridgeM (Expr × Option NestedRewriteCtx) := do
  let member := classes[classIdx]!
  -- Aux members substitute occurrence levels; originals the block univs.
  let ctorTy :=
    if member.isAux && !member.occurrenceLevelArgs.isEmpty then
      substLevels ctor.cnst.type member.ind.cnst.levelParams
        member.occurrenceLevelArgs
    else
      substLevels ctor.cnst.type member.ind.cnst.levelParams indUnivs

  -- Peel params: originals substitute param FVars; auxiliaries substitute
  -- FVar-converted spec_params.
  let mut cur := ctorTy
  let nCtorParams := ctor.numParams
  let spFvars :=
    if member.isAux then instantiateSpecWithFVars member.specParams paramFvars
    else #[]
  for p in [0:nCtorParams] do
    if let .forallE _ _ body _ _ := cur then
      if member.isAux && p < spFvars.size then
        cur := instantiate1 body spFvars[p]!
      else if p < paramFvars.size then
        cur := instantiate1 body paramFvars[p]!
      else
        cur := instantiate1 body (Expr.mkSort Level.mkZero) -- placeholder
  -- Beta-reduce after spec_param instantiation for auxiliary members.
  if member.isAux then
    cur := betaReduce cur
  -- Rewrite nested type universe levels for original members.
  let mut nestedRewrite := nestedRewrite
  if !member.isAux then
    if let some nr := nestedRewrite then
      let (cur', nr') := nr.rewrite cur
      cur := cur'
      nestedRewrite := some nr'

  -- Collect fields: peel each field with a fresh FVar, detect recursive
  -- fields, and push each decl into the shared TcScope.
  let nFields := ctor.numFields
  let mut fieldDecls : Array LocalDecl := #[]
  let mut fieldFvars : Array Expr := #[]
  let mut recFields : Array (Nat × Nat) := #[] -- (field_idx, target_class)

  let mut scope ← TcScopeSt.new paramDecls recLevelParams maps

  for fi in [0:nFields] do
    match cur with
    | .forallE name dom body bi _ =>
      -- Strip autoParam/optParam/outParam wrappers.
      let cleanDom := consumeTypeAnnotations dom
      let (fvName, fv) := freshFVar "field" fi
      let decl : LocalDecl :=
        { fvarName := fvName, binderName := name, domain := cleanDom, info := bi }
      let (recCi, scope') ← findRecTarget cleanDom classes paramFvars nParams scope
      scope := scope'
      if let some ci := recCi then
        recFields := recFields.push (fi, ci)
      scope ← scope.pushLocals #[decl]
      fieldDecls := fieldDecls.push decl
      fieldFvars := fieldFvars.push fv
      cur := instantiate1 body fv
    | _ => break

  -- Build IH binders for recursive fields. (Rust also collects `ih_fvars`
  -- alongside — never read; not reconstructed here.)
  let mut ihDecls : Array LocalDecl := #[]
  for ((fi, targetCi), k) in recFields.zipIdx do
    let (ihTy, scope') ← buildIhTypeFVar fieldFvars[fi]! fieldDecls[fi]!.domain
      targetCi nParams paramFvars motiveFvars classes scope
    scope := scope'
    -- Lean C++ appendAfter("_ih") on the innermost string component.
    let ihName := nameAppendAfter fieldDecls[fi]!.binderName "_ih"
    let (ihFvName, _ihFv) := freshFVar "ih" k
    ihDecls := ihDecls.push
      { fvarName := ihFvName, binderName := ihName, domain := ihTy
        info := .default }

  -- Conclusion: motive[classIdx](ctor_return_indices, C params fields).
  let mut conclusion := motiveFvars[classIdx]!

  -- Return indices: `cur` is the ctor's return type with FVars; extract
  -- args past params (own_params for aux, block params for originals).
  let skipCount := if member.isAux then member.ownParams else nParams
  let (_, retArgs) := decomposeApps cur
  let retIndices : Array Expr := retArgs.extract skipCount retArgs.size
  for idx in retIndices do
    conclusion := Expr.mkApp conclusion idx

  -- C params/spec_params fields.
  let ctorUnivs :=
    if member.isAux && !member.occurrenceLevelArgs.isEmpty then
      member.occurrenceLevelArgs
    else indUnivs
  let mut ctorApp := mkConst ctor.cnst.name ctorUnivs
  if member.isAux then
    for sp in spFvars do
      ctorApp := Expr.mkApp ctorApp sp
  else
    for pf in paramFvars do
      ctorApp := Expr.mkApp ctorApp pf
  for ff in fieldFvars do
    ctorApp := Expr.mkApp ctorApp ff
  conclusion := Expr.mkApp conclusion ctorApp

  -- Fold: ∀ (fields...) (ihs...), conclusion — IHs innermost.
  let mut allBinders : Array LocalDecl := #[]
  allBinders := allBinders ++ fieldDecls
  allBinders := allBinders ++ ihDecls
  return (mkForall conclusion allBinders, nestedRewrite)

/-! ## Recursor type construction (recursor.rs:917) -/

/-- Mirrors Rust `build_rec_type` (recursor.rs:936).

    Full recursor type for flat member `di`:
    `∀ params motives minors indices major, motive_di indices major`, all
    domains kept in FVar form and batch-abstracted by one final `mkForall`.
    Follows `declare_recursors` (inductive.cpp:752-774). `paramFvars` /
    `paramDecls` are shared across every recursor in the block;
    `classInfos` are the WHNF-decomposed `IndRecInfo`s for the original
    classes. Aux recursors (`di >= nClasses`) peel their type in place
    (spec_params substitution). Ends with `inferImplicit(ty, 1000)`. -/
def buildRecType (di : Nat) (classes : Array FlatInfo)
    (flat : Array CompileFlatMember) (nParams nClasses : Nat)
    (_paramBinders : Array Binder) (paramFvars : Array Expr)
    (paramDecls : Array LocalDecl) (classInfos : Array IndRecInfo)
    (elimLevel : Level) (indUnivs : Array Level) (recLevelParams : Array Name)
    (overlay : Option (Std.HashMap Name ConstantInfo)) (maps : AddrMaps)
    (nestedRewrite : Option NestedRewriteCtx) :
    KBridgeM (Expr × Option NestedRewriteCtx) := do
  let nFlat := flat.size

  -- Collect ALL binders in a single array with FVar-based domains;
  -- `mkForall` at the end handles all BVar abstraction in one batch.
  let mut allDecls : Array LocalDecl := #[]

  -- --- Params: shared across recursors in this block ---
  allDecls := allDecls ++ paramDecls

  -- --- Motives (Cs): one per flat member, FVar domains ---
  let mut motiveFvars : Array Expr := #[]
  for j in [0:nFlat] do
    let motiveTy ←
      if j < nClasses then
        pure (buildMotiveType classInfos[j]! elimLevel)
      else
        buildMotiveTypeAux classes[j]! nParams elimLevel indUnivs overlay
          paramFvars
    let motiveName :=
      if nFlat > 1 then
        Name.mkStr .mkAnon s!"motive_{j + 1}"
      else
        Name.mkStr .mkAnon "motive"
    let (fvName, fv) := freshFVar "motive" j
    motiveFvars := motiveFvars.push fv
    allDecls := allDecls.push
      { fvarName := fvName, binderName := motiveName, domain := motiveTy
        info := .default }

  -- --- Minors: for each flat member's constructors, FVar domains ---
  -- `nestedRewrite` is caller-owned and shared across the whole block.
  let mut nestedRewrite := nestedRewrite
  for j in [0:nFlat] do
    let memberCtors : Array ConstructorVal ←
      if j < nClasses then
        pure classes[j]!.ctors
      else do
        match ← envGet overlay flat[j]!.name with
        | some (.inductInfo ind) => do
          let mut cs : Array ConstructorVal := #[]
          for cn in ind.ctors do
            if let some (.ctorInfo c) ← envGet overlay cn then
              cs := cs.push c
          pure cs
        | _ => pure #[]
    let indName := flat[j]!.name
    for ctor in memberCtors do
      let (minorTy, nr') ← buildMinorType j ctor classes nParams nClasses
        paramFvars paramDecls motiveFvars indUnivs recLevelParams maps
        nestedRewrite
      nestedRewrite := nr'
      -- Minor binder name: ctor name with the inductive prefix stripped.
      let minorName :=
        match stripPrefixComponents ctor.cnst.name indName with
        | some suffix =>
          suffix.foldl (init := Name.mkAnon) fun acc c =>
            match c with
            | .inl s => Name.mkStr acc s
            | .inr i => Name.mkNat acc i
        | none => ctor.cnst.name
      let (fvName, _fv) := freshFVar "minor" allDecls.size
      allDecls := allDecls.push
        { fvarName := fvName, binderName := minorName, domain := minorTy
          info := .default }

  -- --- Indices + major for member di ---
  -- Non-aux: drop the pre-computed `IndRecInfo` decls straight in. Aux:
  -- substitute spec_params and peel syntactically (see Rust note about
  -- WHNF-on-reducible-target for aux members — not observed in the wild).
  let diMember := classes[di]!
  let diIsAux := diMember.isAux

  let mut indexFvars : Array Expr := #[]
  let mut majorFv : Expr := default

  if !diIsAux then
    let info := classInfos[di]!
    allDecls := allDecls ++ info.indices
    for d in info.indices do
      indexFvars := indexFvars.push (Expr.mkFVar d.fvarName)
    majorFv := Expr.mkFVar info.major.fvarName
    allDecls := allDecls.push info.major
  else
    -- Legacy aux path: substitute spec_params, peel syntactically.
    let diTy :=
      if !diMember.occurrenceLevelArgs.isEmpty then
        substLevels diMember.ind.cnst.type diMember.ind.cnst.levelParams
          diMember.occurrenceLevelArgs
      else
        substLevels diMember.ind.cnst.type diMember.ind.cnst.levelParams
          indUnivs
    let mut ity := diTy
    let diNExtParams := diMember.ownParams
    let diSpFvars := instantiateSpecWithFVars diMember.specParams paramFvars
    for p in [0:diNExtParams] do
      if let .forallE _ _ body _ _ := ity then
        if p < diSpFvars.size then
          ity := instantiate1 body diSpFvars[p]!
        else if p < paramFvars.size then
          ity := instantiate1 body paramFvars[p]!
        else
          ity := body
    -- Beta-reduce: lambda-valued spec_params create redexes.
    ity := betaReduce ity

    -- Peel nIndices leading Pi's (syntactic for aux members).
    let nIndices := diMember.nIndices
    let mut indexDecls : Array LocalDecl := #[]
    for fi in [0:nIndices] do
      match ity with
      | .forallE name dom body bi _ =>
        let (fvName, fv) := freshFVar "idx" fi
        indexDecls := indexDecls.push
          { fvarName := fvName, binderName := name, domain := dom, info := bi }
        indexFvars := indexFvars.push fv
        ity := instantiate1 body fv
      | _ => break
    allDecls := allDecls ++ indexDecls

    -- Major domain: I spec_params indices.
    let majorUnivs :=
      if !diMember.occurrenceLevelArgs.isEmpty then
        diMember.occurrenceLevelArgs
      else indUnivs
    let mut app := mkConst diMember.ind.cnst.name majorUnivs
    for sp in diSpFvars do
      app := Expr.mkApp app sp
    for idxFv in indexFvars do
      app := Expr.mkApp app idxFv
    let (name, fv) := freshFVar "major" 0
    majorFv := fv
    allDecls := allDecls.push
      { fvarName := name, binderName := Name.mkStr .mkAnon "t"
        domain := app, info := .default }

  -- --- Return: motive_di(index_fvars, major_fv) ---
  let mut ret := motiveFvars[di]!
  for idxFv in indexFvars do
    ret := Expr.mkApp ret idxFv
  ret := Expr.mkApp ret majorFv

  -- Single batch abstraction: all FVars → BVars in one pass.
  let recType := mkForall ret allDecls

  -- Lean calls inferImplicit(ty, 1000, false) over ALL binders.
  return (inferImplicit recType 1000, nestedRewrite)

/-! ## Rule RHS construction (recursor.rs:1611) -/

/-- Mirrors Rust `build_rule_ih_fvar` (recursor.rs:1907).

    IH value for a recursive field in a rule RHS, WHNF-peeling the field
    domain so reducible-alias heads unfold before `idx_args` extraction:
    `λ (xs...), rec[target] params motives minors idx_args (field xs)`. -/
def buildRuleIhFVar (fieldFvar fieldDom : Expr) (targetCi : Nat)
    (recName : Name) (recUnivs : Array Level)
    (paramFvars motiveFvars minorFvars : Array Expr)
    (classes : Array FlatInfo) (scope : TcScopeSt) :
    KBridgeM (Expr × TcScopeSt) := do
  let mut scope := scope
  let targetNParams := classes[targetCi]!.ind.numParams

  let mut xsFvars : Array Expr := #[]
  let mut xsDecls : Array LocalDecl := #[]
  let mut cur ← scope.whnfLean fieldDom

  repeat
    match cur with
    | .forallE name dom body bi _ =>
      -- Block-head stop check, ported verbatim (see buildIhTypeFVar note).
      let (h, _) := decomposeApps cur
      let mut isBlockHead := false
      if let .const cname _ _ := h then
        if classes.any (fun c => c.allNames.any (· == cname)) then
          isBlockHead := true
      if isBlockHead then
        break
      let (fvName, fv) := freshFVar "rih_xs" xsFvars.size
      let decl : LocalDecl :=
        { fvarName := fvName, binderName := name, domain := dom, info := bi }
      scope ← scope.pushLocals #[decl]
      xsDecls := xsDecls.push decl
      xsFvars := xsFvars.push fv
      cur ← scope.whnfLean (instantiate1 body fv)
    | _ => break
  scope ← scope.popLocals xsDecls

  let (_, innerArgs) := decomposeApps cur
  let idxArgs : Array Expr := innerArgs.extract targetNParams innerArgs.size

  let mut ih := mkConst recName recUnivs
  for pf in paramFvars do
    ih := Expr.mkApp ih pf
  for mf in motiveFvars do
    ih := Expr.mkApp ih mf
  for mf in minorFvars do
    ih := Expr.mkApp ih mf
  for idx in idxArgs do
    ih := Expr.mkApp ih idx
  let mut fieldApp := fieldFvar
  for fv in xsFvars do
    fieldApp := Expr.mkApp fieldApp fv
  ih := Expr.mkApp ih fieldApp

  return (mkLambda ih xsDecls, scope)

/-- Mirrors Rust `build_rec_rules` (recursor.rs:1623).

    Recursor rules for flat member `di` (one per constructor of
    `classes[di]`): RHS `λ params motives minors fields, minor fields ihs`.
    The full `classes` array is still consulted for recursive-field
    detection. Errors (`invalidMutualBlock`) when `sourceOfCanonical` is
    missing an entry needed for an aux `rec_N` reference. -/
def buildRecRules (di : Nat) (classes : Array FlatInfo)
    (nParams nClasses : Nat) (indUnivs : Array Level)
    (recLevelParams : Array Name) (recType : Expr)
    (sourceOfCanonical : Option (Array Nat)) (maps : AddrMaps)
    (nestedRewrite : Option NestedRewriteCtx) :
    KBridgeM (Array RecursorRule × Option NestedRewriteCtx) := do
  let nFlat := classes.size
  let nMotives := nFlat
  let nMinors : Nat := classes.foldl (init := 0) fun acc c => acc + c.ctors.size
  let pmm := nParams + nMotives + nMinors

  -- (Rust extracts `_pmm_binders = collect_binders(rec_type, pmm)` here —
  -- dead value, not reconstructed.)

  -- Param binder infos from the inductive type (for rule RHS lambdas).
  let paramBinderInfos : Array Lean.BinderInfo :=
    let indTy := substLevels classes[0]!.ind.cnst.type
      classes[0]!.ind.cnst.levelParams indUnivs
    (collectBinders indTy nParams).map (·.info)

  -- Create FVars for params, motives, minors by walking the rec type.
  let mut pmmDecls : Array LocalDecl := #[]
  let mut paramFvars : Array Expr := #[]
  let mut motiveFvars : Array Expr := #[]
  let mut minorFvars : Array Expr := #[]
  let mut recTyCur := recType
  for i in [0:pmm] do
    let (kind, localIdx) :=
      if i < nParams then ("rparam", i)
      else if i < nParams + nMotives then ("rmotive", i - nParams)
      else ("rminor", i - nParams - nMotives)
    let (fvName, fv) := freshFVar kind localIdx
    let mut binderName := Name.mkAnon
    let mut domain := Expr.mkSort Level.mkZero
    match recTyCur with
    | .forallE n d b _bi _ =>
      binderName := n
      domain := d
      recTyCur := instantiate1 b fv
    | _ => pure () -- (Name.anon(), Sort 0, Default) fallback stands.
    pmmDecls := pmmDecls.push
      { fvarName := fvName, binderName, domain
        -- Rule RHS lambda binder info: params use the inductive type's
        -- original binder info; motives and minors are Default.
        info :=
          if i < nParams then (paramBinderInfos[i]?).getD .default
          else .default }
    if i < nParams then
      paramFvars := paramFvars.push fv
    else if i < nParams + nMotives then
      motiveFvars := motiveFvars.push fv
    else
      minorFvars := minorFvars.push fv

  let recUnivs : Array Level := recLevelParams.map Level.mkParam

  -- TcScope seeded with params+motives+minors (delta-unfolding of
  -- reducible-alias heads during recursive-field detection).
  let mut scope ← TcScopeSt.new pmmDecls recLevelParams maps

  let mut rules : Array RecursorRule := #[]

  -- Minor FVar offset for class di: sum of ctor counts before di.
  let mut globalMinorIdx : Nat :=
    (classes.extract 0 di).foldl (init := 0) fun acc c => acc + c.ctors.size

  let mut nestedRewrite := nestedRewrite

  let class_ := classes[di]!
  for ctor in class_.ctors do
    let nFields := ctor.numFields

    -- Walk ctor type past params using FVars (aux: occurrence levels and
    -- spec_params).
    let ctorTy :=
      if class_.isAux && !class_.occurrenceLevelArgs.isEmpty then
        substLevels ctor.cnst.type class_.ind.cnst.levelParams
          class_.occurrenceLevelArgs
      else
        substLevels ctor.cnst.type class_.ind.cnst.levelParams indUnivs
    let mut ty := ctorTy
    let nCtorParams := ctor.numParams
    let ruleSpFvars :=
      if class_.isAux then
        instantiateSpecWithFVars class_.specParams paramFvars
      else #[]
    for p in [0:nCtorParams] do
      if let .forallE _ _ b _ _ := ty then
        if class_.isAux && p < ruleSpFvars.size then
          ty := instantiate1 b ruleSpFvars[p]!
        else if p < paramFvars.size then
          ty := instantiate1 b paramFvars[p]!
        else
          ty := instantiate1 b (Expr.mkSort Level.mkZero)
    if class_.isAux then
      ty := betaReduce ty
    -- Nested-aux level rewrite for original members (shared block scratch).
    if !class_.isAux then
      if let some nr := nestedRewrite then
        let (ty', nr') := nr.rewrite ty
        ty := ty'
        nestedRewrite := some nr'

    -- Collect fields with FVars, detect recursive fields.
    let mut fieldDecls : Array LocalDecl := #[]
    let mut fieldFvars : Array Expr := #[]
    let mut recFieldData : Array (Expr × Nat) := #[] -- (field_fvar, target_ci)

    for fi in [0:nFields] do
      match ty with
      | .forallE fname dom b fbi _ =>
        let cleanDom := consumeTypeAnnotations dom
        let (fvName, fv) := freshFVar "rfield" fi
        let decl : LocalDecl :=
          { fvarName := fvName, binderName := fname, domain := cleanDom
            info := fbi }
        let (target?, scope') ← findRecTarget cleanDom classes paramFvars
          nParams scope
        scope := scope'
        if let some targetCi := target? then
          recFieldData := recFieldData.push (fv, targetCi)
        scope ← scope.pushLocals #[decl]
        fieldDecls := fieldDecls.push decl
        fieldFvars := fieldFvars.push fv
        ty := instantiate1 b fv
      | _ => break

    -- Body: minor(fields)(ihs).
    let mut body := minorFvars[globalMinorIdx]!
    for fv in fieldFvars do
      body := Expr.mkApp body fv

    -- Build and apply IHs for recursive fields.
    for (fieldFv, targetCi) in recFieldData do
      -- Recursor name for the target: originals `<target>.rec`,
      -- auxiliaries `<all[0]>.rec_N` (Lean hangs `_N` under all[0]).
      let recName ←
        if targetCi < nClasses then
          pure (Name.mkStr classes[targetCi]!.ind.cnst.name "rec")
        else do
          let all0 := (classes[0]!.ind.all[0]?).getD classes[0]!.ind.cnst.name
          let canonicalI := targetCi - nClasses
          let auxIdx ← match sourceOfCanonical with
            | some s =>
              match s[canonicalI]? with
              | some v => pure v
              | none => throw (.invalidMutualBlock
                  s!"source_of_canonical missing canonical aux \
#{canonicalI} while building rule IH")
            | none => pure canonicalI
          pure (Name.mkStr all0 s!"rec_{auxIdx + 1}")

      -- The field's original domain: find it in fieldDecls by FVar hash.
      let fieldDom := (fieldDecls.find? fun d =>
        (Expr.mkFVar d.fvarName).getHash == fieldFv.getHash).map (·.domain)

      let ih ← match fieldDom with
        | some dom => do
          let (ih, scope') ← buildRuleIhFVar fieldFv dom targetCi recName
            recUnivs paramFvars motiveFvars minorFvars classes scope
          scope := scope'
          pure ih
        | none => pure fieldFv -- fallback — shouldn't happen
      body := Expr.mkApp body ih

    -- Pop this ctor's field decls so the scope is clean for the next ctor.
    scope ← scope.popLocals fieldDecls

    -- Abstract and wrap: fields (innermost), then PMM (outermost).
    let mut allDecls : Array LocalDecl := #[]
    allDecls := allDecls ++ pmmDecls
    allDecls := allDecls ++ fieldDecls
    let rhs := mkLambda body allDecls

    rules := rules.push { ctor := ctor.cnst.name, nfields := nFields, rhs }

    globalMinorIdx := globalMinorIdx + 1

  return (rules, nestedRewrite)

/-! ## is_large / k / is_prop computation (recursor.rs:2311)

NOTE (Rust recursor.rs:1976-1985): the old syntactic
`elim_only_at_universe_zero` fallback trio was removed upstream — a TC
failure here surfaces as a hard error, never a silent fallback. -/

/-- Mirrors Rust `collect_const_refs` (recursor.rs:2694).

    Collect all constant names referenced in an expression, appended onto
    `out` (a work queue, NOT a set — dedup happens at the consumer's
    `seen`). Explicit stack, matching the Rust traversal order. -/
def collectConstRefs (expr : Expr) (out : Array Name) : Array Name := Id.run do
  let mut out := out
  let mut stack : Array Expr := #[expr]
  repeat
    if let some e := stack.back? then
      stack := stack.pop
      match e with
      | .const n _ _ => out := out.push n
      | .app f a _ =>
        stack := stack.push f
        stack := stack.push a
      | .forallE _ d b _ _ | .lam _ d b _ _ =>
        stack := stack.push d
        stack := stack.push b
      | .letE _ t v b _ _ =>
        stack := stack.push t
        stack := stack.push v
        stack := stack.push b
      | .proj name _ e' _ =>
        out := out.push name
        stack := stack.push e'
      | .mdata _ e' _ =>
        stack := stack.push e'
      | _ => pure ()
    else
      break
  return out

/-- Mirrors Rust `ingress_type_stub` (recursor.rs:2649).

    Insert a type-only `KConst.axio` stub for `name` into the bridge kenv
    (skipped when an entry already exists under the resolved address). -/
def ingressTypeStub (name : Name) (typ : Expr) (levelParams : Array Name)
    (maps : AddrMaps) : KBridgeM Unit := do
  let addr := maps.resolve name
  let zid : MKId := ⟨addr, name⟩
  if (← kenvGet? zid).isSome then
    return
  let tyZ ← leanExprToKexpr typ levelParams maps
  let nLvls := UInt64.ofNat levelParams.size
  kenvInsert zid (.axio name levelParams false nLvls tyZ)

/-- Mirrors Rust `ingress_aux_gen_dep` (recursor.rs:2597).

    Ingress one dependency with the right fidelity: definitions /
    inductives / ctors as full entries (`ensureFullInKenvOf`), everything
    else as type stubs. New const refs discovered in the entry's types
    are appended to the returned queue (Rust `&mut Vec<Name>`). -/
def ingressAuxGenDep (name : Name) (ci : ConstantInfo) (maps : AddrMaps)
    (queue : Array Name) : KBridgeM (Array Name) := do
  match ci with
  | .defnInfo v => do
    ensureFullInKenvOf name maps
    let queue := collectConstRefs v.cnst.type queue
    return collectConstRefs v.value queue
  | .inductInfo v => do
    ensureFullInKenvOf name maps
    let mut queue := collectConstRefs v.cnst.type queue
    for ctorName in v.ctors do
      if let some (.ctorInfo ctor) ← lookupConst? ctorName then
        queue := collectConstRefs ctor.cnst.type queue
    return queue
  | .ctorInfo v => do
    ensureFullInKenvOf name maps
    return collectConstRefs v.cnst.type queue
  | .axiomInfo v => do
    ingressTypeStub name v.cnst.type v.cnst.levelParams maps
    return collectConstRefs v.cnst.type queue
  | .thmInfo v => do
    ingressTypeStub name v.cnst.type v.cnst.levelParams maps
    return collectConstRefs v.cnst.type queue
  | .opaqueInfo v => do
    ingressTypeStub name v.cnst.type v.cnst.levelParams maps
    return collectConstRefs v.cnst.type queue
  | .recInfo v => do
    ingressTypeStub name v.cnst.type v.cnst.levelParams maps
    return collectConstRefs v.cnst.type queue
  | .quotInfo v => do
    ingressTypeStub name v.cnst.type v.cnst.levelParams maps
    return collectConstRefs v.cnst.type queue

/-- Mirrors Rust `ingress_target_type_deps` (recursor.rs:2548).

    Ingress constants referenced by an inductive target type with enough
    fidelity for WHNF (target aliases like `Set α := α → Prop` must
    unfold). -/
def ingressTargetTypeDeps (targetTy : Expr) (maps : AddrMaps) :
    KBridgeM Unit := do
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := collectConstRefs targetTy #[]
  repeat
    let some name := queue.back? | break
    queue := queue.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    if let some ci ← lookupConst? name then
      queue ← ingressAuxGenDep name ci maps queue
  return ()

/-- Mirrors Rust `ingress_field_deps` (recursor.rs:2572).

    Walk field domains of the class's constructors and ingress referenced
    constants into the bridge kenv so `infer`/WHNF can look them up
    (reducible definitions as real `Defn` entries — recursive occurrences
    hidden under aliases like `constType (I α) (I α)` are missed
    otherwise). -/
def ingressFieldDeps (cls : FlatInfo) (_lvlParams : Array Name)
    (maps : AddrMaps) : KBridgeM Unit := do
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for ctor in cls.ctors do
    queue := collectConstRefs ctor.cnst.type queue
  repeat
    let some name := queue.back? | break
    queue := queue.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    let some ci ← lookupConst? name | continue
    queue ← ingressAuxGenDep name ci maps queue
  return ()

/-- Mirrors Rust `peek_result_sort` (recursor.rs:2732).

    Syntactic-only peek at the result sort of a KExpr type. Dead code in
    Rust too (`#[allow(dead_code)]`) — no longer wired into the K-target
    check, kept for the historical record and potential future callers. -/
partial def peekResultSort (ty : MKExpr) : Option MKUniv := Id.run do
  let mut cur := ty
  repeat
    match cur with
    | .all _ _ _ body _ => cur := body
    | .sort u _ => return some u
    | _ => return none
  return none -- unreachable

/-- Mirrors Rust `compute_is_large_and_k` (recursor.rs:2328).

    Compute `(isLarge, k, isProp)` for the canonical recursor using the
    kernel's `isLargeEliminator`:
    - ephemeral `KConst.indc`/`KConst.ctor` entries for ALL original
      classes go into the bridge kenv (provisional addresses), so the
      kernel sees the full mutual block and can apply the
      "mutual Prop → small" rule;
    - `getResultSortLevel` WHNF-peels params+indices (crucial for
      reducible-alias targets like `Set σ := σ → Prop`);
    - spec-level override: non-Prop inductives always eliminate large
      (inductive.cpp:539-548) — corrects syntactically-nonzero Params;
    - C1 fix: a Prop block with nested auxiliaries the kenv didn't see is
      forced small;
    - K: single flat member (aux included), single ctor, 0 fields, Prop.
    TC failures are hard `invalidMutualBlock` errors (no syntactic
    fallback). Rust's `IX_TIMING` diagnostics block is not ported. -/
def computeIsLargeAndK (classes : Array FlatInfo) (nClasses nParams : Nat)
    (maps : AddrMaps) : KBridgeM (Bool × Bool × Bool) := do
  let mut indInfos : Array (MKId × UInt64 × UInt64 × Array MKId × MKExpr) := #[]

  -- The first class's block KId is the shared block reference.
  let blockAddr := maps.resolve classes[0]!.ind.cnst.name
  let blockZid : MKId := ⟨blockAddr, classes[0]!.ind.cnst.name⟩

  for ci in [0:nClasses] do
    let cls := classes[ci]!
    let clsInd := cls.ind
    let clsLvlParams := clsInd.cnst.levelParams
    let clsNLvls := UInt64.ofNat clsLvlParams.size
    let clsNIndices := UInt64.ofNat clsInd.numIndices

    let clsAddr := maps.resolve clsInd.cnst.name
    let clsZid : MKId := ⟨clsAddr, clsInd.cnst.name⟩
    let clsTyZ ← leanExprToKexpr clsInd.cnst.type clsLvlParams maps

    -- Convert constructors.
    let mut clsCtorZids : Array MKId := #[]
    for ctor in cls.ctors do
      let ctorAddr := maps.resolve ctor.cnst.name
      let ctorZid : MKId := ⟨ctorAddr, ctor.cnst.name⟩
      let ctorTyZ ← leanExprToKexpr ctor.cnst.type clsLvlParams maps
      let ctorFields := UInt64.ofNat ctor.numFields
      let ctorParams := UInt64.ofNat ctor.numParams
      kenvInsert ctorZid (.ctor ctor.cnst.name clsLvlParams ctor.isUnsafe
        clsNLvls clsZid (UInt64.ofNat clsCtorZids.size) ctorParams ctorFields
        ctorTyZ)
      clsCtorZids := clsCtorZids.push ctorZid

    -- Insert inductive.
    kenvInsert clsZid (.indc clsInd.cnst.name clsLvlParams clsNLvls
      (UInt64.ofNat nParams) clsNIndices clsInd.isUnsafe blockZid
      (UInt64.ofNat ci) clsTyZ clsCtorZids #[])

    -- Target types may hide their final Sort behind reducible aliases.
    ingressTargetTypeDeps clsInd.cnst.type maps
    -- Ingress field deps for this class.
    ingressFieldDeps cls clsLvlParams maps

    indInfos := indInfos.push
      (clsZid, UInt64.ofNat nParams, clsNIndices, clsCtorZids, clsTyZ)

  let (_, _, firstNIndices, _, firstTyZ) := indInfos[0]!

  -- Fresh TypeChecker over the persistent kenv (Rust
  -- `TypeChecker::new(&mut kctx.kenv)`).
  modify fun kctx => { kctx with
    tcState := Ix.Tc.TcState.new kctx.tcState.env kctx.tcState.prims }

  -- WHNF-reduced result sort level via the kernel.
  let resultKuniv ←
    match ← runTc ((Ix.Tc.RecM.getResultSortLevel firstTyZ
        (nParams + firstNIndices.toNat)).run Ix.Tc.methods) with
    | .ok u => pure u
    | .error e =>
      throw (.invalidMutualBlock
        s!"compute_is_large_and_k: TC failed for \
{classes[0]!.ind.cnst.name.pretty}: {e}")

  let isLarge ←
    match ← runTc ((Ix.Tc.RecM.isLargeEliminator resultKuniv indInfos).run
        Ix.Tc.methods) with
    | .ok b => pure b
    | .error e =>
      throw (.invalidMutualBlock
        s!"compute_is_large_and_k: is_large_eliminator failed for \
{classes[0]!.ind.cnst.name.pretty}: {e}")

  -- Spec-level override: non-Prop inductives always get large elimination.
  let isLarge := if !isLarge && !resultKuniv.isZero then true else isLarge

  -- Prop determination from the WHNF-reduced kernel-derived level.
  let isProp := resultKuniv.isZero

  -- C1 fix: Prop block with nested auxiliaries the KEnv didn't see →
  -- small elimination (Lean treats nested auxes as full mutual members).
  let isLarge :=
    if isLarge && isProp && classes.size > nClasses then false else isLarge

  -- K-target: single flat member (aux included, matching Lean's expanded
  -- `m_ind_types.size() == 1`), single ctor, 0 fields, Prop.
  let k := classes.size == 1 && classes[0]!.ctors.size == 1
    && classes[0]!.ctors[0]!.numFields == 0 && isProp

  return (isLarge, k, isProp)

/-! ## Aux-layout reordering (recursor.rs:322) -/

/-- Mirrors Rust `reorder_flat_by_layout` (recursor.rs:340).

    Reorder the aux section of a flat block per a stored `AuxLayout` perm
    (`perm[sourceJ] = canonicalI`). For each canonical slot the FIRST
    source position mapping to it wins (stable rule under alpha-collapse
    many-to-one perms). Errors return the original flat plus a message
    (the caller wraps into `invalidMutualBlock`):
    - perm's canonical slot count mismatches the discovered aux count;
    - perm has fewer source positions than discovered auxes;
    - a canonical slot has no source mapping. -/
def reorderFlatByLayout (flat : Array CompileFlatMember) (nClasses : Nat)
    (layout : Ixon.AuxLayout) :
    Except (Array CompileFlatMember × String) (Array CompileFlatMember) :=
  Id.run do
  let nAux := flat.size - nClasses
  if nAux == 0 then
    return .ok flat -- Nothing to reorder.

  -- Canonical slot count from perm (may exceed under alpha-collapse).
  let maxCanon : Nat := layout.perm.foldl (init := 0) fun acc v =>
    if v.toNat != PERM_OUT_OF_SCC then Nat.max acc (v.toNat + 1) else acc
  if maxCanon != nAux then
    return .error (flat,
      s!"aux_layout perm claims {maxCanon} canonical slots but flat has \
{nAux} aux members")
  if layout.perm.size != nAux then
    -- Discovery-order decompile keeps perm.len() == nAux for bijective
    -- cases; alpha-collapse may exceed — allow, but shorter is an error.
    if layout.perm.size < nAux then
      return .error (flat,
        s!"aux_layout perm has {layout.perm.size} source positions but \
flat discovered {nAux} auxes (need perm.len() >= n_aux)")

  -- First source_j per canonical slot (stable rule). Sentinel is Rust
  -- `usize::MAX`, numerically identical to `PERM_OUT_OF_SCC`.
  let mut canonRepr : Array Nat := Array.replicate nAux PERM_OUT_OF_SCC
  for (canonI64, sourceJ) in layout.perm.zipIdx do
    let canonI := canonI64.toNat
    if canonI != PERM_OUT_OF_SCC && canonI < nAux
        && canonRepr[canonI]! == PERM_OUT_OF_SCC && sourceJ < nAux then
      canonRepr := canonRepr.set! canonI sourceJ

  -- Verify every canonical slot has a source representative.
  for (sj, ci) in canonRepr.zipIdx do
    if sj == PERM_OUT_OF_SCC then
      return .error (flat,
        s!"aux_layout perm: canonical slot {ci} has no source mapping")

  -- Rebuild with the aux section in canonical order.
  let mut primary : Array CompileFlatMember := flat.extract 0 nClasses
  let auxSrc : Array CompileFlatMember := flat.extract nClasses flat.size
  for (sourceJ, canonicalI) in canonRepr.zipIdx do
    if sourceJ >= auxSrc.size then
      return .error (flat,
        s!"aux_layout perm: canon_repr[{canonicalI}] = {sourceJ} >= n_aux \
({auxSrc.size})")
    primary := primary.push auxSrc[sourceJ]!

  return .ok primary

/-! ## Public API (recursor.rs:28) -/

/-- Mirrors Rust `generate_canonical_recursors_with_layout` (recursor.rs:462).

    Generate canonical recursors for all classes in a block: one
    `RecursorVal` per flat member (originals + nested auxiliaries), plus
    `isProp` for the downstream `.below`/`.brecOn` phases.

    - `sortedClasses[i]`: names in equivalence class `i` (first is the
      representative whose `InductiveVal`/`ConstructorVal`s are used).
    - `overlay`: optional overlay env checked before the base CompileM env.
    - `preFlat`: pre-built flat block (expand/restore path); when `none`,
      falls back to `buildCompileFlatBlockWithOverlay` discovery.
    - `auxLayout`: optional stored layout that reorders the discovered aux
      section (decompile pinning hook); shape mismatches are hard errors.
    - `sourceOfCanonical`: Lean source-walk index per canonical aux
      position for `_N` naming. Precedence: explicit parameter, then
      derived from `auxLayout.perm` (min source_j per canonical), then
      discovery order (`canonical_i`). -/
def generateCanonicalRecursorsWithLayout (sortedClasses : Array (Array Name))
    (overlay : Option (Std.HashMap Name ConstantInfo))
    (preFlat : Option (Array CompileFlatMember)) (maps : AddrMaps)
    (auxLayout : Option Ixon.AuxLayout) (sourceOfCanonical : Option (Array Nat)) :
    KBridgeM (Array (Name × RecursorVal) × Bool) := do
  -- One FlatInfo per equivalence class (representative's data).
  let mut classes : Array FlatInfo := #[]
  for cls in sortedClasses do
    let rep := cls[0]!
    let ind ← match ← envGet overlay rep with
      | some (.inductInfo v) => pure v
      | _ => throw (.invalidMutualBlock
          s!"aux_gen: {rep.pretty} not an inductive")
    let mut ctors : Array ConstructorVal := #[]
    for cn in ind.ctors do
      if let some (.ctorInfo c) ← envGet overlay cn then
        ctors := ctors.push c
    let ownParams := ind.numParams
    let nIndices := ind.numIndices
    classes := classes.push
      { name := ind.cnst.name
        ind, ctors
        allNames := cls
        isAux := false
        specParams := #[]
        occurrenceLevelArgs := #[]
        ownParams, nIndices }

  let nClasses := classes.size
  let nParams := classes[0]!.ind.numParams

  -- Flat block: pre-built (expand/restore) or detected from ctor types.
  let orderedOriginals : Array Name := classes.map (·.name)
  let flat0 ← match preFlat with
    | some pf => pure pf
    | none => buildCompileFlatBlockWithOverlay orderedOriginals overlay

  -- Optional AuxLayout reorder (decompile pinning). Hard error on
  -- size/shape mismatch — a stored layout is an assertion, silently
  -- falling back would mislabel the canonical form.
  let flat ← match auxLayout with
    | some layout =>
      match reorderFlatByLayout flat0 nClasses layout with
      | .ok f => pure f
      | .error (_, msg) =>
        throw (.invalidMutualBlock
          (s!"aux_layout override rejected: {msg}. The stored layout is " ++
           "inconsistent with the current flat-block discovery — usually " ++
           "because the `sorted_classes` passed here don't match the " ++
           "sort_consts-collapsed classes compile originally saw. See " ++
           "`docs/ix_canonicity.md` §17.2."))
    | none => pure flat0

  -- Add auxiliary members (nested occurrences) to classes. NOTE: entries
  -- whose lookup fails are silently skipped, as in Rust.
  for fm in flat.extract nClasses flat.size do
    if let some (.inductInfo ind) ← envGet overlay fm.name then
      let mut ctors : Array ConstructorVal := #[]
      for cn in ind.ctors do
        if let some (.ctorInfo c) ← envGet overlay cn then
          ctors := ctors.push c
      classes := classes.push
        { name := fm.name
          ind, ctors
          allNames := #[fm.name]
          isAux := true
          specParams := fm.specParams
          occurrenceLevelArgs := fm.occurrenceLevelArgs
          ownParams := fm.ownParams
          nIndices := fm.nIndices }

  let nFlat := classes.size
  let nAux := nFlat - nClasses

  -- Derive `sourceOfCanonical` for aux naming. Precedence: explicit
  -- parameter (compile path); `auxLayout.perm` → min-source_j per
  -- canonical (decompile path); else discovery order.
  let sourceOfCanonicalOwned : Option (Array Nat) ←
    match sourceOfCanonical, auxLayout with
    | none, some layout => do
      -- Sentinel is Rust `usize::MAX` == PERM_OUT_OF_SCC numerically.
      let mut s : Array Nat := Array.replicate nAux PERM_OUT_OF_SCC
      for (canonI64, srcJ) in layout.perm.zipIdx do
        let canonI := canonI64.toNat
        if canonI != PERM_OUT_OF_SCC && canonI < nAux
            && s[canonI]! == PERM_OUT_OF_SCC then
          s := s.set! canonI srcJ
      for (slot, ci) in s.zipIdx do
        if slot == PERM_OUT_OF_SCC then
          throw (.invalidMutualBlock
            s!"aux_layout perm has no source mapping for canonical aux \
#{ci}; refusing to synthesize canonical-indexed _N names")
      pure (some s)
    | some _, _ | none, none => pure none
  let sourceOfCanonical :=
    sourceOfCanonical.orElse fun _ => sourceOfCanonicalOwned
  if let some soc := sourceOfCanonical then
    if soc.size < nAux then
      throw (.invalidMutualBlock
        s!"source_of_canonical has {soc.size} entries for {nAux} canonical \
aux members")
    for (sourceJ, ci) in (soc.extract 0 nAux).zipIdx do
      if sourceJ == PERM_OUT_OF_SCC then
        throw (.invalidMutualBlock
          s!"source_of_canonical has no source mapping for canonical aux \
#{ci}; refusing to synthesize canonical-indexed _N names")

  let nMinors : Nat := classes.foldl (init := 0) fun acc fi => acc + fi.ctors.size

  -- is_large / k / is_prop via the kernel (hard error on TC failure).
  let (isLarge, k, isProp) ← computeIsLargeAndK classes nClasses nParams maps

  -- Canonical elim level name following Lean C++ init_elim_level: "u",
  -- with "u_{i}" fallback on conflict with existing level params.
  let indLevelParams := classes[0]!.ind.cnst.levelParams
  let elimLevelName := Id.run do
    let mut u := Name.mkStr .mkAnon "u"
    let mut i := 1
    while indLevelParams.contains u do
      u := Name.mkStr .mkAnon s!"u_{i}"
      i := i + 1
    return u
  let mut recLevelParams : Array Name := #[]
  if isLarge then
    recLevelParams := recLevelParams.push elimLevelName
  recLevelParams := recLevelParams ++ indLevelParams

  let nIndLvls := classes[0]!.ind.cnst.levelParams.size
  let univOffset : Nat := if isLarge then 1 else 0

  -- Shifted universe args for inductives.
  let indUnivs : Array Level := (Array.range nIndLvls).map fun i =>
    Level.mkParam recLevelParams[i + univOffset]!

  -- Elim level.
  let elimLevel :=
    if isLarge then Level.mkParam recLevelParams[0]! else Level.mkZero

  -- === Collect binder info following Lean C++ mk_rec_infos ===
  let firstTy := substLevels classes[0]!.ind.cnst.type
    classes[0]!.ind.cnst.levelParams indUnivs
  let paramBinders := collectBinders firstTy nParams

  -- One shared set of param FVars for the whole block (C++ `m_params`).
  let (sharedParamFvars, rawParamDecls, _) :=
    forallTelescope firstTy nParams "param" 0
  let sharedParamDecls : Array LocalDecl :=
    (rawParamDecls.zip paramBinders).map fun (d, pb) =>
      { d with domain := consumeTypeAnnotations d.domain, info := pb.info }

  -- WHNF-decompose each ORIGINAL class's stored type (the `mk_rec_infos`
  -- analog; exposes Pis hidden inside reducible aliases).
  let mut classInfos : Array IndRecInfo := #[]
  for ci in [0:nClasses] do
    classInfos := classInfos.push
      (← decomposeInductiveType classes[ci]!.ind indUnivs sharedParamDecls maps)

  -- Generate one recursor per flat member (originals + auxiliaries), with
  -- the block-wide nested-aux rewrite scratch threaded through.
  let mut blockNestedRewrite := NestedRewriteCtx.new classes nClasses
  let mut results : Array (Name × RecursorVal) := #[]
  for di in [0:nFlat] do
    let diMember := classes[di]!
    let nIndices := diMember.nIndices

    -- Name: original → <ind>.rec; auxiliary → <all[0]>.rec_N (Lean hangs
    -- `_N` names under all[0], not the class representative).
    let recName :=
      if di < nClasses then
        Name.mkStr diMember.ind.cnst.name "rec"
      else
        let all0 := (classes[0]!.ind.all[0]?).getD classes[0]!.ind.cnst.name
        let canonicalI := di - nClasses
        -- Prefer source-indexed `_N` when a perm was supplied; missing
        -- entries were validated above and are construction errors.
        let auxIdx :=
          match sourceOfCanonical with
          | some s => s[canonicalI]!
          | none => canonicalI
        Name.mkStr all0 s!"rec_{auxIdx + 1}"

    -- `all` lists only the original inductives, matching Lean.
    let all : Array Name := (classes.extract 0 nClasses).map (·.ind.cnst.name)

    -- Rec type: ∀ params motives minors indices major, motive indices major.
    let (recType, nr1) ← buildRecType di classes flat nParams nClasses
      paramBinders sharedParamFvars sharedParamDecls classInfos elimLevel
      indUnivs recLevelParams overlay maps blockNestedRewrite
    blockNestedRewrite := nr1

    -- Rules.
    let (rules, nr2) ← buildRecRules di classes nParams nClasses indUnivs
      recLevelParams recType sourceOfCanonical maps blockNestedRewrite
    blockNestedRewrite := nr2

    -- Safety: originals from the class representative; auxiliaries take
    -- the block-wide flag (the aux class's `ind` is the EXTERNAL
    -- inductive, whose own flag is unrelated — see inductive.cpp:774 and
    -- the Rust comment about `mkBRecOnFromRec`).
    let isUnsafe :=
      if diMember.isAux then classes[0]!.ind.isUnsafe
      else diMember.ind.isUnsafe

    results := results.push (recName,
      { cnst :=
          { name := recName
            levelParams := recLevelParams
            type := recType }
        all
        numParams := nParams
        numIndices := nIndices
        numMotives := nFlat
        numMinors := nMinors
        rules
        k
        isUnsafe })

  return (results, isProp)

/-- Mirrors Rust `generate_canonical_recursors_with_overlay`
    (recursor.rs:435): the no-layout, no-source-mapping entry point (used
    by the standard flat-block path and `compile_below_recursors`). -/
def generateCanonicalRecursorsWithOverlay (sortedClasses : Array (Array Name))
    (overlay : Option (Std.HashMap Name ConstantInfo))
    (preFlat : Option (Array CompileFlatMember)) (maps : AddrMaps) :
    KBridgeM (Array (Name × RecursorVal) × Bool) :=
  generateCanonicalRecursorsWithLayout sortedClasses overlay preFlat maps
    none none

/-- Mirrors Rust `generate_canonical_recursors` (recursor.rs:293) — the
    Rust version is `#[cfg(test)]`-only; kept callable here for tests. -/
def generateCanonicalRecursors (sortedClasses : Array (Array Name))
    (maps : AddrMaps) : KBridgeM (Array (Name × RecursorVal) × Bool) :=
  generateCanonicalRecursorsWithOverlay sortedClasses none none maps

/-- Mirrors Rust `generate_recursors_from_expanded` (recursor.rs:46).

    Generate canonical recursors using an expanded block (expand/restore
    model): builds an overlay env holding BOTH originals (rewritten ctor
    types) and synthetic auxiliaries, seeds a pre-built flat block
    (originals with empty spec_params; auxes with identity spec_params and
    the block's level params), and delegates to
    `generateCanonicalRecursorsWithLayout`. The caller applies
    `RestoreCtx.restore` to the output.

    `sourceOfCanonical[canonicalI] = sourceJ` drives `all0.rec_{sourceJ+1}`
    naming (Lean's exported `.rec_N` numbering); pass `none` to fall back
    to `canonicalI + 1` — only safe with no alpha-collapse and no
    nested-aux hash-sort permutation. -/
def generateRecursorsFromExpanded (sortedClasses : Array (Array Name))
    (expanded : ExpandedBlock) (sourceOfCanonical : Option (Array Nat))
    (maps : AddrMaps) : KBridgeM (Array (Name × RecursorVal) × Bool) := do
  if expanded.types.isEmpty then
    return (#[], false)

  -- Build overlay environment from the expanded block.
  let mut overlay : Std.HashMap Name ConstantInfo := {}

  -- The `all` field for InductiveVals: just the original names (not aux).
  let originalNames : Array Name :=
    (expanded.types.extract 0 expanded.nOriginals).map (·.name)

  -- Block-wide `isUnsafe`: mutual blocks are uniformly safe or unsafe;
  -- synthetic aux inductives inherit the flag.
  let blockIsUnsafe ←
    match originalNames[0]? with
    | some n =>
      (do match ← lookupConst? n with
          | some (.inductInfo v) => pure v.isUnsafe
          | _ => pure false : KBridgeM Bool)
    | none => pure false

  for member in expanded.types do
    let ctorNames : Array Name := member.ctors.map (·.name)

    -- Use the original env's `all`/`isRec`/`isReflexive`/`isUnsafe` when
    -- available; aux types fall back to block-wide defaults.
    let (allField, isRec, isReflexive, indIsUnsafe) ←
      match ← lookupConst? member.name with
      | some (.inductInfo orig) =>
        pure (orig.all, orig.isRec, orig.isReflexive, orig.isUnsafe)
      | _ => pure (originalNames, true, false, blockIsUnsafe)

    let indVal : InductiveVal :=
      { cnst :=
          { name := member.name
            levelParams := expanded.levelParams
            type := member.typ }
        numParams := member.nParams
        numIndices := member.nIndices
        all := allField
        ctors := ctorNames
        numNested := 0
        isRec
        isUnsafe := indIsUnsafe
        isReflexive }
    overlay := overlay.insert member.name (.inductInfo indVal)

    for (ctor, ci) in member.ctors.zipIdx do
      -- Original ctor's safety when available; else the parent's flag
      -- (ctor safety always matches its parent inductive).
      let ctorIsUnsafe ←
        match ← lookupConst? ctor.name with
        | some (.ctorInfo orig) => pure orig.isUnsafe
        | _ => pure indIsUnsafe
      let ctorVal : ConstructorVal :=
        { cnst :=
            { name := ctor.name
              levelParams := expanded.levelParams
              type := ctor.typ }
          induct := member.name
          cidx := ci
          numParams := member.nParams
          numFields := ctor.nFields
          isUnsafe := ctorIsUnsafe }
      overlay := overlay.insert ctor.name (.ctorInfo ctorVal)

  let identitySpecParams := fun (n : Nat) =>
    (Array.range n).map fun i => Expr.mkBVar (n - 1 - i)

  -- Pre-flat from the expanded block's members: originals with identity
  -- (empty) spec_params, auxes with identity spec_params (NOT empty —
  -- `find_rec_target` matches by spec_params, so fields like
  -- `List (A α)` need the identity substitution) and the block's levels.
  let mut preFlat : Array CompileFlatMember := #[]
  for member in expanded.types.extract 0 expanded.nOriginals do
    preFlat := preFlat.push
      { name := member.name
        specParams := #[] -- originals don't use spec_params
        occurrenceLevelArgs := #[]
        ownParams := member.nParams
        nIndices := member.nIndices }
  for member in expanded.types.extract expanded.nOriginals expanded.types.size do
    preFlat := preFlat.push
      { name := member.name
        specParams := identitySpecParams member.nParams
        occurrenceLevelArgs := expanded.levelParams.map Level.mkParam
        ownParams := member.nParams
        nIndices := member.nIndices }

  generateCanonicalRecursorsWithLayout sortedClasses (some overlay)
    (some preFlat) maps none sourceOfCanonical

end Ix.AuxGen

end
