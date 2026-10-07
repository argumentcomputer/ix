/-
  Ix.AuxSource: the source side of a Lean block's auxiliaries, read by the
  compiler's passes.

  Contents (each mirrors the Rust function named in its docstring; the Rust
  side is `crates/compile/src/compile/aux_source.rs` and, for the name
  classification, `crates/compile/src/decompile.rs`):
  - `classifyAuxGen`, `isAuxGenSuffix`: which Lean names are auxiliaries
    aux-gen regenerates, and the inductive each hangs off.
  - `collectLeanTelescope`, `collectIxonTelescope`: application spines.
  - The split-minor helpers of O2 (`Ix.Compile.Pass.Opt.O2`) and O11a
    (`Ix.Compile.Pass.Opt.O11a`): `AuxMotiveSig`/`auxMotiveSigs` (the nested
    motives of a source recursor), `sourceCtorForMinor` (the constructor a
    source minor eliminates), `sourceMinorType` (its type in caller terms),
    `peelBinders`, `SourceRecTarget`/`findSourceRecTarget` (the recursive
    target of a minor's field).
  - `isPropFormer`, `belowFamilyLeanExists` (whether Lean generates the
    `.below`/`.brecOn` families of a block), `blockLabel` (the block a
    refusal names).

  History: until M6R slice 6 (2026-10-07) these lived beside the legacy
  call-site surgery (`Ix/CallSiteSurgery.lean`, `Ix/CallSitePlan.lean`,
  `Ix/AuxGen/Surgery.lean`), which rewrote the call sites of a changed block
  by plans under `IX_PASS3=off`. Pass 3 replaced it (the flip, M6) and slice 6
  deleted it; O2 and O11a read a split block's source minors with the same
  helpers, which is why they stay.

  Lives below `Ix.CompileM` (imports only the environment, Ixon and
  `Ix.AuxGen.ExprUtils`), so the compiler and aux-gen can both use it.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Name.mkStr`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.AuxGen.ExprUtils
public section

namespace Ix.AuxGen

/-- Kind of a Lean auto-generated auxiliary, as classified by name
    suffix. Mirrors Rust `AuxKind` (decompile.rs). Constructor-name
    renames forced by Lean's auto-generated declarations on this very
    inductive (`AuxKind.rec`/`recOn`/`casesOn` would collide):
    `Rec → recr`, `RecOn → recOnAux`, `CasesOn → casesOnAux`; the rest
    keep Rust's names. -/
inductive AuxKind where
  | recr | recOnAux | casesOnAux | below | belowRec
  | brecOn | brecOnGo | brecOnEq
  deriving BEq, Repr, Inhabited

/-- Classify an aux_gen constant by suffix, returning
    `(kind, root inductive)` — the base inductive the auxiliary is
    derived from. Mirrors Rust `classify_aux_gen` (decompile.rs:2157)
    branch-for-branch. -/
def classifyAuxGen (name : Name) : Option (AuxKind × Name) :=
  match name with
  | .str p1 s1 _ =>
    if s1 == "rec" || s1.startsWith "rec_" then
      -- X.rec / X.rec_N or X.below.rec / X.below_N.rec
      match p1 with
      | .str gp ps _ =>
        if ps == "below" || ps.startsWith "below_" then
          some (.belowRec, gp)
        else
          some (.recr, p1)
      | _ => some (.recr, p1)
    else if s1 == "recOn" || s1.startsWith "recOn_" then
      some (.recOnAux, p1)
    else if s1 == "casesOn" || s1.startsWith "casesOn_" then
      -- X.casesOn / X.casesOn_N or X.below.casesOn. The below wrapper
      -- roots under the FAMILY (like `X.below.rec` above) so it joins
      -- the family block's aux members and the decompiler's Phase 3b
      -- can regenerate it against the canonical below-rec.
      match p1 with
      | .str gp ps _ =>
        if ps == "below" || ps.startsWith "below_" then
          some (.casesOnAux, gp)
        else
          some (.casesOnAux, p1)
      | _ => some (.casesOnAux, p1)
    else if s1 == "below" || s1.startsWith "below_" then
      some (.below, p1)
    else if s1 == "brecOn" || s1.startsWith "brecOn_" then
      some (.brecOn, p1)
    else if s1 == "go" then
      -- X.brecOn.go or X.brecOn_N.go (nested auxiliary)
      match p1 with
      | .str gp ps _ =>
        if ps == "brecOn" || ps.startsWith "brecOn_" then
          some (.brecOnGo, gp)
        else
          none
      | _ => none
    else if s1 == "eq" then
      -- X.brecOn.eq or X.brecOn_N.eq (nested auxiliary)
      match p1 with
      | .str gp ps _ =>
        if ps == "brecOn" || ps.startsWith "brecOn_" then
          some (.brecOnEq, gp)
        else
          none
      | _ => none
    else
      none
  | _ => none

/-- Is `name` a Lean auto-generated auxiliary that aux-gen regenerates
    (`.rec`/`.rec_N`, `.recOn*`, `.casesOn*`, `.below*`, `.below.rec`,
    `.brecOn*`, `.brecOn*.go`, `.brecOn*.eq`)?

    Boolean projection of `classifyAuxGen` — Rust `is_aux_gen_suffix`
    (decompile.rs:2151). Used by the decompiler's Pass-1 skip and the validators. -/
def isAuxGenSuffix (name : Name) : Bool :=
  (classifyAuxGen name).isSome

/-! ## Telescope utilities (aux_source.rs) -/

/-- Mirrors Rust `collect_lean_telescope` (aux_source.rs).

    Collect a Lean App telescope: peel App nodes to get
    `(head, #[a1, ..., aN])`, arguments in application order (leftmost
    first). Same walk as `decomposeApps` (Rust keeps both — aux_source.rs's
    reference-based collector and expr_utils' owned `decompose_apps`);
    the Lean port delegates so the two can never drift. -/
def collectLeanTelescope (e : Expr) : Expr × Array Expr :=
  decomposeApps e

/-- Mirrors Rust `collect_ixon_telescope` (aux_source.rs).

    Collect an Ixon App telescope: peel App nodes to get
    `(head, #[a1, ..., aN])`, arguments in application order (leftmost
    first). -/
def collectIxonTelescope (e : Ixon.Expr) : Ixon.Expr × Array Ixon.Expr :=
  Id.run do
    let mut args : Array Ixon.Expr := #[]
    let mut cur := e
    repeat
      match cur with
      | .app f a =>
        args := args.push a
        cur := f
      | _ => break
    return (cur, args.reverse)

/-! ## Aux motive signatures (aux_source.rs) -/

/-- Signature of a nested-aux motive read off a source recursor's type:
    motive `sourcePos` targets `extName specs… idx…`. Spec args are
    concrete (the recursor type is instantiated with call-site params
    before extraction), so field types can be matched against them by
    hash. Mirrors Rust `AuxMotiveSig` (aux_source.rs). -/
structure AuxMotiveSig where
  sourcePos : Nat
  extName : Name
  extNParams : Nat
  specs : Array Expr
  deriving Repr, Nonempty, Inhabited

/-- Extract `AuxMotiveSig`s for every aux motive position (`≥ all.size`)
    of `recVal`, by walking its type instantiated with the call site's
    levels, params, and motives. Mirrors Rust `aux_motive_sigs`
    (aux_source.rs). -/
def auxMotiveSigs (recVal : RecursorVal) (recLevels : Array Level)
    (params : Array Expr) (motives : Array Expr) (env : Ix.Environment) :
    Array AuxMotiveSig := Id.run do
  let nUser := recVal.all.size
  let nMotives := recVal.numMotives
  let mut out : Array AuxMotiveSig := #[]
  if nMotives <= nUser then
    return out
  let mut cur :=
    substLevels recVal.cnst.type recVal.cnst.levelParams recLevels
  for arg in params do
    match cur with
    | .forallE _ _ body _ _ =>
      -- Shift-aware substitution — args may reference the caller's
      -- telescope (see `source_minor_type`, aux_source.rs).
      cur := instantiateRev body #[arg]
    | _ => return out
  for (motive, mIdx) in motives.zipIdx do
    if mIdx >= nMotives then
      break
    match cur with
    | .forallE _ dom body _ _ =>
      if mIdx >= nUser then
        -- dom = `∀ idx…, Ext specs… idx… → Sort _` — the major's type is
        -- the last peeled domain (aux_source.rs).
        let mut d := consumeTypeAnnotations dom
        let mut lastDom : Option Expr := none
        let mut i : Nat := 0
        repeat
          match d with
          | .forallE _ dd db _ _ =>
            lastDom := some (consumeTypeAnnotations dd)
            let (_, fv) := freshFVar "aux_sig_idx" (mIdx * 64 + i)
            d := instantiate1 db fv
            i := i + 1
          | _ => break
        if let some t := lastDom then
          let (head, tArgs) := decomposeApps t
          if let .const extName _ _ := head then
            match env.get? extName with
            | some (.inductInfo ind) =>
              let extNParams := ind.numParams
              if tArgs.size >= extNParams then
                out := out.push {
                  sourcePos := mIdx
                  extName, extNParams
                  specs := tArgs.extract 0 extNParams }
            | _ => pure ()
      cur := instantiateRev body #[motive]
    | _ => return out
  return out

/-! ## The source side of a split minor (O2, O11a) -/

/-- Source minor index → `(sourcePos, ConstructorVal)` across the user
    minor bands (one per `rec.all` inductive, in source order) followed
    by the aux minor bands (one per source aux, the external inductive's
    own ctor list). Mirrors Rust `source_ctor_for_minor`
    (aux_source.rs). -/
def sourceCtorForMinor (srcMinorIdx : Nat) (recVal : RecursorVal)
    (env : Ix.Environment) (auxSigs : Array AuxMotiveSig) :
    Option (Nat × ConstructorVal) := Id.run do
  let mut offset : Nat := 0
  for (indName, sourcePos) in recVal.all.zipIdx do
    let some ci := env.get? indName | return none
    let .inductInfo ind := ci | return none
    let nCtors := ind.ctors.size
    if srcMinorIdx < offset + nCtors then
      let ctorName := ind.ctors[srcMinorIdx - offset]!
      let some cci := env.get? ctorName | return none
      let .ctorInfo ctor := cci | return none
      return some (sourcePos, ctor)
    offset := offset + nCtors
  -- Aux minor bands follow the user bands, one per source aux in source
  -- order. The ctor list is the external inductive's own (the aux is the
  -- external applied at spec args, so field counts match).
  for sig in auxSigs do
    let some (.inductInfo ind) := env.get? sig.extName
      | return none
    let nCtors := ind.ctors.size
    if srcMinorIdx < offset + nCtors then
      let ctorName := ind.ctors[srcMinorIdx - offset]!
      let some cci := env.get? ctorName | return none
      let .ctorInfo ctor := cci | return none
      return some (sig.sourcePos, ctor)
    offset := offset + nCtors
  return none

/-- Instantiated type of the `srcMinorIdx`-th minor binder of a source
    recursor, expressed in caller terms. Mirrors Rust `source_minor_type`
    (aux_source.rs). -/
def sourceMinorType (recVal : RecursorVal) (recLevels : Array Level)
    (params : Array Expr) (motives : Array Expr) (minors : Array Expr)
    (srcMinorIdx : Nat) : Option Expr := Id.run do
  let mut cur :=
    substLevels recVal.cnst.type recVal.cnst.levelParams recLevels
  for arg in params ++ motives ++ minors.extract 0 srcMinorIdx do
    match cur with
    | .forallE _ _ body _ _ =>
      -- `instantiateRev`, not `instantiate1`: call-site args may carry
      -- loose BVars into the caller's telescope (rec applications under
      -- binders, e.g. `.brecOn_N.go` bodies) and must be lifted when
      -- substituted under the type's remaining binders (aux_source.rs).
      cur := instantiateRev body #[arg]
    | _ => return none
  match cur with
  | .forallE _ dom _ _ _ => return some (consumeTypeAnnotations dom)
  | _ => return none

/-- Open `n` foralls into fresh-FVar `LocalDecl`s, returning
    `(decls, fvars, remainder)`. Mirrors Rust `peel_binders`
    (aux_source.rs). -/
def peelBinders (cur₀ : Expr) (n : Nat) (pfx : String) (offset : Nat) :
    Option (Array LocalDecl × Array Expr × Expr) := Id.run do
  let mut cur := cur₀
  let mut decls : Array LocalDecl := #[]
  let mut fvars : Array Expr := #[]
  for i in [0:n] do
    match cur with
    | .forallE name dom body bi _ =>
      let (fvName, fv) := freshFVar pfx (offset + i)
      let decl : LocalDecl := {
        fvarName := fvName
        binderName := name
        domain := consumeTypeAnnotations dom
        info := bi }
      cur := instantiate1 body fv
      fvars := fvars.push fv
      decls := decls.push decl
    | _ => return none
  return some (decls, fvars, cur)

/-- A minor field whose (peeled) type targets a source or aux inductive:
    the target's source position, the index args of the occurrence, and
    the field's own binder telescope. Mirrors Rust `SourceRecTarget`
    (aux_source.rs). -/
structure SourceRecTarget where
  sourcePos : Nat
  idxArgs : Array Expr
  xsDecls : Array LocalDecl
  xsFvars : Array Expr
  deriving Repr, Nonempty, Inhabited

/-- Detect whether a minor field's domain targets one of the source
    inductives (`originalAll`) at the call-site params, or a nested-aux
    occurrence matching one of the recursor's aux motive signatures.
    Mirrors Rust `find_source_rec_target` (aux_source.rs).

    (Rust indexes fresh FVars with `field_idx.saturating_mul(1024)`;
    `Nat` multiplication cannot overflow, and the saturation point is
    unreachable for real field counts, so a plain `*` is exact.) -/
def findSourceRecTarget (dom : Expr) (originalAll : Array Name)
    (params : Array Expr) (env : Ix.Environment) (pfx : String)
    (fieldIdx : Nat) (auxSigs : Array AuxMotiveSig) :
    Option SourceRecTarget := Id.run do
  let mut cur := consumeTypeAnnotations dom
  let mut xsDecls : Array LocalDecl := #[]
  let mut xsFvars : Array Expr := #[]
  repeat
    match cur with
    | .forallE name d body bi _ =>
      let (fvName, fv) := freshFVar pfx (fieldIdx * 1024 + xsFvars.size)
      let decl : LocalDecl := {
        fvarName := fvName
        binderName := name
        domain := consumeTypeAnnotations d
        info := bi }
      cur := instantiate1 body fv
      xsFvars := xsFvars.push fv
      xsDecls := xsDecls.push decl
    | _ => break
  let (head, args) := decomposeApps cur
  let .const targetName _ _ := head | return none
  match originalAll.findIdx? (· == targetName) with
  | some sourcePos =>
    let some ci := env.get? targetName | return none
    let .inductInfo ind := ci | return none
    let targetNParams := ind.numParams
    if args.size < targetNParams || params.size < targetNParams then
      return none
    for i in [0:targetNParams] do
      if args[i]!.getHash != params[i]!.getHash then
        return none
    return some {
      sourcePos
      idxArgs := args.extract targetNParams args.size
      xsDecls, xsFvars }
  | none =>
    -- Nested-aux target: the field's type is an external-inductive
    -- application matching one of the recursor's aux motive signatures
    -- (`List B` targeting motive `n_user + j`). Spec args are compared by
    -- hash — both sides are instantiated with the same call-site params.
    let matched? := auxSigs.find? fun sig =>
      targetName == sig.extName
        && args.size >= sig.extNParams
        && ((args.extract 0 sig.extNParams).zip sig.specs |>.all
              fun (a, s) => a.getHash == s.getHash)
    let some matched := matched? | return none
    return some {
      sourcePos := matched.sourcePos
      idxArgs := args.extract matched.extNParams args.size
      xsDecls, xsFvars }

/-! ## Existence of the `.below`/`.brecOn` families (A0, WB-B1) -/

/-- Whether a type is a Prop former: a forall telescope ending in `Prop`
    (Lean's `isPropFormerType` on an inductive's type, a syntactic telescope
    for every inductive the elaborator emits). Mirrors Rust
    `is_prop_former` (aux_gen.rs). -/
def isPropFormer (typ : Expr) : Bool := Id.run do
  let mut cur := typ
  repeat
    match cur with
    | .forallE _ _ body _ _ => cur := body
    | .sort (.zero _) _ => return true
    | _ => return false
  return false -- unreachable: the loop always returns

/-- Whether Lean generates the `.below`/`.brecOn` families (and their nested
    `_N` members) for the Lean mutual block `originalAll`, by Lean's own
    conditions, never by name shape:

    - Type-level (`Lean.Meta.mkBelow`/`mkBRecOn`): the inductive is
      recursive (`isRec`) and not a Prop former;
    - Prop-level (`Lean.Meta.IndPredBelow.mkBelow`): the inductive predicate
      is recursive and not `unsafe` (Lean also skips classes, which the
      compiler's environment does not record).

    `isRec` is a property of the whole Lean block, so the first member found
    decides. A user constant named `T.below`/`T.brecOn` for a non-recursive
    `T` (a definition, or a structure field accessor such as
    `IndPredBelow.NewDecl.below`) is therefore never taken for the
    auxiliary. Mirrors Rust `below_family_lean_exists` (aux_gen.rs). -/
def belowFamilyLeanExists (lookup : Name → Option ConstantInfo)
    (originalAll : Array Name) : Bool := Id.run do
  for n in originalAll do
    match lookup n with
    | some (.inductInfo v) =>
      return v.isRec && !(v.isUnsafe && isPropFormer v.cnst.type)
    | _ => pure ()
  return false

/-- The block a refusal names: the first member of its first canonical
    class. Mirrors Rust `aux_gen::block_label`. -/
def blockLabel (sortedClasses : Array (Array Name)) : String :=
  match sortedClasses[0]? >>= (·[0]?) with
  | some n => n.pretty
  | none => "<empty>"

end Ix.AuxGen
