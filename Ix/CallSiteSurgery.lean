/-
  Ix.CallSiteSurgery: call-site surgery — CONSUMPTION half.

  Port of the consumption half of `crates/compile/src/compile/surgery.rs`:
  the expression-rewriting machinery `compile_expr`'s call-site arms apply
  when a compiled body calls an auxiliary whose canonical layout differs
  from Lean source order.

  Like `Ix.CallSitePlan`, this lives BELOW `Ix.CompileM` as a leaf module
  (unlike Rust, where everything shares one crate): plans are COMPUTED by
  `Ix.AuxGen.Surgery` (above CompileM) but CONSUMED by
  `Ix.CompileM.compileExpr` — so the consumption functions must sit below
  both. Namespace stays `Ix.AuxGen`. Environment access: Rust threads
  `lean_env: &LeanEnv`; here every consumer takes an explicit
  `env : Ix.Environment` parameter (the same canonicalized environment
  `CompileEnv.env` holds).

  Contents:
  - `isAuxGenSuffix` (decompile.rs:2151 / `classify_aux_gen`
    decompile.rs:2157) — the compile-side aux-regen guard predicate. Only
    the boolean projection is ported; the `(AuxKind, root)` payload is
    used exclusively by the decompiler (out of scope).
  - `collectLeanTelescope` / `collectIxonTelescope` (surgery.rs:208/225).
  - `AuxMotiveSig` / `auxMotiveSigs` (surgery.rs:992/1002).
  - `deriveHeadRewriteApp` (surgery.rs:1076) — head-rewrite spine pieces.
  - `sourceCtorForMinor` (surgery.rs:942), `sourceMinorType`
    (surgery.rs:1168), `peelBinders` (surgery.rs:1197),
    `SourceRecTarget` / `findSourceRecTarget` (surgery.rs:1226/1233),
    `synthesizeExternalIh` (surgery.rs:1306), `adaptSplitMinor`
    (surgery.rs:834).

  Not ported: `dump_plan_state` (surgery.rs:1354) and the
  `IX_SPLIT_MINOR_DUMP` stderr diagnostic inside `adapt_split_minor` —
  env-var debug blocks are not ported, matching the `IX_RECURSOR_DUMP`
  precedent in `Ix.AuxGen.Nested`.

  PARITY RULE: every constructed node goes through the hash-maintaining
  smart constructors in `Ix.Environment` (`Expr.mkApp`, `Name.mkStr`, ...)
  so the embedded blake3 hashes stay bit-identical with the Rust compiler.
-/
module
public import Ix.Common
public import Ix.Address
public import Ix.Environment
public import Ix.Ixon
public import Ix.CallSitePlan
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
      some (.casesOnAux, p1)
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
    (decompile.rs:2151). Used by the compile-side aux-regen guard in
    `compile_expr` (compile.rs:829) and the decompiler's Pass-1 skip. -/
def isAuxGenSuffix (name : Name) : Bool :=
  (classifyAuxGen name).isSome

/-! ## Telescope utilities (surgery.rs:201) -/

/-- Mirrors Rust `collect_lean_telescope` (surgery.rs:208).

    Collect a Lean App telescope: peel App nodes to get
    `(head, #[a1, ..., aN])`, arguments in application order (leftmost
    first). Same walk as `decomposeApps` (Rust keeps both — surgery.rs's
    reference-based collector and expr_utils' owned `decompose_apps`);
    the Lean port delegates so the two can never drift. -/
def collectLeanTelescope (e : Expr) : Expr × Array Expr :=
  decomposeApps e

/-- Mirrors Rust `collect_ixon_telescope` (surgery.rs:225).

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

/-! ## Aux motive signatures (surgery.rs:992) -/

/-- Signature of a nested-aux motive read off a source recursor's type:
    motive `sourcePos` targets `extName specs… idx…`. Spec args are
    concrete (the recursor type is instantiated with call-site params
    before extraction), so field types can be matched against them by
    hash. Mirrors Rust `AuxMotiveSig` (surgery.rs:992). -/
structure AuxMotiveSig where
  sourcePos : Nat
  extName : Name
  extNParams : Nat
  specs : Array Expr
  deriving Repr, Nonempty, Inhabited

/-- Extract `AuxMotiveSig`s for every aux motive position (`≥ all.size`)
    of `recVal`, by walking its type instantiated with the call site's
    levels, params, and motives. Mirrors Rust `aux_motive_sigs`
    (surgery.rs:1002). -/
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
      -- telescope (see `source_minor_type`, surgery.rs:1019).
      cur := instantiateRev body #[arg]
    | _ => return out
  for (motive, mIdx) in motives.zipIdx do
    if mIdx >= nMotives then
      break
    match cur with
    | .forallE _ dom body _ _ =>
      if mIdx >= nUser then
        -- dom = `∀ idx…, Ext specs… idx… → Sort _` — the major's type is
        -- the last peeled domain (surgery.rs:1031).
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
            match env.consts.get? extName with
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

/-- Derive the pieces needed to rebuild a head-rewritten call site onto
    the external recursor's telescope: the extended universe-level list
    and the external inductive's parameter (spec) arguments.

    Both are read off the SOURCE aux recursor's type — the motive binder
    at `hr.targetMotivePos` has domain `∀ idx…, Ext.{occ} specs… idx… →
    Sort _` — instantiated with the call site's levels, params, and
    preceding motives, so the result is expressed in caller terms.

    Mirrors Rust `derive_head_rewrite_app` (surgery.rs:1076), including
    its `Result<_, String>` error channel (`Except String` — the
    consumption caller decides how to wrap failures). -/
def deriveHeadRewriteApp (recName : Name) (recLevels : Array Level)
    (hr : AuxHeadRewrite) (params : Array Expr) (motives : Array Expr)
    (env : Ix.Environment) :
    Except String (Array Level × Array Expr) := Id.run do
  let some (.recInfo recVal) := env.consts.get? recName
    | return .error s!"'{recName.pretty}' is not a recursor"
  let sigs := auxMotiveSigs recVal recLevels params motives env
  let some sig := sigs.find? fun s => s.sourcePos == hr.targetMotivePos
    | return .error s!"no aux motive signature at position {hr.targetMotivePos}"
  if Name.mkStr sig.extName "rec" != hr.targetRec then
    return .error s!"aux motive targets '{sig.extName.pretty}' but the \
plan's target is '{hr.targetRec.pretty}'"
  -- Occurrence levels: re-extract the external const's level args from
  -- the motive's major type — `auxMotiveSigs` keeps only the value args
  -- (surgery.rs:1105).
  let mut cur :=
    substLevels recVal.cnst.type recVal.cnst.levelParams recLevels
  for arg in params ++ motives.extract 0 hr.targetMotivePos do
    match cur with
    | .forallE _ _ body _ _ =>
      -- Shift-aware substitution — args may reference the caller's
      -- telescope (see `source_minor_type`, surgery.rs:1110).
      cur := instantiateRev body #[arg]
    | _ => return .error "recursor telescope too short"
  let .forallE _ dom _ _ _ := cur
    | return .error "missing target motive binder"
  let mut d := consumeTypeAnnotations dom
  let mut lastDom : Option Expr := none
  let mut i : Nat := 0
  repeat
    match d with
    | .forallE _ dd db _ _ =>
      lastDom := some (consumeTypeAnnotations dd)
      let (_, fv) := freshFVar "hr_idx" i
      d := instantiate1 db fv
      i := i + 1
    | _ => break
  let some t := lastDom
    | return .error "motive domain has no major binder"
  let (head, _) := decomposeApps t
  let occLevels : Array Level ←
    match head with
    | .const _ lvls _ => pure lvls
    | _ => return .error "major type head is not a constant"
  let some (.recInfo target) := env.consts.get? hr.targetRec
    | return .error
        s!"target recursor '{hr.targetRec.pretty}' missing from env"
  let needed := target.cnst.levelParams.size
  let targetLevels : Array Level ←
    if needed == occLevels.size + 1 then
      -- Elimination level first (Lean's recursor level convention), then
      -- the external inductive's own levels from the occurrence.
      let some elim := recLevels[0]?
        | return .error "source recursor has no elimination level"
      pure (#[elim] ++ occLevels)
    else if needed == occLevels.size then
      pure occLevels
    else
      return .error s!"cannot map universe levels: target \
'{hr.targetRec.pretty}' has {needed} level params, occurrence supplies \
{occLevels.size}"
  return .ok (targetLevels, sig.specs)

/-! ## Split-minor adaptation (surgery.rs:834-1352) -/

/-- Source minor index → `(sourcePos, ConstructorVal)` across the user
    minor bands (one per `rec.all` inductive, in source order) followed
    by the aux minor bands (one per source aux, the external inductive's
    own ctor list). Mirrors Rust `source_ctor_for_minor`
    (surgery.rs:942). -/
def sourceCtorForMinor (srcMinorIdx : Nat) (recVal : RecursorVal)
    (env : Ix.Environment) (auxSigs : Array AuxMotiveSig) :
    Option (Nat × ConstructorVal) := Id.run do
  let mut offset : Nat := 0
  for (indName, sourcePos) in recVal.all.zipIdx do
    let some ci := env.consts.get? indName | return none
    let .inductInfo ind := ci | return none
    let nCtors := ind.ctors.size
    if srcMinorIdx < offset + nCtors then
      let ctorName := ind.ctors[srcMinorIdx - offset]!
      let some cci := env.consts.get? ctorName | return none
      let .ctorInfo ctor := cci | return none
      return some (sourcePos, ctor)
    offset := offset + nCtors
  -- Aux minor bands follow the user bands, one per source aux in source
  -- order. The ctor list is the external inductive's own (the aux is the
  -- external applied at spec args, so field counts match).
  for sig in auxSigs do
    let some (.inductInfo ind) := env.consts.get? sig.extName
      | return none
    let nCtors := ind.ctors.size
    if srcMinorIdx < offset + nCtors then
      let ctorName := ind.ctors[srcMinorIdx - offset]!
      let some cci := env.consts.get? ctorName | return none
      let .ctorInfo ctor := cci | return none
      return some (sig.sourcePos, ctor)
    offset := offset + nCtors
  return none

/-- Instantiated type of the `srcMinorIdx`-th minor binder of a source
    recursor, expressed in caller terms. Mirrors Rust `source_minor_type`
    (surgery.rs:1168). -/
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
      -- substituted under the type's remaining binders (surgery.rs:1180).
      cur := instantiateRev body #[arg]
    | _ => return none
  match cur with
  | .forallE _ dom _ _ _ => return some (consumeTypeAnnotations dom)
  | _ => return none

/-- Open `n` foralls into fresh-FVar `LocalDecl`s, returning
    `(decls, fvars, remainder)`. Mirrors Rust `peel_binders`
    (surgery.rs:1197). -/
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
    (surgery.rs:1226). -/
structure SourceRecTarget where
  sourcePos : Nat
  idxArgs : Array Expr
  xsDecls : Array LocalDecl
  xsFvars : Array Expr
  deriving Repr, Nonempty, Inhabited

/-- Detect whether a minor field's domain targets one of the source
    inductives (`originalAll`) at the call-site params, or a nested-aux
    occurrence matching one of the recursor's aux motive signatures.
    Mirrors Rust `find_source_rec_target` (surgery.rs:1233).

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
    let some ci := env.consts.get? targetName | return none
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

/-- Build the recursive-call IH for a field targeting an out-of-block
    source position: eliminate with the target's own source recursor
    (user targets) or the source aux recursor `<all0>.rec_{j+1}` (aux
    targets), passing the full source telescope verbatim — the inner call
    then goes through its own call-site surgery (plan lookup by head
    name), which canonicalizes it for its SCC. Mirrors Rust
    `synthesize_external_ih` (surgery.rs:1306). -/
def synthesizeExternalIh (target : SourceRecTarget) (fieldFVar : Expr)
    (originalAll : Array Name) (recLevels : Array Level)
    (params : Array Expr) (motives : Array Expr) (minors : Array Expr) :
    Expr := Id.run do
  let targetRecName :=
    if target.sourcePos < originalAll.size then
      Name.mkStr originalAll[target.sourcePos]! "rec"
    else
      let auxJ := target.sourcePos - originalAll.size
      Name.mkStr originalAll[0]! s!"rec_{auxJ + 1}"
  let mut ih := Expr.mkConst targetRecName recLevels
  for arg in params do
    ih := Expr.mkApp ih arg
  for arg in motives do
    ih := Expr.mkApp ih arg
  for arg in minors do
    ih := Expr.mkApp ih arg
  for idx in target.idxArgs do
    ih := Expr.mkApp ih idx
  let mut fieldApp := fieldFVar
  for fv in target.xsFvars do
    fieldApp := Expr.mkApp fieldApp fv
  ih := Expr.mkApp ih fieldApp
  return mkLambda ih target.xsDecls

/-- Adapt a kept source minor for a canonical recursor whose SCC is
    smaller than Lean's original mutual `all` block.

    Lean's source recursor minor for a constructor receives an IH
    argument for every recursive field targeting any inductive in the
    original mutual block. After canonical SCC splitting, the regenerated
    recursor only supplies IHs for fields targeting the current SCC. For
    fields targeting another SCC, we synthesize the missing IH by
    recursively calling the target's source recursor with the original
    source-order motive/minor telescope. That inner recursor call then
    goes through the normal call-site surgery for its own SCC.

    Returns `none` when no adaptation is needed (every source position is
    in-block, or the minor's fields target nothing out-of-block).
    Mirrors Rust `adapt_split_minor` (surgery.rs:834). The
    `IX_SPLIT_MINOR_DUMP` leak diagnostic is not ported. -/
def adaptSplitMinor (recName : Name) (recLevels : Array Level)
    (plan : CallSitePlan) (srcMinorIdx : Nat) (minor : Expr)
    (params : Array Expr) (motives : Array Expr) (minors : Array Expr)
    (env : Ix.Environment) : Option Expr := Id.run do
  if plan.sourceInBlock.all (fun inBlock => inBlock) then
    return none
  let some recCi := env.consts.get? recName | return none
  let .recInfo recVal := recCi | return none
  let originalAll := recVal.all
  -- Nested-aux motive signatures: fields targeting an aux occurrence
  -- (`List B` rather than a user original) also carry IH binders in the
  -- source minor; they must be detected for the peel below to stay
  -- aligned, and synthesized/kept like user-target IHs.
  let auxSigs := auxMotiveSigs recVal recLevels params motives env
  let some (_parentSrc, ctor) :=
    sourceCtorForMinor srcMinorIdx recVal env auxSigs | return none
  let nFields := ctor.numFields
  let some sourceMinorTy :=
    sourceMinorType recVal recLevels params motives minors srcMinorIdx
    | return none
  let some (fieldDecls, fieldFVars, afterFields) :=
    peelBinders sourceMinorTy nFields "split_field" 0 | return none
  let mut recFields : Array (Nat × SourceRecTarget) := #[]
  for (decl, fieldIdx) in fieldDecls.zipIdx do
    if let some target := findSourceRecTarget decl.domain originalAll
        params env "split_xs" fieldIdx auxSigs then
      recFields := recFields.push (fieldIdx, target)
  if !recFields.any (fun (_, target) =>
      !(plan.sourceInBlock.getD target.sourcePos false)) then
    return none
  let some (sourceIhDecls, sourceIhFVars, _) :=
    peelBinders afterFields recFields.size "split_ih" 0 | return none
  if sourceIhDecls.size != recFields.size then
    return none
  let mut wrapperDecls := fieldDecls
  let mut body := minor
  for fv in fieldFVars do
    body := Expr.mkApp body fv
  for ((fieldIdx, target), ihIdx) in recFields.zipIdx do
    if plan.sourceInBlock.getD target.sourcePos false then
      wrapperDecls := wrapperDecls.push sourceIhDecls[ihIdx]!
      body := Expr.mkApp body sourceIhFVars[ihIdx]!
    else
      let synth := synthesizeExternalIh target fieldFVars[fieldIdx]!
        originalAll recLevels params motives minors
      body := Expr.mkApp body synth
  return some (mkLambda body wrapperDecls)

end Ix.AuxGen
