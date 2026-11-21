module

public import Ix.Compile.SourceContract.Registry
public import Ix.Compile.SourceContract.Syntax
public meta import Ix.Compile.SourceContract.Registry
public meta import Ix.Compile.SourceContract.Syntax

/-!
# Scoped `@`-prefixed mode syntax elaboration

Activates strictly under `open scoped Ix.Modes` (`namespace Ix.Modes`).
Elaborates:
- Binder modes (7, composable, order-insensitive) in `(...)`, `{...}`, `⦃...⦄`,
  `[...]`, including multi-name groups and optional `: T` in `fun`
- Result modes (4) after `:` in `def`/`abbrev`/`opaque`/`axiom`, after `→`/`->`,
  and after `∀ ...,`
- `let` and `do`-block `let` (8 modes, unparenthesized, optional `: T`,
  including `let @borrow v := owner`)
- `structure` and `inductive` field modes (`@shared` -> `FieldMode.shared`,
  `@erased` -> constructor binder `.erased`)
- Native scoped `DefAsserts` attributes (`@[no_rc]`, `@[no_alloc]`,
  `@[bounded_stack]`)
-/

public section

namespace Ix.Compile.SourceElab

open Lean Elab Command Term

private meta def atomKeyword (atomNode : Syntax) : String :=
  if atomNode.getNumArgs >= 2 && atomNode[1].isAtom then atomNode[1].getAtomVal else ""

private meta def decodeBinderPrefix (modes : Syntax) : TermElabM Ixon.BinderMode := do
  let parts := modes[0].getArgs
  let mut hasBorrowed := false
  let mut hasUnique := false
  let mut hasOnce := false
  let mut hasErased := false
  for part in parts do
    let kw := atomKeyword part
    match kw with
    | "borrowed" =>
      if hasBorrowed then throwErrorAt part "duplicate @borrowed mode annotation"
      hasBorrowed := true
    | "unique" =>
      if hasUnique then throwErrorAt part "duplicate @unique mode annotation"
      hasUnique := true
    | "once" =>
      if hasOnce then throwErrorAt part "duplicate @once mode annotation"
      hasOnce := true
    | "erased" =>
      if hasErased then throwErrorAt part "duplicate @erased mode annotation"
      hasErased := true
    | _ =>
      throwErrorAt part "unsupported binder mode annotation '@{kw}'"
  if hasErased then
    if hasBorrowed || hasUnique || hasOnce then
      throwErrorAt modes "@erased cannot be combined with other mode annotations"
    return .erased
  if hasOnce && hasUnique then
    throwErrorAt modes "@once cannot be combined with @unique"
  match hasUnique, hasOnce, hasBorrowed with
  | true, false, false => return .unique
  | true, false, true => return .uniqueBorrowed
  | false, true, false => return .once
  | false, true, true => return .onceBorrowed
  | false, false, true => return .borrowed
  | _, _, _ => return .many

private meta def decodeResultPrefix (modes : Syntax) : TermElabM Ixon.ResultMode := do
  let parts := modes[0].getArgs
  let mut hasBorrowed := false
  let mut hasUnique := false
  for part in parts do
    let kw := atomKeyword part
    match kw with
    | "borrowed" =>
      if hasBorrowed then throwErrorAt part "duplicate @borrowed mode annotation"
      hasBorrowed := true
    | "unique" =>
      if hasUnique then throwErrorAt part "duplicate @unique mode annotation"
      hasUnique := true
    | "once" =>
      throwErrorAt part "@once is not a valid result mode; result modes allow only @unique and @borrowed"
    | "erased" =>
      throwErrorAt part "@erased is not a valid result mode; result modes allow only @unique and @borrowed"
    | _ =>
      throwErrorAt part "unsupported result mode annotation '@{kw}'"
  match hasUnique, hasBorrowed with
  | true, true => return .uniqueBorrowed
  | true, false => return .unique
  | false, true => return .borrowed
  | false, false => return .shared

private meta def decodeLetPrefix (modes : Syntax) : TermElabM (Ixon.BinderMode × Bool) := do
  let parts := modes[0].getArgs
  let mut hasBorrow := false
  let mut hasBorrowed := false
  let mut hasUnique := false
  let mut hasOnce := false
  let mut hasErased := false
  for part in parts do
    let kw := atomKeyword part
    match kw with
    | "borrow" =>
      if hasBorrow then throwErrorAt part "duplicate @borrow mode annotation"
      hasBorrow := true
    | "borrowed" =>
      if hasBorrowed then throwErrorAt part "duplicate @borrowed mode annotation"
      hasBorrowed := true
    | "unique" =>
      if hasUnique then throwErrorAt part "duplicate @unique mode annotation"
      hasUnique := true
    | "once" =>
      if hasOnce then throwErrorAt part "duplicate @once mode annotation"
      hasOnce := true
    | "erased" =>
      if hasErased then throwErrorAt part "duplicate @erased mode annotation"
      hasErased := true
    | _ =>
      throwErrorAt part "unsupported let mode annotation '@{kw}'"
  if hasBorrow then
    if hasBorrowed || hasUnique || hasOnce || hasErased then
      throwErrorAt modes "@borrow cannot be combined with other mode annotations"
    return (.borrowed, true)
  if hasErased then
    if hasBorrowed || hasUnique || hasOnce then
      throwErrorAt modes "@erased cannot be combined with other mode annotations"
    return (.erased, false)
  if hasOnce && hasUnique then
    throwErrorAt modes "@once cannot be combined with @unique"
  let mode : Ixon.BinderMode := match hasUnique, hasOnce, hasBorrowed with
    | true, false, false => .unique
    | true, false, true => .uniqueBorrowed
    | false, true, false => .once
    | false, true, true => .onceBorrowed
    | false, false, true => .borrowed
    | _, _, _ => .many
  return (mode, false)

private meta inductive FieldAnnotation where
  | shared
  | erased
  deriving BEq, DecidableEq, Repr

private meta def decodeFieldPrefix (modes : Syntax) : TermElabM FieldAnnotation := do
  let parts := modes[0].getArgs
  let mut hasShared := false
  let mut hasErased := false
  for part in parts do
    let kw := atomKeyword part
    match kw with
    | "shared" =>
      if hasShared then throwErrorAt part "duplicate @shared mode annotation"
      hasShared := true
    | "erased" =>
      if hasErased then throwErrorAt part "duplicate @erased mode annotation"
      hasErased := true
    | _ =>
      throwErrorAt part "@{kw} is not a valid field mode; structure and inductive fields only allow @shared or @erased"
  if hasShared && hasErased then
    throwErrorAt modes "@erased cannot be combined with @shared on a field"
  if hasShared then return .shared
  if hasErased then return .erased
  throwErrorAt modes "expected @shared or @erased field mode"

private meta def sourceOrigin (stx : Syntax) : Nat :=
  (stx.getPos?.map (·.byteIdx)).getD 0

private meta def markTypeSyntax (ref : Syntax) (binderName : Lean.Name) (type : Term)
    (mode : Ixon.BinderMode) (result : Option Ixon.ResultMode := none)
    (isBorrow : Bool := false) : TermElabM Term := do
  let origin := Syntax.mkNumLit (toString (sourceOrigin ref))
  let nameIdent := mkIdent (if binderName == .anonymous then `_ else binderName)
  let modeLit := Syntax.mkNumLit (toString mode.toCode.toNat)
  let resultLit := Syntax.mkNumLit (toString ((result.map (·.toCode.toNat)).getD 4))
  let borrowLit := Syntax.mkNumLit (if isBorrow then "1" else "0")
  return ⟨Syntax.node (SourceInfo.fromRef ref) ``SourceSyntax.annotatedType
    #[mkAtom "__ix_binder_internal", origin, nameIdent, modeLit, resultLit, borrowLit,
      mkAtom "(", type.raw, mkAtom ")"]⟩

@[term_elab SourceSyntax.annotatedType]
meta def elabAnnotatedType : TermElab := fun stx expectedType? => do
  let some origin := stx[1].isNatLit? | throwErrorAt stx "invalid source annotation origin"
  let rawName := stx[2].getId
  let binder := if rawName == `_ then .anonymous else rawName
  let some modeCode := stx[3].isNatLit? | throwErrorAt stx "invalid source binder mode"
  if modeCode >= 256 then throwErrorAt stx "invalid source binder mode"
  let some mode := Ixon.BinderMode.ofCode? modeCode.toUInt8
    | throwErrorAt stx "invalid source binder mode"
  let some resultCode := stx[4].isNatLit? | throwErrorAt stx "invalid source result mode"
  let result ← if resultCode == 4 then pure none else do
    if resultCode >= 256 then throwErrorAt stx "invalid source result mode"
    let some r := Ixon.ResultMode.ofCode? resultCode.toUInt8
      | throwErrorAt stx "invalid source result mode"
    pure (some r)
  let isBorrow ← match stx[5].isNatLit? with
    | some 0 => pure false
    | some 1 => pure true
    | _ => throwErrorAt stx "invalid source let borrow flag"
  let annotation : BinderAnnotation := { origin, binder, mode, result, isBorrow }
  let type ← elabTerm stx[7] expectedType?
  match annotation.attach type with
  | .ok expr => return expr
  | .error error => throwErrorAt stx "{error}"

private meta def optTypeToTerm (ref : Syntax) (optTy : Syntax) : Term :=
  if optTy.isNone then ⟨mkHole ref⟩ else ⟨optTy[0][1]⟩

private meta def binderIdentName (b : Syntax) : Lean.Name :=
  if b.isIdent then b.getId else .anonymous

private meta def mkBracketedBinder (kind : SyntaxNodeKind) (bIdent : Syntax) (marked : Term) :
    TermElabM Syntax := do
  let typeSpec := mkNullNode #[mkAtom ":", marked.raw]
  if kind == ``SourceSyntax.explicitBinder then
    return (mkNode ``Parser.Term.explicitBinder
      #[mkAtom "(", mkNullNode #[bIdent], typeSpec, mkNullNode #[], mkAtom ")"]).raw
  else if kind == ``SourceSyntax.implicitBinder then
    return (mkNode ``Parser.Term.implicitBinder
      #[mkAtom "{", mkNullNode #[bIdent], typeSpec, mkAtom "}"]).raw
  else if kind == ``SourceSyntax.strictImplicitBinder then
    return (mkNode ``Parser.Term.strictImplicitBinder
      #[mkAtom "⦃", mkNullNode #[bIdent], typeSpec, mkAtom "⦄"]).raw
  else
    throwErrorAt bIdent "unexpected annotated binder kind"

/-- Split multi-name annotated or ordinary final binders before attaching the
result mode. The result belongs only to the last arrow in the group. -/
private meta def rewriteBinder (binder : Syntax)
    (result : Option Ixon.ResultMode := none) : TermElabM (Array Syntax) := do
  let kind := binder.getKind
  if SourceSyntax.isAnnotatedBinderKind kind then
    let mode ← decodeBinderPrefix binder[1]
    if kind == ``SourceSyntax.instanceBinder then
      let optName := binder[2]
      let ty : Term := ⟨binder[3]⟩
      if optName.isNone then
        let marked ← markTypeSyntax binder .anonymous ty mode result
        return #[(← `(bracketedBinder| [$marked])).raw]
      else
        let name : Ident := ⟨optName[0]⟩
        let marked ← markTypeSyntax name name.getId ty mode result
        return #[(← `(bracketedBinder| [$name:ident : $marked])).raw]
    else
      let names := binder[2].getArgs
      let ty := optTypeToTerm binder binder[3]
      let mut out := #[]
      for h : i in [:names.size] do
        let bIdent := names[i]
        let outResult := if i + 1 == names.size then result else none
        let marked ← markTypeSyntax bIdent (binderIdentName bIdent) ty mode outResult
        out := out.push (← mkBracketedBinder kind bIdent marked)
      return out
  if result.isNone then return #[binder]
  if binder.isIdent then
    let name : Ident := ⟨binder⟩
    let marked ← markTypeSyntax binder name.getId ⟨mkHole binder⟩ .many result
    return #[(← `(bracketedBinder| ($name:ident : $marked))).raw]
  if kind == ``Parser.Term.explicitBinder || kind == ``Parser.Term.implicitBinder ||
      kind == ``Parser.Term.strictImplicitBinder then
    if kind == ``Parser.Term.explicitBinder && !binder[3].isNone then
      throwErrorAt binder "put the result mode on an explicit arrow when the final binder has a default value"
    let names := binder[1].getArgs
    let some last := names.back? | throwErrorAt binder "missing result-bearing binder"
    let bName := binderIdentName last
    let type : Term := if binder[2].getNumArgs == 0 then ⟨mkHole binder⟩ else ⟨binder[2][1]⟩
    let marked ← markTypeSyntax last bName type .many result
    let typeSpec := mkNullNode #[mkAtom ":", marked.raw]
    let final := binder.setArg 1 (mkNullNode #[last]) |>.setArg 2 typeSpec
    if names.size == 1 then return #[final]
    return #[binder.setArg 1 (mkNullNode names.pop), final]
  if kind == ``Parser.Term.instBinder then
    let (nameStx, bName) :=
      if binder[1].isNone then (none, .anonymous)
      else (some (⟨binder[1][0]⟩ : Ident), binder[1][0].getId)
    let marked ← markTypeSyntax binder bName ⟨binder[2]⟩ .many result
    match nameStx with
    | none => return #[(← `(bracketedBinder| [$marked])).raw]
    | some name => return #[(← `(bracketedBinder| [$name:ident : $marked])).raw]
  throwErrorAt binder "unsupported result-bearing binder"

private meta def rewriteBinders (binders : Array Syntax)
    (result : Option Ixon.ResultMode := none) : TermElabM (Array Syntax) := do
  if binders.isEmpty && result.isSome then
    throwError "a result mode requires a function arrow"
  let mut rewritten := #[]
  for h : i in [:binders.size] do
    let output := if i + 1 == binders.size then result else none
    rewritten := rewritten ++ (← rewriteBinder binders[i] output)
  return rewritten

/-- Convert an annotated binder into an UNMARKED Lean binder while collecting
per-binder annotations for zero-leak post-attachment. -/
private meta def stripAnnotatedBinder (binder : Syntax)
    (result : Option Ixon.ResultMode := none) :
    TermElabM (Syntax × Array (Lean.BinderInfo × Option BinderAnnotation)) := do
  let kind := binder.getKind
  if SourceSyntax.isAnnotatedBinderKind kind then
    let mode ← decodeBinderPrefix binder[1]
    if kind == ``SourceSyntax.instanceBinder then
      let optName := binder[2]
      let ty : Term := ⟨binder[3]⟩
      if optName.isNone then
        let plain ← `(bracketedBinder| [$ty])
        let ann : BinderAnnotation := { origin := sourceOrigin binder, binder := .anonymous, mode, result }
        return (plain.raw, #[(.instImplicit, some ann)])
      else
        let name : Ident := ⟨optName[0]⟩
        let plain ← `(bracketedBinder| [$name:ident : $ty])
        let ann : BinderAnnotation := { origin := sourceOrigin name, binder := name.getId, mode, result }
        return (plain.raw, #[(.instImplicit, some ann)])
    else
      let names := binder[2].getArgs
      let optTy := binder[3]
      let bi : Lean.BinderInfo :=
        if kind == ``SourceSyntax.explicitBinder then .default
        else if kind == ``SourceSyntax.implicitBinder then .implicit
        else .strictImplicit
      let mut anns := #[]
      for h : i in [:names.size] do
        let bIdent := names[i]
        let outResult := if i + 1 == names.size then result else none
        anns := anns.push (bi, some {
          origin := sourceOrigin bIdent, binder := binderIdentName bIdent, mode, result := outResult })
      let typeSpec : Syntax := if optTy.isNone then mkNullNode #[] else optTy[0]
      let tyArg : Syntax := if optTy.isNone then mkNullNode #[] else mkNullNode #[typeSpec[0], typeSpec[1]]
      let plain : Syntax :=
        if kind == ``SourceSyntax.explicitBinder then
          (mkNode ``Parser.Term.explicitBinder #[binder[0], binder[2], tyArg, mkNullNode #[], binder[4]]).raw
        else if kind == ``SourceSyntax.implicitBinder then
          (mkNode ``Parser.Term.implicitBinder #[binder[0], binder[2], tyArg, binder[4]]).raw
        else
          (mkNode ``Parser.Term.strictImplicitBinder #[binder[0], binder[2], tyArg, binder[4]]).raw
      return (plain, anns)
  -- Ordinary binder
  if binder.isIdent || binder.isOfKind ``Parser.Term.hole then
    let ann := result.map fun r =>
      ({ origin := sourceOrigin binder, binder := binderIdentName binder, mode := .many, result := some r } : BinderAnnotation)
    return (binder, #[(.default, ann)])
  if kind == ``Parser.Term.explicitBinder || kind == ``Parser.Term.implicitBinder ||
      kind == ``Parser.Term.strictImplicitBinder then
    let bi : Lean.BinderInfo :=
      if kind == ``Parser.Term.explicitBinder then .default
      else if kind == ``Parser.Term.implicitBinder then .implicit
      else .strictImplicit
    let names := binder[1].getArgs
    let mut anns := #[]
    for h : i in [:names.size] do
      let ann := if i + 1 == names.size then result.map fun r =>
        ({ origin := sourceOrigin names[i], binder := binderIdentName names[i], mode := .many, result := some r } : BinderAnnotation)
        else none
      anns := anns.push (bi, ann)
    return (binder, anns)
  if kind == ``Parser.Term.instBinder then
    let bName := if binder[1].isNone then .anonymous else binder[1][0].getId
    let ann := result.map fun r =>
      ({ origin := sourceOrigin binder, binder := bName, mode := .many, result := some r } : BinderAnnotation)
    return (binder, #[(.instImplicit, ann)])
  throwErrorAt binder "unsupported binder shape"

private meta def attachLamAnnotations (ref : Syntax)
    (anns : List (Lean.BinderInfo × Option BinderAnnotation)) (e : Expr) : TermElabM Expr :=
  match e, anns with
  | e, [] => return e
  | .lam n ty body eBi, (bi, ann?) :: rest => do
    -- Skip auto-inserted implicit/instance lambdas introduced by an expected type.
    if eBi != bi && eBi != .default then
      return .lam n ty (← attachLamAnnotations ref anns body) eBi
    let ty' ← match ann? with
      | none => pure ty
      | some ann => match ann.attach ty with
        | .ok t => pure t
        | .error err => throwErrorAt ref "{err}"
    return .lam n ty' (← attachLamAnnotations ref rest body) eBi
  | .mdata d inner, _ => return .mdata d (← attachLamAnnotations ref anns inner)
  | _, _ => throwErrorAt ref "elaborated lambda did not match annotated binder telescope"

private meta def attachForallAnnotations (ref : Syntax)
    (anns : List (Lean.BinderInfo × Option BinderAnnotation)) (e : Expr) : TermElabM Expr :=
  match e, anns with
  | e, [] => return e
  | .forallE n ty body eBi, (_, ann?) :: rest => do
    let ty' ← match ann? with
      | none => pure ty
      | some ann => match ann.attach ty with
        | .ok t => pure t
        | .error err => throwErrorAt ref "{err}"
    return .forallE n ty' (← attachForallAnnotations ref rest body) eBi
  | .mdata d inner, _ => return .mdata d (← attachForallAnnotations ref anns inner)
  | _, _ => throwErrorAt ref "elaborated forall did not match annotated binder telescope"

@[term_elab SourceSyntax.annotatedFun]
meta def elabAnnotatedFun : TermElab := fun stx expectedType? => do
  let signature := stx[1]
  let rawBinders := signature[0].getArgs
  -- Check if all binders are standard (no destructuring patterns) for zero-leak attachment.
  let canZeroLeak := rawBinders.all fun b =>
    let k := b.getKind
    SourceSyntax.isAnnotatedBinderKind k || b.isIdent || k == ``Parser.Term.hole ||
    k == ``Parser.Term.explicitBinder || k == ``Parser.Term.implicitBinder ||
    k == ``Parser.Term.strictImplicitBinder || k == ``Parser.Term.instBinder
  if canZeroLeak then
    let mut plainBinders := #[]
    let mut anns := #[]
    for b in rawBinders do
      let (pb, ba) ← stripAnnotatedBinder b none
      plainBinders := plainBinders.push pb
      anns := anns ++ ba
    let basic := mkNode ``Parser.Term.basicFun #[mkNullNode plainBinders, signature[1], stx[2], stx[3]]
    let expr ← elabTerm (mkNode ``Parser.Term.fun #[stx[0], basic]) expectedType?
    attachLamAnnotations stx anns.toList expr
  else
    let binders ← rewriteBinders rawBinders
    let basic := mkNode ``Parser.Term.basicFun #[mkNullNode binders, signature[1], stx[2], stx[3]]
    elabTerm (mkNode ``Parser.Term.fun #[stx[0], basic]) expectedType?

@[term_elab SourceSyntax.annotatedForall]
meta def elabAnnotatedForall : TermElab := fun stx expectedType? => do
  let signature := stx[1]
  let result : Option Ixon.ResultMode ← if signature[3].isNone then pure none else
    some <$> decodeResultPrefix signature[3][0]
  let rawBinders := signature[0].getArgs
  let mut plainBinders := #[]
  let mut anns := #[]
  for h : i in [:rawBinders.size] do
    let outRes := if i + 1 == rawBinders.size then result else none
    let (pb, ba) ← stripAnnotatedBinder rawBinders[i] outRes
    plainBinders := plainBinders.push pb
    anns := anns ++ ba
  let ordinary := mkNode ``Parser.Term.forall
    #[stx[0], mkNullNode plainBinders, signature[1], signature[2], stx[2]]
  let expr ← elabTerm ordinary expectedType?
  attachForallAnnotations stx anns.toList expr

@[term_elab SourceSyntax.annotatedDepArrow]
meta def elabAnnotatedDepArrow : TermElab := fun stx _ => do
  let signature := stx[0]
  let result : Option Ixon.ResultMode ← if signature[2].isNone then pure none else
    some <$> decodeResultPrefix signature[2][0]
  let (plainBinder, anns) ← stripAnnotatedBinder signature[0] result
  let expr ← elabBinders #[plainBinder] fun xs => do
    Lean.Meta.mkForallFVars xs (← elabType stx[1])
  attachForallAnnotations stx anns.toList expr

@[term_elab SourceSyntax.annotatedArrow]
meta def elabAnnotatedArrow : TermElab := fun stx _ => do
  let result ← decodeResultPrefix stx[2]
  let domain ← elabType stx[0]
  let range ← elabType stx[3]
  let name ← mkFreshUserName `_argument
  let annotation : BinderAnnotation := {
    origin := sourceOrigin stx, binder := name, mode := .many, result := some result }
  let domain ← match annotation.attach domain with
    | .ok domain => pure domain
    | .error error => throwErrorAt stx "{error}"
  return .forallE name domain range .default

@[term_elab SourceSyntax.annotatedLet]
meta def elabAnnotatedLet : TermElab := fun stx expectedType? => do
  let (mode, isBorrow) ← decodeLetPrefix stx[1]
  let binderStx := stx[2]
  let name : Ident ← if binderStx.isIdent then pure ⟨binderStx⟩ else mkFreshIdent binderStx
  let binderName := binderIdentName binderStx
  let optTy := stx[3]
  let typeRaw : Syntax := if optTy.isNone then (mkHole stx).raw else optTy[0][1]
  let expr ← elabLetDeclAux name.raw #[] typeRaw stx[5] stx[7] expectedType? {}
  let annotation : BinderAnnotation := {
    origin := sourceOrigin stx, binder := binderName, mode, isBorrow }
  let rec attachLet : Expr → TermElabM Expr
    | .letE n ty val body nonDep =>
      match annotation.attach ty with
      | .ok ty' => return .letE n ty' val body nonDep
      | .error err => throwErrorAt stx "{err}"
    | .mdata d inner => return .mdata d (← attachLet inner)
    | _ => throwErrorAt stx "expected let expression from annotated let"
  attachLet expr

@[doElem_elab SourceSyntax.doAnnotatedLet]
meta def elabDoAnnotatedLet : Do.DoElab := fun stx dec => do
  let (mode, isBorrow) ← decodeLetPrefix stx.raw[1]
  let binderStx := stx.raw[2]
  let name : Ident ← if binderStx.isIdent then pure ⟨binderStx⟩ else mkFreshIdent binderStx
  let binderName := binderIdentName binderStx
  let optTy := stx.raw[3]
  let val : Term := ⟨stx.raw[5]⟩
  let plain : TSyntax `doElem ←
    if optTy.isNone then
      `(doElem| let $name:ident := $val)
    else
      let ty : Term := ⟨optTy[0][1]⟩
      `(doElem| let $name:ident : $ty := $val)
  let expr ← Do.elabDoElem plain dec
  let annotation : BinderAnnotation := {
    origin := sourceOrigin stx.raw, binder := binderName, mode, isBorrow }
  let rec attachLet : Expr → Do.DoElabM Expr
    | .letE n ty v b nonDep =>
      match annotation.attach ty with
      | .ok ty' => return .letE n ty' v b nonDep
      | .error err => throwErrorAt stx "{err}"
    | .mdata d inner => return .mdata d (← attachLet inner)
    | _ => throwErrorAt stx
      "annotated do-block let requires a direct let binding (bind nested monadic '←' expressions first)"
  attachLet expr

/-! ### Declaration elaborator (`def`, `abbrev`, `opaque`, `axiom`) -/

@[command_elab SourceSyntax.declaration]
meta def elabDeclaration : CommandElab := fun stx => do
  let decl := stx[1]
  let declKind := decl.getKind
  let signature := decl[2]
  let annotatedResult := signature[1].isOfKind ``SourceSyntax.resultType
  let result ← if annotatedResult then liftTermElabM do
      return some (← decodeResultPrefix signature[1][1])
    else pure none
  let binders ← liftTermElabM (rewriteBinders signature[0].getArgs result)
  let isReqType := declKind == ``SourceSyntax.opaqueDecl || declKind == ``SourceSyntax.axiomDecl
  let ordinarySig : Syntax :=
    if isReqType then
      let typeSpec : Syntax := if annotatedResult then
          (mkNode ``Parser.Term.typeSpec #[signature[1][0], signature[1][2]]).raw
        else signature[1]
      (mkNode ``Parser.Command.declSig #[mkNullNode binders, typeSpec]).raw
    else
      let optType : Syntax := if annotatedResult then
          mkNullNode #[(mkNode ``Parser.Term.typeSpec #[signature[1][0], signature[1][2]]).raw]
        else signature[1]
      (mkNode ``Parser.Command.optDeclSig #[mkNullNode binders, optType]).raw
  let targetDeclKind : SyntaxNodeKind :=
    if declKind == ``SourceSyntax.definitionDecl then ``Parser.Command.definition
    else if declKind == ``SourceSyntax.abbrevDecl then ``Parser.Command.abbrev
    else if declKind == ``SourceSyntax.opaqueDecl then ``Parser.Command.opaque
    else ``Parser.Command.axiom
  let ordinaryDecl := decl.setKind targetDeclKind |>.setArg 2 ordinarySig
  let ordinary := stx.setKind ``Parser.Command.declaration |>.setArg 1 ordinaryDecl
  elabCommand ordinary
  let name ← resolveGlobalConstNoOverload ordinaryDecl[1][0]
  let source ← getConstInfo name
  if sourceHasAnnotations source then
    let contract ← match SourceContract.fromAnnotations source with
      | .ok contract => pure contract
      | .error error => throwErrorAt stx "{error}"
    let env ← match registerSourceContract (← getEnv) contract with
      | .ok env => pure env
      | .error error => throwErrorAt stx "{error}"
    setEnv env

/-! ### Structure & inductive field elaborators (`@shared`, `@erased`) -/

private meta def registerCtorFieldAnnotations (ref : Syntax) (ctorName : Lean.Name)
    (indexed : Array (Nat × FieldAnnotation)) : CommandElabM Unit := do
  if indexed.isEmpty then return
  let source ← getConstInfo ctorName
  let .ctorInfo ctor := source
    | throwErrorAt ref "expected constructor info for {ctorName}"
  let tele := sourceTelescope source .type
  let mut binders : Array BinderContract := #[]
  let mut fieldModes : Array FieldModeContract := #[]
  for (fieldIdx, ann) in indexed do
    unless fieldIdx < ctor.numFields do
      throwErrorAt ref "annotated field index {fieldIdx} out of range for constructor {ctorName}"
    match ann with
    | .shared =>
      fieldModes := fieldModes.push { fieldIndex := fieldIdx, mode := .shared }
    | .erased =>
      let some (site, _) := tele[ctor.numParams + fieldIdx]?
        | throwErrorAt ref "missing constructor field binder at index {fieldIdx} of {ctorName}"
      binders := binders.push { site, mode := .erased }
  let contract : SourceContract := { source, binders, fieldModes }
  let env ← match registerSourceContract (← getEnv) contract with
    | .ok env => pure env
    | .error err => throwErrorAt ref "{err}"
  setEnv env

@[command_elab SourceSyntax.annotatedStructure]
meta def elabAnnotatedStructure : CommandElab := fun stx => do
  let decl := stx[1]
  let fieldsNode := decl[6]
  let rawFields := fieldsNode[0].getArgs
  let mut plainFields : Array Syntax := #[]
  let mut fieldAnns : Array (Lean.Name × FieldAnnotation) := #[]
  for field in rawFields do
    let k := field.getKind
    if k == ``SourceSyntax.structAnnotatedSimpleField then
      let ann ← liftTermElabM (decodeFieldPrefix field[1])
      fieldAnns := fieldAnns.push (field[2].getId, ann)
      plainFields := plainFields.push <|
        (mkNode ``Parser.Command.structSimpleBinder #[field[0], field[2], field[3], field[4]]).raw
    else if k == ``SourceSyntax.structAnnotatedExplicitBinder then
      let ann ← liftTermElabM (decodeFieldPrefix field[2])
      for id in field[3].getArgs do
        fieldAnns := fieldAnns.push (id.getId, ann)
      plainFields := plainFields.push <|
        (mkNode ``Parser.Command.structExplicitBinder
          #[field[0], field[1], field[3], field[4], field[5], field[6]]).raw
    else if k == ``SourceSyntax.structAnnotatedImplicitBinder then
      let ann ← liftTermElabM (decodeFieldPrefix field[2])
      for id in field[3].getArgs do
        fieldAnns := fieldAnns.push (id.getId, ann)
      plainFields := plainFields.push <|
        (mkNode ``Parser.Command.structImplicitBinder
          #[field[0], field[1], field[3], field[4], field[5]]).raw
    else if k == ``SourceSyntax.structAnnotatedInstBinder then
      let ann ← liftTermElabM (decodeFieldPrefix field[2])
      for id in field[3].getArgs do
        fieldAnns := fieldAnns.push (id.getId, ann)
      plainFields := plainFields.push <|
        (mkNode ``Parser.Command.structInstBinder
          #[field[0], field[1], field[3], field[4], field[5]]).raw
    else
      plainFields := plainFields.push field
  let ordinaryFields := mkNode ``Parser.Command.structFields #[mkNullNode plainFields]
  let bodyOpt := mkNullNode #[decl[4], decl[5], ordinaryFields]
  let ordinaryStruct := mkNode ``Parser.Command.structure
    #[decl[0], decl[1], decl[2], decl[3], bodyOpt, decl[7]]
  let ordinary := stx.setKind ``Parser.Command.declaration |>.setArg 1 ordinaryStruct
  elabCommand ordinary
  let structName ← resolveGlobalConstNoOverload decl[1][0]
  let .inductInfo ind ← getConstInfo structName
    | throwErrorAt stx "expected inductive info for structure {structName}"
  let some ctorName := ind.ctors.head?
    | throwErrorAt stx "structure {structName} has no constructor"
  let ctorInfo ← getConstInfo ctorName
  let .ctorInfo ctor := ctorInfo
    | throwErrorAt stx "expected constructor info for {ctorName}"
  let tele := sourceTelescope ctorInfo .type
  let fieldTele := tele.extract ctor.numParams (ctor.numParams + ctor.numFields)
  let mut indexed : Array (Nat × FieldAnnotation) := #[]
  for (fname, ann) in fieldAnns do
    let matches_ := fieldTele.zipIdx.filter fun ((_, bName), _) =>
      bName == fname || bName.eraseMacroScopes == fname
    let some (_, fIdx) := matches_.back?
      | throwErrorAt stx "annotated field '{fname}' not found in constructor {ctorName}"
    indexed := indexed.push (fIdx, ann)
  registerCtorFieldAnnotations stx ctorName indexed

private meta def stripCtorAnnotatedBinder (binder : Syntax) :
    TermElabM (Syntax × Nat × Option FieldAnnotation) := do
  let k := binder.getKind
  if SourceSyntax.isCtorAnnotatedBinderKind k then
    let ann ← decodeFieldPrefix binder[1]
    if k == ``SourceSyntax.ctorInstBinder then
      let optName := binder[2]
      let ty : Term := ⟨binder[3]⟩
      let plain ← if optName.isNone then `(bracketedBinder| [$ty])
        else let name : Ident := ⟨optName[0]⟩; `(bracketedBinder| [$name:ident : $ty])
      return (plain.raw, 1, some ann)
    else
      let names := binder[2].getArgs
      let optTy := binder[3]
      let tyArg : Syntax := if optTy.isNone then mkNullNode #[] else mkNullNode #[optTy[0][0], optTy[0][1]]
      let plain : Syntax :=
        if k == ``SourceSyntax.ctorExplicitBinder then
          (mkNode ``Parser.Term.explicitBinder #[binder[0], binder[2], tyArg, mkNullNode #[], binder[4]]).raw
        else if k == ``SourceSyntax.ctorImplicitBinder then
          (mkNode ``Parser.Term.implicitBinder #[binder[0], binder[2], tyArg, binder[4]]).raw
        else
          (mkNode ``Parser.Term.strictImplicitBinder #[binder[0], binder[2], tyArg, binder[4]]).raw
      return (plain, names.size, some ann)
  -- Ordinary binder or arrow domain
  let count :=
    if k == ``Parser.Term.explicitBinder || k == ``Parser.Term.implicitBinder ||
       k == ``Parser.Term.strictImplicitBinder then
      binder[1].getNumArgs
    else 1
  return (binder, count, none)

@[command_elab SourceSyntax.annotatedInductive]
meta def elabAnnotatedInductive : CommandElab := fun stx => do
  let decl := stx[1]
  let rawCtors := decl[4].getArgs
  let mut plainCtors := #[]
  let mut ctorAnns : Array (Lean.Name × Array (Nat × FieldAnnotation)) := #[]
  for ctor in rawCtors do
    let ctorRawName := ctor[3].getId
    let sig := ctor[4]
    let mut fieldIdx := 0
    let mut anns : Array (Nat × FieldAnnotation) := #[]
    let mut plainBinders := #[]
    for b in sig[0].getArgs do
      let (pb, count, ann?) ← liftTermElabM (stripCtorAnnotatedBinder b)
      plainBinders := plainBinders.push pb
      if let some ann := ann? then
        for j in [:count] do
          anns := anns.push (fieldIdx + j, ann)
      fieldIdx := fieldIdx + count
    let plainOptType : Syntax ←
      if sig[1].isNone then
        pure (mkNullNode #[])
      else do
        let tSpec := sig[1][0]
        let arrows := tSpec[1].getArgs
        let mut strippedArrows : Array (Syntax × Syntax × Bool) := #[]
        for arr in arrows do
          let dom := arr[0]
          let arrowTk := arr[1]
          let isDep := SourceSyntax.isCtorAnnotatedBinderKind dom.getKind ||
            dom.getKind == ``Parser.Term.explicitBinder ||
            dom.getKind == ``Parser.Term.implicitBinder ||
            dom.getKind == ``Parser.Term.strictImplicitBinder ||
            dom.getKind == ``Parser.Term.instBinder
          let (pDom, count, ann?) ← liftTermElabM (stripCtorAnnotatedBinder dom)
          if let some ann := ann? then
            for j in [:count] do
              anns := anns.push (fieldIdx + j, ann)
          fieldIdx := fieldIdx + count
          strippedArrows := strippedArrows.push (pDom, arrowTk, isDep)
        let mut tyExpr := tSpec[2]
        for (pDom, arrowTk, isDep) in strippedArrows.reverse do
          tyExpr :=
            if isDep then mkNode ``Parser.Term.depArrow #[pDom, arrowTk, tyExpr]
            else mkNode ``Parser.Term.arrow #[pDom, arrowTk, tyExpr]
        pure (mkNullNode #[mkNode ``Parser.Term.typeSpec #[tSpec[0], tyExpr]])
    let plainSig := mkNode ``Parser.Command.optDeclSig #[mkNullNode plainBinders, plainOptType]
    plainCtors := plainCtors.push <|
      mkNode ``Parser.Command.ctor #[ctor[0], ctor[1], ctor[2], ctor[3], plainSig]
    ctorAnns := ctorAnns.push (ctorRawName, anns)
  let ordinaryInd := mkNode ``Parser.Command.inductive
    #[decl[0], decl[1], decl[2], decl[3], mkNullNode plainCtors, decl[5], decl[6]]
  let ordinary := stx.setKind ``Parser.Command.declaration |>.setArg 1 ordinaryInd
  elabCommand ordinary
  let indName ← resolveGlobalConstNoOverload decl[1][0]
  let .inductInfo ind ← getConstInfo indName
    | throwErrorAt stx "expected inductive info for {indName}"
  unless ind.ctors.length == ctorAnns.size do
    throwErrorAt stx "constructor count mismatch for {indName}"
  for (ctorName, (_, anns)) in ind.ctors.zip ctorAnns.toList do
    registerCtorFieldAnnotations stx ctorName anns

/-! ### Native scoped `DefAsserts` attributes (`@[no_rc]`, `@[no_alloc]`, `@[bounded_stack]`) -/

private meta def addDefAssertsAttr (asserts : Ixon.DefAsserts) (declName : Lean.Name) :
    AttrM Unit := do
  let env ← getEnv
  let some source := (env.setExporting false).find? declName
    | throwUnknownConstant declName
  let env ← match registerDefAsserts env { source, asserts } with
    | .ok env => pure env
    | .error err =>
      match err with
      | .invalidDefAsserts _ msg => throwError "{msg}"
      | .conflictingDefAsserts _ msg => throwError "{msg}"
      | other => throwError "{other}"
  setEnv env

meta initialize registerBuiltinAttribute {
  name := `ix_modes_no_rc
  descr := "Assert that a definition performs no reference-counting operations (Ixon.AllocAssert.noRc)."
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do
      throwError "@[no_rc] cannot be local or scoped"
    addDefAssertsAttr { alloc := .noRc } decl
}

meta initialize registerBuiltinAttribute {
  name := `ix_modes_no_alloc
  descr := "Assert that a definition performs no heap allocation (Ixon.AllocAssert.noAlloc)."
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do
      throwError "@[no_alloc] cannot be local or scoped"
    addDefAssertsAttr { alloc := .noAlloc } decl
}

meta initialize registerBuiltinAttribute {
  name := `ix_modes_bounded_stack
  descr := "Assert that a definition's call graph has bounded stack depth (Ixon.DefAsserts.boundedStack)."
  add := fun decl _ kind => do
    unless kind == AttributeKind.global do
      throwError "@[bounded_stack] cannot be local or scoped"
    addDefAssertsAttr { boundedStack := true } decl
}

end Ix.Compile.SourceElab

/-! ### Scoped activation (`open scoped Ix.Modes`) -/

namespace Ix.Modes

attribute [scoped term_parser 2000]
  Ix.Compile.SourceSyntax.annotatedFun
  Ix.Compile.SourceSyntax.annotatedForall
  Ix.Compile.SourceSyntax.annotatedDepArrow
  Ix.Compile.SourceSyntax.annotatedArrow
  Ix.Compile.SourceSyntax.annotatedLet

attribute [scoped doElem_parser 2000]
  Ix.Compile.SourceSyntax.doAnnotatedLet

attribute [scoped command_parser 2000]
  Ix.Compile.SourceSyntax.declaration
  Ix.Compile.SourceSyntax.annotatedStructure
  Ix.Compile.SourceSyntax.annotatedInductive

attribute [scoped attr_parser 2000]
  Ix.Compile.SourceSyntax.ix_modes_no_rc
  Ix.Compile.SourceSyntax.ix_modes_no_alloc
  Ix.Compile.SourceSyntax.ix_modes_bounded_stack

end Ix.Modes

end
