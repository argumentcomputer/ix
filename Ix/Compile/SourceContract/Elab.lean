module

public import Ix.Compile.SourceContract.Registry
public import Ix.Compile.SourceContract.Syntax
public meta import Ix.Compile.SourceContract.Registry
public meta import Ix.Compile.SourceContract.Syntax

/-!
# Source binder elaboration

Opt-in syntax for declaration binders. Lean elaborates the ordinary declaration;
source markers record its binder contracts, which are then registered from the
actual elaborated occurrences. No resource checker or Ixon emitter is implied.
-/

public section

namespace Ix.Compile.SourceElab

open Lean Elab Command Term

private meta def decodePrefix (modes : Syntax) : TermElabM Ixon.BinderContract := do
  let parts := modes[0].getArgs
  let mut uses := Ixon.Uses.many
  let mut owned := Ixon.Owned.shared
  let mut locality := Ixon.Locality.unrestricted
  let mut hasUses := false
  for i in [:parts.size] do
    if i > 0 then
      if let some stop := parts[i - 1]!.getTailPos? then
        if let some start := parts[i]!.getPos? then
          unless start == stop do
            throwErrorAt parts[i]! "binder annotation components must be adjacent"
    let atom := parts[i]![0]
    if atom.isAtom && atom.getAtomVal == "!" then
      if owned == .unique then throwErrorAt atom "duplicate ownership annotation"
      owned := .unique
    else if atom.isAtom && atom.getAtomVal == "~" then
      if locality == .local then throwErrorAt atom "duplicate locality annotation"
      locality := .local
    else
      if hasUses then throwErrorAt atom "duplicate usage annotation"
      uses ← if atom.isAtom && atom.getAtomVal == "&" then pure .affine else
        match atom.isNatLit? with
        | some 0 => pure .erased
        | some 1 => pure .linear
        | _ => throwErrorAt atom "binder usage must be 0, 1, or &"
      hasUses := true
  return ⟨uses, ⟨owned, locality⟩⟩

-- Numeric expansion target avoids carrying parser-specific mode syntax into
-- stored annotations. Result code 4 denotes an absent result annotation.
syntax (name := annotatedType) "__ix_binder% " num ident num num num "(" term ")" : term

private meta def sourceOrigin (stx : Syntax) : Nat :=
  (stx.getPos?.map (·.byteIdx)).getD 0

private meta def markTypeSyntax (ref : Syntax) (name : Ident) (type : Term)
    (contract : Ixon.BinderContract) (result : Option Ixon.ValueContract := none)
    (kind : Ixon.LetKind := .value) : TermElabM Term := do
  let origin : NumLit := ⟨Syntax.mkNumLit (toString (sourceOrigin ref))⟩
  let input : NumLit := ⟨Syntax.mkNumLit (toString contract.toBits.toNat)⟩
  let output : NumLit := ⟨Syntax.mkNumLit (toString ((result.map (·.toBits.toNat)).getD 4))⟩
  let kind : NumLit := ⟨Syntax.mkNumLit (if kind == .borrowShared then "1" else "0")⟩
  `(__ix_binder% $origin:num $name:ident $input:num $output:num $kind:num ($type))

@[term_elab annotatedType]
meta def elabAnnotatedType : TermElab := fun stx expectedType? => do
  let some origin := stx[1].isNatLit? | throwErrorAt stx "invalid source annotation origin"
  let some input := stx[3].isNatLit? | throwErrorAt stx "invalid source input contract"
  if input > 15 then throwErrorAt stx "invalid source input contract"
  let some contract := Ixon.BinderContract.ofBits? input.toUInt8
    | throwErrorAt stx "invalid source input contract"
  let some output := stx[4].isNatLit? | throwErrorAt stx "invalid source result contract"
  let result ← if output == 4 then pure none else do
    if output > 3 then throwErrorAt stx "invalid source result contract"
    let some value := Ixon.ValueContract.ofBits? output.toUInt8
      | throwErrorAt stx "invalid source result contract"
    pure (some value)
  let kind ← match stx[5].isNatLit? with
    | some 0 => pure Ixon.LetKind.value
    | some 1 => pure Ixon.LetKind.borrowShared
    | _ => throwErrorAt stx "invalid source let kind"
  let annotation : BinderAnnotation := {
    origin, binder := stx[2].getId, uses := contract.uses, value := contract.value
    result, letKind := kind }
  let type ← elabTerm stx[7] expectedType?
  match annotation.attach type with
  | .ok expr => return expr
  | .error error => throwErrorAt stx "{error}"

private meta def isAnnotatedBinder (binder : Syntax) : Bool :=
  binder.isOfKind ``SourceSyntax.explicitBinder ||
  binder.isOfKind ``SourceSyntax.implicitBinder ||
  binder.isOfKind ``SourceSyntax.strictImplicitBinder ||
  binder.isOfKind ``SourceSyntax.instanceBinder

/-- Split a multi-name final binder before attaching the result contract.
The result belongs to the last arrow, not to every arrow in that group. -/
private meta def rewriteBinder (binder : Syntax)
    (result : Option Ixon.ValueContract := none) : TermElabM (Array Syntax) := do
  let kind := binder.getKind
  if isAnnotatedBinder binder then
    let name : Ident := ⟨binder[2]⟩
    let contract ← decodePrefix binder[1]
    let marked ← markTypeSyntax binder name ⟨binder[4]⟩ contract result
    let rewritten ← if kind == ``SourceSyntax.explicitBinder then
        `(bracketedBinder| ($name:ident : $marked))
      else if kind == ``SourceSyntax.implicitBinder then
        `(bracketedBinder| {$name:ident : $marked})
      else if kind == ``SourceSyntax.strictImplicitBinder then
        `(bracketedBinder| ⦃$name:ident : $marked⦄)
      else
        `(bracketedBinder| [$name:ident : $marked])
    return #[rewritten.raw]
  if result.isNone then return #[binder]
  if binder.isIdent then
    let name : Ident := ⟨binder⟩
    let marked ← markTypeSyntax binder name ⟨mkHole binder⟩ .many result
    return #[(← `(bracketedBinder| ($name:ident : $marked))).raw]
  if kind == ``Parser.Term.explicitBinder || kind == ``Parser.Term.implicitBinder ||
      kind == ``Parser.Term.strictImplicitBinder then
    if kind == ``Parser.Term.explicitBinder && !binder[3].isNone then
      throwErrorAt binder "put the result contract on an explicit arrow when the final binder has a default value"
    let names := binder[1].getArgs
    let some last := names.back? | throwErrorAt binder "missing result-bearing binder"
    unless last.isIdent do throwErrorAt last "a result-bearing binder must have a name"
    let type : Syntax := if binder[2].getNumArgs == 0 then (mkHole binder).raw else binder[2][1]
    let marked ← markTypeSyntax last ⟨last⟩ ⟨type⟩ .many result
    let typeSpec := mkNullNode #[mkAtom ":", marked.raw]
    let final := binder.setArg 1 (mkNullNode #[last]) |>.setArg 2 typeSpec
    if names.size == 1 then return #[final]
    return #[binder.setArg 1 (mkNullNode names.pop), final]
  if kind == ``Parser.Term.instBinder then
    let name ← if binder[1].isNone then mkFreshIdent binder else pure ⟨binder[1][0]⟩
    let marked ← markTypeSyntax binder name ⟨binder[2]⟩ .many result
    return #[(← `(bracketedBinder| [$name:ident : $marked])).raw]
  throwErrorAt binder "unsupported result-bearing binder"

private meta def rewriteBinders (binders : Array Syntax)
    (result : Option Ixon.ValueContract := none) : TermElabM (Array Syntax) := do
  if binders.isEmpty && result.isSome then
    throwError "a result contract requires a function arrow"
  let mut rewritten := #[]
  for i in [:binders.size] do
    let output := if i + 1 == binders.size then result else none
    rewritten := rewritten ++ (← rewriteBinder binders[i]! output)
  return rewritten

private meta def decodeResult (stx : Syntax) : TermElabM Ixon.ValueContract := do
  return (← decodePrefix stx).value

@[term_elab Ix.Compile.SourceSyntax.annotatedFun]
meta def elabAnnotatedFun : TermElab := fun stx expectedType? => do
  let signature := stx[1]
  let binders ← rewriteBinders signature[0].getArgs
  let basic := mkNode ``Parser.Term.basicFun #[mkNullNode binders, signature[1], stx[2], stx[3]]
  elabTerm (mkNode ``Parser.Term.fun #[stx[0], basic]) expectedType?

@[term_elab Ix.Compile.SourceSyntax.annotatedForall]
meta def elabAnnotatedForall : TermElab := fun stx expectedType? => do
  let signature := stx[1]
  let result : Option Ixon.ValueContract ← if signature[3].isNone then pure none else
    some <$> decodeResult signature[3][0]
  let binders ← rewriteBinders signature[0].getArgs result
  let ordinary := mkNode ``Parser.Term.forall
    #[stx[0], mkNullNode binders, signature[1], signature[2], stx[2]]
  elabTerm ordinary expectedType?

@[term_elab Ix.Compile.SourceSyntax.annotatedDepArrow]
meta def elabAnnotatedDepArrow : TermElab := fun stx _ => do
  let signature := stx[0]
  let result : Option Ixon.ValueContract ← if signature[2].isNone then pure none else
    some <$> decodeResult signature[2][0]
  let binders ← rewriteBinder signature[0] result
  elabBinders binders fun xs => do
    Lean.Meta.mkForallFVars xs (← elabType stx[1])

@[term_elab Ix.Compile.SourceSyntax.annotatedArrow]
meta def elabAnnotatedArrow : TermElab := fun stx _ => do
  let result ← decodeResult stx[2]
  let domain ← elabType stx[0]
  let range ← elabType stx[3]
  let name ← mkFreshUserName `_argument
  let annotation : BinderAnnotation := {
    origin := sourceOrigin stx, binder := name, uses := .many, value := .shared
    result := some result }
  let domain ← match annotation.attach domain with
    | .ok domain => pure domain
    | .error error => throwErrorAt stx "{error}"
  return .forallE name domain range .default

@[term_elab Ix.Compile.SourceSyntax.annotatedLet]
meta def elabAnnotatedLet : TermElab := fun stx expectedType? => do
  let binder := stx[2]
  let name : Ident := ⟨binder[2]⟩
  let contract ← decodePrefix binder[1]
  let kind := if stx[1].isNone then Ixon.LetKind.value else .borrowShared
  if kind == .borrowShared && contract.value != .localShared then
    throwErrorAt binder "a shared borrow requires a shared local view (~)"
  let marked ← markTypeSyntax binder name ⟨binder[4]⟩ contract none kind
  elabLetDeclAux name.raw #[] marked.raw stx[4] stx[6] expectedType? {}

@[command_elab Ix.Compile.SourceSyntax.declaration]
meta def elabDeclaration : CommandElab := fun stx => do
  let definition := stx[1]
  let signature := definition[2]
  let annotatedResult := signature[1].isOfKind ``SourceSyntax.resultType
  let result ← if annotatedResult then liftTermElabM do
      return some (← decodeResult signature[1][1])
    else pure none
  let binders ← liftTermElabM (rewriteBinders signature[0].getArgs result)
  let typeSpec := if annotatedResult then
      mkNullNode #[mkNode ``Parser.Term.typeSpec #[signature[1][0], signature[1][2]]]
    else signature[1]
  let signature := signature.setKind ``Parser.Command.optDeclSig
    |>.setArg 0 (mkNullNode binders) |>.setArg 1 typeSpec
  let definition := definition.setKind ``Parser.Command.definition |>.setArg 2 signature
  let ordinary := stx.setKind ``Parser.Command.declaration |>.setArg 1 definition
  elabCommand ordinary
  let name ← resolveGlobalConstNoOverload definition[1][0]
  let source ← getConstInfo name
  if sourceHasAnnotations source then
    let contract ← match SourceContract.fromAnnotations source with
      | .ok contract => pure contract
      | .error error => throwErrorAt stx "{error}"
    let env ← match registerSourceContract (← getEnv) contract with
      | .ok env => pure env
      | .error error => throwErrorAt stx "{error}"
    setEnv env

attribute [command_parser 2000] Ix.Compile.SourceSyntax.declaration

end Ix.Compile.SourceElab

end
