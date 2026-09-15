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

/-- Lexical frontend context only. Each marker carries its complete parameter
table, so imported source validation does not depend on this extension. -/
meta initialize currentRegions : EnvExtension (Array Lean.Name) ← registerEnvExtension (pure #[])

private meta def decodePrefix (modes : Syntax) : TermElabM (Ixon.Uses × Ixon.Owned × Option Lean.Name) := do
  let parts := modes.getArgs.filter (!·.isNone)
  for i in [1:parts.size] do
    if let some stop := parts[i - 1]!.getTailPos? then
      if let some start := parts[i]!.getPos? then
        unless start == stop do
          throwErrorAt parts[i]! "binder annotation components must be adjacent"
  let owned := if modes[0].isNone then Ixon.Owned.shared else .unique
  let uses ← if modes[1].isNone then pure Ixon.Uses.many else do
    let quantity := modes[1][0][0]
    if quantity.isAtom && quantity.getAtomVal == "&" then pure .affine else
      match quantity.isNatLit? with
      | some 0 => pure .erased
      | some 1 => pure .linear
      | _ => throwErrorAt quantity "binder usage must be 0, 1, or &"
  let region := if modes[2].isNone then none else some modes[2][0][1].getId
  return (uses, owned, region)

-- Internal expansion target. The raw prefix and region table remain syntax
-- until Lean elaborates the corresponding binder domain.
syntax (name := annotatedType) "__ix_binder% " num ident Ix.Compile.SourceSyntax.binderPrefix
    "[" ident,* "]" "(" term ")" : term

@[term_elab annotatedType]
meta def elabAnnotatedType : TermElab := fun stx expectedType? => do
  let some origin := stx[1].isNatLit? | throwErrorAt stx "invalid source annotation origin"
  let (uses, owned, region) ← decodePrefix stx[3]
  let regions := stx[5].getSepArgs.map (·.getId)
  if let some name := region then
    unless regions.contains name do
      throwErrorAt stx[3] "unbound region '{name}; introduce it with `regions '{name} in`"
  let annotation : BinderAnnotation := {
    origin
    binder := stx[2].getId
    uses, owned, region, regions }
  let type ← elabTerm stx[8] expectedType?
  match annotation.attach type with
  | .ok expr => return expr
  | .error error => throwErrorAt stx "{error}"

private meta def rewriteBinder (binder : Syntax) (origin : Nat) (regions : Array Lean.Name) :
    CommandElabM Syntax := do
  let kind := binder.getKind
  unless kind == ``SourceSyntax.explicitBinder || kind == ``SourceSyntax.implicitBinder ||
      kind == ``SourceSyntax.strictImplicitBinder || kind == ``SourceSyntax.instanceBinder do
    return binder
  let name : Ident := ⟨binder[2]⟩
  let modes : TSyntax ``Ix.Compile.SourceSyntax.binderPrefix := ⟨binder[1]⟩
  let (_, _, region) ← liftTermElabM (decodePrefix modes.raw)
  if let some region := region then
    unless regions.contains region do
      throwErrorAt modes "unbound region '{region}; introduce it with `regions '{region} in`"
  let type : Term := ⟨binder[4]⟩
  let origin : NumLit := ⟨Syntax.mkNumLit (toString origin)⟩
  let regions := regions.map Lean.mkIdent
  let marked ← `(__ix_binder% $origin:num $name:ident $modes:binderPrefix
    [$[$regions:ident],*] ($type))
  let rewritten ← if kind == ``SourceSyntax.explicitBinder then
      `(bracketedBinder| ($name:ident : $marked))
    else if kind == ``SourceSyntax.implicitBinder then
      `(bracketedBinder| {$name:ident : $marked})
    else if kind == ``SourceSyntax.strictImplicitBinder then
      `(bracketedBinder| ⦃$name:ident : $marked⦄)
    else
      `(bracketedBinder| [$name:ident : $marked])
  return rewritten.raw

@[command_elab Ix.Compile.SourceSyntax.declaration]
meta def elabDeclaration : CommandElab := fun stx => do
  let definition := stx[1]
  let signature := definition[2]
  let regions := currentRegions.getState (← getEnv)
  let mut binders := #[]
  for i in [:signature[0].getNumArgs] do
    binders := binders.push (← rewriteBinder signature[0][i] i regions)
  let signature := signature.setKind ``Parser.Command.optDeclSig |>.setArg 0 (mkNullNode binders)
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

@[command_elab Ix.Compile.SourceSyntax.regions]
meta def elabRegions : CommandElab := fun stx => do
  let previous := currentRegions.getState (← getEnv)
  let mut regions := previous
  for parameter in stx[1].getArgs do
    let name := parameter[1].getId
    if regions.contains name then throwErrorAt parameter "duplicate region parameter '{name}"
    regions := regions.push name
  modifyEnv fun env => currentRegions.setState env regions
  try
    elabCommand stx[3]
  finally
    modifyEnv fun env => currentRegions.setState env previous

end Ix.Compile.SourceElab

end
