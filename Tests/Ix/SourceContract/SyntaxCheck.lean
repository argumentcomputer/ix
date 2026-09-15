import Tests.Ix.SourceContract.SyntaxFixture

open Lean Ix.Compile

run_cmd do
  let names := #[
    ``Tests.Ix.SourceContract.SyntaxFixture.linear,
    ``Tests.Ix.SourceContract.SyntaxFixture.unique,
    ``Tests.Ix.SourceContract.SyntaxFixture.uniqueAffine,
    ``Tests.Ix.SourceContract.SyntaxFixture.erased,
    ``Tests.Ix.SourceContract.SyntaxFixture.inferred,
    ``Tests.Ix.SourceContract.SyntaxFixture.dependent,
    ``Tests.Ix.SourceContract.SyntaxFixture.inferredImplicit,
    ``Tests.Ix.SourceContract.SyntaxFixture.withInstance,
    ``Tests.Ix.SourceContract.SyntaxFixture.strictImplicit,
    ``Tests.Ix.SourceContract.SyntaxFixture.shadowed,
    ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.twoRegions,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedRegion,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoRegions,
    ``Tests.Ix.SourceContract.SyntaxFixture.unrestrictedRegion,
    ``Tests.Ix.SourceContract.SyntaxFixture.uniqueRegion]
  let selected ← names.toList.mapM fun name => do return (name, ← getConstInfo name)
  let input ← match compileInputFromEnv (← getEnv) selected with
    | .ok input => pure input
    | .error error => throwError "{error}"
  let resolved ← match input.resolve with
    | .ok input => pure input
    | .error error => throwError "{error}"
  unless resolved.contracts.size == names.size do throwError "syntax registrations were lost on import"
  unless resolved.measureHints.size == 1 && resolved.measureHints[0]!.argument == 0 do
    throwError "measure hint on annotated source was lost on import"
  let getContract (name : Name) := do
    let some contract := resolved.contracts.find? (·.source.name == name)
      | throwError "missing syntax contract {name}"
    pure contract
  let unique ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.unique
  unless unique.ownedAt ⟨.type, []⟩ == .unique && unique.ownedAt ⟨.body, []⟩ == .unique &&
      unique.usesAt ⟨.type, []⟩ == .many do
    throwError "unique unrestricted binder changed meaning"
  unless (unique.binders.find? (·.site == ⟨.type, []⟩)).bind (·.resultOwned) == some .shared do
    throwError "unique input silently changed the result ownership"
  let native ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrow
  unless native.usesAt ⟨.type, []⟩ == .affine && native.ownedAt ⟨.type, []⟩ == .unique &&
      native.regionAt ⟨.type, []⟩ == some 0 && native.regionAt ⟨.body, []⟩ == some 0 do
    throwError "combined ownership, usage, and region changed on import"
  let .forallE _ domain _ _ := native.source.type | throwError "native fixture has no binder"
  unless isMarkedBorrowed domain do throwError "source marker hid Lean's native borrow annotation"
  let pair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.twoRegions
  unless pair.regionAt ⟨.type, []⟩ == some 0 &&
      pair.regionAt ⟨.type, [.binderBody]⟩ == some 1 do
    throwError "distinct region parameters were conflated"
  let renamed ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedRegion
  unless renamed.semantics == native.semantics do
    throwError "region renaming changed the resolved assertions"
  let renamedPair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoRegions
  unless renamedPair.semantics == pair.semantics do
    throwError "renaming multiple region and term binders changed the resolved assertions"
  let unrestricted ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.unrestrictedRegion
  unless unrestricted.usesAt ⟨.body, []⟩ == .many &&
      unrestricted.ownedAt ⟨.body, []⟩ == .shared &&
      unrestricted.regionAt ⟨.body, []⟩ == some 0 do
    throwError "region-only prefix changed usage or ownership defaults"
  let dependent ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.dependent
  unless dependent.usesAt ⟨.type, []⟩ == .erased &&
      dependent.usesAt ⟨.body, [.binderBody]⟩ == .linear do
    throwError "implicit parameter shifted the explicit annotation"
  let inferred ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.inferredImplicit
  unless inferred.usesAt ⟨.type, []⟩ == .many &&
      inferred.usesAt ⟨.type, [.binderBody]⟩ == .linear do
    throwError "an auto-implicit parameter received the explicit binder's annotation"
  let instanceContract ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.withInstance
  unless (instanceContract.binders.find? (·.site == ⟨.type, [.binderBody]⟩)).map (·.binderInfo) ==
      some .instImplicit do
    throwError "annotated instance binder lost its BinderInfo"
  let shadowed ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.shadowed
  unless shadowed.usesAt ⟨.body, []⟩ == .linear &&
      shadowed.usesAt ⟨.body, [.binderBody]⟩ == .affine do
    throwError "shadowed binder names were used as occurrence identities"
  let registry := sourceContractExtension.getState (← getEnv)
  unless registry.toArray.any (fun (name, _) => name.toString.endsWith ".privateIdentity") do
    throwError "private annotated declaration was not registered"
  let ordinary ← getConstInfo ``Tests.Ix.SourceContract.SyntaxFixture.ordinaryBinder
  let .ok plain := compileInputFromEnv (← getEnv) [(ordinary.name, ordinary)]
    | throwError "ordinary source no longer exports"
  unless plain.contracts.isEmpty do throwError "ordinary binders gained semantic contracts"
  match (CompileInput.plain selected).resolve with
  | .error (.missingContract _) => pure ()
  | _ => throwError "annotated source accepted an omitted registry"

  -- Test rejected spellings without depending on parser error pretty-printing.
  for text in [
      "def bad (!x : Nat) : Nat := x",
      "def bad (!&x : Nat) : Nat := x",
      "def bad (&!'a x : Nat) : Nat := x"] do
    if (Parser.runParserCategory (← getEnv) `command text).isOk then
      throwError "invalid binder spelling was accepted: {text}"

/-- error: unbound region 'a; introduce it with `regions 'a in` -/
#guard_msgs in
def unboundRegion (&'a x : Nat) : Nat := x

/-- error: duplicate region parameter 'a -/
#guard_msgs in
regions 'a 'a in
def duplicateRegions (&'a x : Nat) : Nat := x

/-- error: binder usage must be 0, 1, or & -/
#guard_msgs in
def invalidQuantity (2 x : Nat) : Nat := x

/-- error: binder annotation components must be adjacent -/
#guard_msgs in
def separatedPrefix (! & x : Nat) : Nat := x

-- A previous `regions ... in` command must not leak to later declarations.
/-- error: unbound region 'a; introduce it with `regions 'a in` -/
#guard_msgs in
def escapedRegionParameter (!&'a x : Nat) : Nat := x
