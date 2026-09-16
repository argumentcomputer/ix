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
    ``Tests.Ix.SourceContract.SyntaxFixture.twoLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.localShared,
    ``Tests.Ix.SourceContract.SyntaxFixture.localUnique,
    ``Tests.Ix.SourceContract.SyntaxFixture.localResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.curriedResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.dependentArrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.anonymousArrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.quantified,
    ``Tests.Ix.SourceContract.SyntaxFixture.nestedLambda,
    ``Tests.Ix.SourceContract.SyntaxFixture.lambdaDefinition,
    ``Tests.Ix.SourceContract.SyntaxFixture.localLet,
    ``Tests.Ix.SourceContract.SyntaxFixture.sharedLoan]
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
  unless unique.valueAt ⟨.type, []⟩ == .unique && unique.valueAt ⟨.body, []⟩ == .unique &&
      unique.usesAt ⟨.type, []⟩ == .many do
    throwError "unique unrestricted binder changed meaning"
  unless (unique.binders.find? (·.site == ⟨.type, []⟩)).bind (·.result) == some .shared do
    throwError "unique input silently changed the result ownership"
  let native ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrow
  unless native.usesAt ⟨.type, []⟩ == .affine && native.valueAt ⟨.type, []⟩ == .localUnique &&
      native.valueAt ⟨.body, []⟩ == .localUnique do
    throwError "combined ownership, usage, and locality changed on import"
  let .forallE _ domain _ _ := native.source.type | throwError "native fixture has no binder"
  unless isMarkedBorrowed domain do throwError "source marker hid Lean's native borrow annotation"
  let pair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.twoLocal
  unless pair.valueAt ⟨.type, []⟩ == .localUnique &&
      pair.valueAt ⟨.type, [.binderBody]⟩ == .localShared do
    throwError "distinct local ownership modes were conflated"
  let renamed ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedLocal
  unless renamed.semantics == native.semantics do
    throwError "term binder renaming changed the resolved assertions"
  let renamedPair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoLocal
  unless renamedPair.semantics == pair.semantics do
    throwError "renaming multiple term binders changed the resolved assertions"
  let unrestricted ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localShared
  unless unrestricted.usesAt ⟨.body, []⟩ == .many &&
      unrestricted.valueAt ⟨.body, []⟩ == .localShared do
    throwError "locality-only prefix changed usage or ownership defaults"
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
  let outputAt (c : ResolvedSourceContract) (site : BinderSite) :=
    ((c.binders.find? (·.site == site)).bind (·.result)).getD Ixon.ValueContract.shared
  let localResult ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localResult
  unless outputAt localResult ⟨.type, []⟩ == .localShared &&
      localResult.valueAt ⟨.body, []⟩ == .localShared do
    throwError "local result or matching input was dropped"
  let localUnique ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResult
  unless outputAt localUnique ⟨.type, []⟩ == .localUnique &&
      localUnique.valueAt ⟨.body, []⟩ == .localUnique &&
      localUnique.usesAt ⟨.body, []⟩ == .linear do
    throwError "local unique result changed another axis"
  let curried ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.curriedResult
  unless outputAt curried ⟨.type, []⟩ == .shared &&
      outputAt curried ⟨.type, [.binderBody]⟩ == .localShared do
    throwError "a final result contract leaked into an intermediate arrow"
  for name in #[``Tests.Ix.SourceContract.SyntaxFixture.dependentArrow,
      ``Tests.Ix.SourceContract.SyntaxFixture.quantified] do
    let c ← getContract name
    unless outputAt c ⟨.type, []⟩ == .localShared &&
        c.valueAt ⟨.type, []⟩ == .localShared &&
        c.valueAt ⟨.body, []⟩ == .localShared do
      throwError "nested arrow or alpha-renamed lambda lost its contract"
  let anonymous ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.anonymousArrow
  unless outputAt anonymous ⟨.type, []⟩ == .localUnique &&
      anonymous.valueAt ⟨.body, []⟩ == .shared do
    throwError "an anonymous arrow confused its input and result contracts"
  for name in #[``Tests.Ix.SourceContract.SyntaxFixture.nestedLambda,
      ``Tests.Ix.SourceContract.SyntaxFixture.lambdaDefinition] do
    let c ← getContract name
    unless c.binders.any (fun b => b.kind == .lam && b.uses == .linear && b.value == .localShared) do
      throwError "a nested lambda annotation was lost"
  let localLet ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localLet
  unless localLet.binders.any (fun b => b.kind == .letE && b.letKind == .value &&
      b.uses == .linear && b.value == .localUnique) do
    throwError "ordinary local let lost a contract field"
  let loan ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.sharedLoan
  unless loan.binders.any (fun b => b.kind == .letE && b.letKind == .borrowShared &&
      b.uses == .many && b.value == .localShared) do
    throwError "explicit shared borrowing became an ordinary let"
  for (_, source) in selected do
    for expr in [source.type] ++ (sourceBody? source).toList do
      if (expr.find? (·.isConstOf ``sorryAx)).isSome then
        throwError "source annotation elaboration introduced a proof placeholder"

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

/-- error: binder usage must be 0, 1, or & -/
#guard_msgs in
def invalidQuantity (2 x : Nat) : Nat := x

/-- error: binder annotation components must be adjacent -/
#guard_msgs in
def separatedPrefix (! & x : Nat) : Nat := x

/-- error: duplicate ownership annotation -/
#guard_msgs in
def duplicateOwnership (!! x : Nat) : Nat := x

/-- error: duplicate locality annotation -/
#guard_msgs in
def duplicateLocality (~~ x : Nat) : Nat := x

/-- error: duplicate usage annotation -/
#guard_msgs in
def duplicateUsage (1& x : Nat) : Nat := x

/-- error: a shared borrow requires a shared local view (~) -/
#guard_msgs in
def invalidUniqueLoan (! owner : Nat) : Nat :=
  let borrow (~! view : Nat) := owner
  view

/-- error: a shared borrow requires a shared local view (~) -/
#guard_msgs in
def invalidEscapingLoan (! owner : Nat) : Nat :=
  let borrow (& view : Nat) := owner
  view
