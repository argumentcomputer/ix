import Tests.Ix.SourceContract.SyntaxFixture

open Lean Ix.Compile

/-! ### 1. Zero `TokenTable` pollution & scoped activation checks -/

run_cmd do
  let baseEnv ← importModules #[{ module := `Ix.Compile.SourceContract.Registry }] {}
  let elabEnv ← importModules #[{ module := `Ix.Compile.SourceContract.Elab }] {}
  let baseTokens := (Parser.parserExtension.getState baseEnv).tokens.values
  let elabTokens := (Parser.parserExtension.getState elabEnv).tokens.values
  let baseSet : Std.HashSet String := baseTokens.foldl (·.insert ·) {}
  let added := elabTokens.filter (!baseSet.contains ·)
  unless added.isEmpty do
    throwError "SourceContract.Elab polluted TokenTable with new tokens: {added}"
  let curTokens := (Parser.parserExtension.getState (← getEnv)).tokens.values
  for forbidden in ["@unique", "@shared", "@borrowed", "@erased", "@once", "@borrow",
      "no_rc", "no_alloc", "bounded_stack", "borrow", "__ix_binder%", "__ix_binder_internal"] do
    if curTokens.contains forbidden then
      throwError "forbidden token '{forbidden}' found in TokenTable"

-- Without `open scoped Ix.Modes`, scoped attributes and parsers must NOT be active.
section ScopedInactive
/-- error: Unknown attribute `[no_rc]` -/
#guard_msgs in
@[no_rc] def inactiveNoRc : Nat := 0

/-- error: Unknown attribute `[no_alloc]` -/
#guard_msgs in
@[no_alloc] def inactiveNoAlloc : Nat := 0

/-- error: Unknown attribute `[bounded_stack]` -/
#guard_msgs in
@[bounded_stack] def inactiveBoundedStack : Nat := 0

run_cmd do
  -- Without `open scoped Ix.Modes`, mode-annotated `def` must NOT parse as SourceSyntax.declaration.
  if (Parser.runParserCategory (← getEnv) `command "def inactiveUnique (@unique x : Nat) : Nat := x").isOk then
    throwError "mode-annotated def parsed without `open scoped Ix.Modes`"
end ScopedInactive

/-! ### 2. Positive fixture resolution & roundtrip checks -/

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
    ``Tests.Ix.SourceContract.SyntaxFixture.withAnonInstance,
    ``Tests.Ix.SourceContract.SyntaxFixture.strictImplicit,
    ``Tests.Ix.SourceContract.SyntaxFixture.shadowed,
    ``Tests.Ix.SourceContract.SyntaxFixture.anonBinder,
    ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrowRev,
    ``Tests.Ix.SourceContract.SyntaxFixture.twoLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.twoLocalRev,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoLocal,
    ``Tests.Ix.SourceContract.SyntaxFixture.localShared,
    ``Tests.Ix.SourceContract.SyntaxFixture.localUnique,
    ``Tests.Ix.SourceContract.SyntaxFixture.onceBorrowed,
    ``Tests.Ix.SourceContract.SyntaxFixture.onceBorrowedRev,
    ``Tests.Ix.SourceContract.SyntaxFixture.multiName,
    ``Tests.Ix.SourceContract.SyntaxFixture.multiNameResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.localResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.uniqueResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResultRev,
    ``Tests.Ix.SourceContract.SyntaxFixture.curriedResult,
    ``Tests.Ix.SourceContract.SyntaxFixture.abbrevUnique,
    ``Tests.Ix.SourceContract.SyntaxFixture.opaqueBorrowed,
    ``Tests.Ix.SourceContract.SyntaxFixture.axiomUnique,
    ``Tests.Ix.SourceContract.SyntaxFixture.dependentArrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.anonymousArrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.arrowPrecedence,
    ``Tests.Ix.SourceContract.SyntaxFixture.arrowChain,
    ``Tests.Ix.SourceContract.SyntaxFixture.quantified,
    ``Tests.Ix.SourceContract.SyntaxFixture.nestedLambda,
    ``Tests.Ix.SourceContract.SyntaxFixture.lambdaDefinition,
    ``Tests.Ix.SourceContract.SyntaxFixture.lambdaNoType,
    ``Tests.Ix.SourceContract.SyntaxFixture.lambdaMultiNoType,
    ``Tests.Ix.SourceContract.SyntaxFixture.lambdaZeroLeak,
    ``Tests.Ix.SourceContract.SyntaxFixture.localLet,
    ``Tests.Ix.SourceContract.SyntaxFixture.localLetNoType,
    ``Tests.Ix.SourceContract.SyntaxFixture.letAllModes,
    ``Tests.Ix.SourceContract.SyntaxFixture.sharedLoan,
    ``Tests.Ix.SourceContract.SyntaxFixture.sharedLoanNoType,
    ``Tests.Ix.SourceContract.SyntaxFixture.doBlockBorrow,
    ``Tests.Ix.SourceContract.SyntaxFixture.doBlockBorrowEscape,
    ``Tests.Ix.SourceContract.SyntaxFixture.doBlockAllModes,
    ``Tests.Ix.SourceContract.SyntaxFixture.SharedBox.mk,
    ``Tests.Ix.SourceContract.SyntaxFixture.SharedOnly.mk,
    ``Tests.Ix.SourceContract.SyntaxFixture.SharedDefault.mk,
    ``Tests.Ix.SourceContract.SyntaxFixture.ExtShared.mk,
    ``Tests.Ix.SourceContract.SyntaxFixture.ModeList.cons,
    ``Tests.Ix.SourceContract.SyntaxFixture.ModeTree.node,
    ``Tests.Ix.SourceContract.SyntaxFixture.ArrowInd.mk,
    ``Tests.Ix.SourceContract.SyntaxFixture.defNoRc,
    ``Tests.Ix.SourceContract.SyntaxFixture.defNoAlloc,
    ``Tests.Ix.SourceContract.SyntaxFixture.defBoundedStack,
    ``Tests.Ix.SourceContract.SyntaxFixture.defNoRcBounded,
    ``Tests.Ix.SourceContract.SyntaxFixture.defNoAllocBounded,
    ``Tests.Ix.SourceContract.SyntaxFixture.defBoundedNoAlloc,
    ``Tests.Ix.SourceContract.SyntaxFixture.defInlineNoRc,
    ``Tests.Ix.SourceContract.SyntaxFixture.defZeroArity,
    ``Tests.Ix.SourceContract.SyntaxFixture.defRecursive]
  let selected ← names.toList.mapM fun name => do return (name, ← getConstInfo name)
  let input ← match compileInputFromEnv (← getEnv) selected with
    | .ok input => pure input
    | .error error => throwError "{error}"
  let resolved ← match input.resolve with
    | .ok input => pure input
    | .error error => throwError "{error}"
  unless resolved.contracts.size == names.size do
    throwError "syntax registrations were lost on import ({resolved.contracts.size} vs {names.size})"
  unless resolved.measureHints.size == 1 && resolved.measureHints[0]!.argument == 0 do
    throwError "measure hint on annotated source was lost on import"
  let getContract (name : Name) := do
    let some contract := resolved.contracts.find? (·.source.name == name)
      | throwError "missing syntax contract {name}"
    pure contract

  -- Binder modes & order-insensitivity
  let unique ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.unique
  unless unique.modeAt ⟨.type, []⟩ == .unique && unique.modeAt ⟨.body, []⟩ == .unique &&
      unique.resultAt ⟨.type, []⟩ == .shared do
    throwError "unique binder changed meaning"
  let native ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrow
  let nativeRev ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.nativeBorrowRev
  unless native.modeAt ⟨.type, []⟩ == .uniqueBorrowed &&
      native.modeAt ⟨.body, []⟩ == .uniqueBorrowed &&
      nativeRev.semantics == native.semantics do
    throwError "uniqueBorrowed or order-insensitivity changed on import"
  let .forallE _ domain _ _ := native.source.type | throwError "native fixture has no binder"
  unless isMarkedBorrowed domain do
    throwError "source marker hid Lean's native @& borrow annotation"
  let pair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.twoLocal
  let pairRev ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.twoLocalRev
  unless pair.modeAt ⟨.type, []⟩ == .uniqueBorrowed &&
      pair.modeAt ⟨.type, [.binderBody]⟩ == .onceBorrowed &&
      pairRev.semantics == pair.semantics do
    throwError "distinct local ownership/usage modes were conflated or order-sensitive"
  let renamed ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedLocal
  unless renamed.semantics == native.semantics do
    throwError "term binder renaming changed the resolved assertions"
  let renamedPair ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.renamedTwoLocal
  unless renamedPair.semantics == pair.semantics do
    throwError "renaming multiple term binders changed the resolved assertions"
  let ob ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.onceBorrowed
  let obRev ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.onceBorrowedRev
  unless ob.modeAt ⟨.type, []⟩ == .onceBorrowed && obRev.semantics == ob.semantics do
    throwError "onceBorrowed order-insensitivity failed"
  let multi ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.multiName
  unless multi.modeAt ⟨.type, []⟩ == .unique &&
      multi.modeAt ⟨.type, [.binderBody]⟩ == .unique &&
      multi.modeAt ⟨.body, []⟩ == .unique &&
      multi.modeAt ⟨.body, [.binderBody]⟩ == .unique &&
      multi.resultAt ⟨.type, []⟩ == .shared &&
      multi.resultAt ⟨.type, [.binderBody]⟩ == .shared do
    throwError "multi-name annotated binder failed"
  let multiRes ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.multiNameResult
  unless multiRes.resultAt ⟨.type, []⟩ == .shared &&
      multiRes.resultAt ⟨.type, [.binderBody]⟩ == .unique do
    throwError "multi-name binder result mode leaked onto earlier binder"
  let dependent ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.dependent
  unless dependent.modeAt ⟨.type, []⟩ == .erased &&
      dependent.modeAt ⟨.body, [.binderBody]⟩ == .once do
    throwError "implicit parameter shifted the explicit annotation"
  let inferred ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.inferredImplicit
  unless inferred.modeAt ⟨.type, []⟩ == .many &&
      inferred.modeAt ⟨.type, [.binderBody]⟩ == .once do
    throwError "auto-implicit parameter received explicit binder's annotation"
  let instC ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.withInstance
  unless (instC.binders.find? (·.site == ⟨.type, [.binderBody]⟩)).map (·.binderInfo) ==
      some .instImplicit do
    throwError "annotated instance binder lost its BinderInfo"
  let anonInst ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.withAnonInstance
  unless anonInst.modeAt ⟨.type, [.binderBody]⟩ == .borrowed &&
      (anonInst.binders.find? (·.site == ⟨.type, [.binderBody]⟩)).map (·.binderInfo) ==
      some .instImplicit do
    throwError "anonymous annotated instance binder failed"
  let shadowed ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.shadowed
  unless shadowed.modeAt ⟨.body, []⟩ == .once &&
      shadowed.modeAt ⟨.body, [.binderBody]⟩ == .borrowed do
    throwError "shadowed binder names were conflated"
  let anonB ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.anonBinder
  unless anonB.modeAt ⟨.type, []⟩ == .erased && anonB.modeAt ⟨.body, []⟩ == .erased do
    throwError "anonymous '_' erased binder failed"

  -- Result modes & arrow precedence & abbrev/opaque/axiom
  let localResult ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localResult
  unless localResult.resultAt ⟨.type, []⟩ == .borrowed &&
      localResult.modeAt ⟨.body, []⟩ == .borrowed do
    throwError "borrowed result or matching input was dropped"
  let localUnique ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResult
  let localUniqueRev ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localUniqueResultRev
  unless localUnique.resultAt ⟨.type, []⟩ == .uniqueBorrowed &&
      localUnique.modeAt ⟨.body, []⟩ == .uniqueBorrowed &&
      localUniqueRev.semantics == localUnique.semantics do
    throwError "uniqueBorrowed result failed or was order-sensitive"
  let curried ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.curriedResult
  unless curried.resultAt ⟨.type, []⟩ == .shared &&
      curried.resultAt ⟨.type, [.binderBody]⟩ == .borrowed do
    throwError "final result mode leaked into intermediate arrow"
  let abbrevU ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.abbrevUnique
  unless abbrevU.modeAt ⟨.type, []⟩ == .unique && abbrevU.resultAt ⟨.type, []⟩ == .unique do
    throwError "abbrev mode annotation failed"
  let opaqB ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.opaqueBorrowed
  unless opaqB.modeAt ⟨.type, []⟩ == .borrowed && opaqB.resultAt ⟨.type, []⟩ == .borrowed do
    throwError "opaque mode annotation failed"
  let axU ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.axiomUnique
  unless axU.modeAt ⟨.type, []⟩ == .unique && axU.resultAt ⟨.type, []⟩ == .unique do
    throwError "axiom mode annotation failed"
  let prec ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.arrowPrecedence
  unless prec.resultAt ⟨.type, []⟩ == .unique &&
      prec.resultAt ⟨.type, [.binderBody]⟩ == .shared do
    throwError "A → @unique B → C precedence was wrong"
  let chain ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.arrowChain
  unless chain.modeAt ⟨.type, []⟩ == .borrowed &&
      chain.resultAt ⟨.type, []⟩ == .unique &&
      chain.modeAt ⟨.type, [.binderBody]⟩ == .many &&
      chain.resultAt ⟨.type, [.binderBody]⟩ == .borrowed do
    throwError "(@borrowed x : Nat) → @unique Nat → @borrowed Nat failed"
  for name in #[``Tests.Ix.SourceContract.SyntaxFixture.dependentArrow,
      ``Tests.Ix.SourceContract.SyntaxFixture.quantified] do
    let c ← getContract name
    unless c.resultAt ⟨.type, []⟩ == .borrowed &&
        c.modeAt ⟨.type, []⟩ == .borrowed &&
        c.modeAt ⟨.body, []⟩ == .borrowed do
      throwError "nested arrow or quantified binder lost its contract"
  let anonymous ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.anonymousArrow
  unless anonymous.resultAt ⟨.type, []⟩ == .uniqueBorrowed &&
      anonymous.modeAt ⟨.body, []⟩ == .many do
    throwError "anonymous arrow confused input and result modes"

  -- Lambdas (with & without `: T`, multi-name, zero-leak)
  for name in #[``Tests.Ix.SourceContract.SyntaxFixture.nestedLambda,
      ``Tests.Ix.SourceContract.SyntaxFixture.lambdaDefinition] do
    let c ← getContract name
    unless c.binders.any (fun b => b.kind == .lam && b.mode == .onceBorrowed) do
      throwError "nested lambda annotation was lost on {name}"
  let lamNoTy ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.lambdaNoType
  unless lamNoTy.binders.any (fun b => b.kind == .lam && b.mode == .unique) do
    throwError "fun (@unique x) without `: T` failed"
  let lamMulti ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.lambdaMultiNoType
  unless lamMulti.modeAt ⟨.body, []⟩ == .unique &&
      lamMulti.modeAt ⟨.body, [.binderBody]⟩ == .unique do
    throwError "fun (@unique x y) without `: T` failed"
  let lamLeak ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.lambdaZeroLeak
  unless lamLeak.binders.size == 2 &&
      lamLeak.modeAt ⟨.type, []⟩ == .unique &&
      lamLeak.modeAt ⟨.body, []⟩ == .unique &&
      !lamLeak.binders.any (·.kind == .letE) do
    throwError "fun (@unique x) leaked annotation onto inner plain let"

  -- `let` and `do`-block `let` (all 8 modes, with and without `: T`)
  let localLet ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localLet
  unless localLet.binders.any (fun b => b.kind == .letE && !b.isBorrow && b.mode == .uniqueBorrowed) do
    throwError "annotated let lost its mode"
  let localLetNoTy ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.localLetNoType
  unless localLetNoTy.binders.size == 1 &&
      localLetNoTy.binders[0]!.kind == .letE && localLetNoTy.binders[0]!.mode == .unique do
    throwError "untyped let @unique leaked onto inner plain let"
  let allLet ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.letAllModes
  for expected in [Ixon.BinderMode.borrowed, .unique, .uniqueBorrowed, .once, .onceBorrowed, .erased] do
    unless allLet.binders.any (fun b => b.kind == .letE && !b.isBorrow && b.mode == expected) do
      throwError "letAllModes missing mode {repr expected}"
  for name in #[``Tests.Ix.SourceContract.SyntaxFixture.sharedLoan,
      ``Tests.Ix.SourceContract.SyntaxFixture.sharedLoanNoType,
      ``Tests.Ix.SourceContract.SyntaxFixture.doBlockBorrow,
      ``Tests.Ix.SourceContract.SyntaxFixture.doBlockBorrowEscape] do
    let loan ← getContract name
    unless loan.binders.any (fun b => b.kind == .letE && b.isBorrow && b.mode == .borrowed) do
      throwError "let @borrow failed on {name}"
  let doAll ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.doBlockAllModes
  for expected in [Ixon.BinderMode.borrowed, .unique, .uniqueBorrowed, .once, .onceBorrowed, .erased] do
    unless doAll.binders.any (fun b => b.kind == .letE && !b.isBorrow && b.mode == expected) do
      throwError "doBlockAllModes missing value let mode {repr expected}"
  unless doAll.binders.any (fun b => b.kind == .letE && b.isBorrow && b.mode == .borrowed) do
    throwError "doBlockAllModes missing @borrow"

  -- Structure & inductive fields (`@shared`, `@erased`)
  let sb ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.SharedBox.mk
  unless sb.fieldModeAt 0 == .shared && sb.fieldModeAt 1 == .inherited && sb.fieldModeAt 2 == .inherited &&
      sb.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .erased do
    throwError "SharedBox.mk field modes or erased field wrong: {repr sb.fieldModes} / {repr sb.binders}"
  let so ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.SharedOnly.mk
  unless so.fieldModeAt 0 == .shared do
    throwError "SharedOnly.mk field mode wrong"
  let sd ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.SharedDefault.mk
  unless sd.fieldModeAt 0 == .shared && sd.fieldModeAt 1 == .shared && sd.fieldModeAt 2 == .shared do
    throwError "SharedDefault.mk field modes wrong: {repr sd.fieldModes}"
  let es ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.ExtShared.mk
  -- field 0 is toBasePair, field 1 is tag (@shared), field 2 is witness (@erased)
  unless es.fieldModeAt 0 == .inherited && es.fieldModeAt 1 == .shared &&
      es.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .erased do
    throwError "ExtShared.mk field modes wrong: {repr es.fieldModes} / {repr es.binders}"
  let ml ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.ModeList.cons
  -- param 0 is α, field 0 is head (@shared), field 1 is proof (@erased), field 2 is tail
  unless ml.fieldModeAt 0 == .shared && ml.fieldModeAt 1 == .inherited &&
      ml.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .erased do
    throwError "ModeList.cons field modes wrong: {repr ml.fieldModes} / {repr ml.binders}"
  let mt ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.ModeTree.node
  -- param 0 is α, field 0 is label (@shared), field 1 is proof (@erased)
  unless mt.fieldModeAt 0 == .shared && mt.fieldModeAt 1 == .inherited &&
      mt.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .erased do
    throwError "ModeTree.node field modes wrong: {repr mt.fieldModes} / {repr mt.binders}"
  let ai ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.ArrowInd.mk
  -- field 0 is Nat, field 1 is x (@shared), field 2 is h (@erased)
  unless ai.fieldModeAt 0 == .inherited && ai.fieldModeAt 1 == .shared &&
      ai.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .erased do
    throwError "ArrowInd.mk field modes wrong: {repr ai.fieldModes} / {repr ai.binders}"

  -- DefAsserts (all 6 values + combined with binder modes & opaque)
  let checkAsserts (n : Name) (expected : Ixon.DefAsserts) : Elab.Command.CommandElabM Unit := do
    let c ← getContract n
    unless c.defAsserts == expected do
      throwError "{n}: expected asserts {repr expected}, got {repr c.defAsserts}"
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defNoRc { alloc := .noRc }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defNoAlloc { alloc := .noAlloc }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defBoundedStack { boundedStack := true }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defNoRcBounded { alloc := .noRc, boundedStack := true }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defNoAllocBounded { alloc := .noAlloc, boundedStack := true }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defBoundedNoAlloc { alloc := .noAlloc, boundedStack := true }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defZeroArity { alloc := .noAlloc, boundedStack := true }
  checkAsserts ``Tests.Ix.SourceContract.SyntaxFixture.defRecursive { alloc := .noRc }
  let inlineNoRc ← getContract ``Tests.Ix.SourceContract.SyntaxFixture.defInlineNoRc
  unless inlineNoRc.defAsserts == { alloc := .noRc } &&
      inlineNoRc.modeAt ⟨.type, []⟩ == .unique &&
      inlineNoRc.resultAt ⟨.type, []⟩ == .unique do
    throwError "defInlineNoRc lost asserts or binder/result modes"

  -- No sorryAx introduced
  for (_, source) in selected do
    for expr in [source.type] ++ (sourceBody? source).toList do
      if (expr.find? (·.isConstOf ``sorryAx)).isSome then
        throwError "source annotation elaboration introduced sorryAx in {source.name}"

  -- Private registration preserved
  let registry := sourceContractExtension.getState (← getEnv)
  unless registry.toArray.any (fun (name, _) => name.toString.endsWith ".privateIdentity") do
    throwError "private annotated declaration was not registered"

  -- Non-interference & ordinary declarations carry ZERO contracts
  for ordName in [
      ``Tests.Ix.SourceContract.SyntaxFixture.ordinaryBinder,
      ``Tests.Ix.SourceContract.SyntaxFixture.nonInterfExplicitApps,
      ``Tests.Ix.SourceContract.SyntaxFixture.nonInterfParenAscription,
      ``Tests.Ix.SourceContract.SyntaxFixture.nonInterfLetPat,
      ``Tests.Ix.SourceContract.SyntaxFixture.nonInterfLetBorrowFn,
      ``Tests.Ix.SourceContract.SyntaxFixture.nonInterfDoOrdinary] do
    let ord ← getConstInfo ordName
    let .ok plain := compileInputFromEnv (← getEnv) [(ord.name, ord)]
      | throwError "ordinary/non-interference decl {ordName} failed to export"
    unless plain.contracts.isEmpty do
      throwError "ordinary/non-interference decl {ordName} unexpectedly gained contracts"

  -- Omitted registry rejected when markers exist
  match (CompileInput.plain selected).resolve with
  | .error (.missingContract _) => pure ()
  | _ => throwError "annotated source accepted an omitted registry"

/-! ### 3. Negative parser & elaborator error cases (with `open scoped Ix.Modes`) -/

section NegativeTests
open scoped Ix.Modes

-- Verify space after `@` is rejected
run_cmd do
  for text in [
      "def bad (@ unique x : Nat) : Nat := x",
      "def bad (@ borrowed x : Nat) : Nat := x",
      "def bad (! x : Nat) : Nat := x",
      "def bad (~1 x : Nat) : Nat := x"] do
    if (Parser.runParserCategory (← getEnv) `command text).isOk then
      throwError "invalid binder spelling was accepted: {text}"

/-- error: @erased cannot be combined with other mode annotations -/
#guard_msgs in
def badErasedUnique (@erased @unique x : Nat) : Nat := x

/-- error: @erased cannot be combined with other mode annotations -/
#guard_msgs in
def badUniqueErased (@unique @erased x : Nat) : Nat := x

/-- error: @erased cannot be combined with other mode annotations -/
#guard_msgs in
def badErasedBorrowed (@erased @borrowed x : Nat) : Nat := x

/-- error: @erased cannot be combined with other mode annotations -/
#guard_msgs in
def badErasedOnce (@erased @once x : Nat) : Nat := x

/-- error: @once cannot be combined with @unique -/
#guard_msgs in
def badOnceUnique (@once @unique x : Nat) : Nat := x

/-- error: @once cannot be combined with @unique -/
#guard_msgs in
def badUniqueOnce (@unique @once x : Nat) : Nat := x

/-- error: duplicate @unique mode annotation -/
#guard_msgs in
def badDupUnique (@unique @unique x : Nat) : Nat := x

/-- error: duplicate @borrowed mode annotation -/
#guard_msgs in
def badDupBorrowed (@borrowed @borrowed x : Nat) : Nat := x

/-- error: duplicate @once mode annotation -/
#guard_msgs in
def badDupOnce (@once @once x : Nat) : Nat := x

/-- error: duplicate @erased mode annotation -/
#guard_msgs in
def badDupErased (@erased @erased x : Nat) : Nat := x

/-- error: @erased is not a valid result mode; result modes allow only @unique and @borrowed -/
#guard_msgs in
def badErasedResult (x : Nat) : @erased Nat := x

/-- error: @once is not a valid result mode; result modes allow only @unique and @borrowed -/
#guard_msgs in
example : Nat → @once Nat := fun x => x

/-- error: duplicate @unique mode annotation -/
#guard_msgs in
def badDupResult (x : Nat) : @unique @unique Nat := x

/-- error: @borrow cannot be combined with other mode annotations -/
#guard_msgs in
example (owner : Nat) : Nat :=
  let @borrow @unique view := owner
  view

/-- error: @borrow cannot be combined with other mode annotations -/
#guard_msgs in
example (owner : Nat) : Nat :=
  let @borrow @borrowed view := owner
  view

/-- error: duplicate @borrow mode annotation -/
#guard_msgs in
example (owner : Nat) : Nat :=
  let @borrow @borrow view := owner
  view

/-- error: @erased cannot be combined with @shared on a field -/
#guard_msgs in
structure BadStructBoth where
  @shared @erased x : Nat

/-- error: duplicate @shared mode annotation -/
#guard_msgs in
structure BadStructDup where
  @shared @shared x : Nat

/-- error: @unique is not a valid field mode; structure and inductive fields only allow @shared or @erased -/
#guard_msgs in
structure BadStructUnique where
  @unique x : Nat

/-- error: @erased cannot be combined with @shared on a field -/
#guard_msgs in
inductive BadIndBoth where
  | mk (@shared @erased x : Nat)

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on theorems -/
#guard_msgs in
@[no_rc] theorem badThmNoRc : True := trivial

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on partial, unsafe, or opaque definitions -/
#guard_msgs in
@[no_alloc] partial def badPartialNoAlloc (n : Nat) : Nat := badPartialNoAlloc n

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on partial or unsafe definitions -/
#guard_msgs in
@[bounded_stack] unsafe def badUnsafeBounded : Nat := 0

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on partial, unsafe, or opaque definitions -/
#guard_msgs in
@[no_rc] opaque badOpaqueNoRc : Nat := 0

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are not allowed on partial, unsafe, or opaque definitions -/
#guard_msgs in
@[no_rc] unsafe opaque badUnsafeOpaque : Nat := 0

/-- error: definition assertions (@[no_rc], @[no_alloc], @[bounded_stack]) are only allowed on safe definitions -/
#guard_msgs in
@[no_rc] axiom badAxiomNoRc : Nat

/-- error: conflicting allocation assertions: @[no_alloc] and @[no_rc] cannot both be specified -/
#guard_msgs in
@[no_rc, no_alloc] def badConflictAlloc : Nat := 0

/-- error: duplicate allocation assertion (Ixon.AllocAssert.noRc) -/
#guard_msgs in
@[no_rc, no_rc] def badDupNoRc : Nat := 0

/-- error: duplicate @[bounded_stack] assertion -/
#guard_msgs in
@[bounded_stack, bounded_stack] def badDupBounded : Nat := 0

end NegativeTests
