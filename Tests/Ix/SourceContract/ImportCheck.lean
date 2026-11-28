import Tests.Ix.SourceContract.Imported

/- This module is elaborated in a separate process after Imported.olean exists.
It deliberately does not rerun that module's registration commands. -/

open Lean Ix.Compile

run_cmd do
  let identity ← getConstInfo ``Tests.Ix.SourceContract.Imported.identity
  let instanceSource ← getConstInfo ``Tests.Ix.SourceContract.Imported.withInstance
  let opaqueSource ← getConstInfo ``Tests.Ix.SourceContract.Imported.opaqueIdentity
  let assertsSource ← getConstInfo ``Tests.Ix.SourceContract.Imported.importedAsserts
  let ctorSource ← getConstInfo ``Tests.Ix.SourceContract.Imported.ImportedShared.mk
  let selected := [(identity.name, identity), (instanceSource.name, instanceSource),
    (opaqueSource.name, opaqueSource), (assertsSource.name, assertsSource),
    (ctorSource.name, ctorSource)]
  let .ok input := compileInputFromEnv (← getEnv) selected
    | throwError "imported contract export failed"
  let .ok resolved := input.resolve
    | throwError "imported contract resolution failed"
  unless resolved.contracts.size == 5 && resolved.measureHints.size == 1 do
    throwError "imported registrations were lost"
  let some contract := resolved.contracts.find? (·.source.name == identity.name)
    | throwError "imported identity contract is absent"
  unless contract.modeAt ⟨.type, []⟩ == .once && contract.modeAt ⟨.body, []⟩ == .once do
    throwError "imported identity modes changed"
  unless contract.resultAt ⟨.type, []⟩ == .uniqueBorrowed do
    throwError "imported result mode changed"
  let hint := resolved.measureHints[0]!
  unless hint.source.name == identity.name && hint.argument == 0 && hint.fixedStep == some 1 do
    throwError "imported measure mapping changed"
  let some contract := resolved.contracts.find? (·.source.name == instanceSource.name)
    | throwError "imported instance fixture contract is absent"
  unless contract.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .once do
    throwError "implicit or instance positions were omitted"
  let some contract := resolved.contracts.find? (·.source.name == opaqueSource.name)
    | throwError "imported opaque fixture contract is absent"
  unless contract.modeAt ⟨.body, []⟩ == .once do
    throwError "opaque declaration body contract was lost"
  let some contract := resolved.contracts.find? (·.source.name == assertsSource.name)
    | throwError "imported DefAsserts fixture contract is absent"
  unless contract.defAsserts == { alloc := .noAlloc, boundedStack := true } do
    throwError "imported DefAsserts changed: {repr contract.defAsserts}"
  let some contract := resolved.contracts.find? (·.source.name == ctorSource.name)
    | throwError "imported constructor fixture contract is absent"
  unless contract.fieldModeAt 0 == .shared && contract.fieldModeAt 2 == .inherited &&
      contract.modeAt ⟨.type, [.binderBody]⟩ == .erased do
    throwError "imported constructor fieldModes or erased field changed"

  -- Unselected registrations do not pollute the explicit selected input.
  let .ok empty := compileInputFromEnv (← getEnv) []
    | throwError "empty selected input should export"
  unless empty.contracts.isEmpty && empty.measureHints.isEmpty do
    throwError "unselected registrations leaked into an export"

  -- Simulate conflicting patches arriving from independently imported modules.
  -- The extension must retain both so export can reject, rather than overwrite.
  let some duplicate := input.contracts.find? (·.source.name == identity.name)
    | throwError "identity input contract is absent"
  let conflicting := { duplicate with
    binders := duplicate.binders.map fun binder => { binder with mode := .borrowed } }
  let forgedEnv := sourceContractExtension.addEntry (← getEnv) conflicting
  match compileInputFromEnv forgedEnv selected with
  | .error (.duplicateSite name _) =>
    unless name == identity.name do throwError "wrong conflicting declaration"
  | _ => throwError "conflicting imported patches silently overwrote a contract"

  -- An additional, disjoint patch must preserve the already-imported sites.
  let .ok extra := SourceContract.ofTelescope instanceSource #[{ binder := .position 0, mode := .erased }]
    | throwError "additional telescope patch failed to resolve"
  let .ok extendedEnv := registerSourceContract (← getEnv) extra
    | throwError "disjoint imported registration patch was rejected"
  let .ok extendedInput := compileInputFromEnv extendedEnv selected
    | throwError "extended registration failed to export"
  let .ok extended := extendedInput.resolve
    | throwError "extended registration failed to resolve"
  let some contract := extended.contracts.find? (·.source.name == instanceSource.name)
    | throwError "extended instance contract is absent"
  unless contract.modeAt ⟨.type, []⟩ == .erased &&
      contract.modeAt ⟨.type, [.binderBody, .binderBody]⟩ == .once do
    throwError "disjoint patches did not preserve both contracts"
