module

public import Ix.Compile.SourceContract
public import LSpec
public import Lean.Compiler.BorrowedAnnotation

public section

namespace Tests.Ix.SourceContract

open Lean LSpec
open Ix.Compile

private def test (description : String) (condition : Bool) : TestSeq :=
  LSpec.test description (condition = true)

private def natType : Expr := .const `Nat []

private def definition (name : Name) (type value : Expr) : ConstantInfo :=
  .defnInfo {
    name, levelParams := [], type, value, hints := .abbrev
    safety := .safe, all := [name] }

private def identity (name : Name := `identity) : ConstantInfo :=
  definition name (.forallE `x natType natType .default)
    (.lam `x natType (.bvar 0) .default)

private def curried : ConstantInfo :=
  definition `curried
    (.forallE `x natType (.forallE `y natType natType .default) .implicit)
    (.lam `x natType (.lam `y natType (.bvar 0) .default) .implicit)

private def resolveTelescope (source : ConstantInfo) (contracts : Array TelescopeContract) :
    Except SourceContractError ResolvedSourceContract := do
  (← SourceContract.ofTelescope source contracts).resolve source

private def expectError (actual : Except SourceContractError α) (expected : SourceContractError) : Bool :=
  match actual with
  | .error error => error == expected
  | .ok _ => false

private def resolvedModes (actual : Except SourceContractError ResolvedSourceContract) :
    Array (BinderSite × Ixon.Uses × Option Ixon.ValueContract) :=
  match actual with
  | .error _ => #[]
  | .ok contract => contract.binders.map fun binder => (binder.site, binder.uses, binder.result)

def telescopeTests : TestSeq :=
  test "identity resolves linear/unique type and linear body at independent sites"
    (resolvedModes (resolveTelescope (identity) #[{ binder := .position 0, uses := .linear, result := some .unique }]) ==
      #[(⟨.type, []⟩, .linear, some .unique), (⟨.body, []⟩, .linear, none)]) ++
  test "all four usage modes are accepted without inferring resource validity"
    ([Ixon.Uses.erased, .linear, .affine, .many].all fun uses =>
      (resolveTelescope (identity) #[{ binder := .position 0, uses, result := some .shared }]).isOk) ++
  test "ownership shorthand affects only the selected curried arrow"
    (resolvedModes (resolveTelescope curried #[{ binder := .name `y, uses := .linear, result := some .unique }]) ==
      #[(⟨.type, [.binderBody]⟩, .linear, some .unique),
        (⟨.body, [.binderBody]⟩, .linear, none)]) ++
  test "implicit argument retains its position and does not imply erasure"
    (match resolveTelescope curried #[{ binder := .position 0, uses := .many }] with
      | .ok result => result.binders.all fun binder =>
        binder.binderInfo == .implicit && binder.uses == .many
      | .error _ => false) ++
  test "out-of-range elaborated positions are rejected"
    (expectError (resolveTelescope curried #[{ binder := .position 2, uses := .linear }])
      (.argumentOutOfRange `curried 2)) ++
  test "missing binder names are rejected"
    (expectError (resolveTelescope curried #[{ binder := .name `missing, uses := .linear }])
      (.unknownBinder `curried `missing)) ++
  test "name and position annotations cannot silently overwrite the same site"
    (expectError (resolveTelescope curried #[{ binder := .name `y, uses := .linear },
      { binder := .position 1, uses := .affine }])
      (.duplicateSite `curried ⟨.type, [.binderBody]⟩))

def occurrenceTests : TestSeq := Id.run do
  let lam := Expr.lam `shadow natType (.bvar 0) .default
  let nested := definition `nested (.forallE `x natType natType .default)
    (.lam `x natType (.app lam (.app lam (.bvar 0))) .default)
  let left : BinderSite := ⟨.body, [.binderBody, .appFn]⟩
  let right : BinderSite := ⟨.body, [.binderBody, .appArg, .appFn]⟩
  let distinct : SourceContract := {
    source := nested
    binders := #[{ site := left, uses := .linear }, { site := right, uses := .affine }] }
  let shadowed := definition `shadowed
    (.forallE `x natType (.forallE `x natType natType .default) .default)
    (.lam `x natType (.lam `x natType (.bvar 0) .default) .default)
  let wrapped := definition `wrapped
    (.mdata {} (.forallE `x natType natType .default))
    (.mdata {} (.lam `x natType (.bvar 0) .default))
  return test "equal nested lambdas can carry different occurrence contracts"
      (resolvedModes (distinct.resolve nested) == #[(left, .linear, none), (right, .affine, none)]) ++
    test "annotation order has a canonical resolved order"
      (resolvedModes (({ distinct with binders := distinct.binders.reverse }).resolve nested) ==
        resolvedModes (distinct.resolve nested)) ++
    test "shadowed declaration binders require an explicit position"
      (expectError (resolveTelescope shadowed #[{ binder := .name `x, uses := .linear }])
        (.ambiguousBinder `shadowed `x)) ++
    test "position disambiguates shadowed declaration binders"
      ((resolveTelescope shadowed #[{ binder := .position 1, uses := .linear }]).isOk) ++
    test "metadata wrappers appear in resolved telescope paths"
      (resolvedModes (resolveTelescope wrapped #[{ binder := .position 0, uses := .linear, result := some .unique }]) ==
        #[(⟨.type, [.metadata]⟩, .linear, some .unique),
          (⟨.body, [.metadata]⟩, .linear, none)]) ++
    test "invalid structural edges fail before canonicalization"
      (expectError (({ source := identity, binders := #[{ site := ⟨.body, [.appArg]⟩, uses := .linear }] } : SourceContract).resolve identity)
        (.invalidSite `identity ⟨.body, [.appArg]⟩)) ++
    test "an expression occurrence must actually be a binder"
      (expectError (({ source := identity, binders := #[{ site := ⟨.body, [.binderBody]⟩, uses := .linear }] } : SourceContract).resolve identity)
        (.expectedBinder `identity ⟨.body, [.binderBody]⟩))

def rejectionTests : TestSeq := Id.run do
  let bodySite : BinderSite := ⟨.body, []⟩
  let typeSite : BinderSite := ⟨.type, []⟩
  let contract : SourceContract := {
    source := identity
    binders := #[{ site := typeSite, uses := .linear }, { site := bodySite, uses := .linear }] }
  let renamed := definition `identity (.forallE `renamed natType natType .default)
    (.lam `renamed natType (.bvar 0) .default)
  let changedInfo := definition `identity (.forallE `x natType natType .implicit)
    (.lam `x natType (.bvar 0) .implicit)
  let changedMetadata := definition `identity (.forallE `x natType natType .default)
    (.mdata {} (.lam `x natType (.bvar 0) .default))
  let alias := definition `alias (.forallE `x natType natType .default) (.const `identity [])
  return test "type/body usage disagreement is rejected"
      (expectError (({ source := identity, binders := #[{ site := typeSite, uses := .linear }] } : SourceContract).resolve identity)
        (.inconsistentTelescope `identity 0 .linear .many)) ++
    test "a lambda has no independent result-ownership field"
      (expectError (({ source := identity, binders := #[{ site := bodySite, uses := .many, result := some .shared }] } : SourceContract).resolve identity)
        (.resultOnNonArrow `identity bodySite)) ++
    test "source binder spelling is part of the occurrence fingerprint"
      (expectError (contract.resolve renamed) (.staleSource `identity)) ++
    test "source BinderInfo drift invalidates a previously resolved contract"
      (expectError (contract.resolve changedInfo) (.staleSource `identity)) ++
    test "source metadata shape drift invalidates structural paths"
      (expectError (contract.resolve changedMetadata) (.staleSource `identity)) ++
    test "unsupported body telescope normalization gets a diagnostic"
      (expectError (resolveTelescope alias #[{ binder := .position 0, uses := .linear }])
        (.missingBodyBinder `alias 0))

def inputTests : TestSeq := Id.run do
  let source := identity
  let constants := [(source.name, source)]
  let first : SourceContract := {
    source
    binders := #[{ site := ⟨.type, []⟩, uses := .linear }, { site := ⟨.body, []⟩, uses := .linear }] }
  let second := identity `second
  let secondContract : SourceContract :=
    { source := second
      binders := #[{ site := ⟨.type, []⟩, uses := .affine }, { site := ⟨.body, []⟩, uses := .affine }] }
  let sameBody : CompileInput :=
    { constants := constants ++ [(second.name, second)], contracts := #[first, secondContract] }
  let hinted : CompileInput :=
    { constants, contracts := #[], measureHints := #[⟨source, .name `x, some 1⟩] }
  return test "plain input preserves selected source and has no semantic contracts"
      (match (CompileInput.plain constants).resolve with
        | .ok result => result.constants == constants && result.contracts.isEmpty
        | .error _ => false) ++
    test "equal declaration bodies retain their distinct semantic contracts"
      (match sameBody.resolve with
        | .ok result => result.contracts.size == 2 &&
          result.contracts[0]!.usesAt ⟨.body, []⟩ == .linear &&
          result.contracts[1]!.usesAt ⟨.body, []⟩ == .affine
        | .error _ => false) ++
    test "duplicate selected declarations are rejected"
      (expectError ((CompileInput.plain (constants ++ constants)).resolve)
        (.duplicateDeclaration `identity)) ++
    test "selected names must match their declaration"
      (expectError ((CompileInput.plain [(`wrong, source)]).resolve)
        (.declarationNameMismatch `wrong `identity)) ++
    test "a dangling registry entry cannot be silently dropped"
      (expectError (({ constants := [], contracts := #[first] } : CompileInput).resolve)
        (.missingDeclaration `identity)) ++
    test "duplicate declaration contracts cannot overwrite each other"
      (expectError (({ constants, contracts := #[first, first] } : CompileInput).resolve)
        (.duplicateContract `identity)) ++
    test "measure hints resolve to positions without changing source or modes"
      (match hinted.resolve with
        | .ok result => result.constants == constants && result.contracts.isEmpty &&
          result.measureHints.size == 1 && result.measureHints[0]!.argument == 0 &&
          result.measureHints[0]!.site == ⟨.type, []⟩
        | .error _ => false) ++
    test "zero-step proposals receive a diagnostic"
      (expectError (({ hinted with measureHints := #[⟨source, .position 0, some 0⟩] }).resolve)
        (.zeroFixedStep `identity)) ++
    test "multiple measure proposals for one declaration are rejected"
      (expectError (({ hinted with measureHints := hinted.measureHints ++ hinted.measureHints }).resolve)
        (.duplicateMeasure `identity))

def valueContractTests : TestSeq := Id.run do
  let source := identity
  let typeSite : BinderSite := ⟨.type, []⟩
  let bodySite : BinderSite := ⟨.body, []⟩
  let unique : TelescopeContract := { binder := .position 0, uses := .many, value := .unique }
  let ownershipMismatch : SourceContract := {
    source, binders := #[{ site := typeSite, uses := .many, value := .unique }] }
  let localityMismatch : SourceContract := {
    source, binders := #[{ site := typeSite, uses := .many, value := .localShared }] }
  let values : List Ixon.ValueContract := [.shared, .unique, .localShared, .localUnique]
  let modes : List Ixon.Uses := [.erased, .linear, .affine, .many]
  let binding := definition `binding natType (.letE `view natType (.const `owner []) (.bvar 0) false)
  let borrow : SourceContract := {
    source := binding
    binders := #[{ site := bodySite, uses := .affine, value := .localShared, letKind := .borrowShared }] }
  return test "unique input is independent of the arrow result"
      (match resolveTelescope source #[unique] with
        | .ok result => result.valueAt typeSite == .unique && result.valueAt bodySite == .unique &&
          result.usesAt typeSite == .many &&
          (result.binders.find? (·.site == typeSite)).bind (·.result) == some .shared
        | .error _ => false) ++
    test "all 64 arrow contracts preserve input, result, and matching lambda fields"
      (modes.all fun uses => values.all fun value => values.all fun output =>
        match resolveTelescope source #[{ binder := .position 0, uses, value, result := some output }] with
        | .ok c => c.valueAt typeSite == value && c.valueAt bodySite == value &&
          c.usesAt typeSite == uses && c.usesAt bodySite == uses &&
          (c.binders.find? (·.site == typeSite)).bind (·.result) == some output
        | .error _ => false) ++
    test "type and body must agree on ownership"
      (expectError (ownershipMismatch.resolve source)
        (.inconsistentValue `identity 0 .unique .shared)) ++
    test "type and body must agree on locality"
      (expectError (localityMismatch.resolve source)
        (.inconsistentValue `identity 0 .localShared .shared)) ++
    test "borrow let retains its explicit kind and shared local view"
      (match borrow.resolve binding with
        | .ok c => c.binders[0]!.kind == .letE && c.binders[0]!.letKind == .borrowShared &&
          c.binders[0]!.value == .localShared && c.binders[0]!.result.isNone
        | .error _ => false) ++
    test "a shared borrow cannot manufacture unique ownership"
      (expectError (({ borrow with binders := borrow.binders.map fun (b : BinderContract) => { b with value := .localUnique } }).resolve binding)
        (.invalidBorrowView `binding bodySite)) ++
    test "a borrow flag cannot annotate a function binder"
      (expectError (resolveTelescope source #[{ unique with letKind := .borrowShared }])
        (.borrowOnNonLet `identity typeSite))

def markerTests : TestSeq := Id.run do
  let annotation : BinderAnnotation := {
    origin := 0, binder := `x, uses := .affine, value := .localUnique }
  let data := annotation.toMetadata
  let borrowed := Lean.markBorrowed natType
  let duplicate := { data with entries := (sourceAnnotationKey, .ofNat 1) :: data.entries }
  let missingVersion := ({} : Lean.MData).setNat `ix.source.binder.uses 1
  let marked := definition `marked
    (.forallE `x (.mdata data natType) natType .default)
    (.lam `x natType (.bvar 0) .default)
  let input := CompileInput.plain [(marked.name, marked)]
  let recursor : ConstantInfo := .recInfo {
    name := `markedRecursor, levelParams := [], type := .sort .zero
    all := [], numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0
    rules := [⟨`constructor, 0, .mdata missingVersion natType⟩]
    k := false, isUnsafe := false }
  let shared := (List.range 28).foldl (fun expr _ => Expr.app expr expr) natType
  return test "source annotation metadata roundtrips ownership, usage, locality, and origin"
      (match BinderAnnotation.ofMetadata? data with
        | .ok decoded => decoded == some annotation
        | .error _ => false) ++
    test "adding source markers preserves Lean's singleton native borrow wrapper"
      (match annotation.attach borrowed with
        | .ok type => Lean.isMarkedBorrowed type &&
          match binderAnnotation? type with
          | .ok decoded => decoded == some annotation
          | .error _ => false
        | .error _ => false) ++
    test "strict source metadata rejects unknown keys, duplicates, versions, and overflowing modes"
      ([data.setNat `ix.source.binder.future 0, duplicate, missingVersion,
        data.setNat sourceAnnotationKey 2, data.setNat `ix.source.binder.uses 256,
        data.setNat `ix.source.binder.owned 256].all fun malformed =>
          !(BinderAnnotation.ofMetadata? malformed).isOk) ++
    test "malformed reserved metadata is still detected by the preflight"
      (exprHasSourceAnnotations (.mdata missingVersion natType)) ++
    test "source markers in raw recursor rules are detected and explicitly unsupported"
      (sourceHasAnnotations recursor &&
        expectError (SourceContract.fromAnnotations recursor) (.annotatedRecursorRule recursor.name)) ++
    test "annotation scan handles heavily shared ordinary source and nearby markers"
      (!exprHasSourceAnnotations shared &&
        exprHasSourceAnnotations (.app shared (.mdata data natType))) ++
    test "source markers require explicit matching records and cannot be overridden"
      (expectError input.resolve (.missingContract marked.name) &&
        match SourceContract.fromAnnotations marked with
        | .ok contract =>
          let changed : SourceContract := { contract with
            binders := contract.binders.map fun binder => { binder with value := .shared } }
          contract.binders.size == 2 && (contract.resolve marked).isOk &&
          !(changed.resolve marked).isOk
        | .error _ => false)

def suite : List TestSeq :=
  [telescopeTests, occurrenceTests, rejectionTests, inputTests, valueContractTests, markerTests]

end Tests.Ix.SourceContract

end
