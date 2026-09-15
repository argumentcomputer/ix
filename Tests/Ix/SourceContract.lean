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
    Array (BinderSite × Ixon.Uses × Option Ixon.Owned) :=
  match actual with
  | .error _ => #[]
  | .ok contract => contract.binders.map fun binder => (binder.site, binder.uses, binder.resultOwned)

def telescopeTests : TestSeq :=
  test "identity resolves linear/unique type and linear body at independent sites"
    (resolvedModes (resolveTelescope (identity) #[{ binder := .position 0, uses := .linear, resultOwned := some .unique }]) ==
      #[(⟨.type, []⟩, .linear, some .unique), (⟨.body, []⟩, .linear, none)]) ++
  test "all four usage modes are accepted without inferring resource validity"
    ([Ixon.Uses.erased, .linear, .affine, .many].all fun uses =>
      (resolveTelescope (identity) #[{ binder := .position 0, uses, resultOwned := some .shared }]).isOk) ++
  test "ownership shorthand affects only the selected curried arrow"
    (resolvedModes (resolveTelescope curried #[{ binder := .name `y, uses := .linear, resultOwned := some .unique }]) ==
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
      (resolvedModes (resolveTelescope wrapped #[{ binder := .position 0, uses := .linear, resultOwned := some .unique }]) ==
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
      (expectError (({ source := identity, binders := #[{ site := bodySite, uses := .many, resultOwned := some .shared }] } : SourceContract).resolve identity)
        (.ownershipOnLambda `identity bodySite)) ++
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

def ownershipRegionTests : TestSeq := Id.run do
  let source := identity
  let typeSite : BinderSite := ⟨.type, []⟩
  let bodySite : BinderSite := ⟨.body, []⟩
  let unique : TelescopeContract := { binder := .position 0, uses := .many, owned := .unique }
  let regional (name : Name) : TelescopeContract :=
    { unique with uses := .affine, region := some name }
  let resolveRegion (names : Array Name) (name : Name) := do
    (← SourceContract.ofTelescope source #[regional name] names).resolve source
  let ownershipMismatch : SourceContract := {
    source, binders := #[{ site := typeSite, uses := .many, owned := .unique }] }
  let regionMismatch : SourceContract := {
    source, regions := #[`a],
    binders := #[{ site := typeSite, uses := .many, region := some `a }] }
  return test "unique binder ownership is independent of arrow-result ownership"
      (match resolveTelescope source #[unique] with
        | .ok result => result.ownedAt typeSite == .unique && result.ownedAt bodySite == .unique &&
          result.usesAt typeSite == .many &&
          (result.binders.find? (·.site == typeSite)).bind (·.resultOwned) == some .shared
        | .error _ => false) ++
    test "binder ownership composes with all four usages without claiming validity"
      ([Ixon.Uses.erased, .linear, .affine, .many].all fun uses =>
        (resolveTelescope source #[{ unique with uses }]).isOk) ++
    test "region parameters resolve to declaration-local indices on both roots"
      (match resolveRegion #[`b, `a] `a with
        | .ok result => result.regionAt typeSite == some 1 && result.regionAt bodySite == some 1 &&
          result.ownedAt bodySite == .unique && result.usesAt bodySite == .affine
        | .error _ => false) ++
    test "renaming a bound region preserves all resolved assertions"
      (match resolveRegion #[`a] `a, resolveRegion #[`renamed] `renamed with
        | .ok first, .ok second => first.semantics == second.semantics
        | _, _ => false) ++
    test "unbound region names are rejected"
      (expectError (resolveRegion #[`a] `missing) (.unknownRegion `identity `missing)) ++
    test "duplicate region parameters are rejected"
      (expectError (resolveRegion #[`a, `a] `a) (.duplicateRegion `identity `a)) ++
    test "type and body must agree on binder ownership"
      (expectError (ownershipMismatch.resolve source)
        (.inconsistentOwnership `identity 0 .unique .shared)) ++
    test "type and body must agree on the region bound"
      (expectError (regionMismatch.resolve source)
        (.inconsistentRegion `identity 0 (some 0) none))

def markerTests : TestSeq := Id.run do
  let annotation : BinderAnnotation := {
    origin := 0, binder := `x, uses := .affine, owned := .unique
    region := some `a, regions := #[`a] }
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
  return test "source annotation metadata roundtrips ownership, usage, region, and origin"
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
            binders := contract.binders.map fun binder => { binder with owned := .shared } }
          contract.binders.size == 2 && (contract.resolve marked).isOk &&
          !(changed.resolve marked).isOk
        | .error _ => false)

def suite : List TestSeq :=
  [telescopeTests, occurrenceTests, rejectionTests, inputTests, ownershipRegionTests, markerTests]

end Tests.Ix.SourceContract

end
