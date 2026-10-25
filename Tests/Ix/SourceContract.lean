module

public import Ix.Compile.SourceContract
public import Ix.Compile.SourceContract.Transport
public import Ix.CompileM
public import Ix.CanonM
public import Ix.LeanIngress.Expr
public import Ix.Compile.Image.Develop
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

def arityProducerTests : TestSeq := Id.run do
  let canonical := fun source => (Id.run ((_root_.Ix.CanonM.canonConst source).run {})).1
  let frame := fun (kind : _root_.Ix.SemanticContract.Kind) (e : _root_.Ix.Expr) => match e with
    | .mdata data _ _ => data.size == 3 && ((_root_.Ix.SemanticContract.read data).toOption).any (·.kind == kind)
    | _ => false
  let readable := fun e => (_root_.Ix.LeanIngress.ingressExpr (fun _ => 0) e).isOk
  let linear := resolveTelescope identity #[{ binder := .position 0, uses := .linear, result := some .unique }]
  let pair := linear.toOption.bind (fun c => c.decorate.toOption)
  let pairOK := pair.any fun out => match canonical out with
    | .defnInfo v => frame .all v.cnst.type && frame .lam v.value && readable v.cnst.type && readable v.value
    | _ => false
  let binding := definition `arityLet natType (.letE `view natType (.lit (.natVal 0)) (.bvar 0) false)
  let borrow : SourceContract := {
    source := binding
    binders := #[{ site := ⟨.body, []⟩, uses := .affine, value := .localShared, letKind := .borrowShared }] }
  let letOK := ((borrow.resolve binding).toOption.bind (fun c => c.decorate.toOption)).any fun out =>
    match canonical out with | .defnInfo v => frame .letE v.value && readable v.value | _ => false
  let theoremSource : ConstantInfo := .thmInfo {
    name := `arityTheorem, levelParams := [], type := .const `True [], value := .const `True.intro [], all := [`arityTheorem] }
  let opaqueSource : ConstantInfo := .opaqueInfo {
    name := `arityOpaque, levelParams := [], type := natType, value := .lit (.natVal 0), isUnsafe := false, all := [`arityOpaque] }
  let axiomSource : ConstantInfo := .axiomInfo {
    name := `arityAxiom, levelParams := [], type := natType, isUnsafe := false }
  let kinds := [(theoremSource, 0), (opaqueSource, 1), (axiomSource, 2)].all fun (source, expected) =>
    ((resolveTelescope source #[]).toOption.bind (fun c => c.decorate.toOption)).any fun out =>
      out.name == source.name && match canonical out, expected with
      | .thmInfo v, 0 => readable v.cnst.type && readable v.value
      | .opaqueInfo v, 1 => readable v.cnst.type && readable v.value
      | .axiomInfo v, 2 => readable v.cnst.type && (sourceBody? out).isNone
      | _, _ => false
  let body := (sourceBody? identity).getD natType
  let plain := ({} : MData).setNat `native.hint 7
  let marker := ({ origin := 0, binder := `x, uses := .linear, value := .shared } : BinderAnnotation).toMetadata
  let semantic : _root_.Ix.SemanticContract.Contract := { kind := .lam, binder := ⟨.linear, .shared⟩ }
  let metadata := (resolveTelescope identity #[]).toOption.any fun c =>
    let kept := (decorateExpr c .body [] (.mdata plain body)).toOption
    let stripped := (decorateExpr c .body [] (.mdata marker body)).toOption
    (match kept with | some (.mdata data inner) => data.entries == plain.entries && inner == body | _ => false) &&
    (match stripped with | some (.lam ..) => stripped == some body | _ => false) &&
    (match decorateExpr c .body [] (semantic.attach body) with
      | .error "source transport: reserved semantic metadata in unprocessed source" => true | _ => false)
  return test "actual decorator and CanonM keep distinct type/value semantic frames readable" pairOK ++
    test "actual borrow-let decoration has a readable three-field semantic frame" letOK ++
    test "actual theorem/opaque/axiom outputs preserve kind and optional-value boundaries" kinds ++
    test "decorator preserves plain metadata, removes source markers and refuses original semantic frames" metadata

-- Internal record-frame fixtures exercise the pure decorator, not public
-- compiler input admission or a designated baseline.
def recordSubstitutionTests : TestSeq := Id.run do
  let wrap := fun e => Expr.mdata (({} : MData).setNat `_ix.inline 0) e
  let source := definition `recordIdentity
    (.forallE `x natType (wrap natType) .default)
    (.lam `x natType (wrap (wrap (.bvar 0))) .default)
  let canonical := fun out => (Id.run ((_root_.Ix.CanonM.canonConst out).run {})).1
  let pair := (resolveTelescope source #[{ binder := .position 0, uses := .linear, result := some .unique }]).toOption
    |>.bind (fun c => c.decorate.toOption)
  let mut inputs : Array _root_.Ix.Expr := #[]
  if let some out := pair then
    if let .defnInfo v := canonical out then inputs := #[v.cnst.type, v.value]
  let binding := definition `recordLet natType (.letE `view natType (.lit (.natVal 0)) (wrap (.bvar 0)) false)
  let borrow : SourceContract := { source := binding, binders := #[
    { site := ⟨.body, []⟩, uses := .affine, value := .localShared, letKind := .borrowShared }] }
  if let some out := (borrow.resolve binding).toOption.bind (fun c => c.decorate.toOption) then
    if let .defnInfo v := canonical out then inputs := inputs.push v.value
  let records := ({} : Std.HashMap Nat (Nat × UInt64)).insert 0 (7, 9)
  let anchor := _root_.Ix.Expr.mkBVar 0
  let payloadSame := fun (a b : _root_.Ix.Expr) => match a, b with
    | .mdata data _ hash, .mdata other _ _ =>
      _root_.Ix.Compile.ExactKey.exprEq (.mdata data anchor hash) (.mdata other anchor hash)
    | _, _ => false
  let stable := inputs.all fun e =>
    let out := _root_.Ix.CompileM.substRecords records e
    let before := _root_.Ix.LeanIngress.ingressExpr (fun _ => 0) e
    let after := _root_.Ix.LeanIngress.ingressExpr (fun _ => 0) out
    before.isOk && before.toOption == after.toOption && payloadSame e out &&
      !_root_.Ix.Compile.ExactKey.exprEq e out
  return test "record substitution retains exact lam/all/let semantic arrays and successful readings"
      (inputs.size == 3 && stable) ++
    test "missing record entries retain actual decorated expressions exactly"
      (inputs.size == 3 && inputs.all fun e =>
        _root_.Ix.Compile.ExactKey.exprEq e (_root_.Ix.CompileM.substRecords {} e))

-- These open source expressions exercise raw rewrite helpers. Resolving their
-- contracts does not assert declaration admission or whole-program validity.
open _root_.Ix.Compile.Image in
def rewritePrimitiveTests : TestSeq := Id.run do
  let domain := Expr.sort (.param `u)
  let source := definition `rewriteOpen (.forallE `x domain (.bvar 1) .default)
    (.lam `x domain (.bvar 1) .default)
  let canonical := fun out => (Id.run ((_root_.Ix.CanonM.canonConst out).run {})).1
  let mut inputs : Array _root_.Ix.Expr := #[]
  let linear : TelescopeContract := { binder := .position 0, uses := .linear, result := some .unique }
  if let some out := (resolveTelescope source #[linear]).toOption.bind (fun c => c.decorate.toOption) then
    if let .defnInfo v := canonical out then inputs := #[v.cnst.type, v.value]
  let binding := definition `rewriteLet domain (.letE `view domain (.bvar 0) (.bvar 1) false)
  let borrow : SourceContract := { source := binding, binders := #[
    { site := ⟨.body, []⟩, uses := .affine, value := .localShared, letKind := .borrowShared }] }
  if let some out := (borrow.resolve binding).toOption.bind (fun c => c.decorate.toOption) then
    if let .defnInfo v := canonical out then inputs := inputs.push v.value
  let eq := _root_.Ix.Compile.ExactKey.exprEq
  let anchor := _root_.Ix.Expr.mkBVar 0
  let payloadSame := fun (a b : _root_.Ix.Expr) => match a, b with
    | .mdata data _ hash, .mdata other _ _ => data.size == 3 &&
      eq (.mdata data anchor hash) (.mdata other anchor hash)
    | _, _ => false
  let u := _root_.Ix.Name.fromLeanName `u
  let v := _root_.Ix.Name.fromLeanName `v
  let one := _root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero
  let domainIsOne := fun (e : _root_.Ix.Expr) => match e with
    | .mdata _ (.lam _ ty _ _ _) _ | .mdata _ (.forallE _ ty _ _ _) _ |
      .mdata _ (.letE _ ty _ _ _ _) _ => eq ty (_root_.Ix.Expr.mkSort one)
    | _ => false
  let shiftedBody := fun (e : _root_.Ix.Expr) => match e with
    | .mdata _ (.lam _ _ (.bvar 3 _) _ _) _ |
      .mdata _ (.forallE _ _ (.bvar 3 _) _ _) _ |
      .mdata _ (.letE _ _ (.bvar 2 _) (.bvar 3 _) _ _) _ => true
    | _ => false
  let shifts := inputs.map fun e => (liftM e 2 0).run {}
  let roundTrips := inputs.zip shifts |>.all fun (e, run) => match run with
    | .ok (lifted, after) => shiftedBody lifted && !eq e lifted && payloadSame e lifted &&
      ((lowerM lifted 2 0).run after).toOption.any (fun (out, _) => eq e out && payloadSame e out)
    | .error _ => false
  let warm := inputs.zip shifts |>.all fun (e, run) => match run with
    | .ok (lifted, after) => after.lifted.size > 0 &&
      ((liftM e 2 0).run after).toOption.any fun (again, state) => eq lifted again &&
        state.lifted.size == after.lifted.size && state.range.size == after.range.size &&
        state.nodes.size == after.nodes.size &&
        ((lowerM lifted 2 0).run after).toOption.any fun (lowered, afterLower) =>
          afterLower.lowered.size > 0 && eq lowered e &&
          ((lowerM lifted 2 0).run afterLower).toOption.any fun (again, state) =>
            eq lowered again && state.lowered.size == afterLower.lowered.size &&
            state.range.size == afterLower.range.size && state.nodes.size == afterLower.nodes.size
    | .error _ => false
  let zero := _root_.Ix.Expr.mkBVar 0
  let alias : _root_.Ix.Expr := .bvar 1 zero.getHash
  let liftCollision := ((liftM zero 2 0).run {}).toOption.any fun (first, state) =>
    ((liftM alias 2 0).run state).toOption.any fun (second, _) =>
      eq first (_root_.Ix.Expr.mkBVar 2) && eq second (_root_.Ix.Expr.mkBVar 3)
  let three : _root_.Ix.Expr := .bvar 3 zero.getHash
  let four : _root_.Ix.Expr := .bvar 4 zero.getHash
  let lowerCollision := ((lowerM three 2 0).run {}).toOption.any fun (first, state) =>
    ((lowerM four 2 0).run state).toOption.any fun (second, _) =>
      eq first (_root_.Ix.Expr.mkBVar 1) && eq second (_root_.Ix.Expr.mkBVar 2)
  let seeded : DevState := { nodes := ({} : TotalMemo.Nodes).insert (hash zero) zero }
  let ty := _root_.Ix.Expr.mkSort _root_.Ix.Level.mkZero
  let lam := fun body => _root_.Ix.Expr.mkLam _root_.Ix.Name.mkAnon ty body .default
  let ident := lam zero
  let value := _root_.Ix.Expr.mkLit (.natVal 7)
  let eta := lam (lam (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkBVar 1) zero))
  let projection := lam (_root_.Ix.Expr.mkProj _root_.Ix.Compile.LibraryNames.nPProd 0 zero)
  let pair := fun e => Canon.mkAppN
    (_root_.Ix.Expr.mkConst _root_.Ix.Compile.LibraryNames.nPProdMk #[one, one]) #[ty, ty, e, value]
  let develops := fun f args expected => (instantiateWith {} f args).toOption.any fun (out, _) => eq out expected
  let history := inputs.all fun e => (instantiateWith {} ident #[e]).toOption.any fun (out, after) =>
    eq e out && payloadSame e out && after.insts.size > 0 &&
    (instProbe after e zero 0).any (fun r => eq r.1 e && r.2 == .direct) &&
    (instantiateWith after ident #[e]).toOption.any fun (again, next) =>
      eq out again && next.insts.size == after.insts.size
  let instCollision := ((hinst 8 value 0 zero).run {}).toOption.any fun (first, after) =>
    ((hinst 8 value 0 alias).run after).toOption.any fun (second, _) =>
      eq first.1 value && first.2 == .direct && eq second.1 zero && second.2 == .no
  -- This forged state is not an executed history from{}. Matching exact
  -- keys alone does not certify its deliberately malformed retained result.
  let badData := #[(_root_.Ix.Name.fromLeanName `ix.contract, _root_.Ix.DataValue.ofNat 3)]
  let bad := _root_.Ix.Expr.mkMData badData zero
  let poisoned : DevState := {
    insts := ({} : Std.HashMap UInt64 InstEntry).insert (instBucket value zero 0)
      ⟨value, zero, 0, (bad, .direct)⟩ }
  return test "rewrite universe substitution retains exact lam/all/let frames and changes their domains"
      (inputs.size == 3 && inputs.all fun e =>
        let out := Canon.substLevels #[u] #[one] e
        domainIsOne out && !eq e out && payloadSame e out) ++
    test "rewrite universe substitution preserves empty and unequal-array branches"
      (inputs.size == 3 && inputs.all fun e =>
        eq e (Canon.substLevels #[] #[one] e) && eq e (Canon.substLevels #[u] #[] e) &&
        eq e (Canon.substLevels #[v, u] #[one] e) &&
        domainIsOne (Canon.substLevels #[u] #[one, _root_.Ix.Level.mkZero] e)) ++
    test "actual lift/lower changes open variables and roundtrips exact semantic frames"
      (inputs.size == 3 && roundTrips) ++
    test "actual warm lift/lower caches retain exact outputs and table sizes" (inputs.size == 3 && warm) ++
    test "actual zero-shift and range fast paths retain decorated inputs"
      (inputs.size == 3 && inputs.all fun e => [liftM e 0 0, lowerM e 0 0,
        liftM e 2 4, lowerM e 2 4].all fun action =>
          (action.run {}).toOption.any fun (out, _) => eq e out && payloadSame e out) ++
    test "actual lift cache rejects a distinct raw input with the same digest"
      (hash zero == hash alias && !eq zero alias && liftCollision) ++
    test "actual lower cache rejects a distinct raw input with the same digest"
      (hash three == hash four && !eq three four && lowerCollision) ++
    test "actual sharing confirms equal nodes, rejects raw digest aliases and fills empty tables"
      ([zero, alias].all fun e => [share e, shareInput e].all fun action =>
        [seeded, {}].all fun state => (action.run state).toOption.any fun (out, _) => eq e out) ++
    test "actual cold/warm instantiateWith histories retain decorated results and exact hits"
      (inputs.size == 3 && history) ++
    test "actual hinst rebuilds semantic lam/all/let frames around changed children"
      (inputs.size == 3 && inputs.all fun e => ((hinst 16 value 0 e).run {}).toOption.any
        fun (r, _) => !eq e r.1 && payloadSame e r.1) ++
    test "actual hereditary beta contracts the substituted function"
      (develops (lam (_root_.Ix.Expr.mkApp zero value)) #[ident] value) ++
    test "actual eta and constructor projection return the selected decorated expressions"
      (inputs.size == 3 && inputs.all fun e => develops eta #[e] e && develops projection #[pair e] e) ++
    test "actual hinst rejects different retained inputs at the same bucket"
      (instBucket value zero 0 == instBucket value alias 0 && !eq zero alias && instCollision) ++
    test "actual zero-fuel errors precede even a matching forged cache hit"
      ((match (hinst 0 value 0 zero).run poisoned with | .error msg => msg == developExhausted | _ => false) &&
        (match (happ 0 ident [value]).run poisoned with | .error msg => msg == developExhausted | _ => false)) ++
    test "an arbitrary exact-key cache can return malformed frames and is outside the history contract"
      (!(_root_.Ix.SemanticContract.read badData).isOk &&
        (instProbe poisoned value zero 0).any (fun r => eq r.1 bad) &&
        (instantiateWith poisoned ident #[value]).toOption.any fun (out, _) => eq out bad)

def inspectionTests : TestSeq := Id.run do
  let digest := fun (n : UInt8) => Address.mk (ByteArray.mk (Array.replicate 32 n))
  let scalar := _root_.Ix.Expr.lit (.natVal 0) (digest 3)
  let lam := _root_.Ix.Expr.lam _root_.Ix.Name.mkAnon scalar
    (.bvar 0 (digest 4)) .default (digest 2)
  let contract : _root_.Ix.SemanticContract.Contract := { kind := .lam, binder := ⟨.linear, .shared⟩ }
  let data := contract.ixMetadata
  let frame := fun md => _root_.Ix.Expr.mdata md lam (digest 0)
  let good := frame data
  let codeKey := data[2]!.1
  let unknown := match codeKey with
    | .str parent _ hash => _root_.Ix.Name.str parent "unknown" hash | _ => codeKey
  let malformed := "malformed semantic contract frame"
  let misplaced := "semantic contract is not attached to its original binder"
  let cases := #[
    ("malformed payload", data.pop, malformed),
    ("valid-size wrong-kind payload", { contract with kind := .all }.ixMetadata, misplaced),
    ("nonnatural field", data.set! 2 (codeKey, .ofBool true), "semantic contract fields must be natural numbers"),
    ("reserved bits", data.set! 2 (codeKey, .ofNat 16), "reserved semantic contract bits"),
    ("aliased metadata-key hash", data.set! 2 (unknown, .ofNat 1), "unknown or duplicate semantic contract field")]
  let inspect := _root_.Ix.SemanticContract.inspect
  let eq := _root_.Ix.Compile.ExactKey.exprEq
  let mut tests := TestSeq.done
  for (label, md, message) in cases do
    let bad := frame md
    let refused := [bad, .app bad good (digest 1), .app good bad (digest 1)].all fun e =>
      match inspect e with | .error actual => actual == message | _ => false
    tests := tests ++ test s!"exact inspection rejects {label} despite equal digests in either visitation order"
      (bad.getHash == good.getHash && !eq bad good && refused)
  let twin := _root_.Ix.Expr.mdata contract.ixMetadata
    (.lam _root_.Ix.Name.mkAnon scalar (.bvar 0 (digest 4)) .default (digest 2)) (digest 0)
  let plain := _root_.Ix.Expr.mdata #[(_root_.Ix.Name.fromLeanName `native.hint, .ofNat 7)] lam (digest 0)
  return tests ++ test "exact inspection accepts plain, equal and shared valid nodes"
    ((inspect scalar).toOption == some false && (inspect plain).toOption == some false && eq good twin &&
      (inspect (.app good good (digest 1))).toOption == some true &&
      (inspect (.app good twin (digest 1))).toOption == some true)

def suite : List TestSeq :=
  [telescopeTests, occurrenceTests, rejectionTests, inputTests, valueContractTests, markerTests,
    arityProducerTests, recordSubstitutionTests, rewritePrimitiveTests, inspectionTests]

end Tests.Ix.SourceContract

end
