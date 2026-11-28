module

public import Ix.Compile.SourceContract
public import Ix.Compile.SourceContract.Transport
public import Ix.CompileM
public import Ix.CanonM
public import Ix.LeanIngress.Expr
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
    Array (BinderSite × Ixon.BinderMode × Option Ixon.ResultMode) :=
  match actual with
  | .error _ => #[]
  | .ok contract => contract.binders.map fun binder => (binder.site, binder.mode, binder.result)

def telescopeTests : TestSeq :=
  test "identity resolves once/unique type and once body at independent sites"
    (resolvedModes (resolveTelescope (identity) #[{ binder := .position 0, mode := .once, result := some .unique }]) ==
      #[(⟨.type, []⟩, .once, some .unique), (⟨.body, []⟩, .once, none)]) ++
  test "all seven binder modes are accepted without inferring resource validity"
    ([Ixon.BinderMode.many, .borrowed, .unique, .uniqueBorrowed, .once, .onceBorrowed, .erased].all fun mode =>
      (resolveTelescope (identity) #[{ binder := .position 0, mode, result := some .shared }]).isOk) ++
  test "result mode shorthand affects only the selected curried arrow"
    (resolvedModes (resolveTelescope curried #[{ binder := .name `y, mode := .once, result := some .unique }]) ==
      #[(⟨.type, [.binderBody]⟩, .once, some .unique),
        (⟨.body, [.binderBody]⟩, .once, none)]) ++
  test "implicit argument retains its position and does not imply erasure"
    (match resolveTelescope curried #[{ binder := .position 0, mode := .many }] with
      | .ok result => result.binders.all fun binder =>
        binder.binderInfo == .implicit && binder.mode == .many
      | .error _ => false) ++
  test "out-of-range elaborated positions are rejected"
    (expectError (resolveTelescope curried #[{ binder := .position 2, mode := .once }])
      (.argumentOutOfRange `curried 2)) ++
  test "missing binder names are rejected"
    (expectError (resolveTelescope curried #[{ binder := .name `missing, mode := .once }])
      (.unknownBinder `curried `missing)) ++
  test "name and position annotations cannot silently overwrite the same site"
    (expectError (resolveTelescope curried #[{ binder := .name `y, mode := .once },
      { binder := .position 1, mode := .borrowed }])
      (.duplicateSite `curried ⟨.type, [.binderBody]⟩))

def occurrenceTests : TestSeq := Id.run do
  let lam := Expr.lam `shadow natType (.bvar 0) .default
  let nested := definition `nested (.forallE `x natType natType .default)
    (.lam `x natType (.app lam (.app lam (.bvar 0))) .default)
  let left : BinderSite := ⟨.body, [.binderBody, .appFn]⟩
  let right : BinderSite := ⟨.body, [.binderBody, .appArg, .appFn]⟩
  let distinct : SourceContract := {
    source := nested
    binders := #[{ site := left, mode := .once }, { site := right, mode := .borrowed }] }
  let shadowed := definition `shadowed
    (.forallE `x natType (.forallE `x natType natType .default) .default)
    (.lam `x natType (.lam `x natType (.bvar 0) .default) .default)
  let wrapped := definition `wrapped
    (.mdata {} (.forallE `x natType natType .default))
    (.mdata {} (.lam `x natType (.bvar 0) .default))
  return test "equal nested lambdas can carry different occurrence contracts"
      (resolvedModes (distinct.resolve nested) == #[(left, .once, none), (right, .borrowed, none)]) ++
    test "annotation order has a canonical resolved order"
      (resolvedModes (({ distinct with binders := distinct.binders.reverse }).resolve nested) ==
        resolvedModes (distinct.resolve nested)) ++
    test "shadowed declaration binders require an explicit position"
      (expectError (resolveTelescope shadowed #[{ binder := .name `x, mode := .once }])
        (.ambiguousBinder `shadowed `x)) ++
    test "position disambiguates shadowed declaration binders"
      ((resolveTelescope shadowed #[{ binder := .position 1, mode := .once }]).isOk) ++
    test "metadata wrappers appear in resolved telescope paths"
      (resolvedModes (resolveTelescope wrapped #[{ binder := .position 0, mode := .once, result := some .unique }]) ==
        #[(⟨.type, [.metadata]⟩, .once, some .unique),
          (⟨.body, [.metadata]⟩, .once, none)]) ++
    test "invalid structural edges fail before canonicalization"
      (expectError (({ source := identity, binders := #[{ site := ⟨.body, [.appArg]⟩, mode := .once }] } : SourceContract).resolve identity)
        (.invalidSite `identity ⟨.body, [.appArg]⟩)) ++
    test "an expression occurrence must actually be a binder"
      (expectError (({ source := identity, binders := #[{ site := ⟨.body, [.binderBody]⟩, mode := .once }] } : SourceContract).resolve identity)
        (.expectedBinder `identity ⟨.body, [.binderBody]⟩))

def rejectionTests : TestSeq := Id.run do
  let bodySite : BinderSite := ⟨.body, []⟩
  let typeSite : BinderSite := ⟨.type, []⟩
  let contract : SourceContract := {
    source := identity
    binders := #[{ site := typeSite, mode := .once }, { site := bodySite, mode := .once }] }
  let renamed := definition `identity (.forallE `renamed natType natType .default)
    (.lam `renamed natType (.bvar 0) .default)
  let changedInfo := definition `identity (.forallE `x natType natType .implicit)
    (.lam `x natType (.bvar 0) .implicit)
  let changedMetadata := definition `identity (.forallE `x natType natType .default)
    (.mdata {} (.lam `x natType (.bvar 0) .default))
  let alias := definition `alias (.forallE `x natType natType .default) (.const `identity [])
  return test "type/body mode disagreement is rejected"
      (expectError (({ source := identity, binders := #[{ site := typeSite, mode := .once }] } : SourceContract).resolve identity)
        (.inconsistentTelescope `identity 0 .once .many)) ++
    test "a lambda has no independent result-mode field"
      (expectError (({ source := identity, binders := #[{ site := bodySite, mode := .many, result := some .shared }] } : SourceContract).resolve identity)
        (.resultOnNonArrow `identity bodySite)) ++
    test "source binder spelling is part of the occurrence fingerprint"
      (expectError (contract.resolve renamed) (.staleSource `identity)) ++
    test "source BinderInfo drift invalidates a previously resolved contract"
      (expectError (contract.resolve changedInfo) (.staleSource `identity)) ++
    test "source metadata shape drift invalidates structural paths"
      (expectError (contract.resolve changedMetadata) (.staleSource `identity)) ++
    test "unsupported body telescope normalization gets a diagnostic"
      (expectError (resolveTelescope alias #[{ binder := .position 0, mode := .once }])
        (.missingBodyBinder `alias 0))

def inputTests : TestSeq := Id.run do
  let source := identity
  let constants := [(source.name, source)]
  let first : SourceContract := {
    source
    binders := #[{ site := ⟨.type, []⟩, mode := .once }, { site := ⟨.body, []⟩, mode := .once }] }
  let second := identity `second
  let secondContract : SourceContract :=
    { source := second
      binders := #[{ site := ⟨.type, []⟩, mode := .borrowed }, { site := ⟨.body, []⟩, mode := .borrowed }] }
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
          result.contracts[0]!.modeAt ⟨.body, []⟩ == .once &&
          result.contracts[1]!.modeAt ⟨.body, []⟩ == .borrowed
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

def modeBijectionTests : TestSeq := Id.run do
  let source := identity
  let typeSite : BinderSite := ⟨.type, []⟩
  let bodySite : BinderSite := ⟨.body, []⟩
  let unique : TelescopeContract := { binder := .position 0, mode := .unique }
  let ownershipMismatch : SourceContract := {
    source, binders := #[{ site := typeSite, mode := .unique }] }
  let localityMismatch : SourceContract := {
    source, binders := #[{ site := typeSite, mode := .borrowed }] }
  let binderModes : List Ixon.BinderMode := [.many, .borrowed, .unique, .uniqueBorrowed, .once, .onceBorrowed, .erased]
  let resultModes : List Ixon.ResultMode := [.shared, .borrowed, .unique, .uniqueBorrowed]
  let binding := definition `binding natType (.letE `view natType (.const `owner []) (.bvar 0) false)
  let borrow : SourceContract := {
    source := binding
    binders := #[{ site := bodySite, mode := .borrowed, isBorrow := true }] }
  let ctor : ConstantInfo := .ctorInfo {
    name := `MyBox.mk, levelParams := []
    type := .forallE `a natType (.forallE `b natType (.const `MyBox []) .default) .default
    induct := `MyBox, cidx := 0, numParams := 0, numFields := 2, isUnsafe := false }
  let ctorShared : SourceContract := {
    source := ctor
    binders := #[{ site := ⟨.type, [.binderBody]⟩, mode := .erased }]
    fieldModes := #[{ fieldIndex := 0, mode := .shared }] }
  let ctorConflict : SourceContract := {
    source := ctor
    binders := #[{ site := ⟨.type, []⟩, mode := .erased }]
    fieldModes := #[{ fieldIndex := 0, mode := .shared }] }
  return test "unique input is independent of the arrow result"
      (match resolveTelescope source #[unique] with
        | .ok result => result.modeAt typeSite == .unique && result.modeAt bodySite == .unique &&
          result.resultAt typeSite == .shared
        | .error _ => false) ++
    test "all 28 AllMode combinations preserve input, result, and matching lambda fields"
      (binderModes.all fun mode => resultModes.all fun output =>
        match resolveTelescope source #[{ binder := .position 0, mode, result := some output }] with
        | .ok c => c.modeAt typeSite == mode && c.modeAt bodySite == mode &&
          c.resultAt typeSite == output
        | .error _ => false) ++
    test "type and body must agree on unique mode"
      (expectError (ownershipMismatch.resolve source)
        (.inconsistentTelescope `identity 0 .unique .many)) ++
    test "type and body must agree on borrowed mode"
      (expectError (localityMismatch.resolve source)
        (.inconsistentTelescope `identity 0 .borrowed .many)) ++
    test "borrow let retains its explicit borrow flag and borrowed mode"
      (match borrow.resolve binding with
        | .ok c => c.binders[0]!.kind == .letE && c.binders[0]!.isBorrow &&
          c.binders[0]!.mode == .borrowed && c.binders[0]!.result.isNone
        | .error _ => false) ++
    test "a shared borrow cannot manufacture unique ownership"
      (expectError (({ borrow with binders := borrow.binders.map fun (b : BinderContract) => { b with mode := .uniqueBorrowed } }).resolve binding)
        (.invalidBorrowView `binding bodySite)) ++
    test "a borrow flag cannot annotate a function binder"
      (expectError (resolveTelescope source #[{ unique with mode := .borrowed, isBorrow := true }])
        (.borrowOnNonLet `identity typeSite)) ++
    test "constructor fieldModes and erased field resolve cleanly and reject @erased + @shared conflict"
      (match ctorShared.resolve ctor with
        | .ok r => r.fieldModeAt 0 == .shared && r.fieldModeAt 1 == .inherited &&
          r.modeAt ⟨.type, [.binderBody]⟩ == .erased
        | .error _ => false) ++
    test "constructor rejects field that is both @erased and @shared"
      (expectError (ctorConflict.resolve ctor) (.erasedSharedField `MyBox.mk 0)) ++
    test "fieldMode on non-constructor is rejected"
      (expectError (({ source, fieldModes := #[{ fieldIndex := 0, mode := .shared }] } : SourceContract).resolve source)
        (.fieldModeOnNonCtor `identity))

def markerTests : TestSeq := Id.run do
  let annotation : BinderAnnotation := {
    origin := 0, binder := `x, mode := .uniqueBorrowed }
  let data := annotation.toMetadata
  let borrowed := Lean.markBorrowed natType
  let duplicate := { data with entries := (sourceAnnotationKey, .ofNat 4) :: data.entries }
  let missingVersion := ({} : Lean.MData).setNat `ix.source.binder.mode 1
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
  return test "source annotation metadata roundtrips v5 BinderMode, ResultMode, borrow flag, and origin"
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
    test "strict source metadata rejects unknown keys, duplicates, old versions, and overflowing codes"
      ([data.setNat `ix.source.binder.future 0, duplicate, missingVersion,
        data.setNat sourceAnnotationKey 3, data.setNat `ix.source.binder.mode 7,
        data.setNat `ix.source.binder.mode 256, data.setNat `ix.source.binder.borrow 2].all fun malformed =>
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
            binders := contract.binders.map fun binder => { binder with mode := .many } }
          contract.binders.size == 2 && (contract.resolve marked).isOk &&
          !(changed.resolve marked).isOk
        | .error _ => false)

def arityProducerTests : TestSeq := Id.run do
  let canonical := fun source => (Id.run ((_root_.Ix.CanonM.canonConst source).run {})).1
  let frame := fun (kind : _root_.Ix.SemanticContract.Kind) (e : _root_.Ix.Expr) => match e with
    | .mdata data _ _ => data.size == 3 && ((_root_.Ix.SemanticContract.read data).toOption).any (·.kind == kind)
    | _ => false
  let readable := fun e => (_root_.Ix.LeanIngress.ingressExpr (fun _ => 0) e).isOk
  let once := resolveTelescope identity #[{ binder := .position 0, mode := .once, result := some .unique }]
  let pair := once.toOption.bind (fun c => c.decorate.toOption)
  let pairOK := pair.any fun out => match canonical out with
    | .defnInfo v => frame .all v.cnst.type && frame .lam v.value && readable v.cnst.type && readable v.value
    | _ => false
  let binding := definition `arityLet natType (.letE `view natType (.lit (.natVal 0)) (.bvar 0) false)
  let borrow : SourceContract := {
    source := binding
    binders := #[{ site := ⟨.body, []⟩, mode := .borrowed, isBorrow := true }] }
  let letOK := ((borrow.resolve binding).toOption.bind (fun c => c.decorate.toOption)).any fun out =>
    match canonical out with | .defnInfo v => frame .letE v.value && readable v.value | _ => false
  -- DefAsserts decoration & extraction
  let assertsContract : SourceContract := {
    source := identity
    defAsserts := { alloc := .noAlloc, boundedStack := true } }
  let assertsOK := ((assertsContract.resolve identity).toOption.bind (fun c => c.decorate.toOption)).any fun out =>
    match canonical out with
    | .defnInfo v =>
      frame .defAsserts v.cnst.type && readable v.cnst.type &&
      _root_.Ix.SemanticContract.defAsserts .defn v.cnst.type == { alloc := .noAlloc, boundedStack := true } &&
      _root_.Ix.SemanticContract.defAsserts .thm v.cnst.type == {}
    | _ => false
  -- Constructor FieldMode decoration & extraction
  let ctor : ConstantInfo := .ctorInfo {
    name := `ArityBox.mk, levelParams := []
    type := .forallE `a natType (.forallE `b natType (.const `ArityBox []) .default) .default
    induct := `ArityBox, cidx := 0, numParams := 0, numFields := 2, isUnsafe := false }
  let ctorContract : SourceContract := {
    source := ctor
    fieldModes := #[{ fieldIndex := 1, mode := .shared }] }
  let ctorOK := ((ctorContract.resolve ctor).toOption.bind (fun c => c.decorate.toOption)).any fun out =>
    match canonical out with
    | .ctorInfo v =>
      readable v.cnst.type &&
      (_root_.Ix.SemanticContract.ctorFieldModes v.numParams v.numFields.toUInt64 v.cnst.type).toArray ==
        #[.inherited, .shared]
    | _ => false
  let thmId : ConstantInfo := .thmInfo {
    name := `arityThmId, levelParams := []
    type := .forallE `p (.sort .zero) (.bvar 0) .default
    value := .lam `p (.sort .zero) (.bvar 0) .default
    all := [`arityThmId] }
  let thmStripped := ((resolveTelescope thmId #[{ binder := .position 0, mode := .erased }]).toOption.bind
    (fun c => c.decorate.toOption)).any fun out =>
      !exprHasSemanticContracts out.type && match out with
        | .thmInfo v => !exprHasSemanticContracts v.value
        | _ => false
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
  let marker := ({ origin := 0, binder := `x, mode := .once } : BinderAnnotation).toMetadata
  let semantic : _root_.Ix.SemanticContract.Contract := .lam .once
  let metadata := (resolveTelescope identity #[]).toOption.any fun c =>
    let kept := (decorateExpr c .body [] (.mdata plain body)).toOption
    let stripped := (decorateExpr c .body [] (.mdata marker body)).toOption
    (match kept with | some (.mdata data inner) => data.entries == plain.entries && inner == body | _ => false) &&
    (match stripped with | some (.lam ..) => stripped == some body | _ => false) &&
    (match decorateExpr c .body [] (semantic.attach body) with
      | .error "source transport: reserved semantic metadata in unprocessed source" => true | _ => false)
  return test "actual decorator and CanonM keep distinct type/value semantic frames and ingress accepts valid modes"
      (pairOK && thmStripped) ++
    test "actual borrow-let decoration has a three-field semantic frame accepted by the ingress" letOK ++
    test "DefAsserts and constructor FieldMode decoration roundtrip cleanly through CanonM and ingress"
      (assertsOK && ctorOK) ++
    test "actual theorem/opaque/axiom outputs preserve kind and optional-value boundaries" kinds ++
    test "decorator preserves plain metadata, removes source markers and refuses original semantic frames" metadata

def inspectionTests : TestSeq := Id.run do
  let digest := fun (n : UInt8) => Address.mk (ByteArray.mk (Array.replicate 32 n))
  let scalar := _root_.Ix.Expr.lit (.natVal 0) (digest 3)
  let lam := _root_.Ix.Expr.lam _root_.Ix.Name.mkAnon scalar
    (.bvar 0 (digest 4)) .default (digest 2)
  let contract : _root_.Ix.SemanticContract.Contract := .lam .once
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
    ("valid-size wrong-kind payload", (_root_.Ix.SemanticContract.Contract.all { input := .once }).ixMetadata, misplaced),
    ("nonnatural field", data.set! 2 (codeKey, .ofBool true), "semantic contract fields must be natural numbers"),
    ("reserved bits", data.set! 2 (codeKey, .ofNat 7), "reserved semantic contract bits"),
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

def presenceMemoTests : TestSeq := Id.run do
  let plain := Expr.lit (.natVal 0)
  let binder := Expr.lam `x natType (.bvar 0) .default
  let contract : _root_.Ix.SemanticContract.Contract := .lam .once
  let marked := contract.attach binder
  let hinted := Expr.mdata (({} : MData).setNat `native.hint 7) binder
  let bucket := fun (_ : Expr) => (0 : USize)
  let mut memo : SemanticPresence.Memo := {}
  let mut valid := true
  for e in [plain, marked, hinted, plain, marked, marked] do
    let (result, after) := Id.run ((SemanticPresence.go bucket e).run memo)
    valid := valid && result.1 == SemanticPresence.spec e
    memo := after
  let seeded : SemanticPresence.Memo := ({} : SemanticPresence.Memo).insert 0
    ⟨plain, SemanticPresence.spec plain, rfl⟩
  return test "presence memo preserves real results through constant-bucket collisions, overwrites and warm hits" valid ++
    test "presence memo confirms retained source and computes both positive and negative answers"
      ((SemanticPresence.probe seeded 0 marked).isNone &&
        SemanticPresence.runWith bucket marked && !SemanticPresence.runWith bucket hinted)

def suite : List TestSeq :=
  [telescopeTests, occurrenceTests, rejectionTests, inputTests, modeBijectionTests, markerTests,
    arityProducerTests, inspectionTests, presenceMemoTests]

end Tests.Ix.SourceContract

end
