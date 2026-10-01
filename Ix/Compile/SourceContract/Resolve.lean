module

public import Ix.Compile.SourceContract.Marker

public section

namespace Ix.Compile

/-- Unlike ConstantInfo.value?'s default, include opaque declaration bodies. -/
def sourceBody? : Lean.ConstantInfo → Option Lean.Expr
  | .defnInfo info => some info.value
  | .thmInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

def sourceRoot? (source : Lean.ConstantInfo) : SourceRoot → Option Lean.Expr
  | .type => some source.type
  | .body => sourceBody? source

def sourceHasAnnotations (source : Lean.ConstantInfo) : Bool :=
  exprHasSourceAnnotations source.type ||
    ((sourceBody? source).map exprHasSourceAnnotations).getD false ||
    match source with
    | .recInfo info => info.rules.any (exprHasSourceAnnotations ·.rhs)
    | _ => false

def sourceChild? : Lean.Expr → SourceStep → Option Lean.Expr
  | .app fn _, .appFn => some fn
  | .app _ arg, .appArg => some arg
  | .lam _ type _ _, .binderType | .forallE _ type _ _, .binderType => some type
  | .lam _ _ body _, .binderBody | .forallE _ _ body _, .binderBody => some body
  | .letE _ type _ _ _, .letType => some type
  | .letE _ _ value _ _, .letValue => some value
  | .letE _ _ _ body _, .letBody => some body
  | .mdata _ inner, .metadata => some inner
  | .proj _ _ value, .projection => some value
  | _, _ => none

@[expose] def sourceAtPath? (expr : Lean.Expr) : List SourceStep → Option Lean.Expr
  | [] => some expr
  | step :: rest => do sourceAtPath? (← sourceChild? expr step) rest

def sourceAtSite? (source : Lean.ConstantInfo) (site : BinderSite) : Option Lean.Expr := do
  sourceAtPath? (← sourceRoot? source site.root) site.path

@[simp] theorem sourceAtPath?_nil (expr : Lean.Expr) :
    sourceAtPath? expr [] = some expr := rfl

/-- Only metadata is transparent to telescope selection. No beta/let reduction,
typeclass inference, or source telescope permutation happens at this boundary. -/
def telescopePaths (kind : SourceBinderKind) (expr : Lean.Expr)
    (path : List SourceStep := []) : List (List SourceStep × Lean.Name) :=
  match expr with
  | .mdata _ inner => telescopePaths kind inner (path ++ [.metadata])
  | .lam name _ body _ =>
    if kind == .lam then
      (path, name) :: telescopePaths kind body (path ++ [.binderBody])
    else []
  | .forallE name _ body _ =>
    if kind == .all then
      (path, name) :: telescopePaths kind body (path ++ [.binderBody])
    else []
  | _ => []

def sourceTelescope (source : Lean.ConstantInfo) (root : SourceRoot) :
    Array (BinderSite × Lean.Name) :=
  match sourceRoot? source root with
  | none => #[]
  | some expr =>
    let kind := match root with | .type => .all | .body => .lam
    ((telescopePaths kind expr).map fun (path, name) => (⟨root, path⟩, name)).toArray

def resolveBinderSelector (source : Lean.ConstantInfo) (selector : BinderSelector) :
    Except SourceContractError Nat := do
  let telescope := sourceTelescope source .type
  match selector with
  | .position index =>
    if index < telescope.size then return index
    throw (.argumentOutOfRange source.name index)
  | .name name =>
    let indices := (List.range telescope.size).filter fun i => telescope[i]!.2 == name
    match indices with
    | [] => throw (.unknownBinder source.name name)
    | [index] => return index
    | _ => throw (.ambiguousBinder source.name name)

/-- Expand declaration shorthand into separate type/body occurrences. The
result never marks earlier or later curried arrow results unique implicitly. -/
def SourceContract.ofTelescope (source : Lean.ConstantInfo)
    (contracts : Array TelescopeContract) :
    Except SourceContractError SourceContract := do
  let types := sourceTelescope source .type
  let bodies := sourceTelescope source .body
  let mut binders := #[]
  for contract in contracts do
    let index ← resolveBinderSelector source contract.binder
    let some (typeSite, _) := types[index]?
      | throw (.argumentOutOfRange source.name index)
    binders := binders.push {
      site := typeSite, uses := contract.uses, result := contract.result
      value := contract.value, letKind := contract.letKind }
    if (sourceBody? source).isSome then
      let some (bodySite, _) := bodies[index]?
        | throw (.missingBodyBinder source.name index)
      binders := binders.push {
        site := bodySite, uses := contract.uses, value := contract.value, letKind := contract.letKind }
  return { source, binders }

def resolveBinderContract (source : Lean.ConstantInfo) (contract : BinderContract) :
    Except SourceContractError ResolvedBinderContract := do
  let some expr := sourceAtSite? source contract.site
    | throw (.invalidSite source.name contract.site)
  let (kind, name, binderInfo) ← match expr with
    | .lam name _ _ info => pure (SourceBinderKind.lam, name, info)
    | .forallE name _ _ info => pure (SourceBinderKind.all, name, info)
    | .letE name _ _ _ _ => pure (SourceBinderKind.letE, name, Lean.BinderInfo.default)
    | _ => throw (.expectedBinder source.name contract.site)
  if kind != .all && contract.result.isSome then
    throw (.resultOnNonArrow source.name contract.site)
  if kind != .letE && contract.letKind != .value then
    throw (.borrowOnNonLet source.name contract.site)
  if contract.letKind == .borrowShared && contract.value != .localShared then
    throw (.invalidBorrowView source.name contract.site)
  return {
    site := contract.site, kind, name, binderInfo
    uses := contract.uses, value := contract.value, letKind := contract.letKind
    result := if kind == .all then some (contract.result.getD .shared) else none }

def ResolvedSourceContract.usesAt (contract : ResolvedSourceContract)
    (site : BinderSite) : Ixon.Uses :=
  ((contract.binders.find? fun binder => binder.site == site).map (·.uses)).getD .many

def ResolvedSourceContract.valueAt (contract : ResolvedSourceContract)
    (site : BinderSite) : Ixon.ValueContract :=
  ((contract.binders.find? fun binder => binder.site == site).map (·.value)).getD .shared

/-- One elaborated copy of a source marker. `binder` is set when the marker is
on the outer metadata chain of a lambda, forall, or let domain. -/
structure MarkerOccurrence where
  site : BinderSite
  annotation : BinderAnnotation
  binder : Option Lean.Name := none
  isLambda : Bool := false
  deriving Inhabited

/-- Identity of an original source marker: its source offset and the binder
name it was written on. Copies keep both fields. -/
def BinderAnnotation.key (annotation : BinderAnnotation) : Nat × Lean.Name :=
  (annotation.origin, annotation.binder)

private def collectMarkers (declaration : Lean.Name) (root : SourceRoot)
    (expr : Lean.Expr) (path : List SourceStep) (acc : Array MarkerOccurrence) :
    Except SourceContractError (Array MarkerOccurrence) := do
  let site : BinderSite := ⟨root, path⟩
  let mut acc := acc
  match expr with
  | .lam name type _ _ | .forallE name type _ _ | .letE name type _ _ _ =>
    let annotation ← (binderAnnotation? type).mapError (.malformedAnnotation declaration site)
    if let some annotation := annotation then
      let isLambda := match expr with | .lam .. => true | _ => false
      acc := acc.push { site, annotation, binder := some name, isLambda }
  | .mdata data _ =>
    let annotation ← (BinderAnnotation.ofMetadata? data).mapError (.malformedAnnotation declaration site)
    if let some annotation := annotation then
      acc := acc.push { site, annotation }
  | _ => pure ()
  match expr with
  | .app fn arg =>
    let next ← collectMarkers declaration root fn (path ++ [.appFn]) acc
    collectMarkers declaration root arg (path ++ [.appArg]) next
  | .lam _ type body _ | .forallE _ type body _ =>
    let next ← collectMarkers declaration root type (path ++ [.binderType]) acc
    collectMarkers declaration root body (path ++ [.binderBody]) next
  | .letE _ type value body _ =>
    let next ← collectMarkers declaration root type (path ++ [.letType]) acc
    let final ← collectMarkers declaration root value (path ++ [.letValue]) next
    collectMarkers declaration root body (path ++ [.letBody]) final
  | .mdata _ inner => collectMarkers declaration root inner (path ++ [.metadata]) acc
  | .proj _ _ value => collectMarkers declaration root value (path ++ [.projection]) acc
  | _ => return acc

/-- Every source-marker occurrence of a declaration, in both roots. -/
def sourceMarkerOccurrences (source : Lean.ConstantInfo) :
    Except SourceContractError (Array MarkerOccurrence) := do
  let acc ← collectMarkers source.name .type source.type [] #[]
  match sourceBody? source with
  | some body => collectMarkers source.name .body body [] acc
  | none => pure acc

/-- Split marker occurrences into binder sites and copies.

A marker annotates a binder only on that binder's own domain, under the name it
was written with. The one exception is an alpha-renamed lambda at the same
position of the body telescope as an annotated arrow of the declaration type:
Lean elaborates such a lambda against that arrow, and it is the arrow's body
counterpart. A theorem's proof is never a binder site, since contracts have no
meaning inside an erased proof.

Every other occurrence is a copy that Lean's elaborator made of some binder
domain: a numeral or instance argument elaborated against a marked expected
type, a matcher motive, the packed domain of a well-founded `_unary`, or a
matcher binder that generalizes a marked let. A copy annotates nothing. When
the same declaration contains the original, the copy must agree with it. A
copy of another declaration's marker is foreign; it is ignored here, and the
transport strips it. -/
def classifyMarkers (source : Lean.ConstantInfo) (occurrences : Array MarkerOccurrence) :
    Except SourceContractError (Array MarkerOccurrence × Array MarkerOccurrence) := do
  let isTheorem := match source with | .thmInfo _ => true | _ => false
  let types := sourceTelescope source .type
  let bodies := sourceTelescope source .body
  let ownBinder := fun (occurrence : MarkerOccurrence) =>
    !(isTheorem && occurrence.site.root == .body) &&
    occurrence.binder == some occurrence.annotation.binder
  let named := occurrences.filter ownBinder
  let mut genuine := #[]
  let mut copies := #[]
  for occurrence in occurrences do
    let counterpart := Id.run do
      unless occurrence.binder.isSome && occurrence.isLambda && occurrence.site.root == .body &&
          !isTheorem do
        return false
      let some index := bodies.findIdx? (·.1 == occurrence.site) | return false
      let some (typeSite, _) := types[index]? | return false
      return named.any fun original =>
        original.site == typeSite && original.annotation == occurrence.annotation
    if ownBinder occurrence || counterpart then genuine := genuine.push occurrence
    else copies := copies.push occurrence
  for copy in copies do
    if let some original := genuine.find? (·.annotation.key == copy.annotation.key) then
      if copy.annotation != original.annotation then
        throw (.conflictingAnnotation source.name copy.site)
  return (genuine, copies)

/-- Recover the explicit source records from elaborated binder-domain markers.
Copies of a marker, inside or outside binder domains, arise during
elaboration; see `classifyMarkers`. A duplicated binder origin is unsupported. -/
def SourceContract.fromAnnotations (source : Lean.ConstantInfo) :
    Except SourceContractError SourceContract := do
  if let .recInfo info := source then
    if info.rules.any (exprHasSourceAnnotations ·.rhs) then
      throw (.annotatedRecursorRule source.name)
  let (genuine, _) ← classifyMarkers source (← sourceMarkerOccurrences source)
  let mut origins : Std.HashSet (SourceRoot × Nat) := {}
  let mut binders := #[]
  for occurrence in genuine do
    let site := occurrence.site
    let annotation := occurrence.annotation
    let key := (site.root, annotation.origin)
    if origins.contains key then throw (.duplicateAnnotation source.name site.root annotation.origin)
    origins := origins.insert key
    let isArrow := match sourceAtSite? source site with | some (.forallE ..) => true | _ => false
    if !isArrow && annotation.result.isSome then
      let copiedFromType := site.root == .body && genuine.any fun original =>
        original.site.root == .type && original.annotation == annotation
      unless copiedFromType do throw (.resultOnNonArrow source.name site)
    binders := binders.push {
      site, uses := annotation.uses, value := annotation.value
      result := if isArrow then annotation.result else none, letKind := annotation.letKind }
  -- Lean retains binder-domain metadata in the declaration type while erasing
  -- it from generated lambdas. Expand that one header to both occurrences,
  -- requiring an unchanged direct telescope; do not infer a rewrite mapping.
  if (sourceBody? source).isSome then
    let types := sourceTelescope source .type
    let bodies := sourceTelescope source .body
    for index in [:types.size] do
      let typeSite := types[index]!.1
      if let some annotation := binders.find? (·.site == typeSite) then
        let some (bodySite, _) := bodies[index]?
          | throw (.missingBodyBinder source.name index)
        let some (.forallE typeName typeDomain _ typeInfo) := sourceAtSite? source typeSite
          | throw (.expectedBinder source.name typeSite)
        let some (.lam bodyName bodyDomain _ bodyInfo) := sourceAtSite? source bodySite
          | throw (.expectedBinder source.name bodySite)
        if typeInfo != bodyInfo ||
            typeDomain.consumeMData != bodyDomain.consumeMData then
          throw (.annotationBinderMismatch source.name bodySite typeName bodyName)
        if !binders.any (·.site == bodySite) then
          binders := binders.push { annotation with site := bodySite, result := none }
  return { source, binders }

/-- Copies are ignored only because some declaration keeps the original. A
declaration command and the auxiliary definitions it generates must therefore
keep a binder site for every marker written in that command (source offsets in
`[start, stop)`); otherwise a contract the user wrote would disappear. -/
def checkAnnotationsSurvive (declaration : Lean.Name) (sources : Array Lean.ConstantInfo)
    (start stop : Nat) : Except SourceContractError Unit := do
  let mut written : Array (Nat × Lean.Name) := #[]
  let mut kept : Std.HashSet (Nat × Lean.Name) := {}
  for source in sources do
    let occurrences ← sourceMarkerOccurrences source
    let (genuine, _) ← classifyMarkers source occurrences
    for occurrence in genuine do kept := kept.insert occurrence.annotation.key
    for occurrence in occurrences do
      let key := occurrence.annotation.key
      if start ≤ key.1 && key.1 < stop && !written.contains key then written := written.push key
  for (origin, binder) in written do
    unless kept.contains (origin, binder) do
      throw (.lostAnnotation declaration origin binder)

/-- Check direct declaration telescope correspondence. This is a structural
preflight, not inference of nested function types or proof of resource validity.
A body whose telescope needs normalization is explicitly unsupported when a
contract addresses an unmatched declaration arrow. -/
def checkTelescopeConsistency (contract : ResolvedSourceContract) :
    Except SourceContractError Unit := do
  let types := sourceTelescope contract.source .type
  let bodies := sourceTelescope contract.source .body
  if (sourceBody? contract.source).isNone then return
  for index in [:max types.size bodies.size] do
    match types[index]?, bodies[index]? with
    | some (typeSite, _), some (bodySite, _) =>
      let typeUses := contract.usesAt typeSite
      let bodyUses := contract.usesAt bodySite
      if typeUses != bodyUses then
        throw (.inconsistentTelescope contract.source.name index typeUses bodyUses)
      let typeValue := contract.valueAt typeSite
      let bodyValue := contract.valueAt bodySite
      if typeValue != bodyValue then
        throw (.inconsistentValue contract.source.name index typeValue bodyValue)
    | some (site, _), none | none, some (site, _) =>
      if contract.binders.any (fun binder => binder.site == site) then
        throw (.missingBodyBinder contract.source.name index)
    | none, none => pure ()

/-- Validate source binding and occurrence annotations. Sort sites so declaration
annotation order cannot become an accidental cache or serialization input. -/
def SourceContract.resolve (contract : SourceContract) (actual : Lean.ConstantInfo) :
    Except SourceContractError ResolvedSourceContract := do
  -- Ix.Common supplies derived structural equality for the complete source,
  -- including metadata and BinderInfo. Do not substitute Expr's hash equality.
  if contract.source != actual then throw (.staleSource contract.source.name)
  if sourceHasAnnotations actual then
    let expected ← SourceContract.fromAnnotations actual
    for annotation in expected.binders do
      let some supplied := contract.binders.find? (·.site == annotation.site)
        | throw (.missingAnnotation actual.name annotation.site)
      if supplied != annotation then
        throw (.conflictingAnnotation actual.name annotation.site)
  let mut seen : Std.HashSet BinderSite := {}
  let mut binders := #[]
  for binder in contract.binders do
    if seen.contains binder.site then throw (.duplicateSite actual.name binder.site)
    seen := seen.insert binder.site
    binders := binders.push (← resolveBinderContract actual binder)
  binders := binders.qsort fun a b => compare a.site b.site == .lt
  let result : ResolvedSourceContract := { source := actual, binders }
  checkTelescopeConsistency result
  return result

/-- Resolve a nonsemantic measure proposal independently of binder contracts. -/
def MeasureHint.resolve (hint : MeasureHint) (actual : Lean.ConstantInfo) :
    Except SourceContractError ResolvedMeasureHint := do
  let name := hint.source.name
  if hint.source != actual then throw (.staleSource name)
  let argument ← resolveBinderSelector actual hint.argument
  let some (site, _) := (sourceTelescope actual .type)[argument]?
    | throw (.argumentOutOfRange name argument)
  if hint.fixedStep == some 0 then throw (.zeroFixedStep name)
  return ⟨actual, argument, site, hint.fixedStep⟩

/-- Resolve a complete input without consulting a Lean environment. The explicit
registry is checked before a caller may canonicalize or merge source terms. -/
def CompileInput.resolve (input : CompileInput) :
    Except SourceContractError ResolvedCompileInput := do
  let mut selected : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for (name, source) in input.constants do
    if name != source.name then throw (.declarationNameMismatch name source.name)
    if selected.contains name then throw (.duplicateDeclaration name)
    selected := selected.insert name source
  let mut seen : Std.HashSet Lean.Name := {}
  let mut contracts := #[]
  for contract in input.contracts do
    let name := contract.source.name
    if seen.contains name then throw (.duplicateContract name)
    seen := seen.insert name
    let some actual := selected[name]? | throw (.missingDeclaration name)
    contracts := contracts.push (← contract.resolve actual)
  for (name, source) in input.constants do
    if sourceHasAnnotations source && !seen.contains name then throw (.missingContract name)
  contracts := contracts.qsort fun a b => a.source.name.cmp b.source.name == .lt
  let mut seenHints : Std.HashSet Lean.Name := {}
  let mut measureHints := #[]
  for hint in input.measureHints do
    let name := hint.source.name
    if seenHints.contains name then throw (.duplicateMeasure name)
    seenHints := seenHints.insert name
    let some actual := selected[name]? | throw (.missingDeclaration name)
    measureHints := measureHints.push (← hint.resolve actual)
  measureHints := measureHints.qsort fun a b => a.source.name.cmp b.source.name == .lt
  return { constants := input.constants, contracts, measureHints }

end Ix.Compile

end
