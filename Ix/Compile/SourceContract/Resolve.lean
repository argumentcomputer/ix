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
    (contracts : Array TelescopeContract) (regions : Array Lean.Name := #[]) :
    Except SourceContractError SourceContract := do
  let types := sourceTelescope source .type
  let bodies := sourceTelescope source .body
  let mut binders := #[]
  for contract in contracts do
    let index ← resolveBinderSelector source contract.binder
    let some (typeSite, _) := types[index]?
      | throw (.argumentOutOfRange source.name index)
    binders := binders.push {
      site := typeSite, uses := contract.uses, resultOwned := contract.resultOwned
      owned := contract.owned, region := contract.region }
    if (sourceBody? source).isSome then
      let some (bodySite, _) := bodies[index]?
        | throw (.missingBodyBinder source.name index)
      binders := binders.push {
        site := bodySite, uses := contract.uses, owned := contract.owned, region := contract.region }
  return { source, binders, regions }

def resolveBinderContract (source : Lean.ConstantInfo) (regions : Array Lean.Name)
    (contract : BinderContract) :
    Except SourceContractError ResolvedBinderContract := do
  let region ← match contract.region with
    | none => pure none
    | some name => match regions.idxOf? name with
      | some index => pure (some index)
      | none => throw (.unknownRegion source.name name)
  let some expr := sourceAtSite? source contract.site
    | throw (.invalidSite source.name contract.site)
  match expr with
  | .lam name _ _ binderInfo =>
    if contract.resultOwned.isSome then
      throw (.ownershipOnLambda source.name contract.site)
    return {
      site := contract.site
      kind := .lam
      name := name
      binderInfo := binderInfo
      uses := contract.uses
      resultOwned := none
      owned := contract.owned
      region }
  | .forallE name _ _ binderInfo =>
    return {
      site := contract.site
      kind := .all
      name := name
      binderInfo := binderInfo
      uses := contract.uses
      resultOwned := some (contract.resultOwned.getD .shared)
      owned := contract.owned
      region }
  | _ => throw (.expectedBinder source.name contract.site)

def ResolvedSourceContract.usesAt (contract : ResolvedSourceContract)
    (site : BinderSite) : Ixon.Uses :=
  ((contract.binders.find? fun binder => binder.site == site).map (·.uses)).getD .many

def ResolvedSourceContract.ownedAt (contract : ResolvedSourceContract)
    (site : BinderSite) : Ixon.Owned :=
  ((contract.binders.find? fun binder => binder.site == site).map (·.owned)).getD .shared

def ResolvedSourceContract.regionAt (contract : ResolvedSourceContract)
    (site : BinderSite) : Option Nat :=
  (contract.binders.find? fun binder => binder.site == site).bind (·.region)

private structure CollectedAnnotations where
  binders : Array (BinderSite × BinderAnnotation) := #[]
  markers : Array (BinderSite × BinderAnnotation) := #[]

private def collectAnnotations (declaration : Lean.Name) (root : SourceRoot)
    (expr : Lean.Expr) (path : List SourceStep) (acc : CollectedAnnotations) :
    Except SourceContractError CollectedAnnotations := do
  let site : BinderSite := ⟨root, path⟩
  let mut acc := acc
  match expr with
  | .lam name type _ _ | .forallE name type _ _ =>
    let annotation ← (binderAnnotation? type).mapError (.malformedAnnotation declaration site)
    if let some annotation := annotation then
      if annotation.binder != name then
        throw (.annotationBinderMismatch declaration site annotation.binder name)
      acc := { acc with binders := acc.binders.push (site, annotation) }
  | .mdata data _ =>
    let annotation ← (BinderAnnotation.ofMetadata? data).mapError (.malformedAnnotation declaration site)
    if let some annotation := annotation then
      acc := { acc with markers := acc.markers.push (site, annotation) }
  | _ => pure ()
  match expr with
  | .app fn arg =>
    let next ← collectAnnotations declaration root fn (path ++ [.appFn]) acc
    collectAnnotations declaration root arg (path ++ [.appArg]) next
  | .lam _ type body _ | .forallE _ type body _ =>
    let next ← collectAnnotations declaration root type (path ++ [.binderType]) acc
    collectAnnotations declaration root body (path ++ [.binderBody]) next
  | .letE _ type value body _ =>
    let next ← collectAnnotations declaration root type (path ++ [.letType]) acc
    let final ← collectAnnotations declaration root value (path ++ [.letValue]) next
    collectAnnotations declaration root body (path ++ [.letBody]) final
  | .mdata _ inner => collectAnnotations declaration root inner (path ++ [.metadata]) acc
  | .proj _ _ value => collectAnnotations declaration root value (path ++ [.projection]) acc
  | _ => return acc

/-- Recover the explicit source records from elaborated binder-domain markers.
Repeated copies of a marker outside binder domains can arise during type
inference. They must agree with the original annotation; they do not annotate
another binder. A duplicated or renamed binder origin is unsupported. -/
def SourceContract.fromAnnotations (source : Lean.ConstantInfo) :
    Except SourceContractError SourceContract := do
  if let .recInfo info := source then
    if info.rules.any (exprHasSourceAnnotations ·.rhs) then
      throw (.annotatedRecursorRule source.name)
  let acc ← collectAnnotations source.name .type source.type [] {}
  let acc ← match sourceBody? source with
    | some body => collectAnnotations source.name .body body [] acc
    | none => pure acc
  let regions := (acc.binders[0]?.map (·.2.regions)).getD #[]
  let mut origins : Std.HashSet (SourceRoot × Nat) := {}
  let mut binders := #[]
  for (site, annotation) in acc.binders do
    if annotation.regions != regions then throw (.conflictingRegions source.name)
    let key := (site.root, annotation.origin)
    if origins.contains key then throw (.duplicateAnnotation source.name site.root annotation.origin)
    origins := origins.insert key
    binders := binders.push {
      site, uses := annotation.uses, owned := annotation.owned, region := annotation.region }
  for (site, marker) in acc.markers do
    let some (_, annotation) := acc.binders.find? fun (binderSite, annotation) =>
        binderSite.root == site.root && annotation.origin == marker.origin
      | throw (.misplacedAnnotation source.name site)
    if marker != annotation then throw (.conflictingAnnotation source.name site)
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
        if typeName != bodyName || typeInfo != bodyInfo ||
            typeDomain.consumeMData != bodyDomain.consumeMData then
          throw (.annotationBinderMismatch source.name bodySite typeName bodyName)
        if !binders.any (·.site == bodySite) then
          binders := binders.push { annotation with site := bodySite, resultOwned := none }
  return { source, binders, regions }

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
      let typeOwned := contract.ownedAt typeSite
      let bodyOwned := contract.ownedAt bodySite
      if typeOwned != bodyOwned then
        throw (.inconsistentOwnership contract.source.name index typeOwned bodyOwned)
      let typeRegion := contract.regionAt typeSite
      let bodyRegion := contract.regionAt bodySite
      if typeRegion != bodyRegion then
        throw (.inconsistentRegion contract.source.name index typeRegion bodyRegion)
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
    if expected.regions != contract.regions then throw (.conflictingRegions actual.name)
    for annotation in expected.binders do
      let some supplied := contract.binders.find? (·.site == annotation.site)
        | throw (.missingAnnotation actual.name annotation.site)
      if supplied.uses != annotation.uses || supplied.owned != annotation.owned ||
          supplied.region != annotation.region then
        throw (.conflictingAnnotation actual.name annotation.site)
  let mut seenRegions : Std.HashSet Lean.Name := {}
  for region in contract.regions do
    if seenRegions.contains region then throw (.duplicateRegion actual.name region)
    seenRegions := seenRegions.insert region
  let mut seen : Std.HashSet BinderSite := {}
  let mut binders := #[]
  for binder in contract.binders do
    if seen.contains binder.site then throw (.duplicateSite actual.name binder.site)
    seen := seen.insert binder.site
    binders := binders.push (← resolveBinderContract actual contract.regions binder)
  binders := binders.qsort fun a b => compare a.site b.site == .lt
  let result : ResolvedSourceContract := { source := actual, binders, regions := contract.regions }
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
