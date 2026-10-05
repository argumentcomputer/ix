import Ix.CompileCert.SourceNormalization

/-! # Installed source projections

The installed shape of a checked constructor cover
(`SourceCoverInstalledShape`), installed projection equations
(`SourceProjectionInstalled`) and projection functions
(`SourceProjectionFunction`) with their semantic readings, and membership in
the normalized installation.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

/-- Inserting subject and proposition binders must leave references to earlier
fields fixed while moving references to original parameters by two slots. -/
def liftSourceFieldDomains : Nat → List (Kernel.Expr × Kernel.BinderMeta) →
    List (Kernel.Expr × Kernel.BinderMeta)
  | _, [] => []
  | index, (domain, binder) :: rest =>
    (domain.liftLooseBVars 2 index, binder) :: liftSourceFieldDomains (index + 1) rest

theorem liftSourceFieldDomains_length (index : Nat) (fields : List (Kernel.Expr × Kernel.BinderMeta)) :
    (liftSourceFieldDomains index fields).length = fields.length := by
  induction fields generalizing index with
  | nil => rfl
  | cons field rest ih => simp only [liftSourceFieldDomains, List.length_cons, ih]

/-- Data extracted from the *installed* headers, independent of the raw
generator's binder annotations. The checker below binds all three headers to
their actual environment entries before this relation is used. -/
structure SourceCoverShapeData where
  owner : Kernel.ConstantVal
  constructor : Kernel.ConstantVal
  theoremHeader : Kernel.ConstantVal
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  constructorParameters : List (Kernel.Expr × Kernel.BinderMeta)
  coverageParameters : List (Kernel.Expr × Kernel.BinderMeta)
  fields : List (Kernel.Expr × Kernel.BinderMeta)
  coverageFields : List (Kernel.Expr × Kernel.BinderMeta)
  constructorResult : Kernel.Expr
  subjectType : Kernel.Expr
  equalityType : Kernel.Expr
  level : Kernel.Level
  subjectBinder : Kernel.BinderMeta
  propositionBinder : Kernel.BinderMeta
  continuationBinder : Kernel.BinderMeta
  equalityBinder : Kernel.BinderMeta
  continuation : Kernel.Expr
  propositionIndex : Nat

def sourceForalls (binders : List (Kernel.Expr × Kernel.BinderMeta)) (body : Kernel.Expr) : Kernel.Expr :=
  binders.foldr (fun (domain, binder) rest => .forallE domain rest binder) body

theorem sourceForalls_binders (binders : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) : InstalledBinderPrefix binders.length (sourceForalls binders body) := by
  induction binders with
  | nil => exact .zero body
  | cons binder rest ih => exact .succ ih

/-- Typed argument tuples depend on binder domains, not the regime of the
enclosing forall. Each complete telescope is interpreted with its own regime. -/
theorem sourceForalls_transfer {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V}
    {sourceBinders targetBinders : List (Kernel.Expr × Kernel.BinderMeta)}
    {sourceBody targetBody result : Kernel.Expr} {arguments : List V}
    (domains : sourceBinders.map Prod.fst = targetBinders.map Prod.fst)
    (length : arguments.length = sourceBinders.length)
    (typed : InstalledTelescope values env levels ρ (sourceForalls sourceBinders sourceBody)
      arguments finalρ result) :
    result = sourceBody ∧
      InstalledTelescope values env levels ρ (sourceForalls targetBinders targetBody)
        arguments finalρ targetBody := by
  induction sourceBinders generalizing targetBinders arguments ρ with
  | nil =>
    have ha : arguments = [] := by simpa using length
    have ht : targetBinders = [] := by simpa using domains.symm
    subst arguments
    subst targetBinders
    cases typed
    exact ⟨rfl, .nil⟩
  | cons sourceBinder rest ih =>
    cases targetBinders with
    | nil => simp at domains
    | cons targetBinder targetRest =>
      simp only [List.map_cons, List.cons.injEq] at domains
      cases arguments with
      | nil => simp at length
      | cons argument arguments =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at length
        cases typed with
        | cons domainDenoted argumentTyped remaining =>
          obtain ⟨resultEq, transferred⟩ := ih domains.2 length remaining
          refine ⟨resultEq, .cons ?_ argumentTyped transferred⟩
          simpa only [← domains.1] using domainDenoted

theorem sourceForalls_lift (binders : List (Kernel.Expr × Kernel.BinderMeta))
    (body : Kernel.Expr) (index : Nat) :
    (sourceForalls binders body).liftLooseBVars 2 index =
      sourceForalls (liftSourceFieldDomains index binders)
        (body.liftLooseBVars 2 (index + binders.length)) := by
  induction binders generalizing index with
  | nil => rfl
  | cons binder rest ih =>
    simp only [sourceForalls, List.foldr_cons, Kernel.Expr.liftLooseBVars,
      liftSourceFieldDomains, List.length_cons]
    congr 1
    simpa only [sourceForalls, Nat.add_assoc, Nat.add_comm 1] using ih (index + 1)

/-- Reflect a typed coverage tuple back to the original constructor telescope.
The original telescope's actual denotation supplies domain existence; this
does not assume raw source annotations denote or infer a source model from a
target model. Earlier dependent arguments are retained in both valuations. -/
theorem sourceForalls_reflect_lift {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    {levels : Kernel.Name → Nat}
    {binders targetBinders : List (Kernel.Expr × Kernel.BinderMeta)}
    {body targetBody result : Kernel.Expr} {arguments : List V}
    {index : Nat} {ρ target finalTarget : Nat → V} {type : V}
    (domains : targetBinders.map Prod.fst = (liftSourceFieldDomains index binders).map Prod.fst)
    (length : arguments.length = binders.length)
    (denoted : Kernel.Denotes values env levels ρ (sourceForalls binders body) type)
    (typed : InstalledTelescope values env levels target (sourceForalls targetBinders targetBody)
      arguments finalTarget result)
    (related : ValuationLift 2 index ρ target) :
    ∃ finalρ, InstalledTelescope values env levels ρ (sourceForalls binders body)
      arguments finalρ body ∧ ValuationLift 2 (index + arguments.length) finalρ finalTarget := by
  induction binders generalizing targetBinders arguments index ρ target type with
  | nil =>
    have ha : arguments = [] := by simpa using length
    have ht : targetBinders = [] := by simpa [liftSourceFieldDomains] using domains
    subst arguments
    subst targetBinders
    cases typed
    exact ⟨ρ, .nil, related⟩
  | cons binder rest ih =>
    cases targetBinders with
    | nil => simp [liftSourceFieldDomains] at domains
    | cons targetBinder targetRest =>
      simp only [liftSourceFieldDomains, List.map_cons, List.cons.injEq] at domains
      cases arguments with
      | nil => simp at length
      | cons argument arguments =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at length
        cases denoted with
        | pi hA hB hP =>
          cases typed with
          | cons targetDomain targetTyped targetRemaining =>
            have shifted := denotes_lift hA related
            rw [← domains.1] at shifted
            obtain rfl := Kernel.Denotes_functional targetDomain shifted
            obtain ⟨finalρ, originalRemaining, finalRelated⟩ :=
              ih domains.2 length (hB argument targetTyped) targetRemaining (related.push argument)
            refine ⟨finalρ, .cons hA targetTyped originalRemaining, ?_⟩
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using finalRelated

/-- Full structural checks, including universe lists, original identities and
dependent domains. Each enclosing telescope retains its own installed binder
regimes: a constructor returns a carrier, whereas the continuation returns Prop.
Only domain expressions are compared across those different telescopes.
Equality is Lean's structural equality, not hash equality. -/
def SourceCoverShape {source : Source} (site : SourceProjectionSite source)
    (coverageHeader : Kernel.ConstantVal) (data : SourceCoverShapeData) : Prop :=
  let levels := data.owner.levelParams.map Kernel.Level.param
  let params := sourceParameterVars site.owner.numParams 0
  let ctorParams := sourceParameterVars site.owner.numParams site.ctor.numFields
  let coverParams := sourceParameterVars site.owner.numParams (site.ctor.numFields + 2)
  data.owner.name = sourceName site.ownerName ∧
  data.constructor.name = sourceName site.ctorName ∧
  data.theoremHeader.name = coverageHeader.name ∧
  data.owner.levelParams = data.constructor.levelParams ∧
  data.owner.levelParams = data.theoremHeader.levelParams ∧
  data.theoremHeader.levelParams = coverageHeader.levelParams ∧
  data.parameters.length = site.owner.numParams ∧
  data.fields.length = site.ctor.numFields ∧
  data.constructorParameters.map Prod.fst = data.parameters.map Prod.fst ∧
  data.coverageParameters.map Prod.fst = data.parameters.map Prod.fst ∧
  data.coverageFields.map Prod.fst = (liftSourceFieldDomains 0 data.fields).map Prod.fst ∧
  data.owner.type = sourceForalls data.parameters (.sort data.level) ∧
  data.constructor.type = sourceForalls data.constructorParameters
    (sourceForalls data.fields data.constructorResult) ∧
  data.constructorResult = Kernel.Expr.mkAppN (.const data.owner.name levels) ctorParams ∧
  data.subjectType = Kernel.Expr.mkAppN (.const data.owner.name levels) params ∧
  data.equalityType = Kernel.Expr.mkAppN (.const Kernel.eqName [data.level])
    [Kernel.Expr.mkAppN (.const data.owner.name levels) coverParams,
      .bvar (site.ctor.numFields + 1),
      Kernel.Expr.mkAppN (.const data.constructor.name levels)
        (coverParams ++ sourceParameterVars site.ctor.numFields 0)] ∧
  data.propositionIndex = site.ctor.numFields + 1 ∧
  data.continuation = sourceForalls data.coverageFields
    (.forallE data.equalityType (.bvar data.propositionIndex) data.equalityBinder) ∧
  data.theoremHeader.type = sourceForalls data.coverageParameters
    (.forallE data.subjectType
      (.forallE (.sort .zero)
        (.forallE data.continuation (.bvar 1) data.continuationBinder)
        data.propositionBinder) data.subjectBinder)

instance {source : Source} (site : SourceProjectionSite source)
    (header : Kernel.ConstantVal) (data : SourceCoverShapeData) :
    Decidable (SourceCoverShape site header data) := by
  unfold SourceCoverShape
  infer_instance

structure SourceCoverInstalledShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) where
  data : SourceCoverShapeData
  ownerCaps : Kernel.IndCaps
  ownerLookup : coverage.env.find? (sourceName site.ownerName) = some (.indInfo data.owner ownerCaps)
  constructorLookup : coverage.env.find? (sourceName site.ctorName) =
    some (.ctorInfo data.constructor site.owner.numParams site.ctor.numFields)
  theoremLookup : coverage.env.find? coverage.header.name = some (.thmInfo data.theoremHeader coverage.value)
  shape : SourceCoverShape site coverage.header data

/-- A fail-closed installed annotation/field-domain receipt. Its success for
every source domain member is a separate obligation, not a new definition of Dom. -/
def checkSourceCoverInstalledShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    (coverage : SourceConstructorCoverChecked installed site) :
    Except String (SourceCoverInstalledShape coverage) := do
  let some (.indInfo owner caps) ← pure (coverage.env.find? (sourceName site.ownerName))
    | throw "installed source coverage owner is missing or has wrong kind"
  let some (.ctorInfo constructor numParams numFields) ← pure (coverage.env.find? (sourceName site.ctorName))
    | throw "installed source coverage constructor is missing or has wrong kind"
  let some (.thmInfo theoremHeader _) ← pure (coverage.env.find? coverage.header.name)
    | throw "installed source coverage theorem is missing or has wrong kind"
  let some (parameters, .sort level) := owner.type.stripPis site.owner.numParams
    | throw "installed source owner telescope is not the original unindexed shape"
  let some (constructorParameters, constructorBody) := constructor.type.stripPis numParams
    | throw "installed source constructor parameter telescope is short"
  let some (fields, constructorResult) := constructorBody.stripPis numFields
    | throw "installed source constructor field telescope is short"
  let some (coverageParameters, .forallE subjectType
      (.forallE (.sort .zero) (.forallE continuation (.bvar 1) continuationBinder)
        propositionBinder) subjectBinder) := theoremHeader.type.stripPis site.owner.numParams
    | throw "installed coverage theorem lacks the exact Church statement"
  let some (coverageFields, .forallE equalityType (.bvar propositionIndex) equalityBinder) :=
      continuation.stripPis site.ctor.numFields
    | throw "installed coverage continuation lacks its exact field/equality telescope"
  let data : SourceCoverShapeData := ⟨owner, constructor, theoremHeader, parameters,
    constructorParameters, coverageParameters, fields, coverageFields, constructorResult,
    subjectType, equalityType, level, subjectBinder, propositionBinder, continuationBinder,
    equalityBinder, continuation, propositionIndex⟩
  if ho : coverage.env.find? (sourceName site.ownerName) = some (.indInfo data.owner caps) then
    if hc : coverage.env.find? (sourceName site.ctorName) =
        some (.ctorInfo data.constructor site.owner.numParams site.ctor.numFields) then
      if ht : coverage.env.find? coverage.header.name = some (.thmInfo data.theoremHeader coverage.value) then
        if hs : SourceCoverShape site coverage.header data then
          return ⟨data, caps, ho, hc, ht, hs⟩
        else throw s!"installed coverage fields or identities do not match the original constructor; fieldDomains={decide (data.coverageFields.map Prod.fst = (liftSourceFieldDomains 0 data.fields).map Prod.fst)}; constructorParams={decide (data.constructorParameters.map Prod.fst = data.parameters.map Prod.fst)}; coverageParams={decide (data.coverageParameters.map Prod.fst = data.parameters.map Prod.fst)}; constructorFieldBinders={reprStr (data.fields.map Prod.snd)}; coverageFieldBinders={reprStr (data.coverageFields.map Prod.snd)}"
      else throw "installed coverage theorem body is not its checked original proposal"
    else throw "installed constructor counts differ from the immutable source"
  else throw "installed coverage owner lookup changed"

theorem SourceCoverInstalledShape.owner_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.indInfo receipt.data.owner receipt.ownerCaps ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.ownerLookup

open Kernel.SetTheory in
/-- The source carrier's universe membership comes from the actual installed
owner and its typed parameter tuple, not from an assumed shape of arbitrary
set-theoretic application. -/
theorem SourceCoverInstalledShape.owner_apply {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V} {result : Kernel.Expr}
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (typed : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters finalρ result) :
    parameters.foldl app (model.cval (sourceName site.ownerName) levels) ∈ˢ
      univ (Kernel.Level.eval levels receipt.data.level) := by
  rcases receipt.shape with ⟨ownerName, _, _, _, _, _, count, _, _, _, _, ownerType, _⟩
  obtain ⟨type, read, member⟩ := typed.model_apply model receipt.owner_member
  rw [ownerType] at typed
  have ⟨resultType, _⟩ := sourceForalls_transfer (targetBinders := receipt.data.parameters)
    (targetBody := Kernel.Expr.sort receipt.data.level) rfl (parameterCount.trans count.symm) typed
  rw [resultType] at read
  cases read
  simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, ownerName] using member

theorem SourceCoverInstalledShape.constructor_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.ctorInfo receipt.data.constructor site.owner.numParams site.ctor.numFields
      ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.constructorLookup

theorem SourceCoverInstalledShape.theorem_member {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) :
    Kernel.ConstantInfo.thmInfo receipt.data.theoremHeader coverage.value ∈ coverage.env.consts :=
  List.mem_of_find?_eq_some receipt.theoremLookup

open Kernel.SetTheory in
/-- Typed original field tuples construct actual carrier members in the same
installed model as the coverage theorem. The immutable source constructor name,
not a reverse content alias or an unrelated model witness, determines the value. -/
theorem SourceCoverInstalledShape.constructor_apply {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    {levels : Kernel.Name → Nat} {ρ finalρ : Nat → V} {result : Kernel.Expr}
    (parameters : List V) (fields : SourceFieldValues site V)
    (typed : InstalledTelescope model.cval coverage.env levels ρ receipt.data.constructor.type
      (parameters ++ fields.val) finalρ result) :
    ∃ carrier, Kernel.Denotes model.cval coverage.env levels finalρ result carrier ∧
      originalConstructorValue site model.cval levels parameters fields ∈ˢ carrier := by
  have applied := typed.model_apply model receipt.constructor_member
  have name : receipt.data.constructor.name = sourceName site.ctorName := receipt.shape.2.1
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name,
    originalConstructorValue, name] using applied

open Kernel.SetTheory in
/-- Read the receipt's exact Eq syntax at its exact argument frame. This
connects the independently checked syntax to semantic constructor values;
the Eq constant's own denotation remains explicit until extracted from the
actually denoted continuation leaf. -/
theorem SourceCoverInstalledShape.equality_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) (subject proposition E : V)
    (eqRead : Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      (.const Kernel.eqName [receipt.data.level]) E) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      receipt.data.equalityType
      (app (app (app E (parameters.foldl app (model.cval (sourceName site.ownerName) levels))) subject)
        (originalConstructorValue site model.cval levels parameters fields)) := by
  rcases receipt.shape with ⟨ownerName, constructorName, _, levelNames, _, _, _, _, _, _, _,
    _, _, _, _, equation, _, _, _⟩
  let base := pushArguments ρ parameters
  let frame := pushArguments (pushArguments base [subject, proposition]) fields.val
  have parameterSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars site.owner.numParams (site.ctor.numFields + 2)) parameters := by
    have read := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
      (levels := levels) ρ parameters ([subject, proposition] ++ fields.val)
    simpa only [pushArguments_append, List.length_append, List.length_cons,
      List.length_nil, parameterCount, fields.property, Nat.add_comm 2, Nat.zero_add,
      Nat.reduceAdd, base, frame] using read
  have fieldSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars site.ctor.numFields 0) fields.val := by
    have read := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
      (levels := levels) (pushArguments base [subject, proposition]) fields.val []
    simpa only [List.length_nil, pushArguments, fields.property, frame] using read
  have ownerRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.ownerLookup
  have constructorRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.constructorLookup
  simp only [Kernel.ConstantInfo.toConstantVal] at ownerRead constructorRead
  rw [← ownerName] at ownerRead
  rw [← constructorName, ← levelNames] at constructorRead
  have ownerApp := denotes_mkAppN ownerRead parameterSpine
  have constructorApp := denotes_mkAppN constructorRead (parameterSpine.append fieldSpine)
  have subjectRead : Kernel.Denotes model.cval coverage.env levels frame
      (.bvar (site.ctor.numFields + 1)) subject := by
    have slot : frame (site.ctor.numFields + 1) = subject := by
      have above := pushArguments_above fields.val (pushArguments base [subject, proposition]) 1
      simpa only [frame, fields.property, pushArguments, Kernel.push] using above
    rw [← slot]
    exact .bvar
  rw [equation]
  have read := Kernel.Denotes.app (Kernel.Denotes.app (Kernel.Denotes.app eqRead ownerApp)
    subjectRead) constructorApp
  simpa only [Kernel.Expr.mkAppN, originalConstructorValue, ownerName, constructorName,
    base, frame] using read

open Kernel.SetTheory in
/-- Extract the Eq instance from the actual leaf denotation and identify its
value with the original carrier/subject/constructor equation. No separate
assumption that Eq resolves in the source environment is needed. -/
theorem SourceCoverInstalledShape.equality_value {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) (subject proposition value : V)
    (read : Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      receipt.data.equalityType value) :
    ∃ E, Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments (pushArguments ρ parameters) [subject, proposition]) fields.val)
      (.const Kernel.eqName [receipt.data.level]) E ∧
      value = app (app (app E (parameters.foldl app (model.cval (sourceName site.ownerName) levels))) subject)
        (originalConstructorValue site model.cval levels parameters fields) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, equation, _, _, _⟩
  have expanded := read
  rw [equation] at expanded
  obtain ⟨E, eqRead⟩ := denotes_mkAppN_head _ expanded
  exact ⟨E, eqRead, Kernel.Denotes_functional read
    (receipt.equality_denotes model levels ρ parameters parameterCount fields subject proposition E eqRead)⟩

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.carrier_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams) (extras : List V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) extras)
      (Kernel.Expr.mkAppN (.const receipt.data.owner.name
        (receipt.data.owner.levelParams.map Kernel.Level.param))
        (sourceParameterVars site.owner.numParams extras.length))
      (parameters.foldl app (model.cval (sourceName site.ownerName) levels)) := by
  have head := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := pushArguments (pushArguments ρ parameters) extras) receipt.ownerLookup
  have spine := sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
    (levels := levels) ρ parameters extras
  rw [parameterCount] at spine
  have result := denotes_mkAppN head spine
  have ownerName := receipt.shape.1
  simpa only [Kernel.ConstantInfo.toConstantVal, ownerName] using result

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_result_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (fields : SourceFieldValues site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.constructorResult
      (parameters.foldl app (model.cval (sourceName site.ownerName) levels)) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, resultType, _⟩
  rw [resultType]
  simpa only [fields.property] using
    receipt.carrier_denotes model levels ρ parameters parameterCount fields.val

/-- Original constructor field typing, read from the independently installed
source constructor. This predicate does not mention the lowered projection. -/
def SourceCoverValidFields {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) (parameters : List V)
    (fields : SourceFieldValues site V) : Prop :=
    InstalledTelescope model.cval coverage.env levels (pushArguments ρ parameters)
      (sourceForalls receipt.data.fields receipt.data.constructorResult) fields.val
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.constructorResult

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_fields {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level)) :
    ∃ type, Kernel.Denotes model.cval coverage.env levels (pushArguments ρ parameters)
      (sourceForalls receipt.data.fields receipt.data.constructorResult) type ∧
      parameters.foldl app (model.cval (sourceName site.ctorName) levels) ∈ˢ type := by
  rcases receipt.shape with ⟨_, constructorName, _, _, _, _, count, _, domains, _, _,
    ownerType, constructorType, _⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer (targetBody := sourceForalls receipt.data.fields
    receipt.data.constructorResult) domains.symm (parameterCount.trans count.symm) parameterTyping).2
  rw [← constructorType] at transferred
  have result := transferred.model_apply model receipt.constructor_member
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name, constructorName] using result

open Kernel.SetTheory in
theorem SourceCoverInstalledShape.constructor_typed {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (fields : SourceFieldValues site V)
    (valid : SourceCoverValidFields receipt model levels ρ parameters fields) :
    originalConstructorValue site model.cval levels parameters fields ∈ˢ
      parameters.foldl app (model.cval (sourceName site.ownerName) levels) := by
  obtain ⟨type, read, member⟩ := receipt.constructor_fields model levels ρ parameters parameterCount parameterTyping
  obtain ⟨result, readResult, memberResult⟩ := valid.apply read member
  obtain rfl := Kernel.Denotes_functional readResult
    (receipt.constructor_result_denotes model levels ρ parameters parameterCount fields)
  simpa only [originalConstructorValue, List.foldl_append] using memberResult

open Kernel.SetTheory in
/-- Specialize the actually admitted coverage theorem to typed original
parameters and an arbitrary member of the original carrier. -/
theorem SourceCoverInstalledShape.church {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    ∃ type, Kernel.Denotes model.cval coverage.env levels
      (Kernel.push subject (pushArguments ρ parameters))
      (.forallE (.sort .zero) (.forallE receipt.data.continuation (.bvar 1)
        receipt.data.continuationBinder) receipt.data.propositionBinder) type ∧
      app (parameters.foldl app (model.cval coverage.header.name levels)) subject ∈ˢ type := by
  rcases receipt.shape with ⟨_, _, theoremName, _, _, _, count, _, _, domains, _,
    ownerType, _, _, subjectType, _, _, _, theoremType⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer
    (targetBody := .forallE receipt.data.subjectType
      (.forallE (.sort .zero) (.forallE receipt.data.continuation (.bvar 1)
        receipt.data.continuationBinder) receipt.data.propositionBinder) receipt.data.subjectBinder)
    domains.symm (parameterCount.trans count.symm) parameterTyping).2
  rw [← theoremType] at transferred
  obtain ⟨type, read, member⟩ := transferred.model_apply model receipt.theorem_member
  have subjectRead := receipt.carrier_denotes model levels ρ parameters parameterCount []
  simp only [List.length_nil, pushArguments] at subjectRead
  rw [← subjectType] at subjectRead
  have specialized := installed_forall_elim read member subjectRead subjectTyped
  simpa only [Kernel.ConstantInfo.toConstantVal, Kernel.ConstantInfo.name, theoremName] using specialized

open Kernel.SetTheory in
/-- The independently admitted coverage theorem covers every member of the
original source carrier, with fields typed by its actual original constructor.
This discharges the semantic coverage premise for a checked installed receipt;
it does not assert full-domain receipt production or projection computation. -/
theorem SourceCoverInstalledShape.semantic_cover {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    SemanticConstructorCover (SourceCoverValidFields receipt model levels ρ parameters)
      (originalConstructorValue site model.cval levels parameters) subject := by
  intro proposition propositionTyped continuation
  obtain ⟨churchType, churchRead, churchMember⟩ :=
    receipt.church model levels ρ parameters parameterCount parameterTyping subject subjectTyped
  apply installed_church_elim churchRead churchMember proposition propositionTyped
  obtain ⟨continuationType, continuationRead⟩ := denotes_church_continuation churchRead propositionTyped
  refine ⟨continuationType, continuationRead, ?_⟩
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, fieldCount, _, _, domains,
    _, _, _, _, _, propositionIndex, continuationShape, _⟩
  have coverageCount : receipt.data.coverageFields.length = site.ctor.numFields := by
    have lengths := congrArg List.length domains
    simpa only [List.length_map, liftSourceFieldDomains_length, fieldCount] using lengths
  have fieldsRead := continuationRead
  rw [continuationShape] at fieldsRead
  apply (sourceForalls_binders receipt.data.coverageFields _).inhabited fieldsRead
  intro arguments finalρ result length typed
  let fields : SourceFieldValues site V := ⟨arguments, length.trans coverageCount⟩
  obtain ⟨constructorType, constructorRead, _⟩ :=
    receipt.constructor_fields model levels ρ parameters parameterCount parameterTyping
  have originalLength : arguments.length = receipt.data.fields.length :=
    (length.trans coverageCount).trans fieldCount.symm
  obtain ⟨originalFinal, originalTyped, _⟩ := sourceForalls_reflect_lift domains originalLength
    constructorRead typed (valuationLift_two (pushArguments ρ parameters) subject proposition)
  have originalFinalEq := originalTyped.final_valuation
  have valid : SourceCoverValidFields receipt model levels ρ parameters fields := by
    rw [originalFinalEq] at originalTyped
    exact originalTyped
  have resultEq := (sourceForalls_transfer (targetBinders := receipt.data.coverageFields)
    (targetBody := Kernel.Expr.forallE receipt.data.equalityType (.bvar receipt.data.propositionIndex)
      receipt.data.equalityBinder) rfl length typed).1
  have finalEq := typed.final_valuation
  obtain ⟨leafType, leafRead⟩ := typed.read fieldsRead
  rw [resultEq, finalEq, propositionIndex] at leafRead
  obtain ⟨equalityType, equalityRead⟩ := denotes_forall_domain leafRead
  obtain ⟨E, eqRead, equalityValue⟩ := receipt.equality_value model levels ρ parameters
    parameterCount fields subject proposition equalityType equalityRead
  rw [equalityValue] at equalityRead
  have carrierTyped := receipt.owner_apply model parameters parameterCount parameterTyping
  have constructorTyped := receipt.constructor_typed model levels ρ parameters parameterCount
    parameterTyping fields valid
  have slot : (pushArguments (Kernel.push proposition (Kernel.push subject (pushArguments ρ parameters)))
      arguments) site.ctor.numFields = proposition := by
    have above := pushArguments_above arguments
      (Kernel.push proposition (Kernel.push subject (pushArguments ρ parameters))) 0
    simpa only [length.trans coverageCount, Nat.add_zero, Kernel.push] using above
  have inhabited := installed_eq_implication_inhabited model eqRead carrierTyped subjectTyped
    constructorTyped equalityRead leafRead slot (fun equal => continuation fields valid equal.symm)
  refine ⟨leafType, ?_, inhabited⟩
  simpa only [resultEq, finalEq, propositionIndex] using leafRead

open Kernel.SetTheory in
/-- Arbitrary carrier values have original-constructor presentations, with
the exact dependent field typing derived above. This is the set-level
coverage conclusion of the admitted Church certificate. -/
theorem SourceCoverInstalledShape.constructor_presentation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {site : SourceProjectionSite source}
    {coverage : SourceConstructorCoverChecked installed site}
    (receipt : SourceCoverInstalledShape coverage) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ receipt.data.owner.type
      parameters (pushArguments ρ parameters) (.sort receipt.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app (model.cval (sourceName site.ownerName) levels)) :
    ∃ fields : SourceFieldValues site V,
      SourceCoverValidFields receipt model levels ρ parameters fields ∧
      originalConstructorValue site model.cval levels parameters fields = subject :=
  (semanticConstructorCover_iff _ _ subject).mp
    (receipt.semantic_cover model levels ρ parameters parameterCount parameterTyping subject subjectTyped)

/-- Full installed projection and equation data. Raw source provenance remains
in `SourceProjectionReceipt`; these fields retain the actual annotated types. -/
structure SourceProjectionInstalledData where
  projection : Kernel.ConstantVal
  value : Kernel.Expr
  hint : Kernel.ReducibilityHint
  rawEquation : Kernel.ConstantVal
  equation : Kernel.ConstantVal
  proof : Kernel.Expr
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  fields : List (Kernel.Expr × Kernel.BinderMeta)
  carrier : Kernel.Expr
  left : Kernel.Expr
  right : Kernel.Expr

def SourceProjectionInstalledShape {source : Source} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    (constructor : SourceCoverShapeData) (data : SourceProjectionInstalledData) : Prop :=
  equation = .thmDecl data.rawEquation data.proof ∧
  data.rawEquation.name = projection.header.name.str "_source_constructor_equation" ∧
  data.equation.name = data.rawEquation.name ∧
  data.equation.levelParams = data.rawEquation.levelParams ∧
  data.rawEquation.levelParams = projection.header.levelParams ∧
  data.projection.name = projection.header.name ∧
  data.projection.levelParams = projection.header.levelParams ∧
  data.hint = projection.hint ∧
  constructor.constructor.levelParams = data.projection.levelParams ∧
  data.parameters.map Prod.fst = constructor.parameters.map Prod.fst ∧
  data.fields.map Prod.fst = constructor.fields.map Prod.fst ∧
  data.equation.type = sourceForalls data.parameters (sourceForalls data.fields
    (.app (.app (.app (.const Kernel.eqName [projection.level]) data.carrier) data.left) data.right)) ∧
  data.left = Kernel.Expr.mkAppN
    (.const data.projection.name (data.projection.levelParams.map Kernel.Level.param))
    (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields ++
      [Kernel.Expr.mkAppN
        (.const constructor.constructor.name (data.projection.levelParams.map Kernel.Level.param))
        (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields ++
          sourceParameterVars projection.site.ctor.numFields 0)]) ∧
  data.right = .bvar (projection.site.ctor.numFields - 1 - projection.site.field)

instance {source : Source} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    (constructor : SourceCoverShapeData) (data : SourceProjectionInstalledData) :
    Decidable (SourceProjectionInstalledShape projection constructor data) := by
  unfold SourceProjectionInstalledShape
  infer_instance

/-- Links an immutable original projection, its submitted equation and the
actual independently installed annotated entries. No equality between raw and
annotated bodies is assumed. The full constructor/owner receipt stays attached. -/
structure SourceProjectionInstalled {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    {coverage : SourceConstructorCoverChecked installed projection.site}
    (constructor : SourceCoverInstalledShape coverage) where
  data : SourceProjectionInstalledData
  replacement_present : replacement ∈ installed.declarations
  equation_present : equation ∈ installed.declarations
  projectionLookup : coverage.env.find? projection.header.name =
    some (.defnInfo data.projection data.value data.hint)
  equationLookup : coverage.env.find? data.rawEquation.name =
    some (.thmInfo data.equation data.proof)
  shape : SourceProjectionInstalledShape projection constructor.data data

def checkSourceProjectionInstalled {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    (projection : SourceProjectionReceipt source original replacement equation)
    {coverage : SourceConstructorCoverChecked installed projection.site}
    (constructor : SourceCoverInstalledShape coverage) :
    Except String (SourceProjectionInstalled projection constructor) := do
  let .thmDecl rawEquation proof := equation
    | throw "source projection equation is not a submitted theorem"
  let some (.defnInfo projectionHeader value hint) ← pure (coverage.env.find? projection.header.name)
    | throw "installed source projection is missing or has wrong kind"
  let some (.thmInfo equationHeader _) ← pure (coverage.env.find? rawEquation.name)
    | throw "installed source projection equation is missing or has wrong kind"
  let some (parameters, body) := equationHeader.type.stripPis projection.site.owner.numParams
    | throw "installed source projection equation parameter telescope is short"
  let some (fields, .app (.app (.app (.const _ _) carrier) left) right) :=
      body.stripPis projection.site.ctor.numFields
    | throw "installed source projection equation lacks its exact field/equality telescope"
  let data : SourceProjectionInstalledData :=
    ⟨projectionHeader, value, hint, rawEquation, equationHeader, proof, parameters, fields, carrier, left, right⟩
  if hr : replacement ∈ installed.declarations then
    if he : equation ∈ installed.declarations then
      if hp : coverage.env.find? projection.header.name =
          some (.defnInfo data.projection data.value data.hint) then
        if hq : coverage.env.find? data.rawEquation.name = some (.thmInfo data.equation data.proof) then
          if hs : SourceProjectionInstalledShape projection constructor.data data then
            return ⟨data, hr, he, hp, hq, hs⟩
          else throw "installed source projection equation differs from its original field/constructor shape"
        else throw "installed source projection equation proof differs from the submitted proof"
      else throw "installed source projection lookup changed"
    else throw "source projection equation is absent from the independently checked stream"
  else throw "source projection replacement is absent from the independently checked stream"

open Kernel.SetTheory in
/-- The checked equation uses exactly the original dependent constructor
domains, while retaining its own actual enclosing binder regimes. -/
theorem SourceProjectionInstalled.typed_equation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (fields : SourceFieldValues projection.site V)
    (valid : SourceCoverValidFields constructor model levels ρ parameters fields) :
    InstalledTelescope model.cval coverage.env levels ρ receipt.data.equation.type
      (parameters ++ fields.val) (pushArguments (pushArguments ρ parameters) fields.val)
      (.app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
        receipt.data.left) receipt.data.right) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, parameterDomains, fieldDomains, equationType, _, _⟩
  rcases constructor.shape with ⟨_, _, _, _, _, _, parameterLength, fieldLength, _, _, _, ownerType, _⟩
  rw [ownerType] at parameterTyping
  have parameterTuple := (sourceForalls_transfer (targetBody := sourceForalls receipt.data.fields
    (.app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
      receipt.data.left) receipt.data.right)) parameterDomains.symm
      (parameterCount.trans parameterLength.symm) parameterTyping).2
  have fieldTuple := (sourceForalls_transfer (targetBody :=
    .app (.app (.app (.const Kernel.eqName [projection.level]) receipt.data.carrier)
      receipt.data.left) receipt.data.right) fieldDomains.symm
      (fields.property.trans fieldLength.symm) valid).2
  rw [equationType]
  exact parameterTuple.append fieldTuple

open Kernel.SetTheory in
theorem SourceProjectionInstalled.left_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (fields : SourceFieldValues projection.site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.left
      (app (parameters.foldl app (model.cval projection.header.name levels))
        (originalConstructorValue projection.site model.cval levels parameters fields)) := by
  rcases receipt.shape with ⟨_, _, _, _, _, projectionName, _, _, levelNames, _, _, _, leftShape, _⟩
  let frame := pushArguments (pushArguments ρ parameters) fields.val
  have parameterSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars projection.site.owner.numParams projection.site.ctor.numFields) parameters := by
    simpa only [parameterCount, fields.property, frame] using
      (sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
        (levels := levels) ρ parameters fields.val)
  have fieldSpine : DenotesSpine model.cval coverage.env levels frame
      (sourceParameterVars projection.site.ctor.numFields 0) fields.val := by
    simpa only [List.length_nil, pushArguments, fields.property, frame] using
      (sourceParameterVars_pushed (values := model.cval) (env := coverage.env)
        (levels := levels) (pushArguments ρ parameters) fields.val [])
  have projectionRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) receipt.projectionLookup
  have constructorRead := denotes_self_instance (values := model.cval) (levels := levels)
    (ρ := frame) constructor.constructorLookup
  simp only [Kernel.ConstantInfo.toConstantVal] at projectionRead constructorRead
  rw [← projectionName] at projectionRead
  have constructorName := constructor.shape.2.1
  rw [← constructorName, levelNames] at constructorRead
  have constructorApp := denotes_mkAppN constructorRead (parameterSpine.append fieldSpine)
  have application := Kernel.Denotes.app (denotes_mkAppN projectionRead parameterSpine) constructorApp
  rw [leftShape]
  simpa only [Kernel.Expr.mkAppN_append_one, List.foldl_append, List.foldl_cons, List.foldl_nil,
    originalConstructorValue, projectionName, constructorName, frame] using application

theorem SourceProjectionInstalled.right_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) (parameters : List V)
    (fields : SourceFieldValues projection.site V) :
    Kernel.Denotes model.cval coverage.env levels
      (pushArguments (pushArguments ρ parameters) fields.val) receipt.data.right
      (originalSelectedField projection.site fields) := by
  rcases receipt.shape with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rightShape⟩
  rw [rightShape]
  have inside : projection.site.field < fields.val.length := by
    rw [fields.property]
    exact projection.site.shape.2.2.2.2.2
  have slot := pushArguments_get fields.val (pushArguments ρ parameters) projection.site.field inside
  rw [fields.property] at slot
  unfold originalSelectedField
  rw [← slot]
  exact .bvar

open Kernel.SetTheory in
/-- Actual semantic constructor computation, obtained from the independently
admitted equation and its installed grading. The equality is for all typed
original dependent fields, not merely closed fixtures or syntactic reduction. -/
theorem SourceProjectionInstalled.constructor_computation {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (fields : SourceFieldValues projection.site V)
    (valid : SourceCoverValidFields constructor strong.public levels ρ parameters fields) :
    app (parameters.foldl app (strong.public.cval projection.header.name levels))
      (originalConstructorValue projection.site strong.public.cval levels parameters fields) =
        originalSelectedField projection.site fields :=
  strong.theorem_eq receipt.data.equation receipt.data.proof
    (List.mem_of_find?_eq_some receipt.equationLookup)
    (receipt.typed_equation strong.public levels ρ parameters parameterCount parameterTyping fields valid)
    (receipt.left_denotes strong.public levels ρ parameters parameterCount fields)
    (receipt.right_denotes strong.public levels ρ parameters fields)

open Kernel.SetTheory in
/-- Arbitrary original carrier members, with both semantic coverage and
constructor computation discharged by their actual installed certificates. -/
theorem SourceProjectionInstalled.arbitrary_value {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (subject : V)
    (subjectTyped : subject ∈ˢ parameters.foldl app
      (strong.public.cval (sourceName projection.site.ownerName) levels)) :
    OriginalProjectionValue projection.site strong.public.cval levels parameters
      (SourceCoverValidFields constructor strong.public levels ρ parameters) subject
      (app (parameters.foldl app (strong.public.cval projection.header.name levels)) subject) ∧
    ∀ value, OriginalProjectionValue projection.site strong.public.cval levels parameters
      (SourceCoverValidFields constructor strong.public levels ρ parameters) subject value →
      value = app (parameters.foldl app (strong.public.cval projection.header.name levels)) subject :=
  original_projection_extensional projection.site strong.public.cval levels parameters
    (SourceCoverValidFields constructor strong.public levels ρ parameters)
    (parameters.foldl app (strong.public.cval (sourceName projection.site.ownerName) levels))
    (parameters.foldl app (strong.public.cval projection.header.name levels))
    (constructor.semantic_cover strong.public levels ρ parameters parameterCount parameterTyping)
    (receipt.constructor_computation strong levels ρ parameters parameterCount parameterTyping)
    subject subjectTyped

/-- The semantic value used in `arbitrary_value` is the denotation of the
actual installed annotated definition body. This is a source-owned lowering
pull-back, not an equality between the raw nested Kernel projection fallback
and the normalized term. Original syntax/provenance stays in `projection`. -/
theorem SourceProjectionInstalled.definition_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    Kernel.Denotes strong.public.cval coverage.env levels ρ receipt.data.value
      (strong.public.cval projection.header.name levels) := by
  have projectionName := receipt.shape.2.2.2.2.2.1
  have read := strong.definition_values receipt.data.projection receipt.data.value receipt.data.hint
    (List.mem_of_find?_eq_some receipt.projectionLookup) levels ρ
  simpa only [StrongInstalledModel.public, projectionName] using read

/-- The precise raw replacement-to-installed annotation calls behind the
projection value theorem. This is the source installation, including the
coverage extension, not target `projRewrite` or an unrelated annotation run. -/
theorem SourceProjectionInstalled.annotation
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (ordinary : (Kernel.natOpNames.contains projection.header.name ||
      Kernel.natDivModNames.contains projection.header.name) = false) :
    receipt.data.projection = { projection.header with type := receipt.data.projection.type } ∧
    receipt.data.hint = projection.hint ∧
    ∃ before : Kernel.FEnv, ∃ initial afterType beforeValue afterValue : Kernel.Cached.CState,
      (Kernel.Cached.coreKnotI .verified before Kernel.checkFuel).annotate 0
        projection.header.type initial.flushed = .ok (receipt.data.projection.type, afterType) ∧
      Kernel.Cached.annotConstantValC .verified before projection.header initial.flushed =
        .ok ((receipt.data.projection, receipt.data.projection.type), beforeValue) ∧
      (Kernel.Cached.coreKnotI .verified before Kernel.checkFuel).annotate 0
        projection.value beforeValue = .ok (receipt.data.value, afterValue) := by
  have present := receipt.replacement_present
  rw [projection.replacement_decl] at present
  have inExtended : Kernel.Declaration.defnDecl projection.header projection.value projection.hint ∈
      (installed.declarations ++ [Kernel.Declaration.thmDecl coverage.header coverage.value]).toArray := by
    simpa using List.mem_append_left [Kernel.Declaration.thmDecl coverage.header coverage.value] present
  exact (AnnotationTrace.definition_checked ordinary inExtended coverage.checked).exact
    (AnnotationTrace.checked_unique_names coverage.checked) receipt.projectionLookup

/-- The unconditional version also records primitive checking paths should
an original source identity select one. No domain exclusion is needed. -/
theorem SourceProjectionInstalled.annotation_all
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) :
    receipt.data.projection = { projection.header with type := receipt.data.projection.type } ∧
    receipt.data.hint = projection.hint ∧
    ∃ before : Kernel.FEnv, ∃ initial : Kernel.Cached.CState,
      AnnotationTrace.ValueAnnotationCalls .verified before projection.header projection.value initial
        receipt.data.projection.type receipt.data.value := by
  have present := receipt.replacement_present
  rw [projection.replacement_decl] at present
  have inExtended : Kernel.Declaration.defnDecl projection.header projection.value projection.hint ∈
      (installed.declarations ++ [Kernel.Declaration.thmDecl coverage.header coverage.value]).toArray := by
    simpa using List.mem_append_left [Kernel.Declaration.thmDecl coverage.header coverage.value] present
  exact (AnnotationTrace.definition_all_checked inExtended coverage.checked).exact
    (AnnotationTrace.checked_unique_names coverage.checked) receipt.projectionLookup

/-- Actual projection function telescope. Its regime is read from the
installed binder; agreement with a separately annotated endpoint is not
silently included in this receipt. -/
structure SourceProjectionFunctionData where
  parameters : List (Kernel.Expr × Kernel.BinderMeta)
  result : Kernel.Expr
  binder : Kernel.BinderMeta

def SourceProjectionFunctionShape {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (data : SourceProjectionFunctionData) : Prop :=
  data.parameters.map Prod.fst = constructor.data.parameters.map Prod.fst ∧
  receipt.data.projection.type = sourceForalls data.parameters
    (.forallE (Kernel.Expr.mkAppN (.const constructor.data.owner.name
      (constructor.data.owner.levelParams.map Kernel.Level.param))
      (sourceParameterVars projection.site.owner.numParams 0)) data.result data.binder)

instance {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor)
    (data : SourceProjectionFunctionData) : Decidable (SourceProjectionFunctionShape receipt data) := by
  unfold SourceProjectionFunctionShape
  infer_instance

structure SourceProjectionFunction {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) where
  data : SourceProjectionFunctionData
  shape : SourceProjectionFunctionShape receipt data

def checkSourceProjectionFunction {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    (receipt : SourceProjectionInstalled projection constructor) :
    Except String (SourceProjectionFunction receipt) := do
  let some (parameters, .forallE _ result binder) :=
      receipt.data.projection.type.stripPis projection.site.owner.numParams
    | throw "installed source projection function has no exact subject telescope"
  let data : SourceProjectionFunctionData := ⟨parameters, result, binder⟩
  if checked : SourceProjectionFunctionShape receipt data then return ⟨data, checked⟩
  else throw "installed source projection function domain differs from original carrier"

open Kernel.SetTheory in
/-- Both the function membership and codomain reading come from the actual
installed type after its typed original parameters are supplied. -/
theorem SourceProjectionFunction.typed {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (model : Kernel.Model V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope model.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    ∃ codomain : V → V,
      parameters.foldl app (model.cval projection.header.name levels) ∈ˢ
        Kernel.SetModel.piR (Kernel.regime levels function.data.binder.pw)
          (parameters.foldl app (model.cval (sourceName projection.site.ownerName) levels)) codomain ∧
      ∀ subject, subject ∈ˢ parameters.foldl app
        (model.cval (sourceName projection.site.ownerName) levels) →
        Kernel.Denotes model.cval coverage.env levels (Kernel.push subject (pushArguments ρ parameters))
          function.data.result (codomain subject) := by
  rcases constructor.shape with ⟨_, _, _, _, _, _, parameterLength, _, _, _, _, ownerType, _⟩
  rw [ownerType] at parameterTyping
  have transferred := (sourceForalls_transfer (targetBody := .forallE
    (Kernel.Expr.mkAppN (.const constructor.data.owner.name
      (constructor.data.owner.levelParams.map Kernel.Level.param))
      (sourceParameterVars projection.site.owner.numParams 0)) function.data.result function.data.binder)
    function.shape.1.symm
    (parameterCount.trans parameterLength.symm) parameterTyping).2
  rw [← function.shape.2] at transferred
  obtain ⟨type, read, member⟩ := transferred.model_apply model
    (List.mem_of_find?_eq_some receipt.projectionLookup)
  have domainRead := constructor.carrier_denotes model levels ρ parameters parameterCount []
  simp only [List.length_nil, pushArguments] at domainRead
  cases read with
  | pi actualDomain bodyRead regimeTyped =>
    obtain rfl := Kernel.Denotes_functional actualDomain domainRead
    refine ⟨_, ?_, bodyRead⟩
    have projectionName := receipt.shape.2.2.2.2.2.1
    simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, projectionName] using member

open Kernel.SetTheory in
/-- Full function-value equality with the independent original-field selector.
The exact installed regime is retained. Independent source/target annotation
agreement remains a separate obligation of the wider semantic simulation. -/
theorem SourceProjectionFunction.value_eq {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level)) :
    parameters.foldl app (strong.public.cval projection.header.name levels) =
      Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl app (strong.public.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site strong.public.cval levels parameters
          (SourceCoverValidFields constructor strong.public levels ρ parameters)) := by
  obtain ⟨codomain, typed, _⟩ := function.typed strong.public levels ρ parameters parameterCount parameterTyping
  rw [← Kernel.SetModel.lamR_eta typed]
  apply Kernel.SetModel.lamR_congr
  intro subject subjectTyped
  have presented := constructor.constructor_presentation strong.public levels ρ parameters
    parameterCount parameterTyping subject subjectTyped
  have selected := originalProjectionSelection_reading projection.site strong.public.cval levels
    parameters (SourceCoverValidFields constructor strong.public levels ρ parameters) subject presented
  exact ((receipt.arbitrary_value strong levels ρ parameters parameterCount parameterTyping
    subject subjectTyped).2 _ selected).symm

/-- Pull back the actual annotated definition body, including a denoting
parameter application spine, to the source-only function interpretation.
This avoids replacing a body equation with a mere name/type coincidence. -/
theorem SourceProjectionFunction.body_application_denotes {V : Type u} [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name}
    {installed : SourceNormalizedInstallation source roots} {original replacement equation}
    {projection : SourceProjectionReceipt source original replacement equation}
    {coverage : SourceConstructorCoverChecked installed projection.site}
    {constructor : SourceCoverInstalledShape coverage}
    {receipt : SourceProjectionInstalled projection constructor}
    (function : SourceProjectionFunction receipt) (strong : StrongInstalledModel V coverage.env)
    (levels : Kernel.Name → Nat) (ρ : Nat → V)
    (parameters : List V) (parameterCount : parameters.length = projection.site.owner.numParams)
    (parameterTyping : InstalledTelescope strong.public.cval coverage.env levels ρ constructor.data.owner.type
      parameters (pushArguments ρ parameters) (.sort constructor.data.level))
    (expressions : List Kernel.Expr)
    (parameterRead : DenotesSpine strong.public.cval coverage.env levels ρ expressions parameters) :
    Kernel.Denotes strong.public.cval coverage.env levels ρ
      (Kernel.Expr.mkAppN receipt.data.value expressions)
      (Kernel.SetModel.lamR (Kernel.regime levels function.data.binder.pw)
        (parameters.foldl Kernel.SetTheory.app (strong.public.cval (sourceName projection.site.ownerName) levels))
        (originalProjectionSelection projection.site strong.public.cval levels parameters
          (SourceCoverValidFields constructor strong.public levels ρ parameters))) := by
  have read := denotes_mkAppN (receipt.definition_denotes strong levels ρ) parameterRead
  rw [function.value_eq strong levels ρ parameters parameterCount parameterTyping] at read
  exact read

/-- Value denotation for the actually installed normalized definitions.
Original-source value correspondence is a separate semantic pull-back. -/
theorem SourceNormalizedInstallation.has_model_values (V : Type u) [Kernel.SetTheory V]
    {source : Source} {roots : List Lean.Name} (installed : SourceNormalizedInstallation source roots) :
    ∃ model : Kernel.Model V installed.env, ∀ header value hint,
      Kernel.ConstantInfo.defnInfo header value hint ∈ installed.env.consts →
        ∀ φ ρ, Kernel.Denotes model.cval installed.env φ ρ value (model.cval header.name φ) :=
  Kernel.Cached.checkDecls_model_defn_values V [] installed.declarations.toArray
    installed.env installed.checked

theorem SourceProjectionNormalization.member {source : Source} {state input output}
    (receipt : SourceProjectionNormalization source state input output)
    {declaration : Kernel.Declaration} (present : declaration ∈ input) :
    declaration ∈ output ∨ ∃ prior replacement equation,
      proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
      Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
      replacement ∈ output ∧ equation ∈ output := by
  induction receipt with
  | nil => simp at present
  | @unchanged state original rest output hp tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inl (by simp)
    · rcases ih present with same | ⟨prior, replacement, equation, hp, association, hr, he⟩
      · exact .inl (List.mem_cons_of_mem _ same)
      · exact .inr ⟨prior, replacement, equation, hp, association,
          List.mem_cons_of_mem _ hr, List.mem_cons_of_mem _ he⟩
  | @lowered state original rest replacement equation output hp association fresh tail ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact .inr ⟨state, replacement, equation, hp, ⟨association⟩, by simp, by simp⟩
    · rcases ih present with same | ⟨prior, next, law, hp, association, hr, he⟩
      · exact .inl (by simp only [List.mem_cons]; exact .inr (.inr same))
      · exact .inr ⟨prior, next, law, hp, association, by simp only [List.mem_cons]; exact .inr (.inr hr),
          by simp only [List.mem_cons]; exact .inr (.inr he)⟩

/-- Every original source entry is retained with its exact raw export,
then associated with either an unchanged checked declaration or the exact
source-owned replacement and checked equation. This does not substitute
the replacement for the original source expression in a semantic theorem. -/
theorem SourceNormalizedInstallation.member {source : Source} {roots : List Lean.Name}
    (installed : SourceNormalizedInstallation source roots) {ci : Lean.ConstantInfo}
    (present : ci ∈ source.declarations) :
    ∃ entry declaration, exportSourceEntry ci = .ok entry ∧ entry ∈ readerEntries declaration ∧
      (declaration ∈ installed.declarations ∨ ∃ prior replacement equation,
        proposeSourceProjection source prior declaration = .ok (some (replacement, equation)) ∧
        Nonempty (SourceProjectionReceipt source declaration replacement equation) ∧
        replacement ∈ installed.declarations ∧ equation ∈ installed.declarations) := by
  have matched := installed.original_members ci present
  cases he : exportSourceEntry ci with
  | error reason => simp [SourceEntryMatches, he] at matched
  | ok entry =>
    have hm : entry ∈ installed.modelProposal.declarations.toList.flatMap readerEntries := by
      simpa only [SourceEntryMatches, he, streamEntries] using matched
    obtain ⟨declaration, hd, hm⟩ := List.mem_flatMap.mp hm
    have retained : ∀ declaration ∈ installed.normalizedDeclarations,
        declaration ∈ installed.declarations := by
      intro declaration present
      rw [installed.semantic_append]
      exact List.mem_append_left _ present
    refine ⟨entry, declaration, rfl, hm, ?_⟩
    rcases installed.normalization.member hd with present | ⟨prior, replacement, equation, hp, receipt, hr, he⟩
    · exact .inl (retained _ present)
    · exact .inr ⟨prior, replacement, equation, hp, receipt, retained _ hr, retained _ he⟩

end Ix.CompileCert
