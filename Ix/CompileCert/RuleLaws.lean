import Ix.CompileCert.Installed

/-! # Rule and capability laws

Installed unit, eta and capability laws (`checkInstalledCapabilities`,
`PublicCapabilityLaws`), installed rule frames and rule-tuple
representations, the checked and universal recursor-rule simulations
(`checked_rules_simulation`, `checked_universal_rules`) and the
universe-level links they need.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission

open Kernel.Semantics Kernel.Model Kernel.Model.Rules in
/-- The value-level telescope required by installed capability laws follows
from the actual application and a stored syntactic Pi prefix. An arbitrary
substitution-created Pi is not treated as evidence of that prefix. -/
theorem AnnotatedApplication.installed_value_fit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (constant : Kernel.ConstantInfo)
    (lookup : env.find? name = some constant) (termEntry : constant.isTowerEntry = false)
    (universes : List Kernel.Level) (arity : universes.length = constant.toConstantVal.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes)
      expressions annotations residual)
    (piPrefix : (constant.toConstantVal.type.stripPis annotations.length).isSome = true) :
    ∃ typeAnnotation result,
      denoteMeta strong.internal.base2.acval env levels 0
        (constant.toConstantVal.type.instantiateLevelParams constant.toConstantVal.levelParams universes) =
          some typeAnnotation ∧
      TeleFit V ρ typeAnnotation (annotations.map (interp V ρ)) result := by
  obtain ⟨typeAnnotation, result, reading, fit, _⟩ :=
    application.installed_fit name constant lookup termEntry universes arity
  exact ⟨typeAnnotation, interp V ρ result, reading,
    teleFit_of_teleFitPA (piChain_of_stripPis annotations.length
      (Kernel.Expr.stripPis_instantiateLevelParams_isSome
        constant.toConstantVal.levelParams universes annotations.length piPrefix) reading) fit⟩

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Fire the actual installed non-basis unit capability using the checked
application. Both the Pi piPrefix and the capability law come from the same
installed model; neither a Boolean claim nor a length equality supplies the
typed telescope. Reserved basis families have separate laws. -/
theorem AnnotatedApplication.installed_unit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (caps : Kernel.IndCaps)
    (lookup : env.find? name = some (.indInfo header caps))
    (enabled : caps.unitlike = true) (nonbasis : Kernel.reservedBasisNames.contains name = false)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (count : annotations.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes))))
    (right : y ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes)))) :
    x = y := by
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have piPrefix : (header.type.stripPis annotations.length).isSome = true := by
    rw [count]
    exact (wf.2.2.2.2.2.2.2 header caps rfl).1 enabled
  obtain ⟨typeAnnotation, result, reading, fit⟩ :=
    application.installed_value_fit name (.indInfo header caps) lookup rfl universes arity piPrefix
  obtain ⟨lawAnnotation, lawReading, _, law⟩ :=
    strong.internal.caps_ok.2 name header caps lookup enabled nonbasis levels universes arity
  have same : typeAnnotation = lawAnnotation := Option.some.inj (reading.symm.trans lawReading)
  subst lawAnnotation
  exact law ρ (annotations.map (interp V ρ)) result x y (by simpa using count) fit left right

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The structural eta equation at the same installed family's actual
parameter application. The stored family/constructor/projection capability
association remains explicit; target content aliases do not establish it. -/
theorem AnnotatedApplication.installed_eta {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (caps : Kernel.IndCaps)
    (lookup : env.find? name = some (.indInfo header caps))
    (enabled : caps.eta = true) (nonbasis : Kernel.reservedBasisNames.contains name = false)
    (stored : Kernel.EtaFamilyStored env name caps)
    (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (count : annotations.length = caps.etaParams) (x : V)
    (member : x ∈ˢ (annotations.map (interp V ρ)).foldl app
      (interp V ρ (strong.internal.base2.acval name (Kernel.Level.substFn levels header.levelParams universes)))) :
    x = (etaFabArgsV
      (fun n => interp V ρ (strong.internal.base2.acval n
        (Kernel.Level.substFn levels header.levelParams universes)))
      name (annotations.map (interp V ρ)) x caps.etaFields).foldl app
      (interp V ρ (strong.internal.base2.acval caps.etaCtor
        (Kernel.Level.substFn levels header.levelParams universes))) := by
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have piPrefix : (header.type.stripPis annotations.length).isSome = true := by
    rw [count]
    exact (wf.2.2.2.2.2.2.2 header caps rfl).2 enabled
  obtain ⟨typeAnnotation, result, reading, fit⟩ :=
    application.installed_value_fit name (.indInfo header caps) lookup rfl universes arity piPrefix
  obtain ⟨lawAnnotation, lawReading, _, law⟩ :=
    strong.internal.caps_ok.1 name header caps lookup enabled nonbasis stored levels universes arity
  have same : typeAnnotation = lawAnnotation := Option.some.inj (reading.symm.trans lawReading)
  subst lawAnnotation
  exact law ρ (annotations.map (interp V ρ)) result x (by simpa using count) fit member

/-- Check the exact stored constructor/projection presence required by the
eta law. This does not establish cross-environment semantic correspondence. -/
def checkInstalledEtaFamily (env : Kernel.Env) (name : Kernel.Name) (caps : Kernel.IndCaps) : Bool :=
  !Kernel.reservedBasisNames.contains caps.etaCtor &&
  (match env.find? caps.etaCtor with | some (.ctorInfo ..) => true | _ => false) &&
  (List.range caps.etaFields).all fun index =>
    match env.find? (Kernel.projFnName name index) with
    | some (.recInfo ..) => true
    | _ => false

theorem checkInstalledEtaFamily_sound {env : Kernel.Env} {name : Kernel.Name} {caps : Kernel.IndCaps}
    (checked : checkInstalledEtaFamily env name caps = true) : Kernel.EtaFamilyStored env name caps := by
  simp only [checkInstalledEtaFamily, Bool.and_eq_true] at checked
  obtain ⟨⟨nonbasis, constructor⟩, projections⟩ := checked
  refine ⟨by simpa using nonbasis, ?_, ?_⟩
  · cases found : env.find? caps.etaCtor with
    | none => simp [found] at constructor
    | some entry =>
      cases entry <;> simp [found] at constructor
      case ctorInfo header params fields => exact ⟨header, params, fields, rfl⟩
  · intro index bound
    have row := List.all_eq_true.mp projections index (List.mem_range.mpr bound)
    cases found : env.find? (Kernel.projFnName name index) with
    | none => simp [found] at row
    | some entry =>
      cases entry <;> simp [found] at row
      case recInfo header major params rules => exact ⟨header, major, params, rules, rfl⟩

/-- All stored capability fields remain visible. The constructor and indexed
projection-name images are required when eta actually uses them. The sort
datum is compared semantically in the owner's universe telescope below. -/
def InstalledCapsHeader (names : Kernel.Name → Kernel.Name) (owner : Kernel.Name)
    (source target : Kernel.IndCaps) : Prop :=
  source.eta = target.eta ∧ source.unitlike = target.unitlike ∧ source.ruleK = target.ruleK ∧
  source.etaParams = target.etaParams ∧ source.etaFields = target.etaFields ∧
  source.unitParams = target.unitParams ∧
  (source.eta = true → target.etaCtor = names source.etaCtor ∧
    ∀ index ∈ List.range source.etaFields,
      names (Kernel.projFnName owner index) = Kernel.projFnName (names owner) index)

instance (names : Kernel.Name → Kernel.Name) (owner : Kernel.Name)
    (source target : Kernel.IndCaps) : Decidable (InstalledCapsHeader names owner source target) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Reuse the proved binder-regime comparison for the capability's exact
sort datum. This carrier expression is not claimed to be a stored type. -/
def capabilityDatumExpr (caps : Kernel.IndCaps) : Kernel.Expr :=
  .forallE (.sort .zero) (.sort .zero) ⟨caps.sortZ⟩

def checkInstalledCapabilities (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .indInfo header caps =>
      decide (source.find? header.name = some entry) &&
      match target.find? (names header.name) with
      | some (.indInfo _ targetCaps) =>
        decide (InstalledCapsHeader names header.name caps targetCaps) &&
        decide (checkInstalledMemberExpr source target names header.name
          (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps) = some true)
      | _ => false
    | _ => true

theorem checkInstalledCapabilities_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledCapabilities source target names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ source.consts) :
    source.find? header.name = some (.indInfo header caps) ∧
    ∃ targetHeader targetCaps,
      target.find? (names header.name) = some (.indInfo targetHeader targetCaps) ∧
      InstalledCapsHeader names header.name caps targetCaps ∧
      checkInstalledMemberExpr source target names header.name
        (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps) = some true := by
  have row := List.all_eq_true.mp checked (.indInfo header caps) present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names header.name) with
  | none => simp [lookup] at row
  | some entry =>
    cases entry <;> simp only [lookup, Bool.and_eq_true, decide_eq_true_eq] at row
    case indInfo targetHeader targetCaps => exact ⟨targetHeader, targetCaps, rfl, row.2⟩
    all_goals simp at row

theorem checkInstalledCapabilities_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts) :
    ∃ targetHeader targetCaps,
      targetEnv.find? (names header.name) = some (.indInfo targetHeader targetCaps) ∧
      InstalledCapsHeader names header.name caps targetCaps ∧
      ∀ levels, Kernel.regime levels caps.sortZ = Kernel.regime
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) targetCaps.sortZ := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, headers, compared⟩ :=
    checkInstalledCapabilities_member checked present
  refine ⟨targetHeader, targetCaps, targetLookup, headers, ?_⟩
  intro levels
  have image := checkInstalledMemberExpr_sound target association sourceLookup compared levels
  cases image with
  | forallE _ _ regimes => exact regimes

/-- The reserved unit-capable family is determined by the actual pinned
declaration table, not by an arbitrary name or capability assertion. -/
theorem StrongInstalledModel.reserved_unit_name {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.unitlike = true) : name = Kernel.punitName := by
  have pinned := (strong.internal.base2.basis_pinned name _ lookup reserved).1
  have table : Kernel.reservedBasisNames.all (fun n => match Kernel.pinnedInfo n with
      | .indInfo _ c => !c.unitlike || decide (n = Kernel.punitName)
      | _ => true) = true := by decide
  have member : name ∈ Kernel.reservedBasisNames := by simpa using reserved
  have row := List.all_eq_true.mp table name member
  rw [← pinned] at row
  simpa [enabled] using row

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
theorem StrongInstalledModel.punit_value {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.punitName = some Kernel.punitA)
    (levels : Kernel.Name → Nat) : strong.public.cval Kernel.punitName levels = (unitSet : V) := by
  have pinned : strong.internal.base2.cvalE Kernel.punitName levels =
      Kernel.Term.punitT (levels Kernel.uN) :=
    (strong.internal.base2.basis_pinned Kernel.punitName _ lookup (by decide)).2 _ levels rfl
  have leaf : strong.internal.base2.acval Kernel.punitName levels = .const .punit [levels Kernel.uN] :=
    erase_eq_const (by rw [strong.internal.base2.acval_erase, pinned]; rfl)
  change interp V (fun _ => empty) (strong.internal.base2.acval Kernel.punitName levels) = unitSet
  rw [leaf, interp_const]
  rfl

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The reserved branch of the unit law, with its zero parameter count
derived from the pinned installed record. -/
theorem StrongInstalledModel.reserved_unit {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.unitlike = true) (levels : Kernel.Name → Nat)
    (values : List V) (count : values.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ values.foldl app (strong.public.cval name levels))
    (right : y ∈ˢ values.foldl app (strong.public.cval name levels)) : x = y := by
  have named := strong.reserved_unit_name lookup reserved enabled
  subst name
  have pinned := (strong.internal.base2.basis_pinned Kernel.punitName _ lookup reserved).1
  have found : env.find? Kernel.punitName = some Kernel.punitA := by
    simpa only [pinned, show Kernel.pinnedInfo Kernel.punitName = Kernel.punitA from rfl] using lookup
  have zero : caps.unitParams = 0 := by
    have h := congrArg (fun entry => match entry with | .indInfo _ c => c.unitParams | _ => 0) pinned
    exact h
  have nil : values = [] := by simpa using count.trans zero
  rw [nil, List.foldl_nil, strong.punit_value found levels] at left right
  exact (mem_unitSet left).trans (mem_unitSet right).symm
open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Source-side unit law for the target-derived interpretation. Installed
type/capability checks and the source typed application assemble the actual
target application; no target telescope or member equality is assumed.
Reserved families use the pinned PUnit law; other families use their stored
unit capability. No reserved-family exclusion is imposed. -/
theorem checked_unit_pullback {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.unitlike = true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    {depth : Nat} {ρ : Nat → V} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceExpressions : List Kernel.Expr} {values : List V} {sourceResidual : Kernel.Expr}
    (application : DenotedApplication
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels ρ (header.type.instantiateLevelParams header.levelParams sourceUs)
      sourceExpressions values sourceResidual)
    (argumentImages : InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth)))
    (count : values.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs)))
    (right : y ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))) : x = y := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, capHeader, _⟩ :=
    checkInstalledCapabilities_member capabilities present
  obtain ⟨associated, associatedLookup, telescope⟩ := association _ _ sourceLookup
  have same := Option.some.inj (associatedLookup.symm.trans targetLookup)
  subst associated
  have targetArity : targetUs.length = targetHeader.levelParams.length := by
    have equalLengths := congrArg List.length universes
    simp only [List.length_map] at equalLengths
    exact equalLengths.symm.trans (sourceArity.trans telescope.2.2)
  obtain ⟨residual, targetApplication, _⟩ := AnnotatedApplication.from_checked_type target association types
    present targetLookup sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
    readings application argumentImages
  have equalValues := (application.arguments.image argumentImages).functional readings.denotes
  have equalFamily :
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs) =
      target.public.cval (names header.name) (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs) := by
    apply target.value_params targetLookup
    exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity universes
  have targetEnabled : targetCaps.unitlike = true := capHeader.2.1.symm.trans enabled
  have targetCount : annotations.length = targetCaps.unitParams := by
    rw [equalValues, List.length_map] at count
    exact count.trans capHeader.2.2.2.2.2.1
  rw [equalValues, equalFamily] at left right
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · exact target.reserved_unit targetLookup reserved targetEnabled
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs)
      (annotations.map (interp V ρ)) (by simpa using targetCount) x y left right
  · have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by
      simpa using reserved
    apply targetApplication.installed_unit (names header.name) targetHeader targetCaps targetLookup
      targetEnabled nonbasis targetUs targetArity targetCount x y
    · simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using left
    · simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using right


/-- Compare a helper's own universe instance inside its family's telescope.
Eta evaluates constructor/projection leaves at that family assignment, not
at an independently chosen helper assignment. Target coverage permits the
proved family-instance locality step; no ambient valuation equality is used. -/
def checkInstalledFamilyMember (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (owner member : Kernel.Name) : Option Bool :=
  match source.find? member, target.find? (names member), target.find? (names owner) with
  | some sourceMember, some targetMember, some targetOwner =>
    if targetMember.toConstantVal.levelParams.all
        (fun parameter => targetOwner.toConstantVal.levelParams.contains parameter) then
      checkInstalledMemberExpr source target names owner
        (.const member (sourceMember.toConstantVal.levelParams.map Kernel.Level.param))
        (.const (names member) (targetMember.toConstantVal.levelParams.map Kernel.Level.param))
    else some false
  | _, _, _ => some false

theorem checkInstalledFamilyMember_lookups {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {owner member : Kernel.Name} {targetOwner : Kernel.ConstantInfo}
    (ownerLookup : target.find? (names owner) = some targetOwner)
    (checked : checkInstalledFamilyMember source target names owner member = some true) :
    ∃ sourceMember targetMember,
      source.find? member = some sourceMember ∧ target.find? (names member) = some targetMember ∧
      (∀ parameter ∈ targetMember.toConstantVal.levelParams, parameter ∈ targetOwner.toConstantVal.levelParams) ∧
      checkInstalledMemberExpr source target names owner
        (.const member (sourceMember.toConstantVal.levelParams.map Kernel.Level.param))
        (.const (names member) (targetMember.toConstantVal.levelParams.map Kernel.Level.param)) = some true := by
  cases sourceLookup : source.find? member with
  | none => simp [checkInstalledFamilyMember, sourceLookup] at checked
  | some sourceMember =>
    cases targetLookup : target.find? (names member) with
    | none => simp [checkInstalledFamilyMember, sourceLookup, targetLookup] at checked
    | some targetMember =>
      simp only [checkInstalledFamilyMember, sourceLookup, targetLookup, ownerLookup] at checked
      split at checked
      next coverage =>
        refine ⟨sourceMember, targetMember, rfl, rfl, ?_, checked⟩
        intro parameter present
        have row := List.all_eq_true.mp coverage parameter present
        simpa using row
      next => contradiction

/-- Accepted owner-relative helper comparison proves its actual value at
the concrete family universe instance. Helper aliases keep their own source
telescope and are never resolved by choosing a reverse representative. -/
theorem checkInstalledFamilyMember_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {owner member : Kernel.Name} {sourceOwner targetOwner : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? owner = some sourceOwner)
    (targetLookup : targetEnv.find? (names owner) = some targetOwner)
    (checked : checkInstalledFamilyMember sourceEnv targetEnv names owner member = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceOwner.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetOwner.toConstantVal.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval member
      (Kernel.Level.substFn sourceLevels sourceOwner.toConstantVal.levelParams sourceUs) =
    target.public.cval (names member)
      (Kernel.Level.substFn targetLevels targetOwner.toConstantVal.levelParams targetUs) := by
  obtain ⟨sourceMember, targetMember, sourceMemberLookup, targetMemberLookup, coverage, compared⟩ :=
    checkInstalledFamilyMember_lookups targetLookup checked
  let sourceInstance := Kernel.Level.substFn sourceLevels sourceOwner.toConstantVal.levelParams sourceUs
  have image := checkInstalledMemberExpr_sound target association sourceLookup compared sourceInstance
  have direct : (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval member sourceInstance =
      target.public.cval (names member)
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels owner sourceInstance) := by
    have sourceRead := denotes_self_instance (V := V)
      (values := (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      (levels := sourceInstance) (ρ := fun _ => Kernel.SetTheory.empty) sourceMemberLookup
    exact Kernel.Denotes_functional (image.denotes sourceRead) (denotes_self_instance targetMemberLookup)
  apply direct.trans
  apply target.value_params targetMemberLookup
  intro parameter present
  exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
    sourceUs targetUs sourceArity targetArity universes parameter (coverage parameter present)

theorem StrongInstalledModel.reserved_eta_name {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.eta = true) : name = Kernel.punitName := by
  have pinned := (strong.internal.base2.basis_pinned name _ lookup reserved).1
  have table : Kernel.reservedBasisNames.all (fun n => match Kernel.pinnedInfo n with
      | .indInfo _ c => !c.eta || decide (n = Kernel.punitName)
      | _ => true) = true := by decide
  have member : name ∈ Kernel.reservedBasisNames := by simpa using reserved
  have row := List.all_eq_true.mp table name member
  rw [← pinned] at row
  simpa [enabled] using row

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
theorem StrongInstalledModel.punit_unit_value {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    (lookup : env.find? Kernel.punitUnitName = some Kernel.punitUnitA)
    (levels : Kernel.Name → Nat) : strong.public.cval Kernel.punitUnitName levels = (pt : V) := by
  have pinned : strong.internal.base2.cvalE Kernel.punitUnitName levels =
      Kernel.Term.punitUnitT (levels Kernel.uN) :=
    (strong.internal.base2.basis_pinned Kernel.punitUnitName _ lookup (by decide)).2 _ levels rfl
  have leaf : strong.internal.base2.acval Kernel.punitUnitName levels = .const .punitUnit [levels Kernel.uN] :=
    erase_eq_const (by rw [strong.internal.base2.acval_erase, pinned]; rfl)
  change interp V (fun _ => empty) (strong.internal.base2.acval Kernel.punitUnitName levels) = pt
  rw [leaf, interp_const]
  rfl

open Kernel.Model Kernel.SetTheory in
/-- Reserved eta uses the actual pinned family and its stored constructor,
including zero parameter/field counts; no general non-basis eta premise is
applied to a reserved family. -/
theorem StrongInstalledModel.reserved_eta {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env)
    {name : Kernel.Name} {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (reserved : Kernel.reservedBasisNames.contains name = true)
    (enabled : caps.eta = true)
    (constructor : ∃ entry, env.find? caps.etaCtor = some entry)
    (levels : Kernel.Name → Nat) (values : List V) (count : values.length = caps.etaParams)
    (x : V) (member : x ∈ˢ values.foldl app (strong.public.cval name levels)) :
    x = (etaFabArgsV (fun n => strong.public.cval n levels) name values x caps.etaFields).foldl app
      (strong.public.cval caps.etaCtor levels) := by
  have named := strong.reserved_eta_name lookup reserved enabled
  subst name
  have pinned := (strong.internal.base2.basis_pinned Kernel.punitName _ lookup reserved).1
  have found : env.find? Kernel.punitName = some Kernel.punitA := by
    simpa only [pinned, show Kernel.pinnedInfo Kernel.punitName = Kernel.punitA from rfl] using lookup
  have zeroParams : caps.etaParams = 0 :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaParams | _ => 0) pinned
  have zeroFields : caps.etaFields = 0 :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaFields | _ => 0) pinned
  have ctorName : caps.etaCtor = Kernel.punitUnitName :=
    congrArg (fun entry => match entry with | .indInfo _ c => c.etaCtor | _ => .anonymous) pinned
  obtain ⟨entry, constructorLookup⟩ := constructor
  rw [ctorName] at constructorLookup
  have ctorPinned := (strong.internal.base2.basis_pinned Kernel.punitUnitName _ constructorLookup (by decide)).1
  have ctorFound : env.find? Kernel.punitUnitName = some Kernel.punitUnitA := by
    simpa only [ctorPinned, show Kernel.pinnedInfo Kernel.punitUnitName = Kernel.punitUnitA from rfl] using constructorLookup
  have nil : values = [] := by simpa using count.trans zeroParams
  rw [nil, List.foldl_nil, strong.punit_value found levels] at member
  simpa [nil, zeroFields, ctorName, etaFabArgsV, projSpines, strong.punit_unit_value ctorFound levels]
    using (mem_unitSet member)

open Kernel.Model in
theorem etaFabArgsV_image {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Name → V} {sourceOwner targetOwner : Kernel.Name}
    (arguments : List V) (value : V) (fields : Nat)
    (projections : ∀ index ∈ List.range fields,
      source (Kernel.projFnName sourceOwner index) = target (Kernel.projFnName targetOwner index)) :
    etaFabArgsV source sourceOwner arguments value fields = etaFabArgsV target targetOwner arguments value fields := by
  unfold etaFabArgsV projSpines
  congr 1
  apply List.map_congr_left
  intro index present
  rw [projections index present]

/-- Select the actual eta-law branch for one installed family. Reserved
families use their pinned law; ordinary families must have every stored
constructor/projection entry required by the general eta law. -/
def checkInstalledEtaAt (env : Kernel.Env) (name : Kernel.Name) : Bool :=
  match env.find? name with
  | some (.indInfo _ caps) => Kernel.reservedBasisNames.contains name || checkInstalledEtaFamily env name caps
  | _ => false

theorem checkInstalledEtaAt_sound {env : Kernel.Env} {name : Kernel.Name}
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (lookup : env.find? name = some (.indInfo header caps))
    (checked : checkInstalledEtaAt env name = true) :
    Kernel.reservedBasisNames.contains name = true ∨ Kernel.EtaFamilyStored env name caps := by
  simp only [checkInstalledEtaAt, lookup, Bool.or_eq_true] at checked
  exact checked.imp_right checkInstalledEtaFamily_sound

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- The source-side eta reconstruction equation, including the reserved
basis branch. Every constructor/projection value is related at the actual
family universe instance by its executable owner-relative comparison. -/
theorem checked_eta_pullback {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.eta = true)
    (family : checkInstalledEtaAt targetEnv (names header.name) = true)
    (constructor : checkInstalledFamilyMember sourceEnv targetEnv names header.name caps.etaCtor = some true)
    (projections : ∀ index ∈ List.range caps.etaFields,
      checkInstalledFamilyMember sourceEnv targetEnv names header.name (Kernel.projFnName header.name index) = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    {depth : Nat} {ρ : Nat → V} {targetExpressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations target targetLevels depth ρ targetExpressions annotations)
    {sourceExpressions : List Kernel.Expr} {values : List V} {sourceResidual : Kernel.Expr}
    (application : DenotedApplication
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels ρ (header.type.instantiateLevelParams header.levelParams sourceUs)
      sourceExpressions values sourceResidual)
    (argumentImages : InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceExpressions (targetExpressions.map (Kernel.Expr.closeN depth)))
    (count : values.length = caps.etaParams) (x : V)
    (member : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))) :
    x = (etaFabArgsV
      (fun n => (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval n
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))
      header.name values x caps.etaFields).foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval caps.etaCtor
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs)) := by
  obtain ⟨sourceLookup, targetHeader, targetCaps, targetLookup, capHeader, _⟩ :=
    checkInstalledCapabilities_member capabilities present
  obtain ⟨associated, associatedLookup, telescope⟩ := association _ _ sourceLookup
  have same := Option.some.inj (associatedLookup.symm.trans targetLookup)
  subst associated
  have targetArity : targetUs.length = targetHeader.levelParams.length := by
    have equalLengths := congrArg List.length universes
    simp only [List.length_map] at equalLengths
    exact equalLengths.symm.trans (sourceArity.trans telescope.2.2)
  obtain ⟨residual, targetApplication, _⟩ := AnnotatedApplication.from_checked_type target association types
    present targetLookup sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
    readings application argumentImages
  have equalValues := (application.arguments.image argumentImages).functional readings.denotes
  have equalFamily :
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs) =
      target.public.cval (names header.name) (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs) := by
    apply target.value_params targetLookup
    exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
      sourceUs targetUs sourceArity targetArity universes
  have targetEnabled : targetCaps.eta = true := capHeader.1.symm.trans enabled
  have targetCount : annotations.length = targetCaps.etaParams := by
    rw [equalValues, List.length_map] at count
    exact count.trans capHeader.2.2.2.1
  have namedHelpers := capHeader.2.2.2.2.2.2 enabled
  have ctorImage := checkInstalledFamilyMember_sound target association sourceLookup targetLookup
    constructor sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
  rw [← namedHelpers.1] at ctorImage
  simp only [Kernel.ConstantInfo.toConstantVal] at ctorImage
  have spineImage := etaFabArgsV_image (source := fun n =>
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval n
        (Kernel.Level.substFn sourceLevels header.levelParams sourceUs))
    (target := fun n => target.public.cval n
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs))
    (sourceOwner := header.name) (targetOwner := names header.name) values x caps.etaFields
    (fun index bound => by
      have image := checkInstalledFamilyMember_sound target association sourceLookup targetLookup
        (projections index bound) sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
      rwa [namedHelpers.2 index bound] at image)
  rw [spineImage, ctorImage, capHeader.2.2.2.2.1, equalValues]
  rw [equalValues, equalFamily] at member
  by_cases reserved : Kernel.reservedBasisNames.contains (names header.name) = true
  · obtain ⟨_, constructorEntry, _, constructorLookup, _⟩ := checkInstalledFamilyMember_lookups targetLookup constructor
    rw [← namedHelpers.1] at constructorLookup
    exact target.reserved_eta targetLookup reserved targetEnabled ⟨constructorEntry, constructorLookup⟩
      (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs)
      (annotations.map (interp V ρ)) (by simpa using targetCount) x member
  · have stored := (checkInstalledEtaAt_sound targetLookup family).resolve_left reserved
    have nonbasis : Kernel.reservedBasisNames.contains (names header.name) = false := by simpa using reserved
    have targetMember : x ∈ˢ (annotations.map (interp V ρ)).foldl app
        (interp V ρ (target.internal.base2.acval (names header.name)
          (Kernel.Level.substFn targetLevels targetHeader.levelParams targetUs))) := by
      simpa only [interp_cvalOf target.internal.base2.cval_closedL,
        StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using member
    have reconstructed := targetApplication.installed_eta (names header.name) targetHeader targetCaps targetLookup
      targetEnabled nonbasis stored targetUs targetArity targetCount x targetMember
    simpa only [interp_cvalOf target.internal.base2.cval_closedL,
      StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM] using reconstructed

open Kernel.Semantics Kernel.Model in
/-- Derive the plain-rule parameter comparisons from source semantic
prefix equality and the actual target argument/field readings. Bounds come
from the constructor field count, not a fabricated default value. -/
theorem ArgumentAnnotations.parameters_image {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv}
    {targetLevels : Kernel.Name → Nat} {depth : Nat} {ρ : Nat → V}
    {targetFields targetArguments : List Kernel.Expr} {fields arguments : List AnnotTerm}
    (fieldReadings : ArgumentAnnotations target targetLevels depth ρ targetFields fields)
    (argumentReadings : ArgumentAnnotations target targetLevels depth ρ targetArguments arguments)
    {sourceValues : Kernel.Name → (Kernel.Name → Nat) → V} {sourceEnv : Kernel.Env}
    {sourceLevels : Kernel.Name → Nat} {sourceFields sourceArguments : List Kernel.Expr}
    {fieldValues argumentValues : List V}
    (fieldRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceFields fieldValues)
    (argumentRead : DenotesSpine sourceValues sourceEnv sourceLevels ρ sourceArguments argumentValues)
    (fieldImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceFields (targetFields.map (Kernel.Expr.closeN depth)))
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceArguments (targetArguments.map (Kernel.Expr.closeN depth)))
    (params : Nat) (fieldBound : params ≤ fields.length)
    (sourceEquation : fieldValues.take params = argumentValues.take params) :
    ∀ index, index < params → index < arguments.length →
      interp V ρ (fields.getD index default) = interp V ρ (arguments.getD index default) := by
  have fieldValuesImage := (fieldRead.image fieldImages).functional fieldReadings.denotes
  have argumentValuesImage := (argumentRead.image argumentImages).functional argumentReadings.denotes
  rw [fieldValuesImage, argumentValuesImage] at sourceEquation
  intro index belowParams belowArguments
  have belowFields : index < fields.length := by omega
  have selected := congrArg (fun values : List V => values[index]?) sourceEquation
  simp only [List.getElem?_take, belowParams, ite_true, List.getElem?_map,
    List.getElem?_eq_getElem belowFields, List.getElem?_eq_getElem belowArguments,
    Option.map_some, Option.some.injEq] at selected
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem belowFields,
    List.getElem?_eq_getElem belowArguments, Option.getD_some] using selected

theorem ArgumentAnnotations.take {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations) (count : Nat) :
    ArgumentAnnotations strong levels depth ρ (expressions.take count) (annotations.take count) := by
  induction readings generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

/-- Prefix application evidence preserves the actual substitution sequence;
it is not a telescope invented from matching lengths. -/
theorem AnnotatedApplication.take {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) (count : Nat) :
    ∃ prefixResidual, AnnotatedApplication strong levels depth ρ type
      (expressions.take count) (annotations.take count) prefixResidual := by
  induction application generalizing count with
  | nil => simp only [List.take_nil]; exact ⟨_, .nil⟩
  | cons domainRead argumentRead argumentScope argumentBounded argumentGraded argumentTyped rest ih =>
    cases count with
    | zero => exact ⟨_, .nil⟩
    | succ count =>
      obtain ⟨prefixResidual, prefixApplication⟩ := ih count
      exact ⟨prefixResidual, .cons domainRead argumentRead argumentScope argumentBounded argumentGraded argumentTyped prefixApplication⟩

theorem AnnotatedApplication.readings {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {type residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (application : AnnotatedApplication strong levels depth ρ type expressions annotations residual) :
    ArgumentAnnotations strong levels depth ρ expressions annotations := by
  induction application with
  | nil => exact .nil
  | cons _ argumentRead scope bounded graded _ _ ih => exact .cons ⟨argumentRead, scope, bounded, graded⟩ ih

open Kernel.Semantics Kernel.Model in
/-- The nested pin's chain grading is supplied by the actual installed rule
and the prefix of the actual typed recursor application. Its open reading is
not assumed uniformly graded outside that fitting context. -/
theorem AnnotatedApplication.installed_nested_pin {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (major params : Nat)
    (rules : List Kernel.RecRule) (rule : Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (prefixBound : params ≤ annotations.length)
    (nestedLevels : List Kernel.Level) (pins : List Kernel.Expr) (nested : rule.fire = .nested nestedLevels pins)
    (index : Nat) (below : index < rule.ctorParams) :
    ∃ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels params
        (Kernel.Verify.openRev 0 params ((pins.getD index default).instantiateLevelParams header.levelParams universes)) =
          some pin ∧
      WellDenotedV V ρ (Kernel.Model.AnnotTerm.instRevChain (annotations.take params) pin) := by
  have fires : rule.fire ≠ .inert := by rw [nested]; intro h; cases h
  obtain ⟨_, _, _, pinsLaw, _⟩ :=
    (strong.recursor_rule levels name header major params rules lookup rule present fires).2 universes arity
  obtain ⟨pin, reading, grade⟩ := pinsLaw nestedLevels pins nested index below
  obtain ⟨prefixResidual, prefixApplication⟩ := application.take params
  obtain ⟨typeAnnotation, result, typeReading, fit, _⟩ := prefixApplication.installed_fit
    name (.recInfo header major params rules) lookup rfl universes arity
  exact ⟨pin, reading, grade ρ (annotations.take params) typeAnnotation result
    (by simp only [List.length_take, Nat.min_eq_left prefixBound])
    prefixApplication.readings.facts.2.2 typeReading fit⟩

theorem ArgumentAnnotations.length {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations) :
    expressions.length = annotations.length := by
  induction readings with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem instSeq_closed_bound (arguments : List Kernel.Expr) {expression : Kernel.Expr}
    (boundedArguments : ∀ argument ∈ arguments, argument.looseBVarsBounded 0 = true)
    (bounded : expression.looseBVarsBounded arguments.length = true) :
    (Kernel.Expr.instSeq arguments (arguments.length - 1) expression).looseBVarsBounded 0 = true := by
  induction arguments generalizing expression with
  | nil => exact bounded
  | cons argument arguments ih =>
    have next := Kernel.Expr.looseBVarsBounded_instantiate1_gen
      (boundedArguments argument List.mem_cons_self) bounded
    simpa only [Kernel.Expr.instSeq, List.length_cons, Nat.add_sub_cancel] using
      ih (fun x hx => boundedArguments x (List.mem_cons_of_mem _ hx)) next

theorem instSeq_scoped (arguments : List Kernel.Expr) (index : Nat) {expression : Kernel.Expr} {depth : Nat}
    (scopedArguments : ∀ argument ∈ arguments, Kernel.Expr.WScoped depth argument)
    (scopeProof : Kernel.Expr.WScoped depth expression) :
    Kernel.Expr.WScoped depth (Kernel.Expr.instSeq arguments index expression) := by
  induction arguments generalizing expression index with
  | nil => exact scopeProof
  | cons argument arguments ih =>
    exact ih (index - 1) (fun x hx => scopedArguments x (List.mem_cons_of_mem _ hx))
      (Kernel.Expr.WScoped.instantiate1_gen (scopedArguments argument List.mem_cons_self) index scopeProof)

open Kernel.Semantics Kernel.Model Kernel.Model.Rules in
/-- Relate the actual reverse-opened pin annotation to substitution by the
actual argument expressions. Both scope and capture bounds are retained. -/
theorem ArgumentAnnotations.instSeq_annotation {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations)
    {expression : Kernel.Expr} (noFree : expression.hasFvar = false)
    (bounded : expression.looseBVarsBounded expressions.length = true)
    {pin : AnnotTerm}
    (reading : denoteMeta strong.internal.base2.acval env levels expressions.length
      (Kernel.Verify.openRev 0 expressions.length expression) = some pin)
    (graded : WellDenotedV V ρ (Kernel.Model.AnnotTerm.instRevChain annotations pin)) :
    ArgumentAnnotation strong levels depth ρ
      (Kernel.Expr.instSeq expressions (expressions.length - 1) expression)
      (Kernel.Model.AnnotTerm.instRevChain annotations pin) := by
  have facts := readings.facts
  refine ⟨?_, instSeq_scoped expressions _ (fun x hx => (facts.2.1 x hx).1)
    (Kernel.Expr.WScoped.of_not_hasFvar noFree),
    instSeq_closed_bound expressions (fun x hx => (facts.2.1 x hx).2) bounded, graded⟩
  rw [denoteMeta_openRev strong.internal.base2.acval_closed (acval_inst_self strong.internal.base2)
    expressions facts.2.1 (Kernel.Expr.WScoped.of_not_hasFvar noFree).fvarsBelow bounded facts.1]
  rw [denoteMeta_openRev_base strong.internal.base2.acval_closed strong.internal.base2.acval_erase
    strong.internal.base2.cval_closed noFree bounded depth, reading]
  rfl

open Kernel.Semantics Kernel.Model in
theorem ArgumentAnnotation.denotes {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expression : Kernel.Expr} {annotation : AnnotTerm}
    (evidence : ArgumentAnnotation strong levels depth ρ expression annotation) :
    Kernel.Denotes strong.public.cval env levels ρ (expression.closeN depth) (interp V ρ annotation) :=
  Denotes_of_denoteMeta strong.internal.base2.cval_closedL depth expression evidence.reading
    evidence.scope.fvarsBelow evidence.bounded ρ evidence.graded

open Kernel.Semantics Kernel.Model in
/-- The actual nested pin after concrete universe substitution and argument
substitution has its actual graded annotation. All scope/bound/grading facts
come from the installed rule and typed application; index validity remains
explicit so a default lookup cannot stand in for a stored pin. -/
theorem AnnotatedApplication.installed_nested_annotation {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (major params : Nat)
    (rules : List Kernel.RecRule) (rule : Kernel.RecRule)
    (lookup : env.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication strong levels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (prefixBound : params ≤ annotations.length)
    (nestedLevels : List Kernel.Level) (pins : List Kernel.Expr) (nested : rule.fire = .nested nestedLevels pins)
    (index : Nat) (belowConstructor : index < rule.ctorParams) (belowPins : index < pins.length) :
    ∃ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels params
        (Kernel.Verify.openRev 0 params ((pins.getD index default).instantiateLevelParams header.levelParams universes)) =
          some pin ∧
      ArgumentAnnotation strong levels depth ρ
        (Kernel.Expr.instSeq (expressions.take params) (params - 1)
          ((pins.getD index default).instantiateLevelParams header.levelParams universes))
        (Kernel.Model.AnnotTerm.instRevChain (annotations.take params) pin) := by
  obtain ⟨pin, reading, graded⟩ := application.installed_nested_pin name header major params rules rule
    lookup present universes arity prefixBound nestedLevels pins nested index belowConstructor
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have ruleWf := wf.2.2.2.2.2.1 header major params rules rfl rule present
  have pinMember : pins.getD index default ∈ pins := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem belowPins, Option.getD_some]
    exact List.getElem_mem belowPins
  have pinWf := (ruleWf.2.2.2.2 nestedLevels pins nested).2.2.1 _ pinMember
  have noFree : ((pins.getD index default).instantiateLevelParams header.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]
    exact pinWf.1
  have bounded : ((pins.getD index default).instantiateLevelParams header.levelParams universes).looseBVarsBounded params = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact pinWf.2.2.2
  have length : (expressions.take params).length = params := by
    rw [List.length_take, application.length, Nat.min_eq_left prefixBound]
  have evidence := (application.readings.take params).instSeq_annotation noFree
    (by simpa only [length] using bounded) (by simpa only [length] using reading) graded
  exact ⟨pin, reading, by simpa only [length] using evidence⟩

/-- Every checked position is instantiated under the actual owner records.
This is the list form needed for nested pins; target universe coverage is
charged to each stored expression, not inferred from a list length. -/
theorem checkInstalledMemberExprs_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (targetModel : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    {sources targets : List Kernel.Expr}
    (targetBounded : ∀ expression ∈ targets,
      expression.allLevelParamsDefined targetEntry.toConstantVal.levelParams = true)
    (checked : checkInstalledMemberExprs sourceEnv targetEnv names name sources targets = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    InstalledSpineImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values targetModel.public.cval)
      targetModel.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (sources.map (Kernel.Expr.instantiateLevelParams sourceEntry.toConstantVal.levelParams sourceUs))
      (targets.map (Kernel.Expr.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs)) := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp [checkInstalledMemberExprs] at checked; exact .nil
  | cons source sources ih =>
    cases targets with
    | nil => simp [checkInstalledMemberExprs] at checked
    | cons target targets =>
      obtain ⟨head, tail⟩ := bothChecks_true checked
      exact .cons (checkInstalledMemberExpr_instance targetModel association sourceLookup targetLookup
        (targetBounded target List.mem_cons_self) head sourceLevels targetLevels sourceUs targetUs
        sourceArity targetArity universes)
        (ih (fun e he => targetBounded e (List.mem_cons_of_mem _ he)) tail)

theorem InstalledSpineImage.get {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl} {sources targets : List Kernel.Expr}
    (images : InstalledSpineImage (V := V) sv tv se te sl tl sources targets)
    (index : Nat) (bound : index < sources.length) :
    InstalledExprImage sv tv se te sl tl (sources.getD index default) (targets.getD index default) := by
  induction images generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index (by simpa using bound)

/-- An executable-selected actual fired rule and its constructor. Every
record is tied to the same environment and ordinal; no default or supplied
constructor record can stand in for a missing lookup. -/
structure InstalledRuleFrame (env : Kernel.Env) (name : Kernel.Name) (index : Nat) where
  header : Kernel.ConstantVal
  major : Nat
  rulePrefix : Nat
  rules : List Kernel.RecRule
  rule : Kernel.RecRule
  constructor : Kernel.ConstantVal
  constructorParams : Nat
  constructorFields : Nat
  recursorLookup : env.find? name = some (.recInfo header major rulePrefix rules)
  ruleLookup : rules[index]? = some rule
  fires : rule.fire ≠ .inert
  constructorLookup : env.find? rule.ctor = some (.ctorInfo constructor constructorParams constructorFields)

def readInstalledRuleFrame (env : Kernel.Env) (name : Kernel.Name) (index : Nat) :
    Option (InstalledRuleFrame env name index) :=
  match recursorLookup : env.find? name with
  | some (.recInfo header major rulePrefix rules) =>
    match ruleLookup : rules[index]? with
    | some rule =>
      if fires : rule.fire = .inert then none else
      match constructorLookup : env.find? rule.ctor with
      | some (.ctorInfo constructor constructorParams constructorFields) =>
        some {
          header := header, major := major, rulePrefix := rulePrefix, rules := rules,
          rule := rule, constructor := constructor, constructorParams := constructorParams,
          constructorFields := constructorFields, recursorLookup := recursorLookup,
          ruleLookup := ruleLookup, fires := fires, constructorLookup := constructorLookup }
      | _ => none
    | none => none
  | _ => none

def checkInstalledRuleUniverses (env : Kernel.Env) (name : Kernel.Name) (index : Nat)
    (universes constructorUniverses : List Kernel.Level) : Option Bool :=
  match readInstalledRuleFrame env name index with
  | none => some false
  | some frame =>
    if universes.length = frame.header.levelParams.length ∧
        constructorUniverses.length = frame.constructor.levelParams.length then
      Kernel.Level.isEquivList constructorUniverses
        (Kernel.recFireComparands frame.rule frame.header.levelParams universes
          frame.constructor.levelParams [] frame.rulePrefix).1
    else some false

/-- Acceptance establishes the exact full assignment equality required by
the stored fired-rule law, for every base valuation. Resource-unknown level
comparison remains `none`; it is not a proof of inequality or a domain cut. -/
theorem checkInstalledRuleUniverses_sound {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    {universes constructorUniverses : List Kernel.Level}
    (checked : checkInstalledRuleUniverses env name index universes constructorUniverses = some true) :
    ∃ frame : InstalledRuleFrame env name index,
      readInstalledRuleFrame env name index = some frame ∧
      universes.length = frame.header.levelParams.length ∧
      constructorUniverses.length = frame.constructor.levelParams.length ∧
      ∀ levels, Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses =
        Kernel.Level.substFn levels frame.constructor.levelParams
          (Kernel.recFireComparands frame.rule frame.header.levelParams universes
            frame.constructor.levelParams [] frame.rulePrefix).1 := by
  cases selected : readInstalledRuleFrame env name index with
  | none => simp [checkInstalledRuleUniverses, selected] at checked
  | some frame =>
    simp only [checkInstalledRuleUniverses, selected] at checked
    split at checked
    next arities =>
      exact ⟨frame, rfl, arities.1, arities.2, fun levels =>
        Kernel.Level.substFn_congr (Kernel.Level.isEquivList_sound checked levels)⟩
    next => contradiction

theorem ArgumentAnnotations.get {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {expressions : List Kernel.Expr} {annotations : List Kernel.Semantics.AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth ρ expressions annotations)
    (index : Nat) (bound : index < annotations.length) :
    ArgumentAnnotation strong levels depth ρ (expressions.getD index default) (annotations.getD index default) := by
  induction readings generalizing index with
  | nil => simp at bound
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih index (by simpa using bound)

open Kernel.Semantics Kernel.Model in
/-- Transport one source nested-parameter equation into the exact comparison
quantified by the actual target fired-rule law. The substituted pin image and
its grading/reading are derived inside the proof. The source equation is the
semantic reduction premise, not inferred from matching shapes or counts. -/
theorem AnnotatedApplication.nested_parameter_image {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} {target : StrongInstalledModel V targetEnv} {targetLevels : Kernel.Name → Nat}
    {depth : Nat} {ρ : Nat → V} {residual : Kernel.Expr}
    {expressions : List Kernel.Expr} {annotations : List AnnotTerm}
    (name : Kernel.Name) (header : Kernel.ConstantVal) (major params : Nat)
    (rules : List Kernel.RecRule) (rule : Kernel.RecRule)
    (lookup : targetEnv.find? name = some (.recInfo header major params rules))
    (present : rule ∈ rules) (universes : List Kernel.Level) (arity : universes.length = header.levelParams.length)
    (application : AnnotatedApplication target targetLevels depth ρ
      (header.type.instantiateLevelParams header.levelParams universes) expressions annotations residual)
    (prefixBound : params ≤ annotations.length)
    (nestedLevels : List Kernel.Level) (pins : List Kernel.Expr) (nested : rule.fire = .nested nestedLevels pins)
    (index : Nat) (belowConstructor : index < rule.ctorParams) (belowPins : index < pins.length)
    {targetField : Kernel.Expr} {fieldAnnotation : AnnotTerm}
    (fieldReading : ArgumentAnnotation target targetLevels depth ρ targetField fieldAnnotation)
    {sourceValues : Kernel.Name → (Kernel.Name → Nat) → V} {sourceEnv : Kernel.Env}
    {sourceLevels : Kernel.Name → Nat} {sourceArguments : List Kernel.Expr} {sourcePin sourceField : Kernel.Expr}
    (argumentImages : InstalledSpineImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceArguments ((expressions.take params).map (Kernel.Expr.closeN depth)))
    (pinImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourcePin ((pins.getD index default).instantiateLevelParams header.levelParams universes))
    (fieldImage : InstalledExprImage sourceValues target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      sourceField (targetField.closeN depth))
    {fieldValue pinValue : V}
    (fieldRead : Kernel.Denotes sourceValues sourceEnv sourceLevels ρ sourceField fieldValue)
    (pinRead : Kernel.Denotes sourceValues sourceEnv sourceLevels ρ
      (Kernel.Expr.instSeqLift sourceArguments (params - 1) sourcePin) pinValue)
    (sourceEquation : fieldValue = pinValue) :
    ∀ pin : AnnotTerm,
      denoteMeta target.internal.base2.acval targetEnv targetLevels params
        (Kernel.Verify.openRev 0 params ((pins.getD index default).instantiateLevelParams header.levelParams universes)) =
          some pin →
      interp V ρ fieldAnnotation = interp V ρ (Kernel.Model.AnnotTerm.instRevChain (annotations.take params) pin) := by
  obtain ⟨actualPin, actualRead, evidence⟩ := application.installed_nested_annotation name header major params rules rule
    lookup present universes arity prefixBound nestedLevels pins nested index belowConstructor belowPins
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem lookup)
  have ruleWf := wf.2.2.2.2.2.1 header major params rules rfl rule present
  have pinMember : pins.getD index default ∈ pins := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem belowPins, Option.getD_some]
    exact List.getElem_mem belowPins
  have pinWf := (ruleWf.2.2.2.2 nestedLevels pins nested).2.2.1 _ pinMember
  have noFree : ((pins.getD index default).instantiateLevelParams header.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]; exact pinWf.1
  have length : (expressions.take params).length = params := by
    rw [List.length_take, application.length, Nat.min_eq_left prefixBound]
  have bounded : ((pins.getD index default).instantiateLevelParams header.levelParams universes).looseBVarsBounded
      (expressions.take params).length = true := by
    rw [length, Kernel.Expr.looseBVarsBounded_instantiateLevelParams]; exact pinWf.2.2.2
  have argumentFacts := (application.readings.take params).facts
  have instantiatedImage := argumentImages.closed_instSeq pinImage noFree
    (fun expression member => (argumentFacts.2.1 expression member).2) bounded
  rw [length] at instantiatedImage
  have pinValueImage := Kernel.Denotes_functional (instantiatedImage.denotes pinRead) evidence.denotes
  have fieldValueImage := Kernel.Denotes_functional (fieldImage.denotes fieldRead) fieldReading.denotes
  intro pin reading
  have same : actualPin = pin := Option.some.inj (actualRead.symm.trans reading)
  subst pin
  exact fieldValueImage.symm.trans (sourceEquation.trans pinValueImage)

open Kernel.SetTheory in
/-- Unit capability for arbitrary typed source semantic arguments. Fresh
variables derive the target readings and component images, so no syntactic
representability premise is imposed on the arguments. Source well-formedness
comes from its own installed stream, not target acceptance. -/
theorem checked_unit_telescope {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.unitlike = true) (levels : Kernel.Name → Nat) (universes : List Kernel.Level)
    (arity : universes.length = header.levelParams.length)
    {ρ finalρ : Nat → V} {values : List V} {result : Kernel.Expr}
    (typed : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels ρ (header.type.instantiateLevelParams header.levelParams universes) values finalρ result)
    (count : values.length = caps.unitParams) (x y : V)
    (left : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn levels header.levelParams universes)))
    (right : y ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn levels header.levelParams universes))) : x = y := by
  have bounded : (header.type.instantiateLevelParams header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact (sourceWf _ present).2.2.2.1
  obtain ⟨residual, application⟩ := DenotedApplication.arbitrary_arguments typed bounded
  have readings := ArgumentAnnotations.variables target levels values.length (pushArguments ρ values)
    (fun _ => Kernel.Expr.sort .zero) (by intro index _; simp [Kernel.Expr.WScoped])
  have images := InstalledSpineImage.argumentVariables
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
    target.public.cval sourceEnv targetEnv levels levels values.length
  apply checked_unit_pullback target association types capabilities present enabled
    levels levels universes universes arity rfl readings application _ count x y left right
  simpa only [argumentFVars_closed] using images

open Kernel.Model Kernel.SetTheory in
/-- Eta capability for arbitrary typed source semantic arguments. The
actual target argument readings/images are constructed, while executable
family/helper checks retain all constructor/projection identity obligations.
Both ordinary and reserved pinned families are covered. -/
theorem checked_eta_telescope {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ sourceEnv.consts)
    (enabled : caps.eta = true)
    (family : checkInstalledEtaAt targetEnv (names header.name) = true)
    (constructor : checkInstalledFamilyMember sourceEnv targetEnv names header.name caps.etaCtor = some true)
    (projections : ∀ index ∈ List.range caps.etaFields,
      checkInstalledFamilyMember sourceEnv targetEnv names header.name (Kernel.projFnName header.name index) = some true)
    (levels : Kernel.Name → Nat) (universes : List Kernel.Level)
    (arity : universes.length = header.levelParams.length)
    {ρ finalρ : Nat → V} {values : List V} {result : Kernel.Expr}
    (typed : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv levels ρ (header.type.instantiateLevelParams header.levelParams universes) values finalρ result)
    (count : values.length = caps.etaParams) (x : V)
    (member : x ∈ˢ values.foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval header.name
        (Kernel.Level.substFn levels header.levelParams universes))) :
    x = (etaFabArgsV
      (fun n => (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval n
        (Kernel.Level.substFn levels header.levelParams universes))
      header.name values x caps.etaFields).foldl app
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval caps.etaCtor
        (Kernel.Level.substFn levels header.levelParams universes)) := by
  have bounded : (header.type.instantiateLevelParams header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact (sourceWf _ present).2.2.2.1
  obtain ⟨residual, application⟩ := DenotedApplication.arbitrary_arguments typed bounded
  have readings := ArgumentAnnotations.variables target levels values.length (pushArguments ρ values)
    (fun _ => Kernel.Expr.sort .zero) (by intro index _; simp [Kernel.Expr.WScoped])
  have images := InstalledSpineImage.argumentVariables
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
    target.public.cval sourceEnv targetEnv levels levels values.length
  apply checked_eta_pullback target association types capabilities present enabled family constructor projections
    levels levels universes universes arity rfl readings application _ count x member
  simpa only [argumentFVars_closed] using images

def checkInstalledEtaEntry (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool :=
  match entry with
  | .indInfo header caps =>
    if caps.eta then
      bothChecks (some (decide (source.find? header.name = some entry) && checkInstalledEtaAt target (names header.name)))
        (bothChecks (checkInstalledFamilyMember source target names header.name caps.etaCtor)
          ((List.range caps.etaFields).foldr (fun index rest => bothChecks
            (checkInstalledFamilyMember source target names header.name (Kernel.projFnName header.name index)) rest)
            (some true)))
    else some true
  | _ => some true

/-- Every source eta-capability row and indexed helper is checked. Optional
comparison failure propagates rather than becoming an established inequality. -/
def checkInstalledEtaAssociations (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (checkInstalledEtaEntry source target names entry) rest) (some true)

theorem bothChecks_fold_true {α : Type} {entries : List α} {check : α → Option Bool}
    (checked : entries.foldr (fun entry rest => bothChecks (check entry) rest) (some true) = some true) :
    ∀ entry ∈ entries, check entry = some true := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨first, rest⟩ := bothChecks_true checked
    intro entry present
    rcases List.mem_cons.mp present with rfl | present
    · exact first
    · exact ih rest entry present

theorem checkInstalledEtaAssociations_sound {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledEtaAssociations source target names = some true)
    {header : Kernel.ConstantVal} {caps : Kernel.IndCaps}
    (present : Kernel.ConstantInfo.indInfo header caps ∈ source.consts) (enabled : caps.eta = true) :
    checkInstalledEtaAt target (names header.name) = true ∧
    checkInstalledFamilyMember source target names header.name caps.etaCtor = some true ∧
    ∀ index ∈ List.range caps.etaFields,
      checkInstalledFamilyMember source target names header.name (Kernel.projFnName header.name index) = some true := by
  have row := bothChecks_fold_true checked _ present
  simp only [checkInstalledEtaEntry, enabled, ite_true] at row
  obtain ⟨family, helpers⟩ := bothChecks_true row
  obtain ⟨constructor, projections⟩ := bothChecks_true helpers
  have familyCheck := Option.some.inj family
  simp only [Bool.and_eq_true] at familyCheck
  exact ⟨familyCheck.2, constructor, bothChecks_fold_true projections⟩

open Kernel.Model Kernel.SetTheory in
/-- Public value-level capability laws. This is not the full internal strong
model: recursor, projection, literal and annotation obligations remain separate. -/
structure PublicCapabilityLaws {V : Type u} [Kernel.SetTheory V]
    (cval : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env) : Prop where
  unit : ∀ header caps, Kernel.ConstantInfo.indInfo header caps ∈ env.consts → caps.unitlike = true →
    ∀ levels universes, universes.length = header.levelParams.length →
    ∀ (ρ finalρ : Nat → V) (values : List V) (result : Kernel.Expr),
      InstalledTelescope cval env levels ρ (header.type.instantiateLevelParams header.levelParams universes)
        values finalρ result → values.length = caps.unitParams →
      ∀ x y, x ∈ˢ values.foldl app (cval header.name (Kernel.Level.substFn levels header.levelParams universes)) →
        y ∈ˢ values.foldl app (cval header.name (Kernel.Level.substFn levels header.levelParams universes)) → x = y
  eta : ∀ header caps, Kernel.ConstantInfo.indInfo header caps ∈ env.consts → caps.eta = true →
    ∀ levels universes, universes.length = header.levelParams.length →
    ∀ (ρ finalρ : Nat → V) (values : List V) (result : Kernel.Expr),
      InstalledTelescope cval env levels ρ (header.type.instantiateLevelParams header.levelParams universes)
        values finalρ result → values.length = caps.etaParams →
      ∀ x, x ∈ˢ values.foldl app (cval header.name (Kernel.Level.substFn levels header.levelParams universes)) →
        x = (etaFabArgsV (fun n => cval n (Kernel.Level.substFn levels header.levelParams universes))
          header.name values x caps.etaFields).foldl app (cval caps.etaCtor (Kernel.Level.substFn levels header.levelParams universes))

theorem checkedCapabilities_publicLaws {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    (etaAssociations : checkInstalledEtaAssociations sourceEnv targetEnv names = some true) :
    PublicCapabilityLaws ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv := by
  constructor
  · intro header caps present enabled levels universes arity ρ finalρ values result typed count x y left right
    exact checked_unit_telescope sourceWf target association types capabilities present enabled levels universes
      arity typed count x y left right
  · intro header caps present enabled levels universes arity ρ finalρ values result typed count x member
    obtain ⟨family, constructor, projections⟩ := checkInstalledEtaAssociations_sound etaAssociations present enabled
    exact checked_eta_telescope sourceWf target association types capabilities present enabled family constructor projections
      levels universes arity typed count x member

/-- The independently checked source stream supplies its own installation
and well-formedness. The checked target supplies one interpretation whose
pull-back has public typing, definition equations and arbitrary-value unit/
eta laws. This is still not the full internal strong model or end-to-end S. -/
theorem checkedStreams_publicCapabilities (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDeclarations targetDeclarations : Array Kernel.Declaration)
    (sourceEnv targetEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDeclarations = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDeclarations = .ok targetEnv)
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (definitions : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    (etaAssociations : checkInstalledEtaAssociations sourceEnv targetEnv names = some true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ target : StrongInstalledModel V targetEnv, ∃ source : PublicValueModel V sourceEnv,
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval ∧
      PublicCapabilityLaws source.model.cval sourceEnv := by
  obtain ⟨sourceExists, target, source, interpretation⟩ := checkedStreams_publicValueModel V
    sourcePins targetPins sourceDeclarations targetDeclarations sourceEnv targetEnv names
    sourceChecked targetChecked telescopes types definitions falsePin eqPin
  obtain ⟨sourceStrong⟩ := sourceExists
  refine ⟨⟨sourceStrong⟩, target, source, interpretation, ?_⟩
  rw [interpretation]
  exact checkedCapabilities_publicLaws sourceStrong.internal.base2.wf target
    (checkTelescopes_sound telescopes) types capabilities etaAssociations

/-- A checked nested rule supplies each actual stored pin image at the same
ordinal. Universe instantiation uses the installed owner's telescope and its
proved pin coverage, not an independently asserted target pin expression. -/
theorem checkInstalledRecursors_nested_pin_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {header : Kernel.ConstantVal} {major rulePrefix : Nat} {rules : List Kernel.RecRule}
    (present : Kernel.ConstantInfo.recInfo header major rulePrefix rules ∈ sourceEnv.consts) :
    ∃ targetHeader targetRules,
      targetEnv.find? (names header.name) = some (.recInfo targetHeader major rulePrefix targetRules) ∧
      ∀ ruleIndex (inside : ruleIndex < rules.length) sourceLevels sourcePins,
        rules[ruleIndex].fire = .nested sourceLevels sourcePins →
        ∃ targetRule targetLevels targetPins,
          targetRules[ruleIndex]? = some targetRule ∧
          targetRule.fire = .nested targetLevels targetPins ∧
          InstalledRuleHeader names rules[ruleIndex] targetRule ∧
          sourcePins.length = targetPins.length ∧
          ∀ index, index < sourcePins.length →
          ∀ sourceBase targetBase sourceUs targetUs,
            sourceUs.length = header.levelParams.length →
            targetUs.length = targetHeader.levelParams.length →
            sourceUs.map (Kernel.Level.eval sourceBase) = targetUs.map (Kernel.Level.eval targetBase) →
            InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
              target.public.cval sourceEnv targetEnv sourceBase targetBase
              ((sourcePins.getD index default).instantiateLevelParams header.levelParams sourceUs)
              ((targetPins.getD index default).instantiateLevelParams targetHeader.levelParams targetUs) := by
  obtain ⟨sourceLookup, targetHeader, targetRules, targetLookup, comparison⟩ :=
    checkInstalledRecursors_member checked present
  have images := checkInstalledRules_sound target association sourceLookup comparison
  refine ⟨targetHeader, targetRules, targetLookup, ?_⟩
  intro ruleIndex inside sourceLevels sourcePins sourceShape
  have targetInside : ruleIndex < targetRules.length := by
    rw [← (images (fun _ => 0)).length]; exact inside
  have fire := ((images (fun _ => 0)).at ruleIndex inside).fire
  rw [sourceShape] at fire
  obtain ⟨targetLevels, targetPins, targetShape⟩ :
      ∃ targetLevels targetPins, targetRules[ruleIndex].fire = .nested targetLevels targetPins := by
    generalize targetRules[ruleIndex].fire = targetFire at fire ⊢
    cases fire with
    | nested _ _ => exact ⟨_, _, rfl⟩
  have pinImages : ∀ levels, InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels header.name levels) sourcePins targetPins := by
    intro levels
    have image := ((images levels).at ruleIndex inside).fire
    rw [sourceShape, targetShape] at image
    cases image with
    | nested _ pins => exact pins
  refine ⟨targetRules[ruleIndex], targetLevels, targetPins,
    List.getElem?_eq_getElem targetInside, targetShape,
    ((images (fun _ => 0)).at ruleIndex inside).header, (pinImages (fun _ => 0)).length, ?_⟩
  intro index bound sourceBase targetBase sourceUs targetUs sourceArity targetArity universeImage
  have targetBound : index < targetPins.length := by
    rw [← (pinImages (fun _ => 0)).length]; exact bound
  have pinMember : targetPins.getD index default ∈ targetPins := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem targetBound, Option.getD_some]
    exact List.getElem_mem targetBound
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetLookup)
  have ruleWf := wf.2.2.2.2.2.1 targetHeader major rulePrefix targetRules rfl
    targetRules[ruleIndex] (List.getElem_mem targetInside)
  have pinWf := (ruleWf.2.2.2.2 targetLevels targetPins targetShape).2.2.1 _ pinMember
  exact PullbackMap.fromEnvs_instantiated_image target association sourceLookup targetLookup pinWf.2.1
    (fun levels => (pinImages levels).get index bound)
    sourceBase targetBase sourceUs targetUs sourceArity targetArity universeImage

/-- Constructor role and arities are checked on every actual source row.
Type and value images remain separate checked obligations; a matching header
alone neither certifies an application nor establishes a constructor law. -/
def checkInstalledConstructors (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .ctorInfo header params fields =>
      decide (source.find? header.name = some entry) &&
      match target.find? (names header.name) with
      | some (.ctorInfo _ targetParams targetFields) => decide (params = targetParams ∧ fields = targetFields)
      | _ => false
    | _ => true

theorem checkInstalledConstructors_member {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledConstructors source target names = true)
    {header : Kernel.ConstantVal} {params fields : Nat}
    (present : Kernel.ConstantInfo.ctorInfo header params fields ∈ source.consts) :
    source.find? header.name = some (.ctorInfo header params fields) ∧
    ∃ targetHeader, target.find? (names header.name) = some (.ctorInfo targetHeader params fields) := by
  have row := List.all_eq_true.mp checked (.ctorInfo header params fields) present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  refine ⟨row.1, ?_⟩
  cases lookup : target.find? (names header.name) with
  | none => simp [lookup] at row
  | some entry =>
    cases entry <;> simp only [lookup, decide_eq_true_eq] at row
    case ctorInfo targetHeader targetParams targetFields =>
      obtain ⟨_, rfl, rfl⟩ := row
      exact ⟨targetHeader, rfl⟩
    all_goals simp at row

/-- The target constructor required by a related fired rule is obtained from
the source frame's actual constructor lookup and the all-row check. Shared
addresses do not replace the source name's own forward lookup evidence. -/
theorem InstalledRuleFrame.target_constructor {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame sourceEnv name index)
    {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledConstructors sourceEnv targetEnv names = true)
    {sv tv sourceLevels targetLevels targetRule}
    (image : InstalledRuleImage (V := V) sv tv sourceEnv targetEnv sourceLevels targetLevels names
      frame.rule targetRule) :
    ∃ targetHeader, targetEnv.find? targetRule.ctor =
      some (.ctorInfo targetHeader frame.constructorParams frame.constructorFields) := by
  obtain ⟨_, targetHeader, lookup⟩ := checkInstalledConstructors_member checked
    (Kernel.Semantics.Env.find?_mem frame.constructorLookup)
  have sourceName : frame.constructor.name = frame.rule.ctor :=
    Kernel.Semantics.Env.find?_name frame.constructorLookup
  refine ⟨targetHeader, ?_⟩
  simpa only [sourceName, image.header.1] using lookup

theorem InstalledFireImage.fires {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl source target}
    (image : InstalledFireImage (V := V) sv tv se te sl tl source target)
    (fires : source ≠ .inert) : target ≠ .inert := by
  cases image <;> simp_all

theorem readInstalledRuleFrame_complete {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) : readInstalledRuleFrame env name index = some frame := by
  cases frame with
  | mk header major rulePrefix rules rule constructor constructorParams constructorFields
      recursorLookup ruleLookup fires constructorLookup =>
    unfold readInstalledRuleFrame
    split
    next targetHeader targetMajor targetPrefix targetRules lookup =>
      have same := lookup.symm.trans recursorLookup
      cases same
      split
      next targetRule lookup =>
        have same := lookup.symm.trans ruleLookup
        cases same
        rw [dite_eq_right fires]
        split
        next targetConstructor targetParams targetFields lookup =>
          have same := lookup.symm.trans constructorLookup
          cases same
          rfl
        next => simp_all
      next => simp_all
    next =>
      simp_all
      rename_i impossible
      exact impossible header major rulePrefix rules rfl rfl rfl rfl

/-- Both actual frames and the executable target selection follow from the
all-source rule/constructor checks. Typed applications and semantic comparison
premises are still supplied separately; frame correspondence is not reduction. -/
theorem InstalledRuleFrame.checked_target {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame sourceEnv name index) :
    ∃ targetFrame : InstalledRuleFrame targetEnv (names name) index,
      readInstalledRuleFrame targetEnv (names name) index = some targetFrame ∧
      targetFrame.major = frame.major ∧ targetFrame.rulePrefix = frame.rulePrefix ∧
      targetFrame.constructorParams = frame.constructorParams ∧
      targetFrame.constructorFields = frame.constructorFields ∧
      ∀ levels, InstalledRuleImage
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv levels
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels)
        names frame.rule targetFrame.rule := by
  have sourceName : frame.header.name = name := Kernel.Semantics.Env.find?_name frame.recursorLookup
  obtain ⟨targetHeader, targetRules, targetLookup, images⟩ := checkInstalledRecursors_sound target association recursors
    (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  obtain ⟨inside, sourceRule⟩ := List.getElem?_eq_some_iff.mp frame.ruleLookup
  have targetInside : index < targetRules.length := by
    rw [← (images (fun _ => 0)).length]; exact inside
  have ruleImages : ∀ levels, InstalledRuleImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels)
      names frame.rule targetRules[index] := by
    intro levels
    simpa only [sourceRule, sourceName] using (images levels).at index inside
  obtain ⟨constructor, constructorLookup⟩ := frame.target_constructor constructors (ruleImages (fun _ => 0))
  let targetFrame : InstalledRuleFrame targetEnv (names name) index := {
    header := targetHeader, major := frame.major, rulePrefix := frame.rulePrefix,
    rules := targetRules, rule := targetRules[index], constructor := constructor,
    constructorParams := frame.constructorParams, constructorFields := frame.constructorFields,
    recursorLookup := by simpa only [sourceName] using targetLookup,
    ruleLookup := List.getElem?_eq_getElem targetInside,
    fires := (ruleImages (fun _ => 0)).fire.fires frame.fires,
    constructorLookup := constructorLookup }
  exact ⟨targetFrame, readInstalledRuleFrame_complete targetFrame, rfl, rfl, rfl, rfl, ruleImages⟩

/-- Accepted type associations transport arbitrary semantic argument tuples
to the actual target declaration's instantiated telescope. The remaining
type is related as well; no separately proposed target header or residual is
accepted as a substitute for its installed record. -/
theorem checkInstalledTypes_telescope {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledTypes sourceEnv targetEnv names = true)
    {entry : Kernel.ConstantInfo} (present : entry ∈ sourceEnv.consts) :
    ∃ targetEntry, targetEnv.find? (names entry.name) = some targetEntry ∧
      ∀ sourceLevels targetLevels sourceUs targetUs,
        sourceUs.length = entry.toConstantVal.levelParams.length →
        targetUs.length = targetEntry.toConstantVal.levelParams.length →
        sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels) →
        ∀ (valuation finalValuation : Nat → V) (arguments : List V) result,
          InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
            sourceEnv sourceLevels valuation
            (entry.toConstantVal.type.instantiateLevelParams entry.toConstantVal.levelParams sourceUs)
            arguments finalValuation result →
          ∃ targetResult,
            InstalledTelescope target.public.cval targetEnv targetLevels valuation
              (targetEntry.toConstantVal.type.instantiateLevelParams targetEntry.toConstantVal.levelParams targetUs)
              arguments finalValuation targetResult ∧
            InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
              target.public.cval sourceEnv targetEnv sourceLevels targetLevels result targetResult := by
  obtain ⟨sourceLookup, targetEntry, targetLookup, comparison⟩ := checkInstalledTypes_member checked present
  refine ⟨targetEntry, targetLookup, ?_⟩
  intro sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universeImage
    valuation finalValuation arguments result typed
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetLookup)
  have image := checkInstalledMemberExpr_instance target association sourceLookup targetLookup wf.2.1 comparison
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universeImage
  exact typed.image image

open Kernel.SetTheory in
/-- The two semantic typing premises of a fired application, tied to actual
installed records. Parameter/index comparisons are deliberately separate. -/
structure RuleTupleTyping {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env)
    (levels : Kernel.Name → Nat) {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (universes constructorUniverses : List Kernel.Level)
    (valuation : Nat → V) (arguments fields : List V) : Prop where
  constructorTyped : ∃ final result, InstalledTelescope values env levels valuation
    (frame.constructor.type.instantiateLevelParams frame.constructor.levelParams constructorUniverses)
    fields final result
  recursorTyped : ∃ final result, InstalledTelescope values env levels valuation
    (frame.header.type.instantiateLevelParams frame.header.levelParams universes)
    (arguments ++ [fields.foldl app (values frame.rule.ctor
      (Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses))]) final result

/-- Actual checked type associations provide both target typing premises,
including the constructor-major value. The constant-instance equality comes
from the exact constructor lookups and telescope map, not a reverse alias or
an assumed equality between independently chosen models. -/
theorem InstalledRuleFrame.checked_tuple_typing {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index)
    (ruleHeader : InstalledRuleHeader names frame.rule targetFrame.rule)
    (sourceLevels targetLevels : Kernel.Name → Nat)
    (sourceUs targetUs sourceConstructorUs targetConstructorUs : List Kernel.Level)
    (sourceArity : sourceUs.length = frame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (sourceConstructorArity : sourceConstructorUs.length = frame.constructor.levelParams.length)
    (targetConstructorArity : targetConstructorUs.length = targetFrame.constructor.levelParams.length)
    (universeImage : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (constructorUniverseImage : sourceConstructorUs.map (Kernel.Level.eval sourceLevels) =
      targetConstructorUs.map (Kernel.Level.eval targetLevels))
    {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels frame sourceUs sourceConstructorUs valuation arguments fields) :
    RuleTupleTyping target.public.cval targetEnv targetLevels targetFrame targetUs targetConstructorUs
      valuation arguments fields := by
  have sourceName : frame.header.name = name := Kernel.Semantics.Env.find?_name frame.recursorLookup
  have sourceConstructorName : frame.constructor.name = frame.rule.ctor :=
    Kernel.Semantics.Env.find?_name frame.constructorLookup
  have mappedConstructorLookup : targetEnv.find? (names frame.rule.ctor) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    rw [ruleHeader.1]
    exact targetFrame.constructorLookup
  obtain ⟨selectedConstructor, constructorLookup, constructorTransport⟩ :=
    checkInstalledTypes_telescope target association types (Kernel.Semantics.Env.find?_mem frame.constructorLookup)
  have expectedConstructorLookup : targetEnv.find? (names
      (Kernel.ConstantInfo.ctorInfo frame.constructor frame.constructorParams frame.constructorFields).name) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, sourceConstructorName] using mappedConstructorLookup
  have constructorEqual := Option.some.inj (constructorLookup.symm.trans expectedConstructorLookup)
  subst selectedConstructor
  obtain ⟨constructorFinal, constructorResult, constructorTyped⟩ := typed.constructorTyped
  obtain ⟨targetConstructorResult, constructorTyped, _⟩ := constructorTransport sourceLevels targetLevels
    sourceConstructorUs targetConstructorUs sourceConstructorArity targetConstructorArity constructorUniverseImage
    valuation constructorFinal fields constructorResult constructorTyped
  have constructorValue :
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval frame.rule.ctor
        (Kernel.Level.substFn sourceLevels frame.constructor.levelParams sourceConstructorUs) =
      target.public.cval targetFrame.rule.ctor
        (Kernel.Level.substFn targetLevels targetFrame.constructor.levelParams targetConstructorUs) := by
    change target.public.cval (names frame.rule.ctor) _ = _
    rw [← ruleHeader.1]
    exact target.value_params mappedConstructorLookup _ _
      (PullbackMap.fromEnvs_instance association frame.constructorLookup mappedConstructorLookup
        sourceLevels targetLevels sourceConstructorUs targetConstructorUs
        sourceConstructorArity targetConstructorArity constructorUniverseImage)
  obtain ⟨selectedRecursor, recursorLookup, recursorTransport⟩ :=
    checkInstalledTypes_telescope target association types (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  have expectedRecursorLookup : targetEnv.find? (names
      (Kernel.ConstantInfo.recInfo frame.header frame.major frame.rulePrefix frame.rules).name) =
      some (.recInfo targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules) := by
    simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, sourceName] using targetFrame.recursorLookup
  have recursorEqual := Option.some.inj (recursorLookup.symm.trans expectedRecursorLookup)
  subst selectedRecursor
  obtain ⟨recursorFinal, recursorResult, recursorTyped⟩ := typed.recursorTyped
  obtain ⟨targetRecursorResult, recursorTyped, _⟩ := recursorTransport sourceLevels targetLevels
    sourceUs targetUs sourceArity targetArity universeImage valuation recursorFinal _ recursorResult recursorTyped
  refine ⟨⟨constructorFinal, targetConstructorResult, constructorTyped⟩,
    ⟨recursorFinal, targetRecursorResult, ?_⟩⟩
  simpa only [Kernel.ConstantInfo.toConstantVal, constructorValue] using recursorTyped

theorem ArgumentAnnotations.drop {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {depth : Nat} {valuation : Nat → V} {expressions : List Kernel.Expr}
    {annotations : List Kernel.Semantics.AnnotTerm}
    (readings : ArgumentAnnotations strong levels depth valuation expressions annotations) (count : Nat) :
    ArgumentAnnotations strong levels depth valuation (expressions.drop count) (annotations.drop count) := by
  induction readings generalizing count with
  | nil => simp; exact .nil
  | cons head tail ih =>
    cases count with
    | zero => exact .cons head tail
    | succ count => exact ih count

/-- Installed types are closed, so the two semantic tuples can be realized
under a common fresh-variable valuation without a representability premise. -/
theorem RuleTupleTyping.rebase {V : Type u} [Kernel.SetTheory V]
    {values : Kernel.Name → (Kernel.Name → Nat) → V} {env : Kernel.Env}
    (wf : Kernel.EnvWF env) {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping values env levels frame universes constructorUniverses valuation arguments fields)
    (fresh : Nat → V) : RuleTupleTyping values env levels frame universes constructorUniverses fresh arguments fields := by
  have constructorWf := wf _ (Kernel.Semantics.Env.find?_mem frame.constructorLookup)
  have recursorWf := wf _ (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  have constructorBound : (frame.constructor.type.instantiateLevelParams
      frame.constructor.levelParams constructorUniverses).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact constructorWf.2.2.2.1
  have recursorBound : (frame.header.type.instantiateLevelParams frame.header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]
    exact recursorWf.2.2.2.1
  obtain ⟨_, result, constructorTyped⟩ := typed.constructorTyped
  obtain ⟨_, recursorResult, recursorTyped⟩ := typed.recursorTyped
  exact ⟨⟨_, result, (constructorTyped.rebase constructorBound (fun _ bound => by omega)).2⟩,
    ⟨_, recursorResult, (recursorTyped.rebase recursorBound (fun _ bound => by omega)).2⟩⟩

open Kernel.Semantics in
/-- A common actual annotation representation of arbitrary argument and
field values. Metadata is used only for scope/read behavior, not as evidence
of source inference or of semantic annotation correspondence. -/
structure RuleTupleRepresentation {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} (strong : StrongInstalledModel V env) (levels : Kernel.Name → Nat)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame env name index)
    (universes constructorUniverses : List Kernel.Level) (argumentValues fieldValues : List V) where
  depth : Nat
  valuation : Nat → V
  argumentExpressions : List Kernel.Expr
  fieldExpressions : List Kernel.Expr
  arguments : List AnnotTerm
  fields : List AnnotTerm
  argumentReadings : ArgumentAnnotations strong levels depth valuation argumentExpressions arguments
  fieldReadings : ArgumentAnnotations strong levels depth valuation fieldExpressions fields
  argumentValuesEq : arguments.map (interp V valuation) = argumentValues
  fieldValuesEq : fields.map (interp V valuation) = fieldValues
  argumentClosed : argumentExpressions.map (Kernel.Expr.closeN depth) = (argumentVariables depth).take argumentValues.length
  fieldClosed : fieldExpressions.map (Kernel.Expr.closeN depth) = (argumentVariables depth).drop argumentValues.length
  typed : RuleTupleTyping strong.public.cval env levels frame universes constructorUniverses valuation argumentValues fieldValues

open Kernel.Semantics in
theorem RuleTupleTyping.represented_exact {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping strong.public.cval env levels frame universes constructorUniverses valuation arguments fields) :
    ∃ representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields,
      representation.depth = (arguments ++ fields).length ∧
      representation.valuation = pushArguments valuation (arguments ++ fields) := by
  let values := arguments ++ fields
  let fresh := pushArguments valuation values
  have readings := ArgumentAnnotations.variables strong levels values.length fresh (fun _ => .sort .zero)
    (fun _ _ => by simp [Kernel.Expr.WScoped])
  have valueEq : (argumentReadings values.length).map (interp V fresh) = values :=
    argumentReadings_values valuation values
  exact ⟨{
    depth := values.length, valuation := fresh,
    argumentExpressions := (argumentFVars values.length (fun _ => .sort .zero)).take arguments.length,
    fieldExpressions := (argumentFVars values.length (fun _ => .sort .zero)).drop arguments.length,
    arguments := (argumentReadings values.length).take arguments.length,
    fields := (argumentReadings values.length).drop arguments.length,
    argumentReadings := readings.take arguments.length,
    fieldReadings := readings.drop arguments.length,
    argumentValuesEq := by rw [List.map_take, valueEq]; simp [values],
    fieldValuesEq := by rw [List.map_drop, valueEq]; simp [values],
    argumentClosed := by rw [List.map_take, argumentFVars_closed],
    fieldClosed := by rw [List.map_drop, argumentFVars_closed],
    typed := typed.rebase strong.internal.base2.wf fresh }, rfl, rfl⟩

theorem RuleTupleTyping.represented {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {valuation : Nat → V} {arguments fields : List V}
    (typed : RuleTupleTyping strong.public.cval env levels frame universes constructorUniverses valuation arguments fields) :
    Nonempty (RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields) := by
  obtain ⟨representation, _, _⟩ := typed.represented_exact
  exact ⟨representation⟩

theorem RuleTupleRepresentation.constructor_application {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields) :
    ∃ residual, AnnotatedApplication strong levels representation.depth representation.valuation
      (frame.constructor.type.instantiateLevelParams frame.constructor.levelParams constructorUniverses)
      representation.fieldExpressions representation.fields residual := by
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem frame.constructorLookup)
  have bounded : (frame.constructor.type.instantiateLevelParams
      frame.constructor.levelParams constructorUniverses).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]; exact wf.2.2.2.1
  have noFree : (frame.constructor.type.instantiateLevelParams
      frame.constructor.levelParams constructorUniverses).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]; exact wf.1
  obtain ⟨_, _, typed⟩ := representation.typed.constructorTyped
  exact AnnotatedApplication.represented_arguments typed bounded noFree representation.fieldReadings
    representation.fieldValuesEq

open Kernel.Semantics Kernel.Model Kernel.SetTheory in
/-- Both real annotated applications are constructed under the common
valuation. The major premise is the actual constructor application reading;
no caller provides an annotation or internal fit for it. -/
theorem RuleTupleRepresentation.recursor_application {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (constructorArity : constructorUniverses.length = frame.constructor.levelParams.length) :
    ∃ residual, AnnotatedApplication strong levels representation.depth representation.valuation
      (frame.header.type.instantiateLevelParams frame.header.levelParams universes)
      (representation.argumentExpressions ++ [Kernel.Expr.mkAppN (.const frame.rule.ctor constructorUniverses)
        representation.fieldExpressions])
      (representation.arguments ++ [AnnotTerm.mkAppN
        (strong.internal.base2.acval frame.rule.ctor (Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses))
        representation.fields]) residual := by
  obtain ⟨_, constructorApplication⟩ := representation.constructor_application
  have majorReading := constructorApplication.applied_argument frame.rule.ctor
    (.ctorInfo frame.constructor frame.constructorParams frame.constructorFields) frame.constructorLookup rfl
    constructorUniverses constructorArity
  have allReadings := representation.argumentReadings.append (.cons majorReading .nil)
  have wf := strong.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  have bounded : (frame.header.type.instantiateLevelParams frame.header.levelParams universes).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]; exact wf.2.2.2.1
  have noFree : (frame.header.type.instantiateLevelParams frame.header.levelParams universes).hasFvar = false := by
    rw [Kernel.Expr.hasFvar_instantiateLevelParams]; exact wf.1
  obtain ⟨_, _, typed⟩ := representation.typed.recursorTyped
  apply AnnotatedApplication.represented_arguments typed bounded noFree allReadings
  simp only [List.map_append, List.map_cons, List.map_nil, interp_mkAppN,
    Kernel.ConstantInfo.toConstantVal, interp_cvalOf strong.internal.base2.cval_closedL,
    StrongInstalledModel.public, Kernel.Model.Model.ofEnvModelM]
  rw [representation.argumentValuesEq, ← List.foldl_map, representation.fieldValuesEq]

open Kernel.Semantics in
/-- The plain-rule comparison is derived from the semantic parameter prefix
equation on arbitrary values. Every annotation lookup is proved in bounds. -/
theorem RuleTupleRepresentation.plain_parameters {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (params : Nat) (fieldBound : params ≤ fields.length)
    (sourceEquation : fields.take params = arguments.take params) :
    ∀ position, position < params → position < representation.arguments.length →
      interp V representation.valuation (representation.fields.getD position default) =
        interp V representation.valuation (representation.arguments.getD position default) := by
  have fieldLength : representation.fields.length = fields.length := by
    simpa only [List.length_map] using congrArg List.length representation.fieldValuesEq
  have aligned := (congrArg (List.take params) representation.fieldValuesEq).trans
    (sourceEquation.trans (congrArg (List.take params) representation.argumentValuesEq).symm)
  intro position belowParams belowArguments
  have belowFields : position < representation.fields.length := by omega
  have selected := congrArg (fun values : List V => values[position]?) aligned
  simp only [List.getElem?_take, belowParams, ite_true, List.getElem?_map,
    List.getElem?_eq_getElem belowFields, List.getElem?_eq_getElem belowArguments,
    Option.map_some, Option.some.injEq] at selected
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem belowFields,
    List.getElem?_eq_getElem belowArguments, Option.getD_some] using selected

/-- Fresh representative variables have an image independently of either
constant interpretation. This does not assert an image for an immutable
source term; it supplies common variables for the value-level rule law. -/
theorem RuleTupleRepresentation.argument_image {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (sourceValues : Kernel.Name → (Kernel.Name → Nat) → V) (sourceEnv : Kernel.Env) (sourceLevels : Kernel.Name → Nat) :
    InstalledSpineImage sourceValues strong.public.cval sourceEnv env sourceLevels levels
      ((argumentVariables representation.depth).take arguments.length)
      (representation.argumentExpressions.map (Kernel.Expr.closeN representation.depth)) := by
  rw [representation.argumentClosed]
  exact (InstalledSpineImage.argumentVariables sourceValues strong.public.cval sourceEnv env sourceLevels levels
    representation.depth).take arguments.length

theorem RuleTupleRepresentation.field_image {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (sourceValues : Kernel.Name → (Kernel.Name → Nat) → V) (sourceEnv : Kernel.Env) (sourceLevels : Kernel.Name → Nat) :
    InstalledSpineImage sourceValues strong.public.cval sourceEnv env sourceLevels levels
      ((argumentVariables representation.depth).drop arguments.length)
      (representation.fieldExpressions.map (Kernel.Expr.closeN representation.depth)) := by
  rw [representation.fieldClosed]
  exact (InstalledSpineImage.argumentVariables sourceValues strong.public.cval sourceEnv env sourceLevels levels
    representation.depth).drop arguments.length

theorem RuleTupleRepresentation.source_readings {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (sourceValues : Kernel.Name → (Kernel.Name → Nat) → V) (sourceEnv : Kernel.Env) (sourceLevels : Kernel.Name → Nat) :
    DenotesSpine sourceValues sourceEnv sourceLevels representation.valuation
      ((argumentVariables representation.depth).take arguments.length) arguments ∧
    DenotesSpine sourceValues sourceEnv sourceLevels representation.valuation
      ((argumentVariables representation.depth).drop arguments.length) fields := by
  constructor
  · have reading := representation.argumentReadings.denotes.image
      (representation.argument_image sourceValues sourceEnv sourceLevels).symm
    simpa only [representation.argumentValuesEq] using reading
  · have reading := representation.fieldReadings.denotes.image
      (representation.field_image sourceValues sourceEnv sourceLevels).symm
    simpa only [representation.fieldValuesEq] using reading

theorem RuleTupleRepresentation.prefix_application {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (constructorArity : constructorUniverses.length = frame.constructor.levelParams.length) :
    ∃ residual, AnnotatedApplication strong levels representation.depth representation.valuation
      (frame.header.type.instantiateLevelParams frame.header.levelParams universes)
      representation.argumentExpressions representation.arguments residual := by
  obtain ⟨_, application⟩ := representation.recursor_application constructorArity
  obtain ⟨residual, prefixApplication⟩ := application.take representation.argumentExpressions.length
  refine ⟨residual, ?_⟩
  have expressions : (representation.argumentExpressions ++
      [Kernel.Expr.mkAppN (.const frame.rule.ctor constructorUniverses) representation.fieldExpressions]).take
      representation.argumentExpressions.length = representation.argumentExpressions := List.take_left
  have annotations : (representation.arguments ++ [Kernel.Semantics.AnnotTerm.mkAppN
      (strong.internal.base2.acval frame.rule.ctor
        (Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses)) representation.fields]).take
      representation.argumentExpressions.length = representation.arguments := by
    rw [representation.argumentReadings.length]
    exact List.take_left
  simpa only [expressions, annotations] using prefixApplication

open Kernel.Semantics Kernel.Model in
/-- Source nested-pin denotation supplies the exact target comparison at a
bounded field position. Common variable images/readings, the target prefix
application, and installed pin annotation/grading are all derived internally.
The source pin's actual rule association and semantic equation remain visible. -/
theorem RuleTupleRepresentation.nested_parameter {V : Type u} [Kernel.SetTheory V]
    {env : Kernel.Env} {strong : StrongInstalledModel V env} {levels : Kernel.Name → Nat}
    {name : Kernel.Name} {index : Nat} {frame : InstalledRuleFrame env name index}
    {universes constructorUniverses : List Kernel.Level} {arguments fields : List V}
    (representation : RuleTupleRepresentation strong levels frame universes constructorUniverses arguments fields)
    (arity : universes.length = frame.header.levelParams.length)
    (constructorArity : constructorUniverses.length = frame.constructor.levelParams.length)
    (prefixBound : frame.rulePrefix ≤ arguments.length)
    (nestedLevels : List Kernel.Level) (pins : List Kernel.Expr) (nested : frame.rule.fire = .nested nestedLevels pins)
    (position : Nat) (belowConstructor : position < frame.rule.ctorParams)
    (belowPins : position < pins.length) (belowFields : position < fields.length)
    (sourceValues : Kernel.Name → (Kernel.Name → Nat) → V) (sourceEnv : Kernel.Env) (sourceLevels : Kernel.Name → Nat)
    (sourcePin : Kernel.Expr)
    (pinImage : InstalledExprImage sourceValues strong.public.cval sourceEnv env sourceLevels levels sourcePin
      ((pins.getD position default).instantiateLevelParams frame.header.levelParams universes))
    (sourceEquation : Kernel.Denotes sourceValues sourceEnv sourceLevels representation.valuation
      (Kernel.Expr.instSeqLift (((argumentVariables representation.depth).take arguments.length).take frame.rulePrefix)
        (frame.rulePrefix - 1) sourcePin) fields[position]) :
    ∀ pin : AnnotTerm,
      denoteMeta strong.internal.base2.acval env levels frame.rulePrefix
        (Kernel.Verify.openRev 0 frame.rulePrefix
          ((pins.getD position default).instantiateLevelParams frame.header.levelParams universes)) = some pin →
      interp V representation.valuation (representation.fields.getD position default) =
        interp V representation.valuation (Kernel.Model.AnnotTerm.instRevChain
          (representation.arguments.take frame.rulePrefix) pin) := by
  obtain ⟨_, application⟩ := representation.prefix_application constructorArity
  have argumentLength : representation.arguments.length = arguments.length := by
    simpa only [List.length_map] using congrArg List.length representation.argumentValuesEq
  have fieldLength : representation.fields.length = fields.length := by
    simpa only [List.length_map] using congrArg List.length representation.fieldValuesEq
  have fieldReading := representation.fieldReadings.get position (by omega)
  have sourceReadings := representation.source_readings sourceValues sourceEnv sourceLevels
  have fieldRead := sourceReadings.2.get position belowFields
  have images := representation.field_image sourceValues sourceEnv sourceLevels
  have sourceBound : position < ((argumentVariables representation.depth).drop arguments.length).length := by
    rw [sourceReadings.2.length]; exact belowFields
  have targetBound : position < representation.fieldExpressions.length := by
    rw [representation.fieldReadings.length, fieldLength]; exact belowFields
  have fieldImage := images.get position sourceBound
  have alignedField : InstalledExprImage sourceValues strong.public.cval sourceEnv env sourceLevels levels
      (((argumentVariables representation.depth).drop arguments.length).getD position default)
      ((representation.fieldExpressions.getD position default).closeN representation.depth) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem targetBound,
      Option.map_some, Option.getD_some] using fieldImage
  have argumentImages := (representation.argument_image sourceValues sourceEnv sourceLevels).take frame.rulePrefix
  rw [← List.map_take] at argumentImages
  exact application.nested_parameter_image name frame.header frame.major frame.rulePrefix frame.rules frame.rule
    frame.recursorLookup (List.mem_of_getElem? frame.ruleLookup) universes arity
    (by omega) nestedLevels pins nested position belowConstructor belowPins fieldReading argumentImages pinImage
    alignedField fieldRead sourceEquation rfl

open Kernel.Semantics Kernel.Model in
/-- Source constructor application and index equations determine the actual
target residual's index condition. Its complete residual image and actual
annotation evidence are constructed from checked installed types, not supplied
as an independent target shape or per-index reading. -/
theorem RuleTupleRepresentation.checked_index_pin {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    {target : StrongInstalledModel V targetEnv} {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    {targetFrame : InstalledRuleFrame targetEnv (names name) index}
    (ruleHeader : InstalledRuleHeader names sourceFrame.rule targetFrame.rule)
    (prefixAgreement : sourceFrame.rulePrefix = targetFrame.rulePrefix)
    {targetLevels : Kernel.Name → Nat} {universes constructorUniverses : List Kernel.Level}
    {arguments fields : List V}
    (representation : RuleTupleRepresentation target targetLevels targetFrame universes constructorUniverses arguments fields)
    (argumentCount : arguments.length = targetFrame.major)
    (ordered : targetFrame.rulePrefix ≤ targetFrame.major)
    (sourceLevels : Kernel.Name → Nat) (sourceUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.constructor.levelParams.length)
    (targetArity : constructorUniverses.length = targetFrame.constructor.levelParams.length)
    (universeImage : sourceUs.map (Kernel.Level.eval sourceLevels) = constructorUniverses.map (Kernel.Level.eval targetLevels))
    {valuation finalValuation : Nat → V} {sourceResult : Kernel.Expr}
    (sourceTyped : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels valuation
      (sourceFrame.constructor.type.instantiateLevelParams sourceFrame.constructor.levelParams sourceUs)
      fields finalValuation sourceResult)
    (sourceIndex : ∀ residual,
      DenotedApplication ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        sourceEnv sourceLevels representation.valuation
        (sourceFrame.constructor.type.instantiateLevelParams sourceFrame.constructor.levelParams sourceUs)
        ((argumentVariables representation.depth).drop arguments.length) fields residual →
      ∃ head indices values, residual = Kernel.Expr.mkAppN head indices ∧
        DenotesSpine ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
          sourceEnv sourceLevels representation.valuation indices values ∧
        values.drop sourceFrame.rule.ctorParams = arguments.drop sourceFrame.rulePrefix) :
    ∀ residual annotation,
      Kernel.piResidual (targetFrame.constructor.type.instantiateLevelParams
        targetFrame.constructor.levelParams constructorUniverses) representation.fieldExpressions = some residual →
      denoteMeta target.internal.base2.acval targetEnv targetLevels representation.depth residual = some annotation →
      IotaIndexPin representation.valuation annotation targetFrame.rule.ctorParams targetFrame.major
        targetFrame.rulePrefix representation.arguments := by
  have sourceConstructorName : sourceFrame.constructor.name = sourceFrame.rule.ctor :=
    Kernel.Semantics.Env.find?_name sourceFrame.constructorLookup
  have mappedLookup : targetEnv.find? (names
      (Kernel.ConstantInfo.ctorInfo sourceFrame.constructor sourceFrame.constructorParams sourceFrame.constructorFields).name) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    simpa only [Kernel.ConstantInfo.name, Kernel.ConstantInfo.toConstantVal, sourceConstructorName, ruleHeader.1]
      using targetFrame.constructorLookup
  have wf := sourceWf _ (Kernel.Semantics.Env.find?_mem sourceFrame.constructorLookup)
  have bounded : (sourceFrame.constructor.type.instantiateLevelParams
      sourceFrame.constructor.levelParams sourceUs).looseBVarsBounded 0 = true := by
    rw [Kernel.Expr.looseBVarsBounded_instantiateLevelParams]; exact wf.2.2.2.1
  have rebased := (sourceTyped.rebase bounded
    (target := representation.valuation) (fun _ bound => by omega)).2
  have readings := representation.source_readings
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels
  obtain ⟨sourceResidual, sourceApplication⟩ := DenotedApplication.of_telescope rebased readings.2
  obtain ⟨head, indices, indexValues, sourceShape, indexReadings, equation⟩ := sourceIndex sourceResidual sourceApplication
  obtain ⟨targetResidual, targetApplication, residualImage⟩ := AnnotatedApplication.from_checked_type target association types
    (Kernel.Semantics.Env.find?_mem sourceFrame.constructorLookup) mappedLookup sourceLevels targetLevels
    sourceUs constructorUniverses sourceArity targetArity universeImage representation.fieldReadings sourceApplication
    (representation.field_image ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels)
  rw [sourceShape] at residualImage
  obtain ⟨actualAnnotation, evidence⟩ := targetApplication.installed_residual targetFrame.rule.ctor
    (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields)
    targetFrame.constructorLookup rfl constructorUniverses targetArity
  have count : representation.arguments.length = targetFrame.major := by
    have length := congrArg List.length representation.argumentValuesEq
    simpa only [List.length_map, argumentCount] using length
  have alignedEquation : indexValues.drop targetFrame.rule.ctorParams = arguments.drop targetFrame.rulePrefix := by
    simpa only [ruleHeader.2.2.1, prefixAgreement] using equation
  have pin := evidence.index_pin_of_residual_image representation.argumentReadings residualImage indexReadings readings.1
    (representation.argument_image ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels)
    targetFrame.rule.ctorParams targetFrame.major targetFrame.rulePrefix count ordered alignedEquation
  intro residual annotation shape reading
  have sameResidual := Option.some.inj (targetApplication.residual_shape.symm.trans shape)
  subst residual
  have sameAnnotation := Option.some.inj (evidence.reading.symm.trans reading)
  subst annotation
  exact pin

/-- A successful universe check refers to this exact executable-selected
frame, including its constructor telescope. -/
theorem InstalledRuleFrame.checked_universes {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) {universes constructorUniverses : List Kernel.Level}
    (checked : checkInstalledRuleUniverses env name index universes constructorUniverses = some true) :
    universes.length = frame.header.levelParams.length ∧
    constructorUniverses.length = frame.constructor.levelParams.length ∧
    ∀ levels, Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses =
      Kernel.Level.substFn levels frame.constructor.levelParams
        (Kernel.recFireComparands frame.rule frame.header.levelParams universes frame.constructor.levelParams [] frame.rulePrefix).1 := by
  obtain ⟨found, reading, arity, constructorArity, selection⟩ := checkInstalledRuleUniverses_sound checked
  have same := Option.some.inj (reading.symm.trans (readInstalledRuleFrame_complete frame))
  subst found
  exact ⟨arity, constructorArity, selection⟩

/-- Checked all-row rule associations apply to any two actual frames at the
same mapped owner and ordinal; no caller-chosen rule can substitute for them. -/
theorem InstalledRuleFrame.checked_images {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index) :
    sourceFrame.major = targetFrame.major ∧ sourceFrame.rulePrefix = targetFrame.rulePrefix ∧
    ∀ levels, InstalledRuleImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) names sourceFrame.rule targetFrame.rule := by
  have sourceName : sourceFrame.header.name = name := Kernel.Semantics.Env.find?_name sourceFrame.recursorLookup
  obtain ⟨header, rules, lookup, images⟩ := checkInstalledRecursors_sound target association checked
    (Kernel.Semantics.Env.find?_mem sourceFrame.recursorLookup)
  have expected : targetEnv.find? (names sourceFrame.header.name) =
      some (.recInfo targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules) := by
    simpa only [sourceName] using targetFrame.recursorLookup
  have equal := Kernel.ConstantInfo.recInfo.inj (Option.some.inj (lookup.symm.trans expected))
  refine ⟨equal.2.1, equal.2.2.1, ?_⟩
  rw [equal.2.2.2] at images
  obtain ⟨inside, sourceRule⟩ := List.getElem?_eq_some_iff.mp sourceFrame.ruleLookup
  obtain ⟨targetInside, targetRule⟩ := List.getElem?_eq_some_iff.mp targetFrame.ruleLookup
  intro levels
  simpa only [sourceRule, targetRule, sourceName] using (images levels).at index inside

theorem InstalledRuleFrame.checked_rhs_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv sourceLevels targetLevels
      (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs)
      (targetFrame.rule.rhs.instantiateLevelParams targetFrame.header.levelParams targetUs) := by
  have images := (sourceFrame.checked_images target association checked targetFrame).2.2
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetFrame.recursorLookup)
  have ruleWf := wf.2.2.2.2.2.1 targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules rfl
    targetFrame.rule (List.mem_of_getElem? targetFrame.ruleLookup)
  exact PullbackMap.fromEnvs_instantiated_image target association sourceFrame.recursorLookup targetFrame.recursorLookup
    ruleWf.2.1 (fun levels => (images levels).rhs) sourceLevels targetLevels sourceUs targetUs
    sourceArity targetArity universes

theorem InstalledFireImage.plain_iff {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl source target}
    (image : InstalledFireImage (V := V) sv tv se te sl tl source target) :
    source = .plain ↔ target = .plain := by
  cases image <;> simp

theorem InstalledFireImage.nested_source {V : Type u} [Kernel.SetTheory V]
    {sv tv se te sl tl source target} {targetLevels : List Kernel.Level} {targetPins : List Kernel.Expr}
    (image : InstalledFireImage (V := V) sv tv se te sl tl source target)
    (shape : target = .nested targetLevels targetPins) :
    ∃ sourceLevels sourcePins, source = .nested sourceLevels sourcePins := by
  cases shape
  cases image with
  | nested _ _ => exact ⟨_, _, rfl⟩

/-- Every nested pin used by the final application is the actual pin from
the two selected records and the same owner universe instance. -/
theorem InstalledRuleFrame.checked_nested_pins {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index)
    {sourceNestedLevels targetNestedLevels : List Kernel.Level} {sourcePins targetPins : List Kernel.Expr}
    (sourceShape : sourceFrame.rule.fire = .nested sourceNestedLevels sourcePins)
    (targetShape : targetFrame.rule.fire = .nested targetNestedLevels targetPins)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    sourcePins.length = targetPins.length ∧
    ∀ position, position < sourcePins.length →
      InstalledExprImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv sourceLevels targetLevels
        ((sourcePins.getD position default).instantiateLevelParams sourceFrame.header.levelParams sourceUs)
        ((targetPins.getD position default).instantiateLevelParams targetFrame.header.levelParams targetUs) := by
  have images := (sourceFrame.checked_images target association checked targetFrame).2.2
  have pinImages : ∀ levels, InstalledSpineImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      target.public.cval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) sourcePins targetPins := by
    intro levels
    have fire := (images levels).fire
    rw [sourceShape, targetShape] at fire
    cases fire with
    | nested _ pins => exact pins
  have lengths := (pinImages (fun _ => 0)).length
  refine ⟨lengths, ?_⟩
  intro position bound
  have targetBound : position < targetPins.length := by omega
  have member : targetPins.getD position default ∈ targetPins := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem targetBound, Option.getD_some]
    exact List.getElem_mem targetBound
  have wf := target.internal.base2.wf _ (Kernel.Semantics.Env.find?_mem targetFrame.recursorLookup)
  have ruleWf := wf.2.2.2.2.2.1 targetFrame.header targetFrame.major targetFrame.rulePrefix targetFrame.rules rfl
    targetFrame.rule (List.mem_of_getElem? targetFrame.ruleLookup)
  have pinWf := (ruleWf.2.2.2.2 targetNestedLevels targetPins targetShape).2.2.1 _ member
  exact PullbackMap.fromEnvs_instantiated_image target association sourceFrame.recursorLookup targetFrame.recursorLookup
    pinWf.2.1 (fun levels => (pinImages levels).get position bound)
    sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes

/-- Exact semantic universe premises of an actual fired frame. These can
come either from a concrete check or from the proved universal recipe link. -/
structure RuleUniverseSelection {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (levels : Kernel.Name → Nat)
    (universes constructorUniverses : List Kernel.Level) : Prop where
  recursorArity : universes.length = frame.header.levelParams.length
  constructorArity : constructorUniverses.length = frame.constructor.levelParams.length
  assignment : Kernel.Level.substFn levels frame.constructor.levelParams constructorUniverses =
    Kernel.Level.substFn levels frame.constructor.levelParams
      (Kernel.recFireComparands frame.rule frame.header.levelParams universes frame.constructor.levelParams [] frame.rulePrefix).1

/-- Public source-side firing conditions on value representatives. These
are semantic reduction premises, not compiler-domain membership conditions.
Nested comparison is a whole spine judgment, so pin length is derived rather
than added as an unrelated bound assumption. -/
structure SourceRuleComparisons {V : Type u} [Kernel.SetTheory V]
    (values : Kernel.Name → (Kernel.Name → Nat) → V) (env : Kernel.Env) (levels : Kernel.Name → Nat)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame env name index)
    (universes constructorUniverses : List Kernel.Level) (valuation : Nat → V)
    (argumentExpressions fieldExpressions : List Kernel.Expr) (arguments fields : List V) : Prop where
  argumentCount : arguments.length = frame.major
  fieldCount : fields.length = frame.rule.ctorParams + frame.rule.nfields
  plain : frame.rule.paramsBlind = false → frame.rule.fire = .plain →
    fields.take frame.rule.ctorParams = arguments.take frame.rule.ctorParams
  nested : ∀ nestedLevels pins, frame.rule.fire = .nested nestedLevels pins →
    DenotesSpine values env levels valuation
      (pins.map fun pin => Kernel.Expr.instSeqLift (argumentExpressions.take frame.rulePrefix) (frame.rulePrefix - 1)
        (pin.instantiateLevelParams frame.header.levelParams universes)) (fields.take frame.rule.ctorParams)
  indices : ∀ residual, DenotedApplication values env levels valuation
    (frame.constructor.type.instantiateLevelParams frame.constructor.levelParams constructorUniverses)
    fieldExpressions fields residual →
    ∃ head indices indexValues, residual = Kernel.Expr.mkAppN head indices ∧
      DenotesSpine values env levels valuation indices indexValues ∧
      indexValues.drop frame.rule.ctorParams = arguments.drop frame.rulePrefix

open Kernel.Semantics Kernel.Model in
/-- Assemble the actual target fired application from source semantic
conditions and exact installed checks. All target scope/grading, residual,
plain/nested/index and typed-application premises are derived in this proof. -/
theorem RuleTupleRepresentation.checked_application {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    {target : StrongInstalledModel V targetEnv} {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    {targetFrame : InstalledRuleFrame targetEnv (names name) index}
    {targetLevels : Kernel.Name → Nat} {universes constructorUniverses : List Kernel.Level}
    {arguments fields : List V}
    (representation : RuleTupleRepresentation target targetLevels targetFrame universes constructorUniverses arguments fields)
    (selectionEvidence : RuleUniverseSelection targetFrame targetLevels universes constructorUniverses)
    (sourceLevels : Kernel.Name → Nat) (sourceUs sourceConstructorUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (sourceConstructorArity : sourceConstructorUs.length = sourceFrame.constructor.levelParams.length)
    (universeImage : sourceUs.map (Kernel.Level.eval sourceLevels) = universes.map (Kernel.Level.eval targetLevels))
    (constructorUniverseImage : sourceConstructorUs.map (Kernel.Level.eval sourceLevels) =
      constructorUniverses.map (Kernel.Level.eval targetLevels))
    {valuation finalValuation : Nat → V} {sourceResult : Kernel.Expr}
    (sourceTyped : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels valuation
      (sourceFrame.constructor.type.instantiateLevelParams sourceFrame.constructor.levelParams sourceConstructorUs)
      fields finalValuation sourceResult)
    (conditions : SourceRuleComparisons ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs representation.valuation
      ((argumentVariables representation.depth).take arguments.length)
      ((argumentVariables representation.depth).drop arguments.length) arguments fields) :
    ∃ application : PublicRecursorApplication target targetLevels targetFrame.header targetFrame.major
        targetFrame.rulePrefix targetFrame.rule universes,
      application.valuation = representation.valuation ∧
      application.depth = representation.depth ∧
      application.argumentExpressions = representation.argumentExpressions ∧
      application.fieldExpressions = representation.fieldExpressions ∧
      application.constructor = targetFrame.constructor ∧
      application.constructorUniverses = constructorUniverses := by
  obtain ⟨majorAgreement, prefixAgreement, images⟩ := sourceFrame.checked_images target association recursors targetFrame
  let image := images (fun _ => 0)
  have header := image.header
  obtain ⟨arity, constructorArity, selection⟩ := selectionEvidence
  have ordered := (target.recursor_rule targetLevels (names name) targetFrame.header targetFrame.major targetFrame.rulePrefix
    targetFrame.rules targetFrame.recursorLookup targetFrame.rule (List.mem_of_getElem? targetFrame.ruleLookup) targetFrame.fires).1
  have argumentLength : representation.arguments.length = arguments.length := by
    simpa only [List.length_map] using congrArg List.length representation.argumentValuesEq
  have fieldLength : representation.fields.length = fields.length := by
    simpa only [List.length_map] using congrArg List.length representation.fieldValuesEq
  have argumentCount : arguments.length = targetFrame.major := conditions.argumentCount.trans majorAgreement
  have fieldCount : fields.length = targetFrame.rule.ctorParams + targetFrame.rule.nfields := by
    simpa only [header.2.1, header.2.2.1] using conditions.fieldCount
  have indexPin := representation.checked_index_pin sourceWf association types sourceFrame header prefixAgreement
    argumentCount ordered sourceLevels sourceConstructorUs sourceConstructorArity constructorArity constructorUniverseImage
    sourceTyped conditions.indices
  let application : PublicRecursorApplication target targetLevels targetFrame.header targetFrame.major
      targetFrame.rulePrefix targetFrame.rule universes := {
    constructor := targetFrame.constructor,
    constructorParams := targetFrame.constructorParams, constructorFields := targetFrame.constructorFields,
    constructorLookup := targetFrame.constructorLookup, constructorUniverses := constructorUniverses,
    constructorArity := constructorArity, depth := representation.depth, valuation := representation.valuation,
    argumentExpressions := representation.argumentExpressions, fieldExpressions := representation.fieldExpressions,
    arguments := representation.arguments, fields := representation.fields,
    argumentReadings := representation.argumentReadings, fieldReadings := representation.fieldReadings,
    argumentCount := argumentLength.trans argumentCount,
    fieldCount := fieldLength.trans fieldCount,
    universeSelection := selection,
    plainParameters := by
      intro blind plain
      have sourcePlain := image.fire.plain_iff.mpr plain
      have sourceBlind : sourceFrame.rule.paramsBlind = false := by rw [header.2.2.2.2.2]; exact blind
      have equation := conditions.plain sourceBlind sourcePlain
      rw [header.2.2.1] at equation
      intro position bound belowMajor
      exact representation.plain_parameters targetFrame.rule.ctorParams (by omega) equation position bound
        (by omega),
    nestedParameters := by
      intro nestedLevels pins nested position belowConstructor pin reading
      obtain ⟨sourceNestedLevels, sourcePins, sourceShape⟩ := image.fire.nested_source nested
      have comparisons := conditions.nested sourceNestedLevels sourcePins sourceShape
      have sourceFieldBound : sourceFrame.rule.ctorParams ≤ fields.length := by
        have count := conditions.fieldCount; omega
      have sourcePinCount : sourcePins.length = sourceFrame.rule.ctorParams := by
        simpa only [List.length_map, List.length_take, Nat.min_eq_left sourceFieldBound] using comparisons.length
      have sourceBound : position < sourcePins.length := by rw [sourcePinCount, header.2.2.1]; exact belowConstructor
      have fieldBound : position < fields.length := by omega
      obtain ⟨pinLengths, pinImages⟩ := sourceFrame.checked_nested_pins target association recursors targetFrame
        sourceShape nested sourceLevels targetLevels sourceUs universes sourceArity arity universeImage
      have selected := comparisons.get position (by simp only [List.length_take]; omega)
      have sourceEquation : Kernel.Denotes
          ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels
          representation.valuation
          (Kernel.Expr.instSeqLift (((argumentVariables representation.depth).take arguments.length).take targetFrame.rulePrefix)
            (targetFrame.rulePrefix - 1)
            ((sourcePins.getD position default).instantiateLevelParams sourceFrame.header.levelParams sourceUs)) fields[position] := by
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem sourceBound,
          Option.map_some, Option.getD_some, List.getElem_take, prefixAgreement] using selected
      exact representation.nested_parameter arity constructorArity (by omega) nestedLevels pins nested position
        belowConstructor (by omega) fieldBound _ sourceEnv sourceLevels _ (pinImages position sourceBound)
        sourceEquation pin reading,
    constructorTyped := by simpa only [representation.fieldValuesEq] using representation.typed.constructorTyped,
    recursorTyped := by simpa only [representation.argumentValuesEq, representation.fieldValuesEq] using representation.typed.recursorTyped,
    indexPin := indexPin }
  exact ⟨application, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual admitted target fired equation is pulled back to the source
recursor, constructor and stored RHS. The only semantic firing conditions
are source-side; the target application's typing and comparisons are built
by `checked_application`. This is a conditional rule theorem, not a complete
immutable-source simulation or a domain/termination claim. -/
theorem RuleTupleRepresentation.checked_fired {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    {target : StrongInstalledModel V targetEnv} {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    {targetFrame : InstalledRuleFrame targetEnv (names name) index}
    {targetLevels : Kernel.Name → Nat} {universes constructorUniverses : List Kernel.Level}
    {arguments fields : List V}
    (representation : RuleTupleRepresentation target targetLevels targetFrame universes constructorUniverses arguments fields)
    (selectionEvidence : RuleUniverseSelection targetFrame targetLevels universes constructorUniverses)
    (sourceLevels : Kernel.Name → Nat) (sourceUs sourceConstructorUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (sourceConstructorArity : sourceConstructorUs.length = sourceFrame.constructor.levelParams.length)
    (universeImage : sourceUs.map (Kernel.Level.eval sourceLevels) = universes.map (Kernel.Level.eval targetLevels))
    (constructorUniverseImage : sourceConstructorUs.map (Kernel.Level.eval sourceLevels) =
      constructorUniverses.map (Kernel.Level.eval targetLevels))
    {valuation finalValuation : Nat → V} {sourceResult : Kernel.Expr}
    (sourceTyped : InstalledTelescope ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels valuation
      (sourceFrame.constructor.type.instantiateLevelParams sourceFrame.constructor.levelParams sourceConstructorUs)
      fields finalValuation sourceResult)
    (conditions : SourceRuleComparisons ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
      sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs representation.valuation
      ((argumentVariables representation.depth).take arguments.length)
      ((argumentVariables representation.depth).drop arguments.length) arguments fields) :
    ∃ value : V,
      Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        sourceEnv sourceLevels representation.valuation
        (Kernel.Expr.mkAppN (.const name sourceUs)
          (((argumentVariables representation.depth).take arguments.length) ++
            [Kernel.Expr.mkAppN (.const sourceFrame.rule.ctor sourceConstructorUs)
              ((argumentVariables representation.depth).drop arguments.length)])) value ∧
      Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        sourceEnv sourceLevels representation.valuation
        (Kernel.Expr.mkAppN (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs)
          ((((argumentVariables representation.depth).take arguments.length).take sourceFrame.rulePrefix) ++
            (((argumentVariables representation.depth).drop arguments.length).drop sourceFrame.rule.ctorParams))) value := by
  obtain ⟨application, valuationEq, depthEq, argumentsEq, fieldsEq, _, constructorUsEq⟩ :=
    representation.checked_application sourceWf association types recursors sourceFrame selectionEvidence
      sourceLevels sourceUs sourceConstructorUs sourceArity sourceConstructorArity universeImage constructorUniverseImage
      sourceTyped conditions
  obtain ⟨_, prefixAgreement, images⟩ := sourceFrame.checked_images target association recursors targetFrame
  have header := (images (fun _ => 0)).header
  obtain ⟨arity, constructorArity, _⟩ := selectionEvidence
  have recursorImage := PullbackMap.fromEnvs_constant_instance target association sourceFrame.recursorLookup
    targetFrame.recursorLookup sourceLevels targetLevels sourceUs universes sourceArity arity universeImage
  have mappedConstructorLookup : targetEnv.find? (names sourceFrame.rule.ctor) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    rw [header.1]; exact targetFrame.constructorLookup
  have constructorImage := PullbackMap.fromEnvs_constant_instance target association sourceFrame.constructorLookup
    mappedConstructorLookup sourceLevels targetLevels sourceConstructorUs constructorUniverses
    sourceConstructorArity constructorArity constructorUniverseImage
  rw [header.1, ← constructorUsEq] at constructorImage
  have rhsImage := sourceFrame.checked_rhs_instance target association recursors targetFrame
    sourceLevels targetLevels sourceUs universes sourceArity arity universeImage
  have argumentImages := representation.argument_image
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels
  have fieldImages := representation.field_image
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels
  rw [← argumentsEq, ← depthEq] at argumentImages
  rw [← fieldsEq, ← depthEq] at fieldImages
  have fired := application.pullback (names name) targetFrame.rules targetFrame.recursorLookup
    (List.mem_of_getElem? targetFrame.ruleLookup) targetFrame.fires arity
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval) sourceEnv sourceLevels
    name sourceFrame.rule.ctor sourceUs sourceConstructorUs
    (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs)
    ((argumentVariables application.depth).take arguments.length)
    ((argumentVariables application.depth).drop arguments.length)
    recursorImage constructorImage rhsImage argumentImages fieldImages
  simpa only [valuationEq, depthEq, ← prefixAgreement, ← header.2.2.1] using fired

/-- Conditional public simulation of every actual source fired-rule frame.
The target frame and common representation are produced, not premises.
Source typing/firing semantics and checked concrete universe selection remain
visible. This is not a claim that every promised source cone passes the checks. -/
def CheckedRuleSimulation {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    (sourceEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Prop :=
  ∀ name index (sourceFrame : InstalledRuleFrame sourceEnv name index),
    ∃ targetFrame : InstalledRuleFrame targetEnv (names name) index,
      readInstalledRuleFrame targetEnv (names name) index = some targetFrame ∧
      ∀ sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs,
        sourceUs.length = sourceFrame.header.levelParams.length →
        sourceConstructorUs.length = sourceFrame.constructor.levelParams.length →
        checkInstalledRuleUniverses targetEnv (names name) index targetUs targetConstructorUs = some true →
        sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels) →
        sourceConstructorUs.map (Kernel.Level.eval sourceLevels) = targetConstructorUs.map (Kernel.Level.eval targetLevels) →
        ∀ valuation arguments fields,
          RuleTupleTyping ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
            sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs valuation arguments fields →
          ∃ representation : RuleTupleRepresentation target targetLevels targetFrame targetUs targetConstructorUs arguments fields,
            SourceRuleComparisons ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
              sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs representation.valuation
              ((argumentVariables representation.depth).take arguments.length)
              ((argumentVariables representation.depth).drop arguments.length) arguments fields →
            ∃ value : V,
              Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
                sourceEnv sourceLevels representation.valuation
                (Kernel.Expr.mkAppN (.const name sourceUs)
                  (((argumentVariables representation.depth).take arguments.length) ++
                    [Kernel.Expr.mkAppN (.const sourceFrame.rule.ctor sourceConstructorUs)
                      ((argumentVariables representation.depth).drop arguments.length)])) value ∧
              Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
                sourceEnv sourceLevels representation.valuation
                (Kernel.Expr.mkAppN (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs)
                  ((((argumentVariables representation.depth).take arguments.length).take sourceFrame.rulePrefix) ++
                    (((argumentVariables representation.depth).drop arguments.length).drop sourceFrame.rule.ctorParams))) value

theorem checked_rules_simulation {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true) :
    CheckedRuleSimulation target sourceEnv names := by
  intro name index sourceFrame
  obtain ⟨targetFrame, reading, _, _, _, _, images⟩ := sourceFrame.checked_target target association recursors constructors
  refine ⟨targetFrame, reading, ?_⟩
  intro sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs
    sourceArity sourceConstructorArity universeCheck universeImage constructorUniverseImage valuation arguments fields typed
  obtain ⟨targetArity, targetConstructorArity, selection⟩ := targetFrame.checked_universes universeCheck
  have targetTyped := sourceFrame.checked_tuple_typing target association types targetFrame (images (fun _ => 0)).header
    sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs
    sourceArity targetArity sourceConstructorArity targetConstructorArity universeImage constructorUniverseImage typed
  obtain ⟨representation⟩ := targetTyped.represented
  refine ⟨representation, ?_⟩
  intro conditions
  obtain ⟨_, _, constructorTyped⟩ := typed.constructorTyped
  exact representation.checked_fired sourceWf association types recursors sourceFrame
    ⟨targetArity, targetConstructorArity, selection targetLevels⟩ sourceLevels
    sourceUs sourceConstructorUs sourceArity sourceConstructorArity universeImage constructorUniverseImage constructorTyped conditions

/-- One admitted target model supplies the checked type/body/pinned-basis,
unit/eta and conditional fired-rule pull-backs. Source well-formedness comes
from its own independent verified fold; its separately selected interpretation
is never equated to the target-derived public source model. -/
theorem checkedStreams_publicRules (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDecls targetDecls : Array Kernel.Declaration)
    {sourceEnv targetEnv : Kernel.Env} (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDecls = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDecls = .ok targetEnv)
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (definitions : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    (etaAssociations : checkInstalledEtaAssociations sourceEnv targetEnv names = some true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ (target : StrongInstalledModel V targetEnv) (source : PublicValueModel V sourceEnv),
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval ∧
      PublicCapabilityLaws source.model.cval sourceEnv ∧ CheckedRuleSimulation target sourceEnv names := by
  obtain ⟨sourceExists, target, source, interpretation, laws⟩ := checkedStreams_publicCapabilities V
    sourcePins targetPins sourceDecls targetDecls sourceEnv targetEnv names sourceChecked targetChecked telescopes types definitions
    falsePin eqPin capabilities etaAssociations
  obtain ⟨sourceStrong⟩ := sourceExists
  exact ⟨⟨sourceStrong⟩, target, source, interpretation, laws,
    checked_rules_simulation sourceStrong.internal.base2.wf target (checkTelescopes_sound telescopes)
      types recursors constructors⟩

/-- Compare a complete universe spine in an actual owner's telescope.
Both sides must stay within that telescope; unknown semantic comparison is
preserved. This is independent of equality of the constants' model values. -/
def checkInstalledOwnerLevels (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (owner : Kernel.Name) (sourceLevels targetLevels : List Kernel.Level) : Option Bool :=
  match target.find? (names owner) with
  | none => some false
  | some targetOwner =>
    if targetLevels.all (fun level => level.allParamsDefined targetOwner.toConstantVal.levelParams) then
      checkInstalledMemberExprs source target names owner (sourceLevels.map Kernel.Expr.sort) (targetLevels.map Kernel.Expr.sort)
    else some false

theorem checkInstalledOwnerLevels_instance {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {owner : Kernel.Name} {sourceOwner targetOwner : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? owner = some sourceOwner)
    (targetLookup : targetEnv.find? (names owner) = some targetOwner)
    {sourceLevels targetLevels : List Kernel.Level}
    (checked : checkInstalledOwnerLevels sourceEnv targetEnv names owner sourceLevels targetLevels = some true)
    (sourceBase targetBase : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceOwner.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetOwner.toConstantVal.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceBase) = targetUs.map (Kernel.Level.eval targetBase)) :
    (sourceLevels.map (Kernel.Level.subst sourceOwner.toConstantVal.levelParams sourceUs)).map (Kernel.Level.eval sourceBase) =
      (targetLevels.map (Kernel.Level.subst targetOwner.toConstantVal.levelParams targetUs)).map (Kernel.Level.eval targetBase) := by
  simp only [checkInstalledOwnerLevels, targetLookup] at checked
  split at checked
  next coverage =>
    have bounded : ∀ expression ∈ targetLevels.map Kernel.Expr.sort,
        expression.allLevelParamsDefined targetOwner.toConstantVal.levelParams = true := by
      intro expression present
      obtain ⟨level, member, rfl⟩ := List.mem_map.mp present
      exact List.all_eq_true.mp coverage level member
    have images := checkInstalledMemberExprs_instance target association sourceLookup targetLookup bounded checked
      sourceBase targetBase sourceUs targetUs sourceArity targetArity universes
    have sorted : InstalledSpineImage
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        target.public.cval sourceEnv targetEnv sourceBase targetBase
        ((sourceLevels.map (Kernel.Level.subst sourceOwner.toConstantVal.levelParams sourceUs)).map Kernel.Expr.sort)
        ((targetLevels.map (Kernel.Level.subst targetOwner.toConstantVal.levelParams targetUs)).map Kernel.Expr.sort) := by
      simpa only [List.map_map, Function.comp_def, Kernel.Expr.instantiateLevelParams] using images
    exact sorted.sorts
  next => contradiction

def InstalledRuleFrame.universeComparands {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) : List Kernel.Level :=
  match frame.rule.fire with
  | .nested levels _ => levels
  | _ => frame.constructor.levelParams.map Kernel.Level.param

theorem InstalledRuleFrame.universeComparands_instance {env : Kernel.Env} {name : Kernel.Name} {index : Nat}
    (frame : InstalledRuleFrame env name index) (universes : List Kernel.Level) :
    (Kernel.recFireComparands frame.rule frame.header.levelParams universes frame.constructor.levelParams [] frame.rulePrefix).1 =
      frame.universeComparands.map (Kernel.Level.subst frame.header.levelParams universes) := by
  cases shape : frame.rule.fire <;>
    simp only [Kernel.recFireComparands, InstalledRuleFrame.universeComparands, shape, List.map_map, Function.comp_def]

/-- A finite, universal owner-relative recipe check. Arity is explicit for
nested level spines; a malformed recipe cannot hide behind `substFn` ignoring
extra arguments or retaining missing ambient parameters. -/
def checkInstalledRuleLevelLink (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (index : Nat) : Option Bool :=
  match readInstalledRuleFrame source name index, readInstalledRuleFrame target (names name) index with
  | some sourceFrame, some targetFrame =>
    if sourceFrame.universeComparands.length = sourceFrame.constructor.levelParams.length ∧
        targetFrame.universeComparands.length = targetFrame.constructor.levelParams.length then
      checkInstalledOwnerLevels source target names name sourceFrame.universeComparands targetFrame.universeComparands
    else some false
  | _, _ => some false

theorem InstalledRuleFrame.checked_level_link {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame source name index)
    (targetFrame : InstalledRuleFrame target (names name) index)
    (checked : checkInstalledRuleLevelLink source target names name index = some true) :
    sourceFrame.universeComparands.length = sourceFrame.constructor.levelParams.length ∧
    targetFrame.universeComparands.length = targetFrame.constructor.levelParams.length ∧
    checkInstalledOwnerLevels source target names name sourceFrame.universeComparands targetFrame.universeComparands = some true := by
  simp only [checkInstalledRuleLevelLink, readInstalledRuleFrame_complete sourceFrame,
    readInstalledRuleFrame_complete targetFrame] at checked
  split at checked
  next arities => exact ⟨arities.1, arities.2, checked⟩
  next => contradiction

/-- Source semantic universe selection transfers to the target for every
concrete instance of the checked owner-level recipe. No per-instance target
level-comparison acceptance or checker completeness is assumed. -/
theorem InstalledRuleFrame.transfer_universe_selection {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index)
    (checked : checkInstalledRuleLevelLink sourceEnv targetEnv names name index = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat)
    (sourceUs targetUs sourceConstructorUs targetConstructorUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceFrame.header.levelParams.length)
    (targetArity : targetUs.length = targetFrame.header.levelParams.length)
    (sourceConstructorArity : sourceConstructorUs.length = sourceFrame.constructor.levelParams.length)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (constructorUniverses : sourceConstructorUs.map (Kernel.Level.eval sourceLevels) =
      targetConstructorUs.map (Kernel.Level.eval targetLevels))
    (sourceSelection : Kernel.Level.substFn sourceLevels sourceFrame.constructor.levelParams sourceConstructorUs =
      Kernel.Level.substFn sourceLevels sourceFrame.constructor.levelParams
        (Kernel.recFireComparands sourceFrame.rule sourceFrame.header.levelParams sourceUs
          sourceFrame.constructor.levelParams [] sourceFrame.rulePrefix).1) :
    Kernel.Level.substFn targetLevels targetFrame.constructor.levelParams targetConstructorUs =
      Kernel.Level.substFn targetLevels targetFrame.constructor.levelParams
        (Kernel.recFireComparands targetFrame.rule targetFrame.header.levelParams targetUs
          targetFrame.constructor.levelParams [] targetFrame.rulePrefix).1 := by
  obtain ⟨sourceLength, _, compared⟩ := sourceFrame.checked_level_link targetFrame checked
  have values := checkInstalledOwnerLevels_instance target association sourceFrame.recursorLookup targetFrame.recursorLookup
    compared sourceLevels targetLevels sourceUs targetUs sourceArity targetArity universes
  obtain ⟨_, _, unique, _, _⟩ := association sourceFrame.rule.ctor _ sourceFrame.constructorLookup
  have compareArity : (Kernel.recFireComparands sourceFrame.rule sourceFrame.header.levelParams sourceUs
      sourceFrame.constructor.levelParams [] sourceFrame.rulePrefix).1.length = sourceFrame.constructor.levelParams.length := by
    rw [sourceFrame.universeComparands_instance]
    simpa only [List.length_map] using sourceLength
  have sourceValues := levelSubst_values_eq sourceLevels unique sourceConstructorArity compareArity sourceSelection
  rw [sourceFrame.universeComparands_instance] at sourceValues
  apply Kernel.Level.substFn_congr
  apply levelEvalEqList_of_values
  rw [targetFrame.universeComparands_instance]
  simpa only [Kernel.ConstantInfo.toConstantVal] using constructorUniverses.symm.trans (sourceValues.trans values)

theorem TelescopeAssociation.target_instance_arity {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation source target names) {name : Kernel.Name}
    {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry) (targetLookup : target.find? (names name) = some targetEntry)
    {sourceLevels targetLevels : Kernel.Name → Nat} {sourceUs targetUs : List Kernel.Level}
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (values : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    targetUs.length = targetEntry.toConstantVal.levelParams.length := by
  obtain ⟨found, lookup, _, _, sameArity⟩ := association name sourceEntry sourceLookup
  have same := Option.some.inj (lookup.symm.trans targetLookup)
  subst found
  have length : sourceUs.length = targetUs.length := by simpa only [List.length_map] using congrArg List.length values
  exact length.symm.trans (sourceArity.trans sameArity)

/-- Accepted finite recipe linkage plus source semantic selection provides
the complete target selection evidence. Target arities follow from the actual
source/target telescope map and concrete level-spine correspondence. -/
theorem InstalledRuleFrame.transfer_selection {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    {name : Kernel.Name} {index : Nat} (sourceFrame : InstalledRuleFrame sourceEnv name index)
    (targetFrame : InstalledRuleFrame targetEnv (names name) index)
    (checked : checkInstalledRuleLevelLink sourceEnv targetEnv names name index = some true)
    {sourceLevels targetLevels : Kernel.Name → Nat}
    {sourceUs targetUs sourceConstructorUs targetConstructorUs : List Kernel.Level}
    (sourceSelection : RuleUniverseSelection sourceFrame sourceLevels sourceUs sourceConstructorUs)
    (universes : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (constructorUniverses : sourceConstructorUs.map (Kernel.Level.eval sourceLevels) =
      targetConstructorUs.map (Kernel.Level.eval targetLevels)) :
    RuleUniverseSelection targetFrame targetLevels targetUs targetConstructorUs := by
  have header := ((sourceFrame.checked_images target association recursors targetFrame).2.2 (fun _ => 0)).header
  have mappedLookup : targetEnv.find? (names sourceFrame.rule.ctor) =
      some (.ctorInfo targetFrame.constructor targetFrame.constructorParams targetFrame.constructorFields) := by
    rw [header.1]; exact targetFrame.constructorLookup
  have recursorArity := association.target_instance_arity sourceFrame.recursorLookup targetFrame.recursorLookup
    sourceSelection.recursorArity universes
  have constructorArity := association.target_instance_arity sourceFrame.constructorLookup mappedLookup
    sourceSelection.constructorArity constructorUniverses
  exact ⟨recursorArity, constructorArity,
    sourceFrame.transfer_universe_selection target association targetFrame checked _ _ _ _ _ _
      sourceSelection.recursorArity recursorArity sourceSelection.constructorArity universes constructorUniverses sourceSelection.assignment⟩

def checkInstalledRuleLevelEntry (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool :=
  match entry with
  | .recInfo header _ _ rules =>
    bothChecks (some (decide (source.find? header.name = some entry)))
      ((List.range rules.length).foldr (fun index rest => bothChecks
        (match rules[index]? with
        | none => some false
        | some rule => if rule.fire = .inert then some true else
            checkInstalledRuleLevelLink source target names header.name index) rest) (some true))
  | _ => some true

/-- Every actual source row and firing-rule position receives a finite
universe-link check. Inert rules need no firing law; their full record relation
is still required by the independent rule association check. -/
def checkInstalledRuleLevelLinks (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (checkInstalledRuleLevelEntry source target names entry) rest) (some true)

theorem checkInstalledRuleLevelLinks_frame {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledRuleLevelLinks source target names = some true)
    {name : Kernel.Name} {index : Nat} (frame : InstalledRuleFrame source name index) :
    checkInstalledRuleLevelLink source target names name index = some true := by
  have row := bothChecks_fold_true checked _ (Kernel.Semantics.Env.find?_mem frame.recursorLookup)
  simp only [checkInstalledRuleLevelEntry] at row
  have rows := (bothChecks_true row).2
  obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp frame.ruleLookup
  have selected := bothChecks_fold_true rows index (List.mem_range.mpr inside)
  have sourceName : frame.header.name = name := Kernel.Semantics.Env.find?_name frame.recursorLookup
  simpa only [frame.ruleLookup, ite_eq_right frame.fires, sourceName] using selected

/-- Every source firing instance with a well-formed source universe
selection has a target representation and source equation. The finite global
recipe check replaces per-instance target checker success; no completeness
of that checker is part of this statement. -/
def UniversalRuleSimulation {V : Type u} [Kernel.SetTheory V]
    {targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    (sourceEnv : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Prop :=
  ∀ name index (sourceFrame : InstalledRuleFrame sourceEnv name index),
    ∃ targetFrame : InstalledRuleFrame targetEnv (names name) index,
      readInstalledRuleFrame targetEnv (names name) index = some targetFrame ∧
      ∀ sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs,
        RuleUniverseSelection sourceFrame sourceLevels sourceUs sourceConstructorUs →
        sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels) →
        sourceConstructorUs.map (Kernel.Level.eval sourceLevels) = targetConstructorUs.map (Kernel.Level.eval targetLevels) →
        ∀ valuation arguments fields,
          RuleTupleTyping ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
            sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs valuation arguments fields →
          ∃ representation : RuleTupleRepresentation target targetLevels targetFrame targetUs targetConstructorUs arguments fields,
            SourceRuleComparisons ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
              sourceEnv sourceLevels sourceFrame sourceUs sourceConstructorUs representation.valuation
              ((argumentVariables representation.depth).take arguments.length)
              ((argumentVariables representation.depth).drop arguments.length) arguments fields →
            ∃ value : V,
              Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
                sourceEnv sourceLevels representation.valuation
                (Kernel.Expr.mkAppN (.const name sourceUs)
                  (((argumentVariables representation.depth).take arguments.length) ++
                    [Kernel.Expr.mkAppN (.const sourceFrame.rule.ctor sourceConstructorUs)
                      ((argumentVariables representation.depth).drop arguments.length)])) value ∧
              Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
                sourceEnv sourceLevels representation.valuation
                (Kernel.Expr.mkAppN (sourceFrame.rule.rhs.instantiateLevelParams sourceFrame.header.levelParams sourceUs)
                  ((((argumentVariables representation.depth).take arguments.length).take sourceFrame.rulePrefix) ++
                    (((argumentVariables representation.depth).drop arguments.length).drop sourceFrame.rule.ctorParams))) value

theorem checked_universal_rules {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceWf : Kernel.EnvWF sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true)
    (levelLinks : checkInstalledRuleLevelLinks sourceEnv targetEnv names = some true) :
    UniversalRuleSimulation target sourceEnv names := by
  intro name index sourceFrame
  obtain ⟨targetFrame, reading, _, _, _, _, images⟩ := sourceFrame.checked_target target association recursors constructors
  refine ⟨targetFrame, reading, ?_⟩
  intro sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs
    sourceSelection universeImage constructorUniverseImage valuation arguments fields typed
  have selection := sourceFrame.transfer_selection target association recursors targetFrame
    (checkInstalledRuleLevelLinks_frame levelLinks sourceFrame) sourceSelection universeImage constructorUniverseImage
  have targetTyped := sourceFrame.checked_tuple_typing target association types targetFrame (images (fun _ => 0)).header
    sourceLevels targetLevels sourceUs targetUs sourceConstructorUs targetConstructorUs
    sourceSelection.recursorArity selection.recursorArity sourceSelection.constructorArity selection.constructorArity
    universeImage constructorUniverseImage typed
  obtain ⟨representation⟩ := targetTyped.represented
  refine ⟨representation, ?_⟩
  intro conditions
  obtain ⟨_, _, constructorTyped⟩ := typed.constructorTyped
  exact representation.checked_fired sourceWf association types recursors sourceFrame selection sourceLevels
    sourceUs sourceConstructorUs sourceSelection.recursorArity sourceSelection.constructorArity
    universeImage constructorUniverseImage constructorTyped conditions

/-- Independent checked streams yield one public source value model with
unit/eta laws and universal rule-instance simulation. Concrete target universe
checker acceptance is no longer a semantic-law premise: the finite all-row
recipe checks discharge selection from each source firing instance. Full
original-source annotation/normalization and domain totality remain separate. -/
theorem checkedStreams_universalRules (V : Type u) [Kernel.SetTheory V]
    (sourcePins targetPins : List Kernel.NatOpPinSet)
    (sourceDecls targetDecls : Array Kernel.Declaration)
    {sourceEnv targetEnv : Kernel.Env} (names : Kernel.Name → Kernel.Name)
    (sourceChecked : Kernel.Cached.checkDecls .verified sourcePins sourceDecls = .ok sourceEnv)
    (targetChecked : Kernel.Cached.checkDecls .verified targetPins targetDecls = .ok targetEnv)
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypes sourceEnv targetEnv names = true)
    (definitions : checkInstalledDefinitions sourceEnv targetEnv names = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true)
    (capabilities : checkInstalledCapabilities sourceEnv targetEnv names = true)
    (etaAssociations : checkInstalledEtaAssociations sourceEnv targetEnv names = some true)
    (recursors : checkInstalledRecursors sourceEnv targetEnv names = true)
    (constructors : checkInstalledConstructors sourceEnv targetEnv names = true)
    (levelLinks : checkInstalledRuleLevelLinks sourceEnv targetEnv names = some true) :
    Nonempty (StrongInstalledModel V sourceEnv) ∧
    ∃ (target : StrongInstalledModel V targetEnv) (source : PublicValueModel V sourceEnv),
      source.model.cval = (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval ∧
      PublicCapabilityLaws source.model.cval sourceEnv ∧ UniversalRuleSimulation target sourceEnv names := by
  obtain ⟨sourceExists, target, source, interpretation, laws, _⟩ := checkedStreams_publicRules V
    sourcePins targetPins sourceDecls targetDecls names sourceChecked targetChecked telescopes types definitions
    falsePin eqPin capabilities etaAssociations recursors constructors
  obtain ⟨sourceStrong⟩ := sourceExists
  exact ⟨⟨sourceStrong⟩, target, source, interpretation, laws,
    checked_universal_rules sourceStrong.internal.base2.wf target (checkTelescopes_sound telescopes)
      types recursors constructors levelLinks⟩

/-- Preserve unavailable expression/rule comparisons before projecting their
successful results into the older Boolean interfaces. A false result is a
failed certificate check, not a theorem of semantic inequality. Every source
row is visited, including all names in a many-to-one fiber. -/
def checkInstalledComparisonAvailability (source target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) : Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (do
    let some targetEntry := target.find? (names entry.name) | return false
    let typeResult ← checkInstalledMemberExpr source target names entry.name
      entry.toConstantVal.type targetEntry.toConstantVal.type
    if !typeResult then return false
    match entry, targetEntry with
    | .defnInfo header value _, .defnInfo _ targetValue _ =>
      checkInstalledMemberExpr source target names header.name value targetValue
    | .recInfo header _ _ rules, .recInfo _ _ _ targetRules =>
      checkInstalledRules source target names header.name rules targetRules
    | .indInfo header caps, .indInfo _ targetCaps =>
      checkInstalledMemberExpr source target names header.name
        (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps)
    | _, _ => return true) rest) (some true)

end Ix.CompileCert
