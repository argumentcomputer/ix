import Ix.CompileCert.AnnotLevels
import IxC.Kernel.Verify.EnvGuards

/-! Assemble the source annotated carrier without identifying independently
chosen model interpretations. Only source syntactic invariants and exact
reserved declaration shapes come from the independent source installation.
All annotation leaves come from the single admitted target model. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics Kernel.Verify

def checkReservedNameMap (source : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    if Kernel.reservedBasisNames.contains entry.name then decide (names entry.name = entry.name)
    else true

theorem checkReservedNameMap_sound {source : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : checkReservedNameMap source names = true)
    {name : Kernel.Name} {entry : Kernel.ConstantInfo} (lookup : source.find? name = some entry)
    (reserved : Kernel.reservedBasisNames.contains name = true) : names name = name := by
  have row := List.all_eq_true.mp checked entry (Kernel.Semantics.Env.find?_mem lookup)
  have named := Kernel.Semantics.Env.find?_name lookup
  simpa only [named, reserved, ↓reduceIte, decide_eq_true_eq] using row

noncomputable def pulledAnnotatedBase {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true) : EnvModel V sourceEnv where
  wf := sourceFacts.wf
  acval := (PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
  cval_closedL := fun name levels => target.internal.base2.cval_closedL _ _
  basis_pinnedL := by
    intro name entry lookup isReserved
    have sourcePinned := sourceFacts.basis_pinnedL name entry lookup isReserved
    have identity := checkReservedNameMap_sound reserved lookup isReserved
    obtain ⟨targetEntry, targetLookup, _⟩ := association name entry lookup
    have targetAtName : targetEnv.find? name = some targetEntry := by simpa only [identity] using targetLookup
    have targetPinned := target.internal.base2.basis_pinnedL name targetEntry targetAtName isReserved
    have same : targetEntry = entry := targetPinned.1.trans sourcePinned.1.symm
    refine ⟨sourcePinned.1, ?_⟩
    intro term levels pinned
    have value := targetPinned.2 term levels pinned
    simpa only [PullbackMap.annotations, PullbackMap.fromEnvs, identity, lookup,
      targetAtName, same, Kernel.Level.substFn_param_self] using value
  proj_ok := sourceFacts.proj_ok
  rec_ctors := sourceFacts.rec_ctors
  acval_closed := fun name levels depth => target.internal.base2.acval_closed _ _ depth
  acval_params := by
    intro name entry lookup first second agree
    exact PullbackMap.annotations_params target association lookup first second agree
  acval_wellDenoted := fun name levels valuation => target.internal.base2.acval_wellDenoted _ _ valuation

theorem pulledAnnotatedBase_valid {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true)
    (name : Kernel.Name) (levels : Kernel.Name → Nat) (valuation : Nat → V) :
    AnnotValid V valuation ((pulledAnnotatedBase sourceFacts target association reserved).acval name levels) :=
  target.internal.acval_validV _ _ valuation

open Kernel.SetTheory in
theorem pulledAnnotatedBase_types {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledTypes sourceEnv targetEnv names = true)
    (entry : Kernel.ConstantInfo) (present : entry ∈ sourceEnv.consts) (levels : Kernel.Name → Nat) :
    ∃ annotation,
      denoteMeta (pulledAnnotatedBase sourceFacts target association reserved).acval sourceEnv levels 0
        entry.toConstantVal.type = some annotation ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ annotation) ∧
      (∀ ρ : Nat → V, interp V ρ
        ((pulledAnnotatedBase sourceFacts target association reserved).acval entry.name levels) ∈ˢ
        interp V ρ annotation) :=
  checkInstalledTypes_annotated target association support checked entry present levels

theorem pulledAnnotatedBase_definitions {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true)
    (support : checkLiteralSupport sourceEnv targetEnv = true)
    (checked : checkInstalledDefinitions sourceEnv targetEnv names = true) :
    AcvalDefnInst (pulledAnnotatedBase sourceFacts target association reserved) :=
  checkInstalledDefinitions_annotated target association support checked

/-- Reserved source rows have the same exact pinned declaration in the target.
This uses the independent source shape evidence, not a content hash or a
choice of interpretation for the independently installed source model. -/
theorem pulledAnnotatedBase_reserved {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true)
    {name : Kernel.Name} {entry : Kernel.ConstantInfo}
    (lookup : sourceEnv.find? name = some entry)
    (isReserved : Kernel.reservedBasisNames.contains name = true) :
    targetEnv.find? name = some entry ∧
      ∀ levels, (pulledAnnotatedBase sourceFacts target association reserved).acval name levels =
        target.internal.base2.acval name levels := by
  have identity := checkReservedNameMap_sound reserved lookup isReserved
  obtain ⟨targetEntry, targetLookup, _⟩ := association name entry lookup
  have targetAtName : targetEnv.find? name = some targetEntry := by
    simpa only [identity] using targetLookup
  have sourcePinned := sourceFacts.basis_pinnedL name entry lookup isReserved
  have targetPinned := target.internal.base2.basis_pinnedL name targetEntry targetAtName isReserved
  have same : targetEntry = entry := targetPinned.1.trans sourcePinned.1.symm
  subst targetEntry
  refine ⟨targetAtName, ?_⟩
  intro levels
  simp only [pulledAnnotatedBase, PullbackMap.annotations, PullbackMap.fromEnvs,
    identity, lookup, targetAtName, Kernel.Level.substFn_param_self]

/-- Transfer the full annotated Eq law, including regime-sensitive grading,
on the actual pulled carrier. Public erased denotation is not used. -/
theorem pulledAnnotatedBase_eqLaw {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true) :
    EqLaw (pulledAnnotatedBase sourceFacts target association reserved) := by
  intro lookup levels
  obtain ⟨targetLookup, leaves⟩ := pulledAnnotatedBase_reserved sourceFacts target association
    reserved lookup (by decide)
  simpa only [leaves] using target.internal.eq_law targetLookup levels

/-- Nat head laws require source support only. Extra target literal support
does not impose global flag equality or restrict a literal-free source cone. -/
theorem pulledAnnotatedBase_natHeads {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (sourceFacts : EnvModel V sourceEnv)
    (target : StrongInstalledModel V targetEnv) {names : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (reserved : checkReservedNameMap sourceEnv names = true) (levels : Kernel.Name → Nat) :
    NatHeads (pulledAnnotatedBase sourceFacts target association reserved) levels := by
  intro supported
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hs, _⟩ :=
    Kernel.natLitSupported_inv supported
  obtain ⟨tn, ln⟩ := pulledAnnotatedBase_reserved sourceFacts target association reserved hn (by decide)
  obtain ⟨tz, lz⟩ := pulledAnnotatedBase_reserved sourceFacts target association reserved hz (by decide)
  obtain ⟨ts, ls⟩ := pulledAnnotatedBase_reserved sourceFacts target association reserved hs (by decide)
  have targetSupported : Kernel.natLitSupported targetEnv = true := by
    rw [← Kernel.natLitSupported_congr (hn.trans tn.symm) (hz.trans tz.symm) (hs.trans ts.symm)]
    exact supported
  simpa only [ln, lz, ls] using target.internal.nat_heads levels targetSupported

end Ix.CompileCert
