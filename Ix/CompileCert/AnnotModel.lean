import Ix.CompileCert.AnnotLevels

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

end Ix.CompileCert
