import Ix.CompileCert.StrongChanged

/-! # Public membership through installed type-equality rows (S+b)

An installed theorem equating a target member's actual type with the image of
its source type suffices to transport membership. It does not supply a
structural `InstalledExprImage` between those two types. This module derives
semantic membership directly, keeping the existing structural evidence intact.

The row name is an untrusted proposal. The check reads the actual target member
and theorem, compares the equation's left endpoint with that member's type, and
checks its right endpoint in the source member's universe telescope. Every
stored source row must own its lookup, so a shadowed row cannot borrow another
row's universe parameters. Extra target support is allowed.

This supplies the type part of S+b. Changed-block capability laws, installed
recursor-rule correspondence and the source-fold bridge remain separate.
-/

namespace Ix.CompileCert

open Kernel.Reader
open Kernel.Admission
open Kernel.SetTheory

/-- The installed type-row alternative for one source member. -/
def installedTypeRowF (fS fT : Lookup) (names rows : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (sourceType : Kernel.Expr) : Bool :=
  match fT (names name), fT (rows name) with
  | some targetEntry, some (.thmInfo row _) =>
    match eqParts row.type with
    | some (_, .sort _, left, right) =>
      decide (left = targetEntry.toConstantVal.type) &&
        decide (checkInstalledMemberExprF fS fT names name sourceType right = some true)
    | _ => false
  | _, _ => false

theorem installedTypeRowF_spec {fS fT : Lookup} {names rows : Kernel.Name → Kernel.Name}
    {name : Kernel.Name} {sourceType : Kernel.Expr}
    (h : installedTypeRowF fS fT names rows name sourceType = true) :
    ∃ targetEntry row proof level sortLevel right,
      fT (names name) = some targetEntry ∧ fT (rows name) = some (.thmInfo row proof) ∧
      row.type = kernelEq level (.sort sortLevel) targetEntry.toConstantVal.type right ∧
      checkInstalledMemberExprF fS fT names name sourceType right = some true := by
  unfold installedTypeRowF at h
  cases hT : fT (names name) with
  | none => simp [hT] at h
  | some targetEntry =>
    cases hR : fT (rows name) with
    | none => simp [hT, hR] at h
    | some rowInfo =>
      cases rowInfo with
      | thmInfo row proof =>
        simp only [hT, hR] at h
        cases hp : eqParts row.type with
        | none => simp [hp] at h
        | some parts =>
          obtain ⟨level, carrier, left, right⟩ := parts
          cases carrier with
          | sort sortLevel =>
            simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨leftType, comparison⟩ := h
            refine ⟨targetEntry, row, proof, level, sortLevel, right, rfl, rfl, ?_, comparison⟩
            simpa only [leftType] using eqParts_sound hp
          | bvar _ | fvar _ _ | const _ _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
          | lit _ | proj _ _ _ => simp [hp] at h
      | axiomInfo _ | defnInfo _ _ _ | recInfo _ _ _ _ | indInfo _ _ | ctorInfo _ _ _ | projInfo _ =>
        simp [hT, hR] at h

/-- Check all actual source types, by direct comparison or an installed equation. -/
def checkInstalledTypesRowsF (source : Kernel.Env) (fS fT : Lookup)
    (names rows : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    decide (fS entry.name = some entry) &&
    ((match fT (names entry.name) with
      | none => false
      | some targetEntry => decide (checkInstalledMemberExprF fS fT names entry.name
          entry.toConstantVal.type targetEntry.toConstantVal.type = some true)) ||
      installedTypeRowF fS fT names rows entry.name entry.toConstantVal.type)

def checkInstalledTypesRows (source target : Kernel.Env)
    (names rows : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledTypesRowsF source source.find? target.find? names rows

theorem checkInstalledTypesRows_member {source target : Kernel.Env}
    {names rows : Kernel.Name → Kernel.Name}
    (checked : checkInstalledTypesRows source target names rows = true)
    {entry : Kernel.ConstantInfo} (present : entry ∈ source.consts) :
    source.find? entry.name = some entry ∧
    ((∃ targetEntry, target.find? (names entry.name) = some targetEntry ∧
        checkInstalledMemberExpr source target names entry.name
          entry.toConstantVal.type targetEntry.toConstantVal.type = some true) ∨
      installedTypeRowF source.find? target.find? names rows entry.name
        entry.toConstantVal.type = true) := by
  unfold checkInstalledTypesRows checkInstalledTypesRowsF at checked
  have row := List.all_eq_true.mp checked entry present
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at row
  refine ⟨row.1, ?_⟩
  rcases row.2 with direct | viaRow
  · left
    cases lookup : target.find? (names entry.name) with
    | none => simp [lookup] at direct
    | some targetEntry =>
      refine ⟨targetEntry, rfl, ?_⟩
      simpa only [lookup, decide_eq_true_eq, checkInstalledMemberExprF_env] using direct
  · exact .inr viaRow

/-- Installed type rows transport membership at every source level assignment
and valuation. The target theorem's own model membership supplies the typed
equation; no equality premise or independently chosen source value is assumed. -/
theorem checkInstalledTypesRows_sound {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names rows : Kernel.Name → Kernel.Name}
    (association : TelescopeAssociation sourceEnv targetEnv names)
    (checked : checkInstalledTypesRows sourceEnv targetEnv names rows = true)
    (entry : Kernel.ConstantInfo) (present : entry ∈ sourceEnv.consts)
    (levels : Kernel.Name → Nat) (valuation : Nat → V) :
    ∃ type,
      Kernel.Denotes ((PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval)
        sourceEnv levels valuation entry.toConstantVal.type type ∧
      (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval entry.name levels ∈ˢ type := by
  obtain ⟨sourceLookup, direct | viaRow⟩ := checkInstalledTypesRows_member checked present
  · obtain ⟨targetEntry, targetLookup, comparison⟩ := direct
    have image := checkInstalledMemberExpr_sound target association sourceLookup comparison levels
    have targetName : targetEntry.name = names entry.name := Kernel.Semantics.Env.find?_name targetLookup
    obtain ⟨type, typeRead, member⟩ := target.public.mem targetEntry
      (Kernel.Semantics.Env.find?_mem targetLookup)
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels entry.name levels) valuation
    refine ⟨type, image.symm.denotes typeRead, ?_⟩
    simpa only [PullbackMap.values, targetName] using member
  · obtain ⟨targetEntry, row, proof, level, sortLevel, right, targetLookup, rowLookup, rowType, comparison⟩ :=
      installedTypeRowF_spec viaRow
    rw [checkInstalledMemberExprF_env] at comparison
    have image := checkInstalledMemberExpr_sound target association sourceLookup comparison levels
    have targetName : targetEntry.name = names entry.name := Kernel.Semantics.Env.find?_name targetLookup
    obtain ⟨type, typeRead, member⟩ := target.public.mem targetEntry
      (Kernel.Semantics.Env.find?_mem targetLookup)
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels entry.name levels) valuation
    have rowPresent := Kernel.Semantics.Env.find?_mem rowLookup
    obtain ⟨rowValue, rowRead, _⟩ := target.public.mem _ rowPresent
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels entry.name levels) valuation
    change Kernel.Denotes _ _ _ _ row.type _ at rowRead
    rw [rowType] at rowRead
    unfold kernelEq at rowRead
    cases rowRead with
    | app prefixRead rightRead =>
      cases prefixRead with
      | app headRead leftRead =>
        have equal := target.theorem_eq row proof rowPresent
          (by rw [rowType]; exact InstalledTelescope.nil) leftRead rightRead
        have leftValue := Kernel.Denotes_functional leftRead typeRead
        have read := image.symm.denotes rightRead
        rw [← equal, leftValue] at read
        refine ⟨type, read, ?_⟩
        simpa only [PullbackMap.values, targetName] using member

/-- Public membership, False and Eq for the actual pulled-back interpretation.
This extends type checking without replacing structural type-image evidence. -/
noncomputable def checkedTypeRowsModel {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names rows : Kernel.Name → Kernel.Name}
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypesRows sourceEnv targetEnv names rows = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true) : Kernel.Model V sourceEnv where
  cval := (PullbackMap.fromEnvs sourceEnv targetEnv names).values target.public.cval
  mem := checkInstalledTypesRows_sound target (checkTelescopes_sound telescopes) types
  false_empty := by
    intro levels valuation value read
    have image := checkInstalledPin_sound target (checkTelescopes_sound telescopes) falsePin [] rfl levels
    exact target.public.false_empty levels valuation value (image.denotes read)
  eq_equality := by
    intro level levels valuation equality type left right read typeMember leftMember rightMember
    have image := checkInstalledPin_sound target (checkTelescopes_sound telescopes) eqPin [level] rfl levels
    exact target.public.eq_equality level levels valuation equality type left right
      (image.denotes read) typeMember leftMember rightMember

/-- The value model combines semantic type-row membership with S+a's checked
definition equations. Capability and recursor-rule transport is still required. -/
noncomputable def checkedTypeRowsValueModel {V : Type u} [Kernel.SetTheory V]
    {sourceEnv targetEnv : Kernel.Env} (target : StrongInstalledModel V targetEnv)
    {names typeRows valueRows : Kernel.Name → Kernel.Name}
    (telescopes : checkTelescopes sourceEnv targetEnv names = true)
    (types : checkInstalledTypesRows sourceEnv targetEnv names typeRows = true)
    (definitions : checkInstalledDefinitionsRows sourceEnv targetEnv names valueRows = true)
    (falsePin : checkInstalledPin sourceEnv names Kernel.falseName 0 = true)
    (eqPin : checkInstalledPin sourceEnv names Kernel.eqName 1 = true) : PublicValueModel V sourceEnv where
  model := checkedTypeRowsModel target telescopes types falsePin eqPin
  parameters := by
    intro name info lookup first second agree
    exact PullbackMap.values_params _ target
      (PullbackMap.fromEnvs_locality (checkTelescopes_sound telescopes)) lookup first second agree
  definitions := by
    intro header value hint present levels valuation
    exact checkInstalledDefinitionsRows_sound target (checkTelescopes_sound telescopes)
      definitions present levels valuation

end Ix.CompileCert
