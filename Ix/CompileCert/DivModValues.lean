import Ix.CompileCert.AnnotReduceEntry

namespace Ix.CompileCert
open Kernel Kernel.Model Kernel.Semantics Kernel.SetTheory

/-- Exactly the constant value leaves used by the selected DivModClausesV
branch. Nat itself is a separate typed-argument membership obligation. -/
def divModValueNames (operation : Kernel.Name) : List Kernel.Name :=
  [boolTrueName, boolFalseName, natSuccName, natZeroName, natBleName, operation] ++
  (if operation = natGcdName then [natModName]
   else if operation = natShiftLeftName then [natMulName, natSubName]
   else if operation = natShiftRightName then [natDivName, natSubName]
   else if operation = natLandName then [natAddName, natMulName, natDivName, natModName]
   else if operation = natLorName then [natAddName, natMulName, natDivName, natModName, natSubName]
   else if operation = natXorName then [natAddName, natMulName, natDivName, natModName]
   else [natSubName])

theorem divModClauses_values {V : Type u} [SetTheory V]
    {left right : Kernel.Name → V} {operation : Kernel.Name} {x y : V}
    (agree : ∀ name ∈ divModValueNames operation, left name = right name) :
    DivModClausesV V left operation x y ↔ DivModClausesV V right operation x y := by
  by_cases gcd : operation = natGcdName
  · simp_all [divModValueNames, DivModClausesV]
  · by_cases shiftLeft : operation = natShiftLeftName
    · simp_all [divModValueNames, DivModClausesV]
    · by_cases shiftRight : operation = natShiftRightName
      · simp_all [divModValueNames, DivModClausesV]
      · by_cases land : operation = natLandName
        · simp_all [divModValueNames, DivModClausesV]
        · by_cases lor : operation = natLorName
          · simp_all [divModValueNames, DivModClausesV]
          · by_cases xor : operation = natXorName
            · simp_all [divModValueNames, DivModClausesV]
            · by_cases div : operation = natDivName <;> simp_all [divModValueNames, DivModClausesV]

/-- The receipt's carrier is the actual canonical target header type.
Its Eq universe remains explicit and checked by the admitted theorem row. -/
structure CheckedCanonicalValue (source target : Env) (names : Kernel.Name → Kernel.Name)
    (name certificate : Kernel.Name) (level : Kernel.Level) where
  targetEntry : Kernel.ConstantInfo
  targetLookup : target.find? name = some targetEntry
  value : CheckedMappedValue source target names name name certificate level targetEntry.toConstantVal.type

def readCheckedCanonicalValue (source target : Env) (names : Kernel.Name → Kernel.Name)
    (name certificate : Kernel.Name) (level : Kernel.Level) : Option (CheckedCanonicalValue source target names name certificate level) := do
  let some targetEntry := target.find? name | none
  if targetLookup : target.find? name = some targetEntry then
    let value ← readCheckedMappedValue source target names name name certificate level targetEntry.toConstantVal.type
    some ⟨targetEntry, targetLookup, value⟩
  else none

def checkCanonicalValues (source target : Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (required : List Kernel.Name) : Option Bool :=
  required.foldr (fun name rest => bothChecks
    (some (readCheckedCanonicalValue source target names name (certificates name) (levels name)).isSome)
    rest) (some true)

theorem checkCanonicalValues_entry {source target : Env} {names certificates : Kernel.Name → Kernel.Name}
    {levels : Kernel.Name → Kernel.Level} {required : List Kernel.Name}
    (checked : checkCanonicalValues source target names certificates levels required = some true)
    {name : Kernel.Name} (member : name ∈ required) :
    Nonempty (CheckedCanonicalValue source target names name (certificates name) (levels name)) := by
  have row := bothChecks_fold_true checked name member
  cases result : readCheckedCanonicalValue source target names name (certificates name) (levels name) with
  | none => simp [result] at row
  | some receipt => exact ⟨receipt⟩

theorem checkCanonicalValues_values {V : Type u} [SetTheory V]
    {source target : Env} {names certificates : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {levels : Kernel.Name → Kernel.Level} {required : List Kernel.Name}
    (checked : checkCanonicalValues source target names certificates levels required = some true)
    (universes : Kernel.Name → Nat) (ρ : Nat → V) :
    ∀ name ∈ required,
      interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval name universes) =
        interp V ρ (targetModel.internal.base2.acval name universes) := by
  intro name member
  obtain ⟨receipt⟩ := checkCanonicalValues_entry checked member
  exact receipt.value.value_eq association sourceModel.internal.base2 targetModel universes ρ

end Ix.CompileCert
