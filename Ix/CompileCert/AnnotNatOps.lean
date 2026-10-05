import Ix.CompileCert.NatEquationValues

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics Kernel.SetTheory

def checkNatEquationReceipts (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (equations : List (Kernel.Expr × Kernel.Expr)) : Option Bool :=
  equations.foldr (fun equation rest => bothChecks
    (bothChecks (some (readCheckedNatEquation source target names certificates levels equation.1).isSome)
      (some (readCheckedNatEquation source target names certificates levels equation.2).isSome)) rest) (some true)

theorem checkNatEquationReceipts_entry {source target : Kernel.Env}
    {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    {equations : List (Kernel.Expr × Kernel.Expr)}
    (checked : checkNatEquationReceipts source target names certificates levels equations = some true)
    {equation : Kernel.Expr × Kernel.Expr} (member : equation ∈ equations) :
    Nonempty (CheckedNatEquation source target names certificates levels equation.1) ∧
      Nonempty (CheckedNatEquation source target names certificates levels equation.2) := by
  have row := bothChecks_true (bothChecks_fold_true checked equation member)
  constructor
  · cases result : readCheckedNatEquation source target names certificates levels equation.1 with
    | none => simp [result] at row
    | some receipt => exact ⟨receipt⟩
  · cases result : readCheckedNatEquation source target names certificates levels equation.2 with
    | none => simp [result] at row
    | some receipt => exact ⟨receipt⟩

structure CheckedNatOperation (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (operation : Kernel.Name) where
  header : Kernel.ConstantVal
  body : Kernel.Expr
  hint : Kernel.ReducibilityHint
  lookup : target.find? operation = some (.defnInfo header body hint)
  natValue : CheckedCanonicalValue source target names Kernel.natName (certificates Kernel.natName) (levels Kernel.natName)
  equations : checkNatEquationReceipts source target names certificates levels (Kernel.natOpEquations 0 operation) = some true

def readCheckedNatOperation (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (operation : Kernel.Name) :
    Option (CheckedNatOperation source target names certificates levels operation) := do
  let some (.defnInfo header body hint) := target.find? operation | none
  if lookup : target.find? operation = some (.defnInfo header body hint) then
    let natValue ← readCheckedCanonicalValue source target names Kernel.natName
      (certificates Kernel.natName) (levels Kernel.natName)
    if equations : checkNatEquationReceipts source target names certificates levels
        (Kernel.natOpEquations 0 operation) = some true then
      some ⟨header, body, hint, lookup, natValue, equations⟩
    else none
  else none

theorem CheckedNatOperation.law {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {operation : Kernel.Name} (receipt : CheckedNatOperation source target names certificates levels operation)
    (member : operation ∈ Kernel.natOpNames) {header : Kernel.ConstantVal} {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (lookup : source.find? operation = some (.defnInfo header body hint)) (universes : Kernel.Name → Nat) :
    Kernel.natOpGuard source operation = true ∧
    ∀ equation ∈ Kernel.natOpEquations 0 operation, ∃ left right,
      denoteMeta (association.modelCore sourceModel.internal.base2 targetModel).base.acval source universes 2 equation.1 = some left ∧
      denoteMeta (association.modelCore sourceModel.internal.base2 targetModel).base.acval source universes 2 equation.2 = some right ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval Kernel.natName universes) →
        y ∈ˢ interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval Kernel.natName universes) →
        interp V (cons y (cons x ρ)) left =
          interp V (cons y (cons x ρ)) right := by
  refine ⟨(sourceModel.internal.nat_ops universes operation member header body hint lookup).1, ?_⟩
  intro equation equationMember
  obtain ⟨⟨leftReceipt⟩, ⟨rightReceipt⟩⟩ := checkNatEquationReceipts_entry receipt.equations equationMember
  obtain ⟨sourceLeft, targetLeft, sourceLeftRead, targetLeftRead, leftEq⟩ := leftReceipt.readings association sourceModel targetModel universes 2
  obtain ⟨sourceRight, targetRight, sourceRightRead, targetRightRead, rightEq⟩ := rightReceipt.readings association sourceModel targetModel universes 2
  obtain ⟨actualLeft, actualRight, actualLeftRead, actualRightRead, equationLaw⟩ :=
    (targetModel.internal.nat_ops universes operation member receipt.header receipt.body receipt.hint receipt.lookup).2 equation equationMember
  have leftIdentity := Option.some.inj (targetLeftRead.symm.trans actualLeftRead)
  have rightIdentity := Option.some.inj (targetRightRead.symm.trans actualRightRead)
  refine ⟨sourceLeft, sourceRight, sourceLeftRead, sourceRightRead, ?_⟩
  intro ρ x y xMember yMember
  have natEq := receipt.natValue.value.value_eq association sourceModel.internal.base2 targetModel universes ρ
  rw [natEq] at xMember yMember
  rw [leftEq, rightEq, leftIdentity, rightIdentity]
  exact equationLaw ρ x y xMember yMember

def checkNatOperationReceipts (source target : Kernel.Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  Kernel.natOpNames.foldr (fun operation rest => bothChecks
    (some (match source.find? operation with
      | some (.defnInfo _ _ _) => (readCheckedNatOperation source target names certificates levels operation).isSome
      | _ => true)) rest) (some true)

theorem checkNatOperationReceipts_entry {source target : Kernel.Env} {names certificates : Kernel.Name → Kernel.Name}
    {levels : Kernel.Name → Kernel.Level}
    (checked : checkNatOperationReceipts source target names certificates levels = some true)
    {operation : Kernel.Name} (member : operation ∈ Kernel.natOpNames)
    {header : Kernel.ConstantVal} {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (lookup : source.find? operation = some (.defnInfo header body hint)) :
    Nonempty (CheckedNatOperation source target names certificates levels operation) := by
  have row := bothChecks_fold_true checked operation member
  simp only [lookup, Option.some.injEq] at row
  cases result : readCheckedNatOperation source target names certificates levels operation with
  | none => simp [result] at row
  | some receipt => exact ⟨receipt⟩

theorem AnnotatedAssociation.nat_ops {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (checked : checkNatOperationReceipts source target names certificates levels = some true) (universes : Kernel.Name → Nat) :
    NatOps (association.modelCore sourceModel.internal.base2 targetModel).base universes := by
  intro operation member header body hint lookup
  obtain ⟨receipt⟩ := checkNatOperationReceipts_entry checked member lookup
  exact receipt.law association sourceModel targetModel member lookup universes

end Ix.CompileCert
