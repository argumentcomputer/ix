import Ix.CompileCert.DivModValues

namespace Ix.CompileCert
open Kernel Kernel.Model Kernel.Semantics Kernel.SetTheory

structure CheckedDivModOperation (source target : Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (operation : Kernel.Name) where
  header : Kernel.ConstantVal
  body : Kernel.Expr
  hint : Kernel.ReducibilityHint
  lookup : target.find? operation = some (.defnInfo header body hint)
  values : checkCanonicalValues source target names certificates levels
    (natName :: divModValueNames operation) = some true

def readCheckedDivModOperation (source target : Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) (operation : Kernel.Name) :
    Option (CheckedDivModOperation source target names certificates levels operation) := do
  let some (.defnInfo header body hint) := target.find? operation | none
  if lookup : target.find? operation = some (.defnInfo header body hint) then
    if values : checkCanonicalValues source target names certificates levels
        (natName :: divModValueNames operation) = some true then
      some ⟨header, body, hint, lookup, values⟩
    else none
  else none

/-- No incomplete source model is used to re-prove a checker install step.
The original source contributes its syntactic guard; the complete target
model contributes its actual canonical recurrence, connected by admitted
value equations for precisely the selected branch's constant leaves. -/
theorem CheckedDivModOperation.law {V : Type u} [SetTheory V]
    {source target : Env} {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {operation : Kernel.Name} (receipt : CheckedDivModOperation source target names certificates levels operation)
    (member : operation ∈ natDivModNames) {header : Kernel.ConstantVal} {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (lookup : source.find? operation = some (.defnInfo header body hint)) (universes : Kernel.Name → Nat) :
    natOpGuard source operation = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval natName universes) →
      y ∈ˢ interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval natName universes) →
      DivModClausesV V (fun name => interp V ρ
        ((association.modelCore sourceModel.internal.base2 targetModel).base.acval name universes)) operation x y := by
  refine ⟨(sourceModel.internal.div_mod universes operation member header body hint lookup).1, ?_⟩
  intro ρ x y xMember yMember
  have agreement := checkCanonicalValues_values association sourceModel targetModel receipt.values universes ρ
  have natEq := agreement natName (List.mem_cons_self)
  rw [natEq] at xMember yMember
  apply (divModClauses_values (fun name member => agreement name (List.mem_cons_of_mem _ member))).mpr
  exact (targetModel.internal.div_mod universes operation member receipt.header receipt.body receipt.hint receipt.lookup).2
    ρ x y xMember yMember

def checkDivModReceipts (source target : Env) (names certificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  natDivModNames.foldr (fun operation rest => bothChecks
    (some (match source.find? operation with
      | some (.defnInfo _ _ _) => (readCheckedDivModOperation source target names certificates levels operation).isSome
      | _ => true)) rest) (some true)

theorem checkDivModReceipts_entry {source target : Env} {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    (checked : checkDivModReceipts source target names certificates levels = some true)
    {operation : Kernel.Name} (member : operation ∈ natDivModNames)
    {header : Kernel.ConstantVal} {body : Kernel.Expr} {hint : Kernel.ReducibilityHint}
    (lookup : source.find? operation = some (.defnInfo header body hint)) :
    Nonempty (CheckedDivModOperation source target names certificates levels operation) := by
  have row := bothChecks_fold_true checked operation member
  simp only [lookup, Option.some.injEq] at row
  cases result : readCheckedDivModOperation source target names certificates levels operation with
  | none => simp [result] at row
  | some receipt => exact ⟨receipt⟩

theorem AnnotatedAssociation.div_mod {V : Type u} [SetTheory V]
    {source target : Env} {names certificates : Kernel.Name → Kernel.Name} {levels : Kernel.Name → Kernel.Level}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    (checked : checkDivModReceipts source target names certificates levels = some true) (universes : Kernel.Name → Nat) :
    DivMod (association.modelCore sourceModel.internal.base2 targetModel).base universes := by
  intro operation member header body hint lookup
  obtain ⟨receipt⟩ := checkDivModReceipts_entry checked member lookup
  exact receipt.law association sourceModel targetModel member lookup universes

end Ix.CompileCert
