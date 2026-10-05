import Ix.CompileCert.ValueReceipt

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics Kernel.SetTheory

/-- Actual canonical operation availability and two independently checked
value associations. Certificate names select complete theorem statements;
they are not operation-name identity assumptions. -/
structure CheckedReduceOperation (source target : Kernel.Env)
    (names : Kernel.Name → Kernel.Name) (operation operationCertificate elementCertificate : Kernel.Name) where
  header : Kernel.ConstantVal
  lookup : target.find? operation = some (.axiomInfo header)
  pin : header.matchesPin (Kernel.reduceOpCvA operation) = true
  operationValue : CheckedMappedValue source target names operation operation
    operationCertificate (.succ .zero) header.type
  elementValue : CheckedMappedValue source target names (Kernel.reduceElemName operation)
    (Kernel.reduceElemName operation) elementCertificate (.succ (.succ .zero)) (.sort (.succ .zero))

def readCheckedReduceOperation (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (operation operationCertificate elementCertificate : Kernel.Name) :
    Option (CheckedReduceOperation source target names operation operationCertificate elementCertificate) := do
  let some (.axiomInfo header) := target.find? operation | none
  if lookup : target.find? operation = some (.axiomInfo header) then
    if pin : header.matchesPin (Kernel.reduceOpCvA operation) = true then
      let operationValue ← readCheckedMappedValue source target names operation operation
        operationCertificate (.succ .zero) header.type
      let elementValue ← readCheckedMappedValue source target names (Kernel.reduceElemName operation)
        (Kernel.reduceElemName operation) elementCertificate (.succ (.succ .zero)) (.sort (.succ .zero))
      some ⟨header, lookup, pin, operationValue, elementValue⟩
    else none
  else none

/-- The operation law transfers on the already selected pulled carrier.
Source installation supplies availability; target installation supplies the
canonical semantic law; exact admitted receipts connect both value leaves. -/
theorem CheckedReduceOperation.law {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {operation operationCertificate elementCertificate : Kernel.Name}
    (receipt : CheckedReduceOperation source target names operation operationCertificate elementCertificate)
    (member : operation ∈ Kernel.reduceOpNames) {sourceHeader : Kernel.ConstantVal}
    (sourceLookup : source.find? operation = some (.axiomInfo sourceHeader))
    (sourcePin : sourceHeader.matchesPin (Kernel.reduceOpCvA operation) = true) :
    (source.find? (Kernel.reduceElemName operation)).isSome = true ∧
    ∀ (levels : Kernel.Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ ((association.modelCore sourceModel.internal.base2 targetModel).base.acval
        (Kernel.reduceElemName operation) levels) →
      Kernel.SetTheory.app (interp V ρ
        ((association.modelCore sourceModel.internal.base2 targetModel).base.acval operation levels)) x = x := by
  refine ⟨(sourceModel.internal.reduce_ops operation member sourceHeader sourceLookup sourcePin).1, ?_⟩
  intro levels ρ x membership
  have operationEq := receipt.operationValue.value_eq association sourceModel.internal.base2 targetModel levels ρ
  have elementEq := receipt.elementValue.value_eq association sourceModel.internal.base2 targetModel levels ρ
  rw [elementEq] at membership
  rw [operationEq]
  exact (targetModel.internal.reduce_ops operation member receipt.header receipt.lookup receipt.pin).2
    levels ρ x membership

/-- Additional per-compile evidence for exactly the source operation rows
to which ReduceOps applies. Missing receipts refuse this evidence tier;
they do not redefine the compiler's promised domain. -/
def checkReduceOperationReceipts (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (operationCertificates elementCertificates : Kernel.Name → Kernel.Name) : Option Bool :=
  Kernel.reduceOpNames.foldr (fun operation rest => bothChecks
    (some (match source.find? operation with
      | some (.axiomInfo header) =>
        if header.matchesPin (Kernel.reduceOpCvA operation) then
          (readCheckedReduceOperation source target names operation
            (operationCertificates operation) (elementCertificates operation)).isSome
        else true
      | _ => true)) rest) (some true)

theorem checkReduceOperationReceipts_entry {source target : Kernel.Env}
    {names operationCertificates elementCertificates : Kernel.Name → Kernel.Name}
    (checked : checkReduceOperationReceipts source target names operationCertificates elementCertificates = some true)
    {operation : Kernel.Name} (member : operation ∈ Kernel.reduceOpNames)
    {header : Kernel.ConstantVal} (lookup : source.find? operation = some (.axiomInfo header))
    (pin : header.matchesPin (Kernel.reduceOpCvA operation) = true) :
    Nonempty (CheckedReduceOperation source target names operation
      (operationCertificates operation) (elementCertificates operation)) := by
  have row := bothChecks_fold_true checked operation member
  simp only [lookup, pin, ↓reduceIte, Option.some.injEq] at row
  cases result : readCheckedReduceOperation source target names operation
      (operationCertificates operation) (elementCertificates operation) with
  | none => simp [result] at row
  | some receipt => exact ⟨receipt⟩

/-- Full ReduceOps on the existing pulled carrier, discharged from the
finite executable receipt check and the two independent installed models.
Receipt production/coverage for the promised domain remains a separate
compiler obligation; this theorem does not assume its completeness. -/
theorem AnnotatedAssociation.reduce_ops {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (association : AnnotatedAssociation source target names)
    (sourceModel : StrongInstalledModel V source) (targetModel : StrongInstalledModel V target)
    {operationCertificates elementCertificates : Kernel.Name → Kernel.Name}
    (checked : checkReduceOperationReceipts source target names operationCertificates elementCertificates = some true) :
    ReduceOps (association.modelCore sourceModel.internal.base2 targetModel).base := by
  intro operation member header lookup pin
  obtain ⟨receipt⟩ := checkReduceOperationReceipts_entry checked member lookup pin
  exact receipt.law association sourceModel targetModel member lookup pin

end Ix.CompileCert
