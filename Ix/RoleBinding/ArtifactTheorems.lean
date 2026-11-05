import Ix.RoleBinding.Artifact
import IxC.Kernel.Admission.Reference

/-! Target-model exports of the receipt's actual certified run. These do
not establish Source value preservation or a host claim commitment. -/
namespace Ix.RoleBinding.Artifact

theorem Receipt.strongModel (V : Type u) [Ix.Kernel.SetTheory V]
    {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits} (receipt : Receipt artifact limits) :
    Nonempty (Ix.Kernel.Cached.StrongModel V receipt.target) := by
  obtain ⟨_, _, _, checked⟩ := Ix.Kernel.Admission.checkBytesWith_checkDecls receipt.checked
  exact Ix.Kernel.Cached.checkDecls_strongModel V checked

theorem Receipt.authentic {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (receipt : Receipt artifact limits) :
    Ix.Kernel.Admission.Authentic Address.admissionHash receipt.prepared.records receipt.prepared.blobs ∧
      Address.admissionHash receipt.prepared.binding.bytes = receipt.prepared.binding.address :=
  Ix.Kernel.Admission.checkBytesWith_authentic receipt.checked

/-- A conditional receipt that lists no user axiom has the certified receipt's
model: it is that receipt (`ReceiptConditional.toReceipt`, T1). One that lists
some has no model claimed. -/
theorem ReceiptConditional.strongModel_of_nil (V : Type u) [Ix.Kernel.SetTheory V]
    {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (receipt : ReceiptConditional artifact limits) (noAxioms : receipt.axioms = []) :
    Nonempty (Ix.Kernel.Cached.StrongModel V receipt.target) :=
  (receipt.toReceipt noAxioms).strongModel V

end Ix.RoleBinding.Artifact
