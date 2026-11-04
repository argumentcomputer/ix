import Ix.RoleBinding.ArtifactTiered
import IxC.Kernel.Admission.TierTheorems
import IxC.Kernel.Admission.Reference

namespace Ix.RoleBinding.Artifact

theorem TierReceipt.strongModel (V : Type u) [Ix.Kernel.SetTheory V]
    {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits} (receipt : TierReceipt artifact limits) :
    Nonempty (Ix.Kernel.Cached.StrongModel V receipt.logical) := by
  obtain ⟨_, _, _, _, _, _, _, checked⟩ := Ix.Kernel.Admission.checkBytesTieredUsing_ok receipt.checked
  obtain ⟨_, _, folded⟩ := Ix.Kernel.Admission.checkConstantsWith_checkDecls
    (Ix.Kernel.Admission.checkConstantsTiered_ok V checked).1
  exact Ix.Kernel.Cached.checkDecls_strongModel V folded

theorem TierReceipt.authentic {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (receipt : TierReceipt artifact limits) :
    Ix.Kernel.Admission.Authentic Address.admissionHash receipt.prepared.records receipt.prepared.blobs ∧
      Address.admissionHash receipt.prepared.binding.bytes = receipt.prepared.binding.address := by
  obtain ⟨authentic, _, _, _, admitted, _, _, _⟩ :=
    Ix.Kernel.Admission.checkBytesTieredUsing_ok receipt.checked
  exact ⟨authentic, ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ _).mp admitted).authentic⟩

theorem TierReceipt.typed (V : Type u) [Ix.Kernel.SetTheory V]
    {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits} (receipt : TierReceipt artifact limits) :
    Ix.Kernel.EnvWF receipt.logical ∧ (∀ c ∈ receipt.tier, receipt.logical.find? c.cv.name = none) ∧
      ∃ declarations : List (Ix.Kernel.Tier.TierDecl .anon),
        ∀ c ∈ receipt.tier, Ix.Kernel.Tier.TypedIn receipt.logical declarations receipt.tier c := by
  obtain ⟨_, _, _, _, _, _, _, checked⟩ := Ix.Kernel.Admission.checkBytesTieredUsing_ok receipt.checked
  obtain ⟨_, wf, fresh, _, declarations, _, typed⟩ := Ix.Kernel.Admission.checkConstantsTiered_ok V checked
  exact ⟨wf, fresh, declarations.toList.map (·.2), typed⟩

end Ix.RoleBinding.Artifact
