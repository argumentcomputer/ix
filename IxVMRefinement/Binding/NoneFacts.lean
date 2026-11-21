import IxVMRefinement.Binding.Glue

/-! # The fabricated roles' keys at a group with no role unit

`RoleNoneFacts` asks, at a group from 6 on with no role unit, that every fabricated role of the
group has its key stored. Every such role is a kept role (decided, `fab_kept`), so its constant
is stored at its role key by `GroupKept`, which the closure gives; and the role key is the key
of the role's address (`Core.keyOf_of_addressOf`). So that clause of `RoleNoneFacts` follows
from the closure (`fabKeys_of_groupKept`).
-/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

set_option maxRecDepth 100000 in
private theorem fab_kept_all : Ix.Kernel.Role.all.all (fun r =>
    decide (6 ≤ Ix.SpecDigest.groupOf r → Core.fabricatedRole r = true →
      r ∉ RoleOps.opRoles → r ∉ standardAxioms →
      ((walkedRole r = true ∨ r ∈ shapeAnchors) ∨ r ∈ standardAxioms))) = true := by
  decide +kernel

/-- **A fabricated role of a group from 6 on that is no role unit is a kept role** (decided). -/
theorem fab_kept {r : Ix.Kernel.Role} (h6 : 6 ≤ Ix.SpecDigest.groupOf r)
    (hf : Core.fabricatedRole r = true) (hop : r ∉ RoleOps.opRoles)
    (hax : r ∉ standardAxioms) : keptRole r :=
  of_decide_eq_true (List.all_eq_true.mp fab_kept_all r (Ix.Kernel.Role.mem_all r)) h6 hf hop hax

/-- **The fabricated roles' keys, from the closure's `GroupKept`** (module docstring). -/
theorem fabKeys_of_groupKept {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (htwf : t.wf = true) (hg6 : 6 ≤ g)
    (hnu : ∀ r ∈ roleGroup g, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms))
    (hk : GroupKept t g R env) :
    ∀ r ∈ roleGroup g, Core.fabricatedRole r = true → ∀ a, t.addressOf? r = some a →
      ∃ ci, env.find? (Core.keyOf t a) = some ci := by
  intro r hr hf a ha
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hr
  have hkr : keptRole r := fab_kept (by omega) hf (fun h => hnu r hr (Or.inl h))
    (fun h => hnu r hr (Or.inr h))
  obtain ⟨ci, hci, -⟩ := hk.1 r hr hkr (hnu r hr) a ha
  rw [Core.keyOf_of_addressOf htwf ha]
  exact ⟨ci, hci⟩

end IxVM.Refinement.Binding
