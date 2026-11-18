import IxVMRefinement.Binding.StoreClausesWalk

/-! # What the walks of the groups up to `g` reach is closed under the walk's steps

`WalkReachedBy t E₀ g x`: some group at or below `g` reaches `x` by its walk (`GroupReach`). A
used reference of such an address is reached by that group's walk when it is not covered at the
group's validation limit, and otherwise it is the address of a walked role of an earlier group,
which that role's group reaches as a root (`walkReachedBy_ref`); the block of a projection record
so reached is reached by the same group (`walkReachedBy_owner`). So the stop of a dependency path
from a walk-reached record, each step a used reference or a projection's block, is walk-reached
(`walkReachedBy_path`), and is a record a group's walk listed and checked. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **Some group at or below `g` reaches `x` by its walk.** -/
def WalkReachedBy (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (x : _root_.Address) :
    Prop :=
  ∃ k, k ≤ g ∧ GroupReach t E₀ k x

/-- **A step of a dependency path** (`KernelModeled::walk_path`): a used reference of the record,
or the block of a projection record. -/
def PathStep (E₀ : Ixon.Env) (a b : _root_.Address) : Prop :=
  UsedRef E₀ a b ∨ ∃ c, recordOf E₀ a = some c ∧ IsProj c ∧ b = Ix.Cert.ownerOf a c

/-- **A dependency path** from `a` to `b`: no step, or a path followed by a step. -/
inductive PathReach (E₀ : Ixon.Env) (a : _root_.Address) : _root_.Address → Prop where
  | refl : PathReach E₀ a a
  | tail {b c : _root_.Address} : PathReach E₀ a b → PathStep E₀ b c → PathReach E₀ a c

section Closed

variable {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

theorem WalkReachedBy.mono {g g' : Nat} (hg : g ≤ g') {x : _root_.Address}
    (h : WalkReachedBy t E₀ g x) : WalkReachedBy t E₀ g' x := by
  obtain ⟨k, hk, hr⟩ := h
  exact ⟨k, Nat.le_trans hk hg, hr⟩

/-- **A used reference of a walk-reached record is walk-reached**: by the same group when it is
not covered at the group's validation limit; otherwise it is bound to a walked role of a group
below that limit, whose group reaches it as a root. -/
theorem walkReachedBy_ref {g : Nat} {a x : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hu : UsedRef E₀ a x) : WalkReachedBy t E₀ g x := by
  obtain ⟨k, hk, hr⟩ := h
  by_cases hcov : Claim.CoveredAt t (some (valLimit k)) x
  · obtain ⟨r, had, hw, hlt⟩ := hcov
    have hlt' : Ix.SpecDigest.groupOf r < k :=
      Nat.lt_of_lt_of_le (hlt (valLimit k) rfl) (valLimit_le k)
    have hwb : RoleVal.roleWalksBound r = true := by
      rw [← Claim.walkedRole_eq_roleWalksBound]
      exact hw
    exact ⟨Ix.SpecDigest.groupOf r, Nat.le_trans (Nat.le_of_lt hlt') hk,
      GroupReach.root (role_mem_roleGroup r) (Or.inl hwb) had⟩
  · exact ⟨k, hk, GroupReach.ref hr hu hcov⟩

/-- **The block of a walk-reached projection record is walk-reached.** -/
theorem walkReachedBy_owner {g : Nat} {a : _root_.Address} {c : Ixon.Constant}
    (h : WalkReachedBy t E₀ g a) (hc : recordOf E₀ a = some c) (hp : IsProj c) :
    WalkReachedBy t E₀ g (Ix.Cert.ownerOf a c) := by
  obtain ⟨k, hk, hr⟩ := h
  exact ⟨k, hk, GroupReach.owner hr hc hp⟩

/-- **A step of a dependency path from a walk-reached record reaches a walk-reached record.** -/
theorem walkReachedBy_step {g : Nat} {a b : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hs : PathStep E₀ a b) : WalkReachedBy t E₀ g b := by
  rcases hs with hu | ⟨c, hc, hp, rfl⟩
  · exact walkReachedBy_ref h hu
  · exact walkReachedBy_owner h hc hp

/-- **The stop of a dependency path from a walk-reached record is walk-reached.** -/
theorem walkReachedBy_path {g : Nat} {a b : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hp : PathReach E₀ a b) : WalkReachedBy t E₀ g b := by
  induction hp with
  | refl => exact h
  | tail _ hs ih => exact walkReachedBy_step ih hs

/-- **A walk-reached address is a record of the walk of its group**, which the run checked under
the role context at that group's validation limit. -/
theorem WalkReachedBy.checked {calls : List (Call F)} {bAddr : _root_.Address}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hws : ∀ k, ∃ recs : List (Claim.TopRec calls bAddr t (some (valLimit k))),
      GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} {x : _root_.Address} (h : WalkReachedBy t E₀ g x) :
    ∃ k, k ≤ g ∧ UnitCheckedAt calls bAddr t E₀ x (some (valLimit k)) := by
  obtain ⟨k, hk, hr⟩ := h
  obtain ⟨recs, hw⟩ := hws k
  obtain ⟨y, -, hya⟩ := hr.listed hH hw
  refine ⟨k, hk, ?_⟩
  rw [← hya]
  exact unitCheckedAt_of_topRec hH y

end Closed

end IxVM.Refinement.Binding
