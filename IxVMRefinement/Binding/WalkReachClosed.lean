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

set_option maxRecDepth 100000 in
private theorem specKind_two_walks (r : Ix.Kernel.Role) :
    RoleVal.roleSpecKindNat r = 2 → RoleVal.roleWalksBound r = true := by
  cases r <;> decide

/-- **A used reference of a walk-reached record is walk-reached** (when it is bound to no standard
axiom or quotient role): by the same group when it is not already stored; otherwise it is bound to
a walked role, walked anchor or operation of an earlier group, whose group reaches it as a root. -/
theorem walkReachedBy_ref {g : Nat} {a x : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hu : UsedRef E₀ a x)
    (hnot : ∀ r : Ix.Kernel.Role, t.addressOf? r = some x →
      r ∉ standardAxioms ∧ RoleVal.isQuotRole r = false) :
    WalkReachedBy t E₀ g x := by
  obtain ⟨k, hk, hr⟩ := h
  by_cases hst : AlreadyStoredRole t k x
  · rcases hst with ⟨r, had, ⟨hw, hlt⟩ | ⟨hnone, -⟩⟩ | ⟨r, had, hlt, hkind⟩ | ⟨r, had, hk2, hlt⟩
    · have hlt' : Ix.SpecDigest.groupOf r < k :=
        Nat.lt_of_lt_of_le (hlt (valLimit k) rfl) (valLimit_le k)
      have hwb : RoleVal.roleWalksBound r = true := by
        rw [← Claim.walkedRole_eq_roleWalksBound]
        exact hw
      exact ⟨Ix.SpecDigest.groupOf r, Nat.le_trans (Nat.le_of_lt hlt') hk,
        GroupReach.root (role_mem_roleGroup r) (Or.inl hwb) had⟩
    · cases hnone
    · have hlt' : Ix.SpecDigest.groupOf r < k := Nat.lt_of_lt_of_le hlt (valLimit_le k)
      rcases hkind with hwk | hs | hq
      · exact ⟨Ix.SpecDigest.groupOf r, Nat.le_trans (Nat.le_of_lt hlt') hk,
          GroupReach.root (role_mem_roleGroup r) (Or.inr hwk) had⟩
      · exact ((hnot r had).1 hs).elim
      · exact absurd hq (by rw [(hnot r had).2]; decide)
    · exact ⟨Ix.SpecDigest.groupOf r, Nat.le_trans (Nat.le_of_lt hlt) hk,
        GroupReach.root (role_mem_roleGroup r) (Or.inl (specKind_two_walks r hk2)) had⟩
  · exact ⟨k, hk, GroupReach.ref hr hu hst⟩

/-- **The block of a walk-reached projection record is walk-reached.** -/
theorem walkReachedBy_owner {g : Nat} {a : _root_.Address} {c : Ixon.Constant}
    (h : WalkReachedBy t E₀ g a) (hc : recordOf E₀ a = some c) (hp : IsProj c) :
    WalkReachedBy t E₀ g (Ix.Cert.ownerOf a c) := by
  obtain ⟨k, hk, hr⟩ := h
  exact ⟨k, hk, GroupReach.owner hr hc hp⟩

/-- **A step of a dependency path from a walk-reached record reaches a walk-reached record.** -/
theorem walkReachedBy_step {g : Nat} {a b : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hs : PathStep E₀ a b)
    (hnot : ∀ r : Ix.Kernel.Role, t.addressOf? r = some b →
      r ∉ standardAxioms ∧ RoleVal.isQuotRole r = false) :
    WalkReachedBy t E₀ g b := by
  rcases hs with hu | ⟨c, hc, hp, rfl⟩
  · exact walkReachedBy_ref h hu hnot
  · exact walkReachedBy_owner h hc hp

/-- **The stop of a dependency path from a walk-reached record is walk-reached.** -/
theorem walkReachedBy_path {g : Nat} {a b : _root_.Address} (h : WalkReachedBy t E₀ g a)
    (hp : PathReach E₀ a b)
    (hnot : ∀ y, PathReach E₀ a y → ∀ r : Ix.Kernel.Role, t.addressOf? r = some y →
      r ∉ standardAxioms ∧ RoleVal.isQuotRole r = false) :
    WalkReachedBy t E₀ g b := by
  induction hp with
  | refl => exact h
  | tail hp' hs ih =>
    exact walkReachedBy_step ih hs (hnot _ (PathReach.tail hp' hs))

/-- **A used-closed sub-store of `E₀` is closed under dependency paths**: every record reachable
by `PathReach` from a stored record is also stored. -/
theorem pathReach_stored_of_usedClosed {R : Ixon.Env}
    (hsub : ∀ a c, recordOf R a = some c → recordOf E₀ a = some c)
    (hcl : UsedClosed R) {a b : _root_.Address} (ha : (recordOf R a).isSome = true)
    (hp : PathReach E₀ a b) : (recordOf R b).isSome = true := by
  induction hp with
  | refl => exact ha
  | @tail x y _ hs ih =>
    obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp ih
    have hcxE := hsub x cx hcx
    rcases hs with ⟨cx', i, hcx', hi, hy⟩ | ⟨cx', hcx', _, rfl⟩
    · cases Option.some.inj (hcx'.symm.trans hcxE)
      exact (hcl.1 x _ hcx).2 i hi y hy
    · cases Option.some.inj (hcx'.symm.trans hcxE)
      exact (hcl.1 x _ hcx).1

/-- **Stored-closure completeness for `AlreadyStoredRole`**: every record reachable along a
dependency path from an `AlreadyStoredRole t g x` address is already held in
`groupStore t E₀ Pay g`. -/
theorem alreadyStored_pathReach_stored {calls : List (Call F)} {bAddr : _root_.Address}
    {Pay : PayloadRel} (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {a b : _root_.Address} (hst : AlreadyStoredRole t g a) (hp : PathReach E₀ a b) :
    (recordOf (groupStore t E₀ Pay g) b).isSome = true := by
  have hs : StoredBelow t E₀ Pay g a := storedBelow_of_alreadyStored hbr hst
  obtain ⟨ca, hca⟩ := storedBelow_record hC hb hax hP hws hs
  have ha : (recordOf (groupStore t E₀ Pay g) a).isSome = true := by
    rw [(groupStore_recordOf hb hg).mpr ⟨hs, hca⟩]
    rfl
  exact pathReach_stored_of_usedClosed (fun x c h => ((groupStore_recordOf hb hg).mp h).2)
    (groupStore_usedClosed_all hC hb hbr hax hP hws g hg) ha hp

/-- **Any unstored stop of a dependency path from a `GroupReach g` node is `GroupReach g`**: if
any intermediate step were already stored, `UsedClosed (groupStore t E₀ Pay g)` would force the
stop to be stored as well. -/
theorem groupReach_of_pathReach_new {calls : List (Call F)} {bAddr : _root_.Address}
    {Pay : PayloadRel} (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    {a b : _root_.Address} (ha : GroupReach t E₀ g a) (hp : PathReach E₀ a b)
    (hnb : recordOf (groupStore t E₀ Pay g) b = none) :
    GroupReach t E₀ g b := by
  have hcl := groupStore_usedClosed_all hC hb hbr hax hP hws g hg
  induction hp with
  | refl => exact ha
  | @tail x y hp' hs ih =>
    have hnx : recordOf (groupStore t E₀ Pay g) x = none := by
      cases hx : recordOf (groupStore t E₀ Pay g) x with
      | none => rfl
      | some cx =>
        have hsy := pathReach_stored_of_usedClosed
          (fun z c h => ((groupStore_recordOf hb hg).mp h).2) hcl
          (by rw [hx]; rfl) (PathReach.tail PathReach.refl hs)
        rw [hnb] at hsy
        cases hsy
    have hrx := ih hnx
    rcases hs with hu | ⟨c, hc, hpr, rfl⟩
    · refine GroupReach.ref hrx hu fun hst => ?_
      have hsy := alreadyStored_pathReach_stored hC hb hbr hax hP hws hg hst PathReach.refl
      rw [hnb] at hsy
      cases hsy
    · exact GroupReach.owner hrx hc hpr

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
