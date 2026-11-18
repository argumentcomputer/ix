import IxVMRefinement.Binding.StoreFieldsRun

/-! # The records a group's admission adds are in Lean's logic

The clause `Admits.logic` for the store sequence `groupStore t E₀`: a record new in group `g`'s
admission is `InLogic`.

* `RootsSafe t E₀`: the record bound to a role whose validation walks it is in Lean's logic,
  and so is the block it projects from (`Claim.SourceSafe`); so is the theorem of a proof in
  the evidence of a definition specified by equations, and every reference a certificate in the
  evidence of an operation uses, other than the operation's address and not covered. It is the
  one premise about the validations; everything else follows from what the walks observed.
* `groupReach_sourceSafe`: every address a group's admission reaches is `Claim.SourceSafe`:
  the roots by `RootsSafe`; a reference the group's standard axiom uses, by the axiom's safety
  and the guard its validation observed (`RoleVal.ValidateRoleIn.axiom_guard`); a reference a
  reached record uses, by the guard of the walk that recorded it (`Claim.TopRec.hguard`,
  `Claim.RecordRefsIn.safe`); the block of a reached projection record, by the owner clause of
  `SourceSafe`; a reference an equation theorem uses, by the theorem's safety and the guard of
  its walk; a reference a certificate uses, by `RootsSafe`.
* `groupStore_logic`: the clause for one group, and `logic_of_rootsSafe` for every group.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **The roots of the groups' admissions are in Lean's logic**: the record bound to a role
whose validation walks it, with the block it projects from (`bound`); the theorem of a proof in
the evidence of a definition specified by equations (`eqnsEvidence`: the validation walks it
with its closure, and its references are guarded against it); and a reference a certificate in
the evidence of an operation uses, other than the operation's address and not covered at the
operation's validation limit (`certRefs`: the validation walks it, the certificate itself is
not walked). -/
structure RootsSafe (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  bound : ∀ r, (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) →
    ∀ a, t.addressOf? r = some a → Claim.SourceSafe E₀ a
  eqnsEvidence : ∀ (r : Ix.Kernel.Role) (arr : Array (Ix.Kernel.Evidence _root_.Address))
    (thm : _root_.Address), RoleVal.roleSpecKindNat r = 5 → (r, arr) ∈ t.evidence.toList →
    Ix.Kernel.Evidence.proof thm ∈ arr.toList → Claim.SourceSafe E₀ thm
  certRefs : ∀ (r : Ix.Kernel.Role) (arr : Array (Ix.Kernel.Evidence _root_.Address))
    (thm x : _root_.Address), RoleVal.roleSpecKindNat r = 2 → (r, arr) ∈ t.evidence.toList →
    Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef E₀ thm x → t.addressOf? r ≠ some x →
    ¬ Claim.CoveredAt t (some (valLimit (Ix.SpecDigest.groupOf r))) x → Claim.SourceSafe E₀ x

/-- A safe axiom record is safe with its owner (itself). -/
theorem axiom_sourceSafe {E₀ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    {ax : Ixon.Axiom} (hc : recordOf E₀ a = some c) (hi : c.info = .axio ax)
    (hs : ax.isUnsafe = false) : Claim.SourceSafe E₀ a := by
  have hl : InLogic c := by simp only [InLogic, hi, hs]
  have hnp : ¬ IsProj c := fun hp => proj_not_axiom hp hi
  intro c' hc'
  have e : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst e
  refine ⟨hl, fun cb hcb => ?_⟩
  rw [ownerOf_of_not_proj hnp, hc] at hcb
  rw [← Option.some.inj hcb]
  exact hl

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- A used reference in the index form the guard reads. -/
private theorem usedRef_guard_form {E₀ : Ixon.Env} {a x : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ a = some c) (hu : UsedRef E₀ a x) :
    ∃ i, i ∈ IxVM.Consistency.usedRefIdxs c ∧ c.refs.toList[i]? = some x := by
  obtain ⟨c', i, hc', hi, hx⟩ := hu
  have e : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst e
  refine ⟨i, hi, ?_⟩
  simpa using hx

/-- **Every address a group's admission reaches is in Lean's logic with its block**, given the
roots. -/
theorem groupReach_sourceSafe (hC : CollisionFreeRun calls E₀) (hax : AxiomRolesDeclared t E₀)
    {g : Nat} {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hguardAx : ∀ r ∈ roleGroup g, r ∈ standardAxioms → ∀ a, t.addressOf? r = some a →
      ∃ c, recordOf E₀ a = some c ∧ Claim.RecordRefsIn calls t bAddr (some (valLimit g)) a c)
    (hguardEv : ∀ r ∈ roleGroup g, RoleVal.roleSpecKindNat r = 5 →
      ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm : _root_.Address),
      (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
      ∃ c, recordOf E₀ thm = some c ∧ Claim.RecordRefsIn calls t bAddr (some (valLimit g)) thm c)
    (hkind : ∀ r ∈ roleGroup g, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)),
      (r, arr) ∈ t.evidence.toList →
      RoleVal.roleSpecKindNat r = 2 ∨ RoleVal.roleSpecKindNat r = 5)
    (hroots : RootsSafe t E₀) :
    ∀ a, GroupReach t E₀ g a → Claim.SourceSafe E₀ a := by
  intro a ha
  induction ha with
  | root hr hwk had => exact hroots.bound _ hwk _ had
  | @evidenceRef r arr thm x hr hm hthm hu hne hnc =>
    rcases hkind r hr arr hm with h2 | h5
    · have hgr := groupOf_of_mem_roleGroup hr
      exact hroots.certRefs r arr thm x h2 hm hthm hu hne (by rw [hgr]; exact hnc)
    · obtain ⟨c, hc, hg⟩ := hguardEv r hr h5 arr thm hm hthm
      obtain ⟨i, hi', hx⟩ := usedRef_guard_form hc hu
      exact Claim.RecordRefsIn.safe hC.runStore hC.hashedStored hc
        (hroots.eqnsEvidence r arr thm h5 hm hthm) hg i hi' x hx hnc
  | @axiomRef r a x hr hs had hu hnc =>
    obtain ⟨c, hc, hg⟩ := hguardAx r hr hs a had
    obtain ⟨c₂, ax, hc₂, hi, hsf⟩ := hax r hs a had
    have e : c₂ = c := Option.some.inj (hc₂.symm.trans hc)
    subst e
    obtain ⟨i, hi', hx⟩ := usedRef_guard_form hc hu
    exact Claim.RecordRefsIn.safe hC.runStore hC.hashedStored hc (axiom_sourceSafe hc hi hsf) hg
      i hi' x hx hnc
  | @ref a x ha hu hnc ih =>
    obtain ⟨y, hy, hya⟩ := ha.listed hC.hashedStored hw
    have hc := topRec_recordOf hC.hashedStored y
    rw [hya] at hc
    have hg := y.hguard
    rw [hya] at hg
    obtain ⟨i, hi', hx⟩ := usedRef_guard_form hc hu
    exact Claim.RecordRefsIn.safe hC.runStore hC.hashedStored hc ih hg i hi' x hx hnc
  | @owner a c ha hc hp ih =>
    obtain ⟨y, hy, hya⟩ := ha.listed hC.hashedStored hw
    have hyc : y.c = c := by
      have h1 := topRec_recordOf hC.hashedStored y
      rw [hya, hc] at h1
      exact (Option.some.inj h1).symm
    obtain ⟨cb₀, hcb₀, hca⟩ := topRec_proj_member hC.runStore hC.hashedStored y (hyc ▸ hp)
    rw [hya, hyc] at hcb₀ hca
    have hnp : ¬ IsProj cb₀ := by
      intro hpb
      rcases hca with ⟨-, hst⟩ | ⟨ms, -, -, hms, -, -⟩
      · exact standalone_not_proj hst hpb
      · exact proj_not_block hpb ⟨ms, hms⟩
    obtain ⟨-, hown⟩ := ih c hc
    have hl : InLogic cb₀ := hown cb₀ hcb₀
    intro cb hcb
    have e : cb = cb₀ := Option.some.inj (hcb.symm.trans hcb₀)
    subst e
    refine ⟨hl, fun cb' hcb' => ?_⟩
    rw [ownerOf_of_not_proj hnp, hcb₀] at hcb'
    rw [← Option.some.inj hcb']
    exact hl

/-- **`Admits.logic` for one group**: a record new in the group's admission is in Lean's
logic. -/
theorem groupStore_logic (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hsafe : ∀ a, GroupReach t E₀ g a → Claim.SourceSafe E₀ a) :
    ∀ a c, New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
      recordOf (groupStore t E₀ (g + 1)) a = some c → InLogic c := by
  intro a c hnew hc
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb (Nat.le_succ_of_le hg)).mp hc).2
  rcases groupAdds_cases hC hax hw hadd with ⟨hr, -⟩ | ⟨r, hr, -, -, p, hp, hproj, -⟩ |
      ⟨ro, hro, hs, had, c₂, ax, hc₂, hinfo, hsf⟩
  · exact (hsafe a hr c hE).1
  · have e : p = c := Option.some.inj (hp.symm.trans hE)
    subst e
    rcases hproj with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> simp only [InLogic, hq]
  · have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
    subst e
    simp only [InLogic, hinfo, hsf]

/-- **`Admits.logic` for every group of a run**, from the safety of the roots. -/
theorem logic_of_rootsSafe (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hroots : RootsSafe t E₀) :
    ∀ g, 6 ≤ g → g < 77 → ∀ a c,
      New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
      recordOf (groupStore t E₀ (g + 1)) a = some c → InLogic c := by
  intro g hg6 hg
  have hax := axiomRoles_of_run hC hval
  obtain ⟨recs, hw⟩ := groupWalked_exists hC.hashedStored (hval g hg)
  refine groupStore_logic hC hb hax hg6 hw
    (groupReach_sourceSafe hC hax hw ?_ ?_ (fun r hr arr hm =>
      evidence_specKind (hval g hg r hr).wf hm) hroots)
  · intro r hr hs a had
    obtain ⟨a', raw, c, had', hsz, hh, hblk, hde, hdeE, hguard⟩ :=
      RoleVal.ValidateRoleIn.axiom_guard
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval g hg r hr)
        ((RoleVal.specKind_three_iff r).mpr hs)
    have e : a = a' := Option.some.inj (had.symm.trans had')
    subst e
    refine ⟨c, ?_, hguard⟩
    rw [← hblk]
    exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
  · intro r hr h5 arr thm hm hthm
    obtain ⟨recs', hcl', hmem⟩ := RoleVal.ValidateRoleIn.eqns_evidence_walks
      (show RoleVal.ValidateRoleIn calls bAddr t g r from hval g hg r hr) h5 hm hthm
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
    refine ⟨y.c, ?_, ?_⟩
    · rw [← hya]
      exact topRec_recordOf hC.hashedStored y
    · have hgd := y.hguard
      rw [hya] at hgd
      exact hgd

end Run

end IxVM.Refinement.Binding
