import IxVMRefinement.Binding.ClaimExport
import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.Claim.TopProj

/-! # What the observed validation of a role gives a group's admission

A group's admission asks, of the run, that every new unit was checked at the group's validation
limit or is a block's selected family record (`FamilyAdmits.checked`), and that the record of
every kept or prelude role of the group is held (`Admits.kept`). This file reads the check and
the holding off the observed validation of a role (`RoleValidationIn`), for the observed run
record.

* `unitCheckedAt_of_topRec`: a record a walk at a limit recorded is the run store's record at
  its address, and its unit was checked under the role context at that limit
  (`UnitCheckedAt`).
* `RoleValidationIn.checked_bound`: for a role whose bound record its validation walks
  (`RoleVal.roleWalksBound`, or one of the fourteen walked anchors `RoleVal.anchorWalked`), a
  closed list of records of the run's store holding the role's bound record, each checked at
  the group's validation limit exactly.
* `kept_walked`: every kept or prelude role of a group from 6 on is such a role or one of the
  two standard axioms. So the walks above hold the record of every role `Admits.kept` asks
  for, but `propext` and `Classical.choice`, whose records the fold installs as the group's
  standard axiom.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **A record a walk recorded is the run store's record at its address.** -/
theorem topRec_recordOf {calls : List (Call F)} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀) {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} (r : Claim.TopRec calls bAddr t lim) :
    recordOf E₀ r.addr = some r.c := by
  obtain ⟨lc, hget, hraw, -⟩ := hH r.rawBytes r.c r.hhashed r.hsz r.hde r.hdeExact
  rw [r.hblake] at hget
  unfold recordOf
  rw [hget]
  simp [hraw, r.hdeExact, Except.toOption]

/-- **The unit a walk recorded was checked under the role context at the walk's limit.** -/
theorem unitCheckedAt_of_topRec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀) {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} (r : Claim.TopRec calls bAddr t lim) :
    UnitCheckedAt calls bAddr t E₀ r.addr lim := by
  rcases r.hchecked with ⟨ms, hms, hk⟩ | hc
  · exact Or.inr ⟨r.c, ms, topRec_recordOf hH r, hms, hk⟩
  · exact Or.inl hc

/-- **What the observed validation of a role whose bound record is walked gives the group's
admission**: a closed list of records of the run's store, holding the role's bound record, each
checked under the role context at the group's validation limit. -/
theorem RoleValidationIn.checked_bound {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hv : RoleValidationIn calls bAddr t g r)
    (hw : RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))),
      t.addressOf? r = some a ∧ Claim.TopRecsClosed recs ∧ a ∈ recs.map (·.addr) ∧
      ∀ x ∈ recs, recordOf E₀ x.addr = some x.c ∧
        UnitCheckedAt calls bAddr t E₀ x.addr (some (valLimit g)) := by
  obtain ⟨a, recs, had, hcl, hmem⟩ :=
    RoleVal.ValidateRoleIn.lim_walks (show RoleVal.ValidateRoleIn calls bAddr t g r from hv) hw
  exact ⟨a, recs, had, hcl, hmem,
    fun x _ => ⟨topRec_recordOf hH x, unitCheckedAt_of_topRec hH x⟩⟩

set_option maxRecDepth 100000 in
private theorem kept_walked_aux (r : Ix.Kernel.Role) :
    6 ≤ Ix.SpecDigest.groupOf r →
    (walkedRole r = true ∨ r ∈ shapeAnchors ∨ r ∈ standardAxioms ∨ r ∈ preludeRoles) →
    RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true ∨ r ∈ standardAxioms := by
  cases r <;> decide +kernel

/-- **Every kept or prelude role of a group from 6 on has its bound record walked by its
validation, or is one of the two standard axioms.** -/
theorem kept_walked {r : Ix.Kernel.Role} (hg : 6 ≤ Ix.SpecDigest.groupOf r)
    (hk : keptRole r ∨ r ∈ preludeRoles) :
    RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true ∨ r ∈ standardAxioms := by
  refine kept_walked_aux r hg ?_
  rcases hk with ((hw | hs) | ha) | hp
  · exact Or.inl hw
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr hp))

/-- **The record of a kept or prelude role of a group from 6 on, other than a standard axiom,
is a record of the run's store checked at the group's validation limit**, with the closed list
of records its walk checked there: what `Admits.kept` and the first alternative of
`FamilyAdmits.checked` ask of the run for that role, from the role's observed validation. -/
theorem RoleValidationIn.kept_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hg6 : 6 ≤ g) (hr : r ∈ roleGroup g)
    (hk : keptRole r ∨ r ∈ preludeRoles) (hns : r ∉ standardAxioms)
    (hv : RoleValidationIn calls bAddr t g r) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))),
      t.addressOf? r = some a ∧ Claim.TopRecsClosed recs ∧ a ∈ recs.map (·.addr) ∧
      ∀ x ∈ recs, recordOf E₀ x.addr = some x.c ∧
        UnitCheckedAt calls bAddr t E₀ x.addr (some (valLimit g)) := by
  have hgr : 6 ≤ Ix.SpecDigest.groupOf r := by
    rw [groupOf_of_mem_roleGroup hr]
    exact hg6
  rcases kept_walked hgr hk with hw | hw | hs
  · exact RoleValidationIn.checked_bound hH hv (Or.inl hw)
  · exact RoleValidationIn.checked_bound hH hv (Or.inr hw)
  · exact absurd hs hns

/-! ## The projection records of a walked block

A walk checks a block member by member, and each member's check hashes the member's projection
record and, for an inductive member, each constructor's. The claim layer reads this off the
check evidence at any limit (`Claim.member_records`, `Claim.proj_member_of_checked`,
`Claim.checked_not_block`); these are the same facts for a record of a walk at a group's
validation limit: the block clause of `UsedClosed` and the clause `Admits.projMember`. -/

/-- **A block a walk recorded was checked member by member.** -/
theorem topRec_block_checked {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (r : Claim.TopRec calls bAddr t lim) {ms : Array Ixon.MutConst}
    (hms : r.c.info = .muts ms) :
    ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t r.addr ms k lim := by
  rcases r.hchecked with ⟨ms', hms', hk⟩ | hc
  · have e : ms' = ms := by
      rw [hms] at hms'
      exact (Ixon.ConstantInfo.muts.inj hms').symm
    subst e
    exact hk
  · exact (Claim.checked_not_block hS (topRec_recordOf hH r) hms hc).elim

/-- **The member and constructor projection records of a block a walk recorded are records of
the run's store.** -/
theorem topRec_block_members {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (r : Claim.TopRec calls bAddr t lim) {ms : Array Ixon.MutConst}
    (hms : r.c.info = .muts ms) {i : Nat} {m : Ixon.MutConst} (hm : ms[i]? = some m) :
    recordOf E₀ (memberAddr r.addr i m) = some (memberProjection r.addr i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr r.addr i j) = some (constructorProjection r.addr i j) :=
  Claim.member_records hS hH (topRec_recordOf hH r) hms hm
    (topRec_block_checked hS hH r hms i (Array.getElem?_eq_some_iff.mp hm).1)

/-- **A projection record a walk recorded is at a member's or a constructor's address of its
block, which the run's store holds.** -/
theorem topRec_proj_member {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (r : Claim.TopRec calls bAddr t lim) (hpr : IsProj r.c) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf r.addr r.c) = some cb ∧
      ConstAddrOf (Ix.Cert.ownerOf r.addr r.c) cb r.addr := by
  rcases r.hchecked with ⟨ms, hms, -⟩ | hc
  · exfalso
    rcases hpr with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ <;>
      (rw [hp] at hms; cases hms)
  · exact Claim.proj_member_of_checked hS hH (topRec_recordOf hH r) hpr hc

end IxVM.Refinement.Binding
