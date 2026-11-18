import IxVMRefinement.Binding.StoreLogic
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.RoleVal.StandingInForce

/-! # A new axiom or quotient record of a group's admission is the group's standard axiom

The clause `Admits.standing` for the store sequence `groupStore t E₀`. A record the admission of
group `g` adds is reached and walked, a projection record beside a walked block, or the record of
the group's standard axiom (`groupAdds_cases`). A walked axiom or quotient record was checked at
the group's validation limit, and the check found a role at its address
(`Claim.checkedLimAt_standing_role`): a quotient role or `quotSound`, bound to basis rows the
store held before; `propext` or `choice` in force, whose own group added the record before; or
an inert role in force, which no walked role is and which a reference the walk asked about
cannot be (`Claim.refAllowed_inert`).

* `GroupReach.root_or_allowed`: an address a group's admission reaches is the record of a role
  of the group whose validation walks it, a block, or a reference the walk asked about
  (`Claim.RefAllowedIn`).
* `groupStore_standing`: the clause for one group; `standing_of_rootsSafe` for every group.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

set_option maxRecDepth 100000 in
/-- A standing role is `propext` or `choice`, standard axioms of groups from 6 on, or a basis
role (decided). -/
theorem standingRole_cases :
    ∀ ro ∈ Typing.standingRoles, (ro ∈ standardAxioms ∧ 6 ≤ Ix.SpecDigest.groupOf ro) ∨
      ro ∈ TableInhabit.basisRoleOrder := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- No role whose bound record its validation walks is inert (decided). -/
theorem walked_not_inert (r : Ix.Kernel.Role) :
    (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) → r.inert = false := by
  rw [RoleVal.anchorWalked_iff]
  cases r <;> decide

/-- **A basis role is bound to a basis row**, at a table that pins the prelude. -/
theorem basisRow_of_basisRole {t : Ix.Kernel.RoleTable} (hpre : PreludePinned t)
    {r : Ix.Kernel.Role} (hr : r ∈ TableInhabit.basisRoleOrder) {a : _root_.Address}
    (had : t.addressOf? r = some a) : (basisStore.consts.get? a).isSome = true := by
  have hrows := List.all_eq_true.mp basisRoles_rows r hr
  simp only [← addressOf_basis hpre hr, had] at hrows
  have hrec : (recordOf basisStore a).isSome = true := StoreInhabit.isSome_of_hasKey hrows
  cases hg : basisStore.consts.get? a with
  | none =>
    unfold recordOf at hrec
    rw [hg] at hrec
    exact absurd hrec (by simp)
  | some lc => rfl

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **How an address a group's admission reaches was reached**: it is the record bound to a
role of the group whose validation walks it, it holds a block record, or the walk asked about it
as a reference (`Claim.RefAllowedIn`): a reference of a walked record, of the group's standard
axiom, or of a proof in the evidence of a role of the group. -/
theorem GroupReach.root_or_allowed (hC : CollisionFreeRun calls E₀) {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a : _root_.Address}
    (h : GroupReach t E₀ g a) :
    (∃ r ∈ roleGroup g, (RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true) ∧
        t.addressOf? r = some a) ∨
      (∃ cb ms, recordOf E₀ a = some cb ∧ cb.info = .muts ms) ∨
      Claim.RefAllowedIn calls t bAddr (some (valLimit g)) a := by
  cases h with
  | root hr hwk had => exact Or.inl ⟨_, hr, hwk, had⟩
  | @axiomRef r a' x hr hs had hu hnc =>
    right; right
    obtain ⟨a₁, rawBytes, c, recs', had₁, hsz, hh, hblk, hde, hdeE, hcl, hrefs⟩ :=
      RoleVal.ValidateRoleIn.axiom_refs
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr)
        ((RoleVal.specKind_three_iff r).mpr hs)
    have e : a' = a₁ := Option.some.inj (had.symm.trans had₁)
    have hrec : recordOf E₀ a' = some c := by
      rw [e, ← hblk]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    obtain ⟨c', i, hc', hi, hx⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    rw [ec] at hi hx
    obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
    have hlt' : i < c.refs.toList.length := by simpa using hlt
    have hused : i ∈ Core.S0.usedRefIdxs c := by
      rw [Assembly.usedRefIdxs_eq]
      exact hi
    have hxl : c.refs.toList[i]'hlt' = x := by simpa using hxe
    have hal := (hrefs i hlt' hused).1
    rw [hxl] at hal
    exact hal
  | @ref a' x ha' hu hnc =>
    right; right
    obtain ⟨y, hy, hya⟩ := ha'.listed hC.hashedStored hw
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    have hrec := topRec_recordOf hC.hashedStored y
    rw [hya] at hrec
    have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hi hx
    exact ((hw.closed y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx).1
  | @owner a' c ha' hc hp =>
    right; left
    obtain ⟨y, hy, hya⟩ := ha'.listed hC.hashedStored hw
    have hyc : y.c = c := by
      have h1 := topRec_recordOf hC.hashedStored y
      rw [hya, hc] at h1
      exact (Option.some.inj h1).symm
    obtain ⟨cb₀, hcb₀, hca⟩ := topRec_proj_member hC.runStore hC.hashedStored y (hyc ▸ hp)
    rw [hya, hyc] at hcb₀ hca
    rcases hca with ⟨hx, hst⟩ | ⟨ms, i, m, hms, -, -⟩
    · exfalso
      rw [← hx, hc] at hcb₀
      have e : c = cb₀ := Option.some.inj hcb₀
      rw [e] at hp
      exact standalone_not_proj hst hp
    · exact ⟨cb₀, ms, hcb₀, hms⟩
  | @evidenceRef r arr thm x hr hm hthm hu hne hnc =>
    right; right
    have hv := hval r hr
    have hv' : RoleVal.ValidateRoleIn calls bAddr t g r := hv
    rcases evidence_specKind hv.wf hm with h2 | h5
    · obtain ⟨a₀, had, -⟩ := (RoleValidationIn.walks hv).1
      obtain ⟨rawBytes, c, hsz, hh, hbl, hde, hwk⟩ :=
        RoleVal.ValidateRoleIn.op_certificate_walks hv' h2 had hm hthm
      have hrec : recordOf E₀ thm = some c := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz
          (L1.deConstant_of_deConstantExact hde) hde
      obtain ⟨c', i, hc', hi, hx⟩ := hu
      have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
      rw [ec] at hi hx
      obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
      have hlt' : i < c.refs.toList.length := by simpa using hlt
      have hxl : c.refs.toList[i]'hlt' = x := by simpa using hxe
      have hne' : c.refs.toList[i]'hlt' ≠ a₀ := by
        rw [hxl]
        intro e
        exact hne (by rw [e]; exact had)
      have hal := (hwk i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) hne').1
      rw [hxl] at hal
      exact hal
    · obtain ⟨recs', hcl', hmem⟩ := RoleVal.ValidateRoleIn.eqns_evidence_walks hv' h5 hm hthm
      obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
      obtain ⟨c, i, hc, hi, hx⟩ := hu
      have hrec := topRec_recordOf hC.hashedStored y
      rw [hya] at hrec
      have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
      rw [ec] at hi hx
      exact ((hcl' y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx).1

/-- **`Admits.standing`**: a new axiom or quotient record of a group's admission is the record of
a standard axiom of the group. -/
theorem groupStore_standing (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hpin : PreludePinned t) {g : Nat} (hg : 6 ≤ g)
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hsafe : ∀ a, GroupReach t E₀ g a → Claim.SourceSafe E₀ a) :
    ∀ a c, New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
      recordOf (groupStore t E₀ (g + 1)) a = some c → IsAxiomLike c →
      ∃ r ∈ roleGroup g, r ∈ standardAxioms ∧ t.addressOf? r = some a := by
  intro a c hnew hc hk
  obtain ⟨c₀, hE₀, hc₀, hadd, hnot⟩ := new_groupStore hb hg hnew
  have hE : recordOf E₀ a = some c := by
    rw [hE₀, Option.some.inj (hc₀.symm.trans hc)]
  have hnotBasis : ∀ ro ∈ TableInhabit.basisRoleOrder, t.addressOf? ro = some a → False :=
    fun ro hr had => hnot (Or.inl (basisRow_of_basisRole hpin hr had))
  have hnotStd : ∀ ro, ro ∈ standardAxioms → 6 ≤ Ix.SpecDigest.groupOf ro →
      Ix.SpecDigest.groupOf ro < g → t.addressOf? ro = some a → False :=
    fun ro hs h6 hlt had => hnot (Or.inr ⟨_, h6, hlt,
      Or.inr (Or.inr ⟨ro, role_mem_roleGroup ro, hs, had⟩)⟩)
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, y, hy, hya⟩ |
      ⟨r, hr, -, -, p, hp, hproj, -⟩ | ⟨ro, hro, hs, had, -⟩
  · have hyc : y.c = c := by
      have h1 := topRec_recordOf hC.hashedStored y
      rw [hya, hE] at h1
      exact (Option.some.inj h1).symm
    have hchk : Claim.CheckedLimAt calls bAddr t a (some (valLimit g)) := by
      rcases y.hchecked with ⟨ms, hms, -⟩ | hck
      · exfalso
        rw [hyc] at hms
        rcases hk with ⟨ax, h⟩ | ⟨q, h⟩ <;> (rw [h] at hms; cases hms)
      · rw [hya] at hck
        exact hck
    have hl : InLogic c := (hsafe a hra c hE).1
    obtain ⟨ro, hb', hcase⟩ := Claim.checkedLimAt_standing_role hC.runStore hE hl hk hchk
    exfalso
    rcases hcase with ⟨⟨ax, hax'⟩, hforce, hrole⟩ | ⟨⟨q, hq⟩, hm⟩
    · have hlt : Ix.SpecDigest.groupOf ro < valLimit g := hforce _ rfl
      rcases hrole with hm | hin
      · rcases standingRole_cases ro hm with ⟨hs, h6⟩ | hbas
        · exact hnotStd ro hs h6 (Nat.lt_of_lt_of_le hlt (valLimit_le g)) hb'
        · exact hnotBasis ro hbas hb'
      · rcases hra.root_or_allowed hC hval hw with ⟨r', hr', hwk, had'⟩ | ⟨cb, ms, hcb, hms⟩ |
          hal
        · have hwf := (hval r' hr').wf
          have hk' := (Core.keyOf_of_addressOf hwf had').symm.trans
            (Core.keyOf_of_addressOf hwf hb')
          injection hk' with e
          rw [← e, walked_not_inert r' hwk] at hin
          cases hin
        · rw [hE] at hcb
          have e : c = cb := Option.some.inj hcb
          rw [← e, hax'] at hms
          cases hms
        · obtain ⟨n, hn, hle⟩ := Claim.refAllowed_inert hal hin hb'
          have e : n = valLimit g := (Option.some.inj hn).symm
          rw [e] at hle
          exact absurd hlt (Nat.not_lt.mpr hle)
    · rcases standingRole_cases ro hm with ⟨hs, -⟩ | hbas
      · obtain ⟨c₂, ax, hc₂, hi, -⟩ := hax ro hs a hb'
        rw [hE] at hc₂
        have e : c = c₂ := Option.some.inj hc₂
        rw [← e, hq] at hi
        cases hi
      · exact hnotBasis ro hbas hb'
  · exfalso
    have e : p = c := Option.some.inj (hp.symm.trans hE)
    rw [e] at hproj
    rcases hk with ⟨ax, h⟩ | ⟨q, h⟩
    · exact proj_not_axiom hproj h
    · rcases hproj with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [h] at h'; cases h')
  · exact ⟨ro, hro, hs, had⟩

/-- **`Admits.standing` for every group of a run**, from the safety of the roots. -/
theorem standing_of_rootsSafe (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hpin : PreludePinned t)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hroots : RootsSafe t E₀) :
    ∀ g, 6 ≤ g → g < 77 → ∀ a c,
      New (groupStore t E₀ g) (groupStore t E₀ (g + 1)) a →
      recordOf (groupStore t E₀ (g + 1)) a = some c → IsAxiomLike c →
      ∃ r ∈ roleGroup g, r ∈ standardAxioms ∧ t.addressOf? r = some a := by
  intro g hg6 hg
  have hax := axiomRoles_of_run hC hval
  obtain ⟨recs, hw⟩ := groupWalked_exists hC.hashedStored (hval g hg)
  exact groupStore_standing hC hb hax hpin hg6 (hval g hg) hw
    (groupReach_sourceSafe_of_run hC hval hroots hg hw)

end Run

end IxVM.Refinement.Binding
