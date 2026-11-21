import IxVMRefinement.RoleVal.GroupWalkLim

/-! # The references of a standard axiom's record, walked at the group's validation limit

The validation of a standard axiom (`KernelRoles::validate_standard_axiom`: `propext`,
`Classical.choice`) does not walk the axiom's own record: the axiom's role is not in force in
its own group, and the axiom arm of the check would refuse it. It loads the record and walks
what the record references (`KernelClaim::walk_refs_transitive` under the role context of the
group's validation).

`validate_role_axiom_refs`: for a role specified as a standard axiom, the record at the role's
bound address is bytes the validation hashed, and every reference the record uses was asked
about, and is a record of a closed list of records checked at the group's validation limit that
is no block record, or is bound to a walked role in force at the limit. So the axiom's record
is a record of the run's store, and its references are records the group's admission holds.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

private theorem refs_size_lt_bound_axiom {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

/-- **The record of a standard axiom and its references, in the role's validation**: the
record at the bound address is bytes the validation hashed, and each reference it uses is a
record of a closed list of records checked at the group's validation limit, or is bound to a
walked role in force there. -/
theorem validate_role_axiom_refs {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {g : Nat} {ro : Ix.Kernel.Role}
    {x_rc x_tbl r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (groupValLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant)
      (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ Claim.TopRecsClosed recs ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
        Claim.RefAllowedIn calls t bAddr (some (groupValLimit g)) c.refs.toList[j] ∧
        ((Claim.NotBlockIn calls c.refs.toList[j] ∧ c.refs.toList[j] ∈ recs.map (·.addr)) ∨
          Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j]) := by
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs288
      ev14 ev47 _ ev80 ev100 _ ev124 ev290 hc323 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    have ext_h_m111 : Heap.Extends h m111 :=
      ext_ba.trans (ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends)))
    match Obs.«KernelRoles::validate_standard_axiom».obs ev290 with
    | .run (m60 := b60) (m128 := b128) (m141 := b141) (m207 := b207) (m192 := b192)
        (m280 := b280) (m_abygsahs := m_sh) (m363 := b363) (cs202 := cs_ld) (cs341 := cs_w)
        (x_refs := x_refs) (v346 := v_idx) (ev72 := e72) (hm136 := hm) (ev109 := e109)
        (ev174 := e174) (ev153 := e153) (ev217 := e217) (ev204 := e204) (ev314 := e314)
        (ev292 := e292) (sg_betjktew := sg_sh) (ev373 := e373) (ev343 := e343)
        (hc388 := hca) .. =>
      have ext_snoc : Heap.Extends b60 b128 := by
        rw [hm]
        exact Heap.Extends.snoc b60 _
      have ext_a : Heap.Extends m111 b141 :=
        e72.heap_extends.trans (ext_snoc.trans (e109.heap_extends.trans
          (e174.heap_extends.trans e153.heap_extends)))
      obtain ⟨ext_ba2, a', ha', had'⟩ :=
        role_bound_addr_uncond ((htbl.mono (ext_h_m111.trans ext_a)).toTableRep) e217
      have ha_eq : a' = a := by
        rw [had] at had'
        exact (Option.some.inj had').symm
      subst ha_eq
      obtain ⟨ext_ld, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        Claim.load_verified_constant_de ha' e204
      have ext_b : Heap.Extends b192 b280 := e314.heap_extends.trans e292.heap_extends
      have hm_sh : m_sh = b280 := by
        match sg_sh with
        | .Nil (he_hvdubghk := hh) .. => exact hh
        | .Cons (heq_htcsbwbd := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
      subst hm_sh
      obtain ⟨ext_idx, hidxs⟩ := Claim.const_idxs_of_spec (hrep.mono ext_b) e373
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem b363 c.refs.toList
            x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ (ext_b.trans ext_idx) hr_list
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound_axiom hsz hdeExact
      have e343' : ObsFn W "KernelClaim::walk_refs_transitive"
          [x_rc, x_refs, v_idx, .field ((0 : Nat) : F)] b363 r h' cs_w := by
        rw [Nat.cast_zero]
        exact e343
      have hrc_w : Claim.RCLimRep t bAddr (some (groupValLimit g)) b363 x_rc :=
        hrc.mono (ext_h_m111.trans (ext_a.trans (ext_ba2.trans (ext_ld.trans
          (ext_b.trans ext_idx)))))
      obtain ⟨-, recs, hmem, hcl, -⟩ :=
        Claim.walk_refs_transitive_lim_spec (lim := some (groupValLimit g)) hrefs_bound hrc_w
          hrefs_rep hidxs e343'
      have hsub_w : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      have hsub_ld : ∀ cl ∈ cs_ld, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      refine ⟨a', rawBytes, c, recs.map (Claim.TopRec.mono hsub_w), had, hsz,
        Claim.hashed_mono hsub_ld hh_load, hblk, hde, hdeExact, hcl.mono hsub_w, ?_⟩
      intro j hj hused
      obtain ⟨hal, hrest⟩ := hmem j hj (by rw [Nat.zero_add]; exact hused)
      refine ⟨hal.mono hsub_w, ?_⟩
      rcases hrest with ⟨hnb, hin⟩ | hcov
      · refine Or.inl ⟨hnb.mono hsub_w, ?_⟩
        rw [Claim.map_addr_topRec_mono]
        exact hin
      · exact Or.inr hcov

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.axiom_refs {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant)
      (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ Claim.TopRecsClosed recs ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
        Claim.RefAllowedIn calls t bAddr (some (groupValLimit g)) c.refs.toList[j] ∧
        ((Claim.NotBlockIn calls c.refs.toList[j] ∧ c.refs.toList[j] ∈ recs.map (·.addr)) ∨
          Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j]) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, recs, had, hsz, hh, hblk, hde, hdeExact, hcl, hrefs⟩ :=
    validate_role_axiom_refs hrc htbl ev hk
  refine ⟨a, rawBytes, c, recs.map (Claim.TopRec.mono hsub), had, hsz,
    Claim.hashed_mono hsub hh, hblk, hde, hdeExact, hcl.mono hsub, ?_⟩
  intro j hj hused
  obtain ⟨hal, hrest⟩ := hrefs j hj hused
  refine ⟨hal.mono hsub, ?_⟩
  rcases hrest with ⟨hnb, hin⟩ | hcov
  · refine Or.inl ⟨hnb.mono hsub, ?_⟩
    rw [Claim.map_addr_topRec_mono]
    exact hin
  · exact Or.inr hcov

set_option maxRecDepth 100000 in
/-- The roles specified as standard axioms are `propext` and `Classical.choice`. -/
theorem specKind_three_iff (ro : Ix.Kernel.Role) :
    roleSpecKindNat ro = 3 ↔ ro ∈ IxVM.Consistency.standardAxioms := by
  cases ro <;> decide

end IxVM.Refinement.RoleVal
