import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.Claim.TopWalkOrder

/-! # The walks of a role's validation, with the operation order of what they walk

The forms of `IxVMRefinement.RoleVal.GroupWalkLim` with `Claim.TopRecsOrdered`: every used
reference of a record the validation walks is `Claim.OpOrderedAt` or covered at the group's
validation limit (`walk_ctx`'s `assert_op_reached_in_order`).

* `ValidateRoleIn.lim_walks_ordered`: the walk of the role's bound record.
* `RunCheckFullIn.lim_walks_ordered`, `ValidateRoleIn.eqns_evidence_walks_ordered`: an observed
  walk; the evidence theorems of a role specified by equations.
* `RefWalkedUnderCtxIn.lim_walks_ordered`, `ValidateRoleIn.op_certificate_walks_ordered`: a
  reference walked under `walk_ctx`, which is itself ordered; the references of an operation's
  certificates.
* `validate_role_axiom_refs_ordered`, `ValidateRoleIn.axiom_refs_ordered`: the references of a
  standard axiom's record (`validate_role_axiom_refs` with the order). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option linter.unusedVariables false

/-- **The walk of a role's bound record, ordered.** -/
theorem ValidateRoleIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro)
    (hw : roleWalksBound ro = true ∨ anchorWalked ro = true) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧
        a ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, x_a, r_w, h_w, h_w', cs_w, had, hrc_w, ha_w, ev_w, hsub_w⟩ :=
    validate_role_bound_walk hrc htbl ev hw
  obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
    Claim.run_check_transitive_lim_ordered (lim := some (groupValLimit g))
      (show Claim.RCLimRep t bAddr (some (groupValLimit g)) h_w x_rc from hrc_w) ha_w ev_w
  have hs : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hcl => hsub cl (hsub_w cl hcl)
  refine ⟨a, recs.map (Claim.TopRec.mono hs), had, hcl.mono hs, hord.mono hs, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **An observed walk, ordered.** -/
theorem RunCheckFullIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {addr : _root_.Address}
    (hv : RunCheckFullIn calls bAddr t n addr) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
      Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ addr ∈ recs.map (·.addr) := by
  obtain ⟨h_w, h_w', rc, ap, r_w, cs_w, hrc, ha, ev, hsub⟩ := hv
  obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
    Claim.run_check_transitive_lim_ordered (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h_w rc from hrc) ha ev
  refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, hord.mono hsub, ?_⟩
  rw [Claim.map_addr_topRec_mono]
  exact hmem

/-- **The evidence theorems of a role specified by equations, walked and ordered.** -/
theorem ValidateRoleIn.eqns_evidence_walks_ordered {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h5 : roleSpecKindNat ro = 5)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm : _root_.Address}
    (hm : (ro, arr) ∈ t.evidence.toList) (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
      Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ thm ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  exact ((validate_role_eqns_evidence_observed hrc htbl ev h5 arr thm hm hthm).mono
    hsub).lim_walks_ordered

/-- **The anchors walked by `validate_eqns_anchors` for an equation role, walked and ordered.** -/
theorem ValidateRoleIn.eqns_anchors_walks_ordered {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {g : Nat} {ro ar : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h5 : roleSpecKindNat ro = 5)
    (har : ar ∈ eqnsAnchorsOf ro) :
    ∃ (a : _root_.Address) (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ar = some a ∧ Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧
        a ∈ recs.map (·.addr) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, had, hw⟩ := validate_role_eqns_anchors_observed hrc htbl ev h5 ar har
  obtain ⟨recs, hcl, hord, hmem⟩ := (hw.mono hsub).lim_walks_ordered
  exact ⟨a, recs, had, hcl, hord, hmem⟩

/-- **A reference walked under the context `walk_ctx` gives it, ordered**: the reference itself
is ordered (`walk_ctx`'s assertion), and it is covered or a record of a closed, ordered list. -/
theorem RefWalkedUnderCtxIn.lim_walks_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {n : Nat} {b : _root_.Address}
    (hv : RefWalkedUnderCtxIn calls bAddr t n b) :
    Claim.OpOrderedAt t (some n) b ∧
    (Claim.CoveredAt t (some n) b ∨
      ∃ recs : List (Claim.TopRec calls bAddr t (some n)),
        Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ b ∈ recs.map (·.addr)) := by
  obtain ⟨⟨h₀, h₀', x_rc₀, x_b₀, r₀, cs₀, hrc₀, hb₀, ev₀, hs₀⟩,
    h₁, h₂, h₃, x_rc, x_b, rc', r_w, cs_c, cs_w, hrc, hb, evc, evw, hsub⟩ := hv
  refine ⟨Claim.walk_ctx_ordered (lim := some n)
    (show Claim.RCLimRep t bAddr (some n) h₁ x_rc from hrc) hb evc, ?_⟩
  obtain ⟨ext, hcase⟩ :=
    Claim.walk_ctx_lim_spec (lim := some n)
      (show Claim.RCLimRep t bAddr (some n) h₁ x_rc from hrc) hb evc
  rcases hcase with hrc' | ⟨hcov, -⟩
  · right
    subst hrc'
    obtain ⟨-, recs, hmem, hcl, hord, -⟩ :=
      Claim.run_check_transitive_lim_ordered (lim := some n)
        (show Claim.RCLimRep t bAddr (some n) h₂ _ from hrc.mono ext) (S0.addr_mono ext hb) evw
    refine ⟨recs.map (Claim.TopRec.mono hsub), hcl.mono hsub, hord.mono hsub, ?_⟩
    rw [Claim.map_addr_topRec_mono]
    exact hmem
  · exact Or.inl hcov

/-- **The references of an operation's certificate, walked and ordered**: each reference the
certificate uses other than the operation's own address is ordered, and covered or a record of
a closed, ordered list walked at the group's validation limit. -/
theorem ValidateRoleIn.op_certificate_walks_ordered {calls : List (Call F)}
    {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (h2 : roleSpecKindNat ro = 2)
    {arr : Array (Ix.Kernel.Evidence _root_.Address)} {thm a : _root_.Address}
    (ha : t.addressOf? ro = some a) (hm : (ro, arr) ∈ t.evidence.toList)
    (hthm : Ix.Kernel.Evidence.proof thm ∈ arr.toList) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = thm ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ S0.usedRefIdxs c →
        c.refs.toList[j] ≠ a →
        Claim.OpOrderedAt t (some (groupValLimit g)) c.refs.toList[j] ∧
        (Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j] ∨
          ∃ recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g))),
            Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧
              c.refs.toList[j] ∈ recs.map (·.addr)) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨rawBytes, c, hsz, hh, hb, hde, hg, hw⟩ :=
    (validate_role_op_certificates_observed hrc htbl ev h2 arr thm a ha hm hthm).mono hsub
  exact ⟨rawBytes, c, hsz, hh, hb, hde, fun j hj hu hne => (hw j hj hu hne).lim_walks_ordered⟩

private theorem refs_size_lt_bound_axiom_ord {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

/-- **The references of a standard axiom's record, walked and ordered**: `validate_role_axiom_refs`
with the walk's records ordered, and each reference the record uses ordered or covered at the
group's validation limit. -/
theorem validate_role_axiom_refs_ordered {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
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
      Claim.TopRecsOrdered recs ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ S0.usedRefIdxs c →
        (Claim.OpOrderedAt t (some (groupValLimit g)) c.refs.toList[j] ∨
          Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j]) ∧
        (c.refs.toList[j] ∈ recs.map (·.addr) ∨
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
        exact refs_size_lt_bound_axiom_ord hsz hdeExact
      have e343' : ObsFn W "KernelClaim::walk_refs_transitive"
          [x_rc, x_refs, v_idx, .field ((0 : Nat) : F)] b363 r h' cs_w := by
        rw [Nat.cast_zero]
        exact e343
      have hrc_w : Claim.RCLimRep t bAddr (some (groupValLimit g)) b363 x_rc :=
        hrc.mono (ext_h_m111.trans (ext_a.trans (ext_ba2.trans (ext_ld.trans
          (ext_b.trans ext_idx)))))
      obtain ⟨-, recs, hmem, hordr, hcl, hord, -⟩ :=
        Claim.walk_refs_transitive_lim_ordered (lim := some (groupValLimit g)) hrefs_bound hrc_w
          hrefs_rep hidxs e343'
      have hsub_w : ∀ cl ∈ cs_w, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      have hsub_ld : ∀ cl ∈ cs_ld, cl ∈ calls := fun cl hm' => by
        rw [hc323]; simp [show cl ∈ cs288 by rw [hca]; simp [hm']]
      refine ⟨a', rawBytes, c, recs.map (Claim.TopRec.mono hsub_w), had, hsz,
        Claim.hashed_mono hsub_ld hh_load, hblk, hde, hdeExact, hcl.mono hsub_w,
        hord.mono hsub_w, ?_⟩
      intro j hj hused
      refine ⟨hordr j hj (by rw [Nat.zero_add]; exact hused), ?_⟩
      rcases (hmem j hj (by rw [Nat.zero_add]; exact hused)).2 with ⟨-, hin⟩ | hcov
      · left
        rw [Claim.map_addr_topRec_mono]
        exact hin
      · exact Or.inr hcov

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.axiom_refs_ordered {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (hk : roleSpecKindNat ro = 3) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant)
      (recs : List (Claim.TopRec calls bAddr t (some (groupValLimit g)))),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ Claim.TopRecsClosed recs ∧
      Claim.TopRecsOrdered recs ∧
      ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ S0.usedRefIdxs c →
        (Claim.OpOrderedAt t (some (groupValLimit g)) c.refs.toList[j] ∨
          Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j]) ∧
        (c.refs.toList[j] ∈ recs.map (·.addr) ∨
          Claim.CoveredAt t (some (groupValLimit g)) c.refs.toList[j]) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, recs, had, hsz, hh, hblk, hde, hdeExact, hcl, hord, hrefs⟩ :=
    validate_role_axiom_refs_ordered hrc htbl ev hk
  refine ⟨a, rawBytes, c, recs.map (Claim.TopRec.mono hsub), had, hsz,
    Claim.hashed_mono hsub hh, hblk, hde, hdeExact, hcl.mono hsub, hord.mono hsub, ?_⟩
  intro j hj hused
  obtain ⟨hor, hrest⟩ := hrefs j hj hused
  refine ⟨hor, ?_⟩
  rcases hrest with hin | hcov
  · left
    rw [Claim.map_addr_topRec_mono]
    exact hin
  · exact Or.inr hcov

end IxVM.Refinement.RoleVal
