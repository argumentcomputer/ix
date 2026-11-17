import IxVMRefinement.Claim.TopBase

/-! # A claim's seeds at a role-context limit (A3)

`KernelClaim::assert_claimable` under the top-level context of either mode: the seed is no
inert axiom, and it is in Lean's logic with its block (`ClaimableSeed`). The proofs are those of
`role_index_of_full_spec`, `role_is_inert_zero_spec` and `assert_claimable_spec` over
`RCLimRep`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

theorem role_index_of_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Option Nat}
    {x_rc x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::role_index_of" [x_rc, x_a] h r h' calls) :
    h' = h ∧
    ((r = .field 0 ∧ ∀ ro, t.addressOf? ro ≠ some a) ∨
      ∃ ro : Ix.Kernel.Role, r = .field (roleNum ro + 1) ∧ t.addressOf? ro = some a) := by
  obtain ⟨ab, hab, hix⟩ := ha
  obtain ⟨_, v8, m18, _, v29, m31, _, ev41, ev28, ev6, -⟩ :=
    Obs.«KernelRoles::role_index_of».obs ev
  obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec hrc ev41
  obtain ⟨rfl, ⟨es, hbst, hie, hmem⟩⟩ := role_addr_index_full_spec htbl ev28
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev6
  obtain ⟨hlk, rfl⟩ := rbtree_map_lookup_or_default_spec hab hbst ev6
  refine ⟨rfl, ?_⟩
  by_cases hex : ∃ w, (ab, w) ∈ es
  · obtain ⟨w, hw⟩ := hex
    rw [lookupEntries_eq_of_mem hbst.2 hw] at hlk
    obtain ⟨ro, hw_eq, hof⟩ := hie (ab, w) hw
    rw [hix] at hof
    exact .inr ⟨ro, hlk.trans hw_eq, hof⟩
  · have hno : ∀ w, (ab, w) ∉ es := fun w hw => hex ⟨w, hw⟩
    rw [lookupEntries_eq_dflt_of_not_mem hno] at hlk
    refine .inl ⟨hlk, ?_⟩
    intro ro hof
    have hm_bound := mem_bound_of_addressOf_eq_some hof
    obtain ⟨b0, hix0, hb0⟩ := hmem ro a hm_bound
    have hb_eq : b0 = ab := ixAddr_injective (hix0.trans hix.symm)
    subst hb_eq
    exact hno _ hb0

theorem role_is_inert_zero_lim_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Option Nat}
    {x_rc x_a : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_a a)
    (ev : ObsFn W "KernelRoles::role_is_inert" [x_rc, x_a] h (.field 0) h' calls) :
    h' = h ∧ ¬ IxVM.Consistency.InertAt t a := by
  rcases Obs.«KernelRoles::role_is_inert».obs ev with
    ⟨m2, cs12, ev14, _, rfl, -⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, he95, -⟩ |
    ⟨v1, m2, cs12, v52, x61, m63, cs72, v75, ev14, hne48, op89, ev74, op68, hne98, _, rfl, -⟩
  · obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha ev14
    rcases hres with ⟨_, hnone⟩ | ⟨ro, heq, _⟩
    · refine ⟨rfl, ?_⟩
      rintro ⟨ro, _, hof⟩
      exact hnone ro hof
    · exact absurd (Value.field.inj heq).symm (RolesAux.roleNum_add_one_ne_zero ro)
  · simp at he95
  · obtain ⟨rfl, hres⟩ := role_index_of_lim_spec hrc ha ev14
    rcases hres with ⟨rfl, _⟩ | ⟨ro, rfl, hof⟩
    · exact absurd rfl hne48
    · simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op89
      subst op89
      refine ⟨(RoleVal.role_spec_kind_spec ev74).2, ?_⟩
      rintro ⟨ro', hinert', hof'⟩
      obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
      have hro_eq : ro' = ro :=
        Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
      subst hro_eq
      obtain ⟨rfl, _⟩ := role_spec_kind_inert_eq hinert' ev74
      simp only [evalBinOp, sub_self, Except.ok.injEq] at op68
      exact hne98 op68.symm

theorem assert_claimable_lim_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {x_rc x_addr r : SourceValue F} {addr : _root_.Address}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCLimRep t bAddr lim h x_rc)
    (ha : S0.addr h x_addr addr)
    (ev : ObsFn Obs.W "KernelClaim::assert_claimable" [x_rc, x_addr] h r h' calls) :
    Heap.Extends h h' ∧ ClaimableSeed calls t addr := by
  rcases Obs.«KernelClaim::assert_claimable».obs ev with
    ⟨m2, cs12, _, _, _, _, _, x_b, v136, m139, cs147, v176, m179, cs187, v216, m219, cs227,
      ev14, ev149, rfl, ev189, rfl, ev229, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_b, v310, m313, cs321, v350, m353, cs361, v390, m393, cs401,
      ev14, ev323, rfl, ev363, rfl, ev403, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, _, x_b, v490, m493, cs501, v530, m533, cs541, v570, m573, cs581,
      ev14, ev503, rfl, ev543, rfl, ev583, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, _, _, _, _, _, x_b, v664, m667, cs675, v704, m707, cs715, v744, m747, cs755,
      ev14, ev677, rfl, ev717, rfl, ev757, rfl, _, rfl, hc⟩ |
    ⟨m2, cs12, x_info, _, _, _, _, v803, m806, cs814, v843, m846, cs854, v883, m886, cs894,
      ev14, hne259, hne433, hne613, hne787, ev816, rfl, ev856, rfl, ev896, rfl, _, rfl, hc⟩
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case dPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev149
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev189
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_lim_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev229
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case iPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev323
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev363
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_lim_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev403
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case cPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev503
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev543
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_lim_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev583
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    cases hc_info : c₀.info <;> rw [hc_info] at hinfo
    case rPrj p =>
      obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
      rw [hpv] at hpv_eq
      injection hpv_eq with _ _ h1
      simp only [List.cons.injEq, and_true] at h1
      injection h1 with _ _ hpargs
      simp only [List.cons.injEq, and_true] at hpargs
      rw [← hpargs.2] at hblk_addr
      obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev677
      obtain ⟨ext3, rawB, cb, hhB, hbB, hdB, hlB⟩ :=
        record_unsafe_zero_spec (S0.addr_mono ext2 hblk_addr) ev717
      obtain ⟨rfl, hn_inert⟩ :=
        role_is_inert_zero_lim_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
          (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev757
      refine ⟨ext1.trans (ext2.trans ext3), hn_inert,
        ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
        ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀,
          .inr ⟨rawB, cb, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hhB,
            by simpa [Ix.Cert.ownerOf, hc_info] using hbB, hdB, hlB⟩⟩⟩
    all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
  · obtain ⟨ext1, raw₀, c₀, _, hh₀, hb₀, hd₀, _, hrep, _⟩ := load_verified_constant_de ha ev14
    obtain ⟨infoVal, _, _, _, _, hv, hinfo, _, _, _, _⟩ := hrep
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hinfo
    have hown_self : Ix.Cert.ownerOf addr c₀ = addr := by
      cases hc_info : c₀.info <;> rw [hc_info] at hinfo
      case dPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne259 [_] rfl)
      case iPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne433 [_] rfl)
      case cPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne613 [_] rfl)
      case rPrj _ => obtain ⟨_, hv', _⟩ := hinfo; exact absurd hv' (hne787 [_] rfl)
      all_goals simp [Ix.Cert.ownerOf, hc_info]
    obtain ⟨ext2, raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ :=
      record_unsafe_zero_spec (S0.addr_mono ext1 ha) ev816
    have ext3 := ev856.heap_extends
    obtain ⟨rfl, hn_inert⟩ :=
      role_is_inert_zero_lim_spec (hrc.mono (ext1.trans (ext2.trans ext3)))
        (S0.addr_mono (ext1.trans (ext2.trans ext3)) ha) ev896
    exact ⟨ext1.trans (ext2.trans ext3), hn_inert,
      ⟨raw₁, c₁, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₁, hb₁, hd₁, hl₁⟩,
      ⟨raw₀, c₀, hashed_mono (fun cl hcl => by rw [hc]; simp [hcl]) hh₀, hb₀, hd₀, .inl hown_self⟩⟩

end IxVM.Refinement.Claim
