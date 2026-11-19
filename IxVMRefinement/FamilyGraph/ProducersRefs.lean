import IxVMRefinement.FamilyGraph.ProducersCarriers
import IxVMRefinement.FamilyGraph.ProducersEdges
import IxVMRefinement.FamilyGraph.ProducersInnerRefs
import IxVMRefinement.FamilyGraph.ProducersCallTree
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.Claim.RefSafetyExcept
import IxVMRefinement.Claim.TopCheckFacts
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.IxonDeserialize0
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelCheck10
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelCheck13
import IxVMRefinement.Obs.KernelClaim0
import IxVMRefinement.Obs.KernelDefEq3
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelRoles1
import IxVMRefinement.Obs.RBTreeMap0

/-! # Reference closure and container witness obligations from `check_family`

Proves the three reference-closure obligations of `BatchGives` (`familyRefs`, `adviceRefs`, and
`contWitness`), together with `rec_family_block` determinism/used-reference facts and
`rprj_check_const_rec_other` (reused for the recursor-block arm):

* Pure-read pullback for `Bytes.RepAddressRef`, `RBTreeMap::rbtree_map_lookup_or_default`,
  `KernelRoles::role_index_of`, `KernelRoles::role_of`, `KernelModeled::addr_covered`, and
  `KernelModeled::assert_covered_past` across heap extensions;
* Unconditional projection hashing specs for `KernelDefEq::compute_iprj_addr` and
  `KernelCheck::projection_addr_ctor`, plus `projection_block`, `used_ref_has`,
  `is_projection_of`, `ref_projects_from`, `projection_of_ref_block`, and `projection_of_advice`;
* Dependency-path and witness specs for `walk_path`, `walk_from_block`, `check_witness`, and
  `check_witnesses`;
* `FamRunCtx.familyRefs_of`, `FamRunCtx.adviceRefs_of`, and `FamRunCtx.contWitness_of`.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

/-! ## Pure-read pullback and role / coverage specifications -/

private theorem canon_addr_cmp_spec_ext {h₁ h₁' h₂ : Heap F} {x y r : SourceValue F}
    {cs : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef Core.addrTy h₁ a x)
    (hk_node : Bytes.RepAddressRef Core.addrTy h₂ ak y)
    (ext : Heap.Extends h₁ h₂)
    (ev : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x, y] h₁ r h₁' cs) :
    r = .field (Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) : F) ∧ h₁' = h₁ := by
  have hk_node₁ : Bytes.RepAddressRef Core.addrTy h₁ ak y := by
    match Obs.«RBTreeMap::canon_addr_cmp».obs ev with
    | .run (ld23 := ld23) .. => exact repAddressRef_pullback ext ld23 hk_node
  exact Claim.canon_addr_cmp_spec hk hk_node₁ ev

private theorem cmp_branch_lt_ext {x_key x_k v_cmp : SourceValue F} {h₁ m1 m2 h₂ : Heap F}
    {cs1 cs2 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef Core.addrTy h₁ a x_key)
    (hk_node : Bytes.RepAddressRef Core.addrTy h₂ ak x_k)
    (ext : Heap.Extends h₁ h₂)
    (ev_cmp : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h₁ v_cmp m1 cs1)
    (ev_z : ObsFn Obs.W "Fields::is_zero" [v_cmp] m1 (.field 1) m2 cs2) :
    m2 = h₁ ∧ Claim.addrRank a < Claim.addrRank ak := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec_ext hk hk_node ext ev_cmp
  obtain ⟨hz, rfl⟩ := Lib.is_zero_field ev_z
  have hc0 : (Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) : F) = 0 := by
    by_cases he : (Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) : F) = 0
    · exact he
    · rw [ite_eq_right he] at hz
      exact absurd (Value.field.inj hz) one_ne_zero
  have hc_eq : Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) = 0 := by
    have hlt1 := Claim.cmpNat_lt_u32 (Claim.addrRank a) (Claim.addrRank ak)
    have h1 := val_cast_lt_u56 (n := Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak))
      (by omega)
    rw [hc0, ZMod.val_zero] at h1
    exact h1.symm
  exact ⟨rfl, Claim.cmpNat_eq_zero_iff.mp hc_eq⟩

private theorem cmp_branch_eq_ext {x_key x_k v_cmp v_lt x_cmp2 : SourceValue F}
    {h₁ m1 m2 m3 h₂ : Heap F} {cs1 cs2 cs3 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef Core.addrTy h₁ a x_key)
    (hk_node : Bytes.RepAddressRef Core.addrTy h₂ ak x_k)
    (ext : Heap.Extends h₁ h₂)
    (ev_cmp1 : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h₁ v_cmp m1 cs1)
    (ev_z : ObsFn Obs.W "Fields::is_zero" [v_cmp] m1 v_lt m2 cs2)
    (ev_cmp2 : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x_key, x_k] m2 x_cmp2 m3 cs3)
    (op_sub : evalBinOp .sub x_cmp2 (.field 1) = .ok (.field 0)) :
    m3 = h₁ ∧ a = ak := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec_ext hk hk_node ext ev_cmp1
  obtain ⟨_, rfl⟩ := Lib.is_zero_field ev_z
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec_ext hk hk_node ext ev_cmp2
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op_sub
  have hc1 : (Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) : F) = (1 : F) := by
    simpa using sub_eq_zero.mp op_sub
  have hc_eq : Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) = 1 := by
    have hlt1 := Claim.cmpNat_lt_u32 (Claim.addrRank a) (Claim.addrRank ak)
    have h1 := val_cast_lt_u56 (n := Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak))
      (by omega)
    rw [hc1, ZMod.val_one] at h1
    exact h1.symm
  exact ⟨rfl, Claim.addrRank_injective (Claim.cmpNat_eq_one_iff.mp hc_eq)⟩

private theorem cmp_branch_gt_ext {x_key x_k v_cmp v_lt x_cmp2 v_sub : SourceValue F}
    {h₁ m1 m2 m3 h₂ : Heap F} {cs1 cs2 cs3 : List (Call F)} {a ak : Bytes.Address}
    (hk : Bytes.RepAddressRef Core.addrTy h₁ a x_key)
    (hk_node : Bytes.RepAddressRef Core.addrTy h₂ ak x_k)
    (ext : Heap.Extends h₁ h₂)
    (ev_cmp1 : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x_key, x_k] h₁ v_cmp m1 cs1)
    (ev_z : ObsFn Obs.W "Fields::is_zero" [v_cmp] m1 v_lt m2 cs2)
    (hne_lt : v_lt ≠ .field 1)
    (ev_cmp2 : ObsFn Obs.W "RBTreeMap::canon_addr_cmp" [x_key, x_k] m2 x_cmp2 m3 cs3)
    (op_sub : evalBinOp .sub x_cmp2 (.field 1) = .ok v_sub)
    (hne_eq : v_sub ≠ .field 0) :
    m3 = h₁ ∧ Claim.addrRank ak < Claim.addrRank a := by
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec_ext hk hk_node ext ev_cmp1
  obtain ⟨hz, rfl⟩ := Lib.is_zero_field ev_z
  obtain ⟨rfl, rfl⟩ := canon_addr_cmp_spec_ext hk hk_node ext ev_cmp2
  have nc0 : Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) ≠ 0 := by
    intro e
    rw [e] at hz
    simp at hz
    exact hne_lt hz
  have nc1 : Claim.cmpNat (Claim.addrRank a) (Claim.addrRank ak) ≠ 1 := by
    intro e
    rw [e] at op_sub
    simp only [Nat.cast_one, evalBinOp, sub_self, Except.ok.injEq] at op_sub
    exact hne_eq op_sub.symm
  rcases Claim.cmpNat_values (Claim.addrRank a) (Claim.addrRank ak) with h0 | h1 | h2
  · exact absurd h0 nc0
  · exact absurd h1 nc1
  · exact ⟨rfl, Claim.cmpNat_eq_two_iff.mp h2⟩

private theorem rbtree_map_lookup_or_default_spec_ext {t_V : Generic.Ty}
    {es : List (Bytes.Address × SourceValue F)} :
    ∀ {x_key x_tree x_default r : SourceValue F} {h₁ h₁' h₂ : Heap F} {calls : List (Call F)}
      {a : Bytes.Address},
      Bytes.RepAddressRef Core.addrTy h₁ a x_key →
      Claim.RBTreeBST t_V h₂ es x_tree →
      Heap.Extends h₁ h₂ →
      ObsFn Obs.W (Instance.mk "RBTreeMap::rbtree_map_lookup_or_default" [t_V]).symbol
        [x_key, x_tree, x_default] h₁ r h₁' calls →
      r = Claim.lookupEntries a es x_default ∧ h₁' = h₁ := by
  intro x_key x_tree x_default r h₁ h₁' h₂ calls a hk ⟨htree, hpw⟩ ext ev
  induction htree generalizing r h₁' calls with
  | nil =>
    rcases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      ⟨_, rfl, rfl, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, _, _, _, _, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv26, _, _, _, _, _, _, _, _, _, -⟩
    · exact ⟨rfl, rfl⟩
    · simp at hv26
    · simp at hv26
    · simp at hv26
  | node hk_node hl hr rl rr ihl ihr =>
    obtain ⟨hpwL, hpwR, _, _⟩ := Claim.pairwise_split hpw
    rcases Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev with
      ⟨hv15, _, _, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, m63, cs73, v76, m78, cs86, cs122,
        _, hv26, ld52, ld60, ev88, ev75, ev124, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, v62, m63, cs73, v76, m78, cs86, x162, m164, cs173,
        _, hv26, ld52, ld60, ev88, ev75, hne150, ev175, op169, rfl, rfl, -⟩ |
      ⟨w28, x_k, x_v, w29, w30, y51, y59, v62, m63, cs73, v76, m78, cs86, v154, x162, m164,
        cs173, cs217, _, hv26, ld52, ld60, ev88, ev75, hne150, ev175, op169, hne210, ev219, -⟩
    · simp at hv15
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Except.ok.inj ((ext.loadValue_eq ld52).symm.trans hl)
      obtain ⟨hm78, hlt⟩ := cmp_branch_lt_ext hk hk_node ext ev88 ev75
      subst hm78
      rw [Claim.lookupEntries_split_lt hpw hlt]
      exact ihl hpwL ev124
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain ⟨hm164, rfl⟩ := cmp_branch_eq_ext hk hk_node ext ev88 ev75 ev175 op169
      exact ⟨(Claim.lookupEntries_split_eq hpw).symm, hm164⟩
    · injection hv26 with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
      obtain rfl := Except.ok.inj ((ext.loadValue_eq ld60).symm.trans hr)
      obtain ⟨hm164, hgt⟩ := cmp_branch_gt_ext hk hk_node ext ev88 ev75 hne150 ev175 op169 hne210
      subst hm164
      rw [Claim.lookupEntries_split_gt hpw hgt]
      exact ihr hpwR ev219

private theorem role_ctx_table_lim_spec_ext {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {x_rc r : SourceValue F} {h₁ h₁' h₂ : Heap F} {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h₂ x_rc) (ext : Heap.Extends h₁ h₂)
    (ev : ObsFn Obs.W "KernelRoles::role_ctx_table" [x_rc] h₁ r h₁' calls) :
    h₁' = h₁ ∧ Claim.TableFullRep t bAddr h₂ r := by
  obtain ⟨tbl, htbl, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::role_ctx_table».obs ev with
    | .Mk (ld12 := ld12) (he38 := he) (he39 := hh) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      injection hl' with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      subst he
      exact ⟨hh, htbl⟩
    | .Assumed (ld12 := ld12) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      simp at hl'
  · match Obs.«KernelRoles::role_ctx_table».obs ev with
    | .Mk (ld12 := ld12) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      simp at hl'
    | .Assumed (ld12 := ld12) (he60 := he) (he61 := hh) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      injection hl' with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      subst he
      exact ⟨hh, htbl⟩

private theorem role_addr_index_full_spec_ext {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {x_tbl r : SourceValue F} {h₁ h₁' h₂ : Heap F} {calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h₂ x_tbl) (ext : Heap.Extends h₁ h₂)
    (ev : ObsFn Obs.W "KernelRoles::role_addr_index" [x_tbl] h₁ r h₁' calls) :
    h₁' = h₁ ∧ Claim.ByAddrInv t t.bound.toList h₂ r := by
  obtain ⟨_, _, _, byAddr, _, hl_tbl, _, _, hba, _⟩ := htbl
  obtain ⟨_, _, x_by_addr, _, ld12, rfl, rfl, -⟩ := Obs.«KernelRoles::role_addr_index».obs ev
  have hl' := ext.loadValue_eq ld12
  rw [hl_tbl] at hl'
  injection hl' with hv
  injection hv with _ _ hargs
  simp only [List.cons.injEq] at hargs
  obtain ⟨_, _, rfl, _⟩ := hargs
  exact ⟨rfl, hba⟩

private theorem addr_index_lookup_ext {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {x_tbl x_a v51 v36 : SourceValue F} {h₁ m61 m37 h₂ : Heap F} {cs69 cs47 : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h₂ x_tbl) (ext : Heap.Extends h₁ h₂)
    (ha : S0.addr h₁ x_a a)
    (ev71 : ObsFn Obs.W "KernelRoles::role_addr_index" [x_tbl] h₁ v51 m61 cs69)
    (ev49 : ObsFn Obs.W Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>»
      [x_a, v51, .field 0] m61 v36 m37 cs47) :
    m61 = h₁ ∧ m37 = h₁ ∧
      ((v36 = .field 0 ∧ ∀ ro, t.addressOf? ro ≠ some a) ∨
        ∃ ro : Ix.Kernel.Role, v36 = .field (RolesAux.roleNum ro + 1) ∧ t.addressOf? ro = some a) := by
  obtain ⟨ab, hab, hix⟩ := ha
  obtain ⟨rfl, ⟨es, hbst, hie, hmem⟩⟩ := role_addr_index_full_spec_ext htbl ext ev71
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev49
  obtain ⟨hlk, rfl⟩ := rbtree_map_lookup_or_default_spec_ext hab hbst ext ev49
  refine ⟨rfl, rfl, ?_⟩
  by_cases hex : ∃ w, (ab, w) ∈ es
  · obtain ⟨w, hw⟩ := hex
    rw [Claim.lookupEntries_eq_of_mem hbst.2 hw] at hlk
    obtain ⟨ro, hw_eq, hof⟩ := hie (ab, w) hw
    rw [hix] at hof
    exact .inr ⟨ro, hlk.trans hw_eq, hof⟩
  · have hno : ∀ w, (ab, w) ∉ es := fun w hw => hex ⟨w, hw⟩
    rw [Claim.lookupEntries_eq_dflt_of_not_mem hno] at hlk
    refine .inl ⟨hlk, ?_⟩
    intro ro hof
    have hm_bound := Claim.mem_bound_of_addressOf_eq_some hof
    obtain ⟨b0, hix0, hb0⟩ := hmem ro a hm_bound
    have hb_eq : b0 = ab := Claim.ixAddr_injective (hix0.trans hix.symm)
    subst hb_eq
    exact hno _ hb0

private theorem role_index_of_lim_spec_ext {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h₁ h₁' h₂ : Heap F}
    {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h₂ x_rc) (ext : Heap.Extends h₁ h₂)
    (ha : S0.addr h₁ x_a a)
    (ev : ObsFn Obs.W "KernelRoles::role_index_of" [x_rc, x_a] h₁ r h₁' calls) :
    h₁' = h₁ ∧
      ((r = .field 0 ∧ ∀ ro, t.addressOf? ro ≠ some a) ∨
        ∃ ro : Ix.Kernel.Role, r = .field (RolesAux.roleNum ro + 1) ∧ t.addressOf? ro = some a) := by
  obtain ⟨_, v8, m18, _, v29, m31, _, ev41, ev28, ev6, -⟩ :=
    Obs.«KernelRoles::role_index_of».obs ev
  obtain ⟨rfl, htbl⟩ := role_ctx_table_lim_spec_ext hrc ext ev41
  obtain ⟨rfl, rfl, hres⟩ := addr_index_lookup_ext htbl ext ha ev28 ev6
  exact ⟨rfl, hres⟩

private theorem role_of_ne_zero_lim_ext {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h₁ h₁' h₂ : Heap F}
    {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h₂ x_rc) (ext : Heap.Extends h₁ h₂)
    (ha : S0.addr h₁ x_a a)
    (ev : ObsFn Obs.W "KernelRoles::role_of" [x_rc, x_a] h₁ r h₁' calls)
    (hne : r ≠ .field 0) :
    ∃ ro : Ix.Kernel.Role, r = .field (RolesAux.roleNum ro + 1) ∧ t.addressOf? ro = some a := by
  obtain ⟨tbl, htbl, ⟨n, -, -, hl⟩ | ⟨-, hl⟩⟩ := hrc.cases
  · match Obs.«KernelRoles::role_of».obs ev with
    | .Mk_n0 (he100 := hr) .. => exact absurd hr hne
    | .Mk_other_other (he222 := hr) .. => exact absurd hr hne
    | .Assumed (ld12 := ld12) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      simp at hl'
    | .Mk_other_n1 (ld12 := ld12) (ev71 := ev71) (ev49 := ev49) (hne103 := hne36)
        (he215 := hr) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      injection hl' with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨_, _, hres⟩ := addr_index_lookup_ext htbl ext ha ev71 ev49
      rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
      · exact absurd h0 hne36
      · exact ⟨ro, hr.trans hro, hof⟩
  · match Obs.«KernelRoles::role_of».obs ev with
    | .Mk_n0 (ld12 := ld12) .. | .Mk_other_n1 (ld12 := ld12) ..
    | .Mk_other_other (ld12 := ld12) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      simp at hl'
    | .Assumed (ld12 := ld12) (ev270 := ev71) (ev248 := ev49) .. =>
      have hl' := ext.loadValue_eq ld12
      rw [hl] at hl'
      injection hl' with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      obtain ⟨_, _, hres⟩ := addr_index_lookup_ext htbl ext ha ev71 ev49
      rcases hres with ⟨h0, -⟩ | ⟨ro, hro, hof⟩
      · exact absurd h0 hne
      · exact ⟨ro, hro, hof⟩

set_option maxRecDepth 100000 in
private theorem admission_of_walks (ro : Ix.Kernel.Role) :
    RoleVal.roleWalksBound ro = true →
      (((RoleVal.roleSpecKindNat ro : Nat) : F) = 0 ∧
        (Claim.memberKindF ro = 0 ∨ Claim.memberKindF ro = 1 ∨ Claim.memberKindF ro = 2)) ∨
      ((RoleVal.roleSpecKindNat ro : Nat) : F) = 2 ∨
      ((RoleVal.roleSpecKindNat ro : Nat) : F) = 5 := by
  cases ro <;> decide

private theorem role_admission_checks_iff {ro : Ix.Kernel.Role} {r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelRoles::role_admission_checks" [.field (RolesAux.roleNum ro)] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 ↔ walkedRole ro = true) := by
  obtain ⟨hh, hdisj⟩ := Claim.role_admission_checks_walks ev
  refine ⟨hh, hdisj.imp id And.left, ⟨fun h1 => ?_, fun hw => ?_⟩⟩
  · rcases hdisj with h0 | ⟨-, hw⟩
    · exact absurd (Value.field.inj (h0.symm.trans h1)) zero_ne_one
    · exact hw
  · rcases hdisj with h0 | ⟨h1, -⟩
    · exfalso
      rw [Claim.walkedRole_eq_roleWalksBound] at hw
      have hadm := admission_of_walks ro hw
      match Obs.«KernelRoles::role_admission_checks».obs ev with
      | .n0_n0 (he55 := he) .. | .n0_n1 (he63 := he) .. | .n0_n2 (he71 := he) ..
      | .n2 (he86 := he) .. | .n5 (he94 := he) .. =>
        exact absurd (Value.field.inj (h0.symm.trans he)) zero_ne_one
      | .n0_other (ev15 := ev15) (ev42 := ev42) (hne58 := hne0) (hne66 := hne1)
          (hne74 := hne2) .. =>
        obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
        obtain ⟨hm, rfl⟩ := Claim.role_member_kind_full ev42
        have hk0 : ((RoleVal.roleSpecKindNat ro : Nat) : F) = 0 := (Value.field.inj hk).symm
        rcases hadm with ⟨-, hm'⟩ | hk2 | hk5
        · rcases hm' with h | h | h
          · exact hne0 (hm.trans (congrArg Value.field h))
          · exact hne1 (hm.trans (congrArg Value.field h))
          · exact hne2 (hm.trans (congrArg Value.field h))
        · exact absurd (hk0.symm.trans hk2) (by decide)
        · exact absurd (hk0.symm.trans hk5) (by decide)
      | .other (ev15 := ev15) (hne81 := hne0) (hne89 := hne2) (hne97 := hne5) .. =>
        obtain ⟨hk, rfl⟩ := RoleVal.role_spec_kind_spec ev15
        rcases hadm with ⟨hk0, -⟩ | hk2 | hk5
        · exact hne0 (hk.trans (congrArg Value.field hk0))
        · exact hne2 (hk.trans (congrArg Value.field hk2))
        · exact hne5 (hk.trans (congrArg Value.field hk5))
    · exact h1

private theorem addr_covered_spec_ext {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h₁ h₁' h₂ : Heap F}
    {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h₂ x_rc) (ext : Heap.Extends h₁ h₂)
    (ha : S0.addr h₁ x_a a)
    (ev : ObsFn Obs.W "KernelModeled::addr_covered" [x_rc, x_a] h₁ r h₁' calls) :
    h₁' = h₁ ∧ (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 ↔ Covered t a) := by
  obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
  match Obs.«KernelModeled::addr_covered».obs ev with
  | .n0 (ev_rcqbqram := ev_ri) (he_daqahcdl := hr) (he_bhektsom := hh) .. =>
    obtain ⟨hm, hres⟩ := role_index_of_lim_spec_ext hrc ext ha ev_ri
    subst hm
    rcases hres with ⟨-, hnone⟩ | ⟨ro, hro, -⟩
    · refine ⟨hh, Or.inl hr, ⟨fun h1 => absurd (Value.field.inj (hr.symm.trans h1)) zero_ne_one, ?_⟩⟩
      rintro ⟨ro, hof, -⟩
      exact (hnone ro hof).elim
    · exact absurd (Value.field.inj hro).symm (RolesAux.roleNum_add_one_ne_zero ro)
  | .other (ev_rcqbqram := ev_ri) (hne_xjnibfzs := hne) (op_buvadoef := op)
      (ev_opsbypwq := ev_adm) .. =>
    obtain ⟨hm, hres⟩ := role_index_of_lim_spec_ext hrc ext ha ev_ri
    subst hm
    rcases hres with ⟨h0, -⟩ | ⟨ro, rfl, hof⟩
    · exact absurd h0 hne
    · simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
      subst op
      obtain ⟨hh, hbin, hiff⟩ := role_admission_checks_iff ev_adm
      refine ⟨hh, hbin, ⟨fun h1 => ⟨ro, hof, hiff.mp h1⟩, ?_⟩⟩
      rintro ⟨ro', hof', hw'⟩
      have hro_eq : ro' = ro :=
        Ix.Kernel.RoleTable.addressOf?_inj (RoleClosure.check_ok_of_wf hwf) hof' hof
      subst hro_eq
      exact hiff.mpr hw'

private theorem assert_covered_past_spec_ext {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_passed x_a r : SourceValue F} {h₁ h₁' h₂ : Heap F}
    {calls : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h₂ x_rc) (ext : Heap.Extends h₁ h₂)
    (ha : S0.addr h₁ x_a a)
    (ev : ObsFn Obs.W "KernelModeled::assert_covered_past" [x_rc, x_passed, x_a] h₁ r h₁' calls) :
    h₁' = h₁ ∧ (x_passed = .field 0 ∨ Covered t a) := by
  match Obs.«KernelModeled::assert_covered_past».obs ev with
  | .n0 (hv_fdljvuxp := h0) (he_nkrxsxon := hh) .. => exact ⟨hh, Or.inl h0⟩
  | .other (ev_irotxrni := ev_cov) (heq_mgsqbtsh := h1) (he_yrjjshnd := hh) .. =>
    obtain ⟨hm, -, hiff⟩ := addr_covered_spec_ext hrc ext ha ev_cov
    exact ⟨hh.trans hm, Or.inr (hiff.mp h1)⟩

set_option maxRecDepth 100000 in
private theorem basis_role_of_num (ro : Ix.Kernel.Role) :
    (RolesAux.roleNum ro = 0 ∨ RolesAux.roleNum ro = 1 ∨ RolesAux.roleNum ro = 2 ∨
      RolesAux.roleNum ro = 3 ∨ RolesAux.roleNum ro = 8 ∨ RolesAux.roleNum ro = 9 ∨
      RolesAux.roleNum ro = 10 ∨ RolesAux.roleNum ro = 11 ∨ RolesAux.roleNum ro = 12 ∨
      RolesAux.roleNum ro = 13 ∨ RolesAux.roleNum ro = 32 ∨ RolesAux.roleNum ro = 33 ∨
      RolesAux.roleNum ro = 34 ∨ RolesAux.roleNum ro = 35 ∨ RolesAux.roleNum ro = 36) →
    ro ∈ basisRoles := by
  cases ro <;> decide

private theorem basis_role_allowed_spec {ro : Ix.Kernel.Role} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::basis_role_allowed" [.field (RolesAux.roleNum ro)] h (.field 1)
      h' calls) :
    h' = h ∧ ro ∈ basisRoles := by
  match Obs.«KernelModeled::basis_role_allowed».obs ev with
  | .n0 (hv14 := hv) (he16 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n1 (hv22 := hv) (he24 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n2 (hv30 := hv) (he32 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n3 (hv38 := hv) (he40 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n8 (hv46 := hv) (he48 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n9 (hv54 := hv) (he56 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n10 (hv62 := hv) (he64 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n11 (hv70 := hv) (he72 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n12 (hv78 := hv) (he80 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n13 (hv86 := hv) (he88 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n32 (hv94 := hv) (he96 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n33 (hv102 := hv) (he104 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n34 (hv110 := hv) (he112 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n35 (hv118 := hv) (he120 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .n36 (hv126 := hv) (he128 := hh) .. =>
    exact ⟨hh, basis_role_of_num ro (by simp [Value.field.inj hv])⟩
  | .other (he150 := he) .. => exact absurd (Value.field.inj he) (by decide)

/-! ## Unconditional projection-address hashing -/

section ProjHash

open Ixon.Verify.Codec Ixon.Verify.Codec.ConstantTables Ixon.Verify.Codec.NonrecursiveConstant

private theorem tag0Bytes_size_le9 (v : UInt64) : (tag0Bytes v).size ≤ 9 := by
  unfold tag0Bytes
  rw [tagNBytes_size]
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

private theorem serConstant_iprj_size_lt (i : UInt64) (b : Bytes.Address) :
    (Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩).size < 4294967296 := by
  have hb : AddressWireWF (Core.ixAddr b) := by
    show (Core.ixAddr b).hash.size = 32
    exact b.size_toArray
  have hcwf : NonrecursiveConstantWireWF ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ :=
    { info := .iPrj hb
      sharingCount := by show (#[] : Array Ixon.Expr).size < UInt64.size; decide
      sharingEntries := by simp
      refsCount := by show (#[] : Array _root_.Address).size < UInt64.size; decide
      refsEntries := by simp
      univsCount := by show (#[] : Array Ixon.Univ).size < UInt64.size; decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  have hser : Ixon.serConstant ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive _ hcwf).runPut
  have hbytes : nonrecursiveConstantBytes ⟨.iPrj ⟨i, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ =
      tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ ++
        (tag0Bytes i ++ (Core.ixAddr b).hash) ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty ++
        tag0Bytes 0 ++ ByteArray.empty ++ tag0Bytes 0 ++ ByteArray.empty := by
    simp [nonrecursiveConstantBytes, nonrecursiveInfoBytes, inductiveProjBytes, listBytes,
      bindersBytes, ByteArray.append_assoc]
  rw [hser, hbytes]
  have h4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).size = 1 := by
    unfold tag4Bytes; rw [tagNBytes_size]; decide
  have h0 : (tag0Bytes 0).size = 1 := by unfold tag0Bytes; rw [tagNBytes_size]; decide
  have hi := tag0Bytes_size_le9 i
  have ha : (Core.ixAddr b).hash.size = 32 := b.size_toArray
  simp only [ByteArray.size_append, ByteArray.size_empty, h4, h0, ha]
  omega

private theorem byteArray_of_toList_local (b : ByteArray) :
    (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  cases b with
  | mk data =>
    simp [Array.toArray_toList]

private theorem compute_iprj_addr_hashed {b : Bytes.Address} {x_blk x_idx r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_blk)
    (ev : ObsFn Obs.W "KernelDefEq::compute_iprj_addr" [x_blk, x_idx] h r h' calls) :
    Heap.Extends h h' ∧
      ∃ (n : Nat) (a : Bytes.Address), n < 72057594037927936 ∧
        Bytes.RepAddressRef Core.addrTy h' a r ∧
        Core.ixAddr a = Core.projAddr (.iPrj ⟨n.toUInt64, Core.ixAddr b⟩) ∧
        Hashed calls (Ixon.serConstant ⟨.iPrj ⟨n.toUInt64, Core.ixAddr b⟩, #[], #[], #[], #[]⟩) := by
  obtain ⟨v1, m2, cs12, m84, m97, m110, m123, v135, m136, cs146, m159, cs174,
    ev14, hm92, hm105, hm118, hm131, hm167, ev148, ev176, hc185⟩ :=
    Obs.«KernelDefEq::compute_iprj_addr».obs ev
  obtain ⟨n, hn56, -, hv1, hm2⟩ := Lib.u64_from_field_spec ev14
  subst m2
  have hu64_sz : UInt64.size = 18446744073709551616 := by decide
  have hu64 : n.toUInt64.toNat = n := UInt64.toNat_ofNat_of_lt (by omega)
  have hrep_u64 : RepU64 h n.toUInt64 v1 := by
    have hv1' : v1 = TagN.u64Value n.toUInt64.toNat := by rw [hv1, hu64]
    rw [hv1']
    exact Deserialize.repU64_u64Value h n.toUInt64
  have e1 : Heap.Extends h m84 := by rw [hm92]; exact Heap.Extends.snoc h _
  have p1 : RepList Core.Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) m84 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length) := by
    rw [hm92]; exact Lib.rep_store_nil h
  have e2 : Heap.Extends m84 m97 := by rw [hm105]; exact Heap.Extends.snoc m84 _
  have p2 : RepList Core.addrListEnum (fun _ (_ : Unit) _ => True) m97 []
      (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m84.length) := by
    rw [hm105]; exact Lib.rep_store_nil m84
  have e3 : Heap.Extends m97 m110 := by rw [hm118]; exact Heap.Extends.snoc m97 _
  have p3 : RepList Core.Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) m110 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m97.length) := by
    rw [hm118]; exact Lib.rep_store_nil m97
  have e4 : Heap.Extends m110 m123 := by rw [hm131]; exact Heap.Extends.snoc m110 _
  have p4 : RepList Core.Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) m123 []
      (.ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m110.length) := by
    rw [hm131]; exact Lib.rep_store_nil m110
  have e5 : Heap.Extends m123 m159 := by rw [hm167]; exact Heap.Extends.snoc m123 _
  have hnil : Bytes.RepByteStream Core.byteListEnum m159 []
      (.ptr (.enum Names.«Lists::Node<Field>») m123.length) := by
    rw [hm167]; exact Lib.rep_store_nil m123
  have e15 := (((e1.trans e2).trans e3).trans e4).trans e5
  let info : Ixon.ConstantInfo := .iPrj ⟨n.toUInt64, Core.ixAddr b⟩
  have hinfo : Core.Specs.Callees.ProjInfoRep m159 info
      (.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [v1, x_blk]]) :=
    ⟨v1, x_blk, b, rfl, repU64_heapMono₂ e15 hrep_u64,
      Bytes.repAddressRef_heapMono₂ Core.addrTy e15 hb, rfl⟩
  have hcv : Core.Specs.Callees.ProjConstRep m159 info
      (.construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" "IPrj"
          [.construct "Ixon::InductiveProj" "Mk" [v1, x_blk]],
         .ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length,
         .ptr (.enum Names.«Lists::Node<&[Field; 32]>») m84.length,
         .ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m97.length,
         .ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m110.length]) :=
    ⟨_, _, _, _, _, rfl, hinfo,
      p1.mono (fun _ _ _ _ _ t => t) (((e2.trans e3).trans e4).trans e5),
      p2.mono (fun _ _ _ _ _ t => t) ((e3.trans e4).trans e5),
      p3.mono (fun _ _ _ _ _ t => t) (e4.trans e5),
      p4.mono (fun _ _ _ _ _ t => t) e5⟩
  obtain ⟨e_put, s_put⟩ := L1.put_constant_proj_spec hcv hnil ev148
  rw [List.append_nil] at s_put
  have hlen_ser : (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList.length < 4294967296 := by
    simpa only [ByteArray.size, Array.length_toList] using serConstant_iprj_size_lt n.toUInt64 b
  obtain ⟨e_b2a, a, ha_rep, ha_eq⟩ := L1.bytes_to_addr_native_spec hlen_ser s_put ev176
  rw [byteArray_of_toList_local] at ha_eq
  have stream : L1.Stream m136 _ v135 := s_put
  have hashMember := (L1.bytes_to_addr_spec stream ev176).2.2
  have hashed : Hashed calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) :=
    ⟨⟨"Blake3::hash", [v135], m136⟩, by rw [hc185]; simp [hashMember], rfl, v135, rfl, stream⟩
  exact ⟨(e15.trans e_put).trans e_b2a, n, a, hn56, ha_rep, ha_eq, hashed⟩

private theorem projection_addr_ctor_hashed {b : Bytes.Address}
    {x_ind x_cidx x_blk r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_blk)
    (ev : ObsFn Obs.W "KernelCheck::projection_addr_ctor" [x_ind, x_cidx, x_blk] h r h' calls) :
    Heap.Extends h h' ∧
      ∃ (ni nc : Nat) (a : Bytes.Address),
        ni < 72057594037927936 ∧ nc < 72057594037927936 ∧
        Bytes.RepAddressRef Core.addrTy h' a r ∧
        Core.ixAddr a = Core.projAddr (.cPrj ⟨ni.toUInt64, nc.toUInt64, Core.ixAddr b⟩) ∧
        Hashed calls (Ixon.serConstant
          ⟨.cPrj ⟨ni.toUInt64, nc.toUInt64, Core.ixAddr b⟩, #[], #[], #[], #[]⟩) := by
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni56, -, hv1, hm2⟩ := Lib.u64_from_field_spec ev14
  subst m2
  obtain ⟨nc, hnc56, -, hv23, hm24⟩ := Lib.u64_from_field_spec ev36
  subst m24
  have hu64_sz : UInt64.size = 18446744073709551616 := by decide
  have hui : ni.toUInt64.toNat = ni := UInt64.toNat_ofNat_of_lt (by omega)
  have huc : nc.toUInt64.toNat = nc := UInt64.toNat_ofNat_of_lt (by omega)
  have hrep_i : RepU64 h ni.toUInt64 v1 := by
    have hv1' : v1 = TagN.u64Value ni.toUInt64.toNat := by rw [hv1, hui]
    rw [hv1']; exact Deserialize.repU64_u64Value h ni.toUInt64
  have hrep_c : RepU64 h nc.toUInt64 v23 := by
    have hv23' : v23 = TagN.u64Value nc.toUInt64.toNat := by rw [hv23, huc]
    rw [hv23']; exact Deserialize.repU64_u64Value h nc.toUInt64
  have e1 : Heap.Extends h m114 := by rw [hm122]; exact Heap.Extends.snoc h _
  have p1 : RepList Core.Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) m114 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length) := by
    rw [hm122]; exact Lib.rep_store_nil h
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc m114 _
  have p2 : RepList Core.addrListEnum (fun _ (_ : Unit) _ => True) m127 []
      (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m114.length) := by
    rw [hm135]; exact Lib.rep_store_nil m114
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc m127 _
  have p3 : RepList Core.Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) m140 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m127.length) := by
    rw [hm148]; exact Lib.rep_store_nil m127
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc m140 _
  have p4 : RepList Core.Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) m153 []
      (.ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m140.length) := by
    rw [hm161]; exact Lib.rep_store_nil m140
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc m153 _
  have hnil : Bytes.RepByteStream Core.byteListEnum m189 []
      (.ptr (.enum Names.«Lists::Node<Field>») m153.length) := by
    rw [hm197]; exact Lib.rep_store_nil m153
  have e15 := (((e1.trans e2).trans e3).trans e4).trans e5
  let info : Ixon.ConstantInfo := .cPrj ⟨ni.toUInt64, nc.toUInt64, Core.ixAddr b⟩
  have hinfo : Core.Specs.Callees.ProjInfoRep m189 info
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [v1, v23, x_blk]]) :=
    ⟨v1, v23, x_blk, b, rfl, repU64_heapMono₂ e15 hrep_i,
      repU64_heapMono₂ e15 hrep_c,
      Bytes.repAddressRef_heapMono₂ Core.addrTy e15 hb, rfl⟩
  have hcv : Core.Specs.Callees.ProjConstRep m189 info
      (.construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" "CPrj"
          [.construct "Ixon::ConstructorProj" "Mk" [v1, v23, x_blk]],
         .ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length,
         .ptr (.enum Names.«Lists::Node<&[Field; 32]>») m114.length,
         .ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m127.length,
         .ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m140.length]) :=
    ⟨_, _, _, _, _, rfl, hinfo,
      p1.mono (fun _ _ _ _ _ t => t) (((e2.trans e3).trans e4).trans e5),
      p2.mono (fun _ _ _ _ _ t => t) ((e3.trans e4).trans e5),
      p3.mono (fun _ _ _ _ _ t => t) (e4.trans e5),
      p4.mono (fun _ _ _ _ _ t => t) e5⟩
  obtain ⟨e_put, s_put⟩ := L1.put_constant_proj_spec hcv hnil ev178
  rw [List.append_nil] at s_put
  have hlen_ser : (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList.length < 4294967296 := by
    simpa only [ByteArray.size, Array.length_toList] using
      Claim.serConstant_cprj_size_lt ni.toUInt64 nc.toUInt64 b
  obtain ⟨e_b2a, a, ha_rep, ha_eq⟩ := L1.bytes_to_addr_native_spec hlen_ser s_put ev206
  rw [byteArray_of_toList_local] at ha_eq
  have stream : L1.Stream m166 _ v165 := s_put
  have hashMember := (L1.bytes_to_addr_spec stream ev206).2.2
  have hashed : Hashed calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) :=
    ⟨⟨"Blake3::hash", [v165], m166⟩, by rw [hc215]; simp [hashMember], rfl, v165, rfl, stream⟩
  exact ⟨(e15.trans e_put).trans e_b2a, ni, nc, a, hni56, hnc56, ha_rep, ha_eq, hashed⟩

end ProjHash

/-! ## Reference helpers: `projection_block`, `used_ref_has`, `is_projection_of`, `projection_of_ref_block` -/

private theorem refs_size_lt_local {bytes : ByteArray} {c : Ixon.Constant}
    (hlen : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 72057594037927936 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem repConstant_refs_eq_local {h : Heap F} {c : Ixon.Constant}
    {x_info x_sh x_refs x_un x_bd : SourceValue F}
    (hrep : Claim.RepConstant h c (.construct "Ixon::Constant" "Mk"
      [x_info, x_sh, x_refs, x_un, x_bd])) :
    RepList Core.addrListEnum Claim.RepAddrElem h c.refs.toList x_refs := by
  obtain ⟨_, _, refsPtr, _, _, hv, -, -, hrf, -, -⟩ := hrep
  injection hv with _ _ hargs
  simp only [List.cons.injEq, and_true] at hargs
  rw [hargs.2.2.1]
  exact hrf

private theorem repIxonAddrList_to_core {h : Heap F} {xs : List _root_.Address}
    {x_refs : SourceValue F}
    (hr : RepList Core.addrListEnum Claim.RepAddrElem h xs x_refs) :
    ∃ bs : List Bytes.Address, bs.map Core.ixAddr = xs ∧
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h bs x_refs := by
  induction hr with
  | nil hld => exact ⟨[], rfl, .nil hld⟩
  | cons hx _ hld ih =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨bs, rfl, hbs⟩ := ih
    exact ⟨b :: bs, rfl, .cons hb hbs hld⟩

private theorem projection_block_spec {h h' : Heap F} {c : Ixon.Constant} {x_c r : SourceValue F}
    {cs : List (Call F)} (a : _root_.Address)
    (hrep : Claim.RepConstant h c x_c)
    (ev : ObsFn Obs.W "KernelModeled::projection_block" [x_c] h r h' cs) :
    h' = h ∧ IsProj c ∧ ∃ b : Bytes.Address, Bytes.RepAddressRef Core.addrTy h b r ∧
      Core.ixAddr b = Ix.Cert.ownerOf a c := by
  obtain ⟨infoVal, _, _, _, _, rfl, hinfo, -, -, -, -⟩ := hrep
  match Obs.«KernelModeled::projection_block».obs ev with
  | .IPrj (hv15 := hv) (he95 := hr) (he96 := hh) .. =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [hargs.1] at hinfo
    cases hc : c.info with
    | iPrj p =>
      rw [hc] at hinfo
      obtain ⟨pv, hpv, blkPtr, hmk, b, hb_rep, hb_eq⟩ := hinfo
      injection hpv with _ _ hpa; simp only [List.cons.injEq] at hpa
      rw [← hpa] at hmk; injection hmk with _ _ hpa2; simp only [List.cons.injEq] at hpa2
      rw [← hpa2.2] at hb_rep; subst hr
      exact ⟨hh, Or.inr (Or.inl ⟨p, hc⟩), b, hb_rep, by rw [hb_eq]; simp [Ix.Cert.ownerOf, hc]⟩
    | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | dPrj _ | muts _ =>
      rw [hc] at hinfo; obtain ⟨_, hbad, -⟩ := hinfo; simp at hbad
  | .CPrj (hv15 := hv) (he145 := hr) (he146 := hh) .. =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [hargs.1] at hinfo
    cases hc : c.info with
    | cPrj p =>
      rw [hc] at hinfo
      obtain ⟨pv, hpv, blkPtr, hmk, b, hb_rep, hb_eq⟩ := hinfo
      injection hpv with _ _ hpa; simp only [List.cons.injEq] at hpa
      rw [← hpa] at hmk; injection hmk with _ _ hpa2; simp only [List.cons.injEq] at hpa2
      rw [← hpa2.2.2] at hb_rep; subst hr
      exact ⟨hh, Or.inr (Or.inr (Or.inl ⟨p, hc⟩)), b, hb_rep, by rw [hb_eq]; simp [Ix.Cert.ownerOf, hc]⟩
    | defn _ | recr _ | axio _ | quot _ | iPrj _ | rPrj _ | dPrj _ | muts _ =>
      rw [hc] at hinfo; obtain ⟨_, hbad, -⟩ := hinfo; simp at hbad
  | .RPrj (hv15 := hv) (he189 := hr) (he190 := hh) .. =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [hargs.1] at hinfo
    cases hc : c.info with
    | rPrj p =>
      rw [hc] at hinfo
      obtain ⟨pv, hpv, blkPtr, hmk, b, hb_rep, hb_eq⟩ := hinfo
      injection hpv with _ _ hpa; simp only [List.cons.injEq] at hpa
      rw [← hpa] at hmk; injection hmk with _ _ hpa2; simp only [List.cons.injEq] at hpa2
      rw [← hpa2.2] at hb_rep; subst hr
      exact ⟨hh, Or.inr (Or.inr (Or.inr ⟨p, hc⟩)), b, hb_rep, by rw [hb_eq]; simp [Ix.Cert.ownerOf, hc]⟩
    | defn _ | recr _ | axio _ | quot _ | iPrj _ | cPrj _ | dPrj _ | muts _ =>
      rw [hc] at hinfo; obtain ⟨_, hbad, -⟩ := hinfo; simp at hbad
  | .DPrj (hv15 := hv) (he233 := hr) (he234 := hh) .. =>
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [hargs.1] at hinfo
    cases hc : c.info with
    | dPrj p =>
      rw [hc] at hinfo
      obtain ⟨pv, hpv, blkPtr, hmk, b, hb_rep, hb_eq⟩ := hinfo
      injection hpv with _ _ hpa; simp only [List.cons.injEq] at hpa
      rw [← hpa] at hmk; injection hmk with _ _ hpa2; simp only [List.cons.injEq] at hpa2
      rw [← hpa2.2] at hb_rep; subst hr
      exact ⟨hh, Or.inl ⟨p, hc⟩, b, hb_rep, by rw [hb_eq]; simp [Ix.Cert.ownerOf, hc]⟩
    | defn _ | recr _ | axio _ | quot _ | iPrj _ | cPrj _ | rPrj _ | muts _ =>
      rw [hc] at hinfo; obtain ⟨_, hbad, -⟩ := hinfo; simp at hbad

private theorem used_ref_has_aux {idxs : List Nat} {rb : Bytes.Address} :
    ∀ {refs : List Bytes.Address} {i : Nat} {x_refs x_used x_r r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      i + refs.length < 72057594037927936 →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h refs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs x_used →
      Bytes.RepAddressRef Core.addrTy h rb x_r →
      ObsFn Obs.W "KernelModeled::used_ref_has" [x_refs, x_used, .field (i : F), x_r] h r h' cs →
      h' = h ∧ (r = .field 1 → ∃ k < refs.length, (i + k) ∈ idxs ∧ refs[k]? = some rb)
  | [], i, x_refs, x_used, x_r, r, h, h', cs, hbound, hrefs, hused, hrb, ev => by
    match Obs.«KernelModeled::used_ref_has».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. =>
      exact ⟨hh, fun h1 => absurd (Value.field.inj (hr.symm.trans h1)) zero_ne_one⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases hbad
  | q :: rest, i, x_refs, x_used, x_r, r, h, h', cs, hbound, hrefs, hused, hrb, ev => by
    have hi : i < 72057594037927936 := by simp at hbound; omega
    match Obs.«KernelModeled::used_ref_has».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases Lib.rep_nil_of_load hrefs ld
    | .Cons_n1 (ld12 := ld) (sg113 := sg) (he128 := hr) (he129 := hh) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      match sg with
      | .n1 (ev54 := ev54) (ev80 := ev80) .. =>
        obtain ⟨hm41, hhas⟩ := Claim.g_list_has_spec idxs hi hused ev54
        subst hm41
        obtain ⟨heq_addr, hm_eq⟩ := Lib.address_eq_spec ev80 hq hrb
        refine ⟨hh.trans hm_eq, fun _ => ?_⟩
        have hqb : q = rb := by
          by_cases h : q = rb
          · exact h
          · rw [ite_eq_right h] at heq_addr
            exact absurd (Value.field.inj heq_addr) one_ne_zero
        subst hqb
        exact ⟨0, by simp, hhas.mp rfl, by simp⟩
      | .other (he102 := h0) .. => exact absurd (Value.field.inj h0) one_ne_zero
    | .Cons_other (ld12 := ld) (sg113 := sg) (op172 := op) (ev140 := ev140) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      have hm106 : _ = h := by
        match sg with
        | .n1 (ev54 := ev54) (ev80 := ev80) .. =>
          obtain ⟨hm41, -⟩ := Claim.g_list_has_spec idxs hi hused ev54
          subst hm41
          exact (Lib.address_eq_spec ev80 hq hrb).2
        | .other (ev54 := ev54) (he103 := hh') .. =>
          exact hh'.trans (Claim.g_list_has_spec idxs hi hused ev54).1
      subst hm106
      have hv : _ = Value.field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]; push_cast; rfl
      rw [hv] at ev140
      obtain ⟨hh', hrec⟩ := used_ref_has_aux (i := i + 1) (by simp at hbound ⊢; omega)
        hrest hused hrb ev140
      refine ⟨hh', fun h1 => ?_⟩
      obtain ⟨k, hk, hmem, hget⟩ := hrec h1
      exact ⟨k + 1, by simp; omega, by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hmem,
        by simpa using hget⟩

private theorem is_projection_of_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {rb bb : Bytes.Address} {x_r x_blk r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hr : Bytes.RepAddressRef Core.addrTy h rb x_r)
    (hblk : Bytes.RepAddressRef Core.addrTy h bb x_blk)
    (ev : ObsFn Obs.W "KernelModeled::is_projection_of" [x_r, x_blk] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      (r = .field 1 →
        ∃ cr, recordOf E₀ (Core.ixAddr rb) = some cr ∧ IsProj cr ∧
          Ix.Cert.ownerOf (Core.ixAddr rb) cr = Core.ixAddr bb ∧
          ∃ cb, recordOf E₀ (Core.ixAddr bb) = some cb ∧
            ConstAddrOf (Core.ixAddr bb) cb (Core.ixAddr rb)) := by
  have handleProj : ∀ {m2 m_ci m_pb : Heap F} {cs12 cs_ci cs_pb cs_eq : List (Call F)}
      {x_c v_ci v_pb : SourceValue F},
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) →
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h x_c m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [x_c] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "Bytes::address_eq" [v_pb, x_blk] m_pb r h' cs_eq →
      Heap.Extends h h' ∧
        (r = .field 1 →
          ∃ cr, recordOf E₀ (Core.ixAddr rb) = some cr ∧ IsProj cr ∧
            Ix.Cert.ownerOf (Core.ixAddr rb) cr = Core.ixAddr bb ∧
            ∃ cb, recordOf E₀ (Core.ixAddr bb) = some cb ∧
              ConstAddrOf (Core.ixAddr bb) cb (Core.ixAddr rb)) := by
    intro m2 m_ci m_pb cs12 cs_ci cs_pb cs_eq x_c v_ci v_pb hsub12 hsub_ci ev14 ev_ci ev_pb ev_eq
    obtain ⟨ext1, rawBytes, cr, hlen, hh, haddr, -, hexact, hrep_cr, -⟩ :=
      Claim.load_verified_constant_de ⟨rb, hr, rfl⟩ ev14
    have hrec_cr : recordOf E₀ (Core.ixAddr rb) = some cr :=
      Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub12 hh) hlen (by rw [haddr]; exact hexact)
    have ext_ci := ev_ci.heap_extends
    obtain ⟨hpb_h, hproj, b_own, hown_rep, hown_eq⟩ :=
      projection_block_spec (Core.ixAddr rb) (hrep_cr.mono ext_ci) ev_pb
    subst hpb_h
    obtain ⟨heq_r, heq_h⟩ :=
      Lib.address_eq_spec ev_eq hown_rep
        (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext1.trans ext_ci) hblk)
    refine ⟨heq_h ▸ ext1.trans ext_ci, fun h1 => ?_⟩
    have hown_bb : b_own = bb := by
      by_cases h : b_own = bb
      · exact h
      · rw [ite_eq_right h] at heq_r
        exact absurd (Value.field.inj (h1.symm.trans heq_r)) one_ne_zero
    subst hown_bb
    obtain ⟨cb, hcb, hca⟩ :=
      Claim.proj_member_of_load hS hcov (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hr)
        ev_ci hsub_ci hrec_cr hproj
    rw [← hown_eq] at hcb hca
    exact ⟨cr, hrec_cr, hproj, hown_eq.symm, cb, hcb, hca⟩
  match Obs.«KernelModeled::is_projection_of».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := cs_ci) (ev14 := ev14) (ev_pvplyepc := ev_ci)
      (ev109 := ev_pb) (ev95 := ev_eq) (hc125 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_eq
  | .CPrj (cs12 := cs12) (cs_tafpebbo := cs_ci) (ev14 := ev14) (ev_rnaxgwez := ev_ci)
      (ev158 := ev_pb) (ev144 := ev_eq) (hc174 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_eq
  | .RPrj (cs12 := cs12) (cs_nwqbwyif := cs_ci) (ev14 := ev14) (ev_jqzwxbpt := ev_ci)
      (ev207 := ev_pb) (ev193 := ev_eq) (hc223 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_eq
  | .other (ev14 := ev14) (he228 := hr0) (he229 := hh) .. =>
    exact ⟨hh ▸ ev14.heap_extends, fun h1 => absurd (Value.field.inj (hr0.symm.trans h1)) zero_ne_one⟩

private theorem ref_projects_from_aux {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr A : _root_.Address} {lim : Option Nat}
    {cA : Ixon.Constant} {rb bb : Bytes.Address}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hA : recordOf E₀ A = some cA) :
    ∀ {refs : List Bytes.Address} {i : Nat}
      {x_rc x_r x_irefs x_iused x_blk r : SourceValue F} {h₁ h₁' h₂ : Heap F} {cs : List (Call F)},
      i + refs.length < 72057594037927936 →
      (∀ k q, refs[k]? = some q → cA.refs[i + k]? = some (Core.ixAddr q)) →
      Claim.RCLimRep t bAddr lim h₂ x_rc →
      Heap.Extends h₁' h₂ →
      Bytes.RepAddressRef Core.addrTy h₁ rb x_r →
      Bytes.RepAddressRef Core.addrTy h₁ bb x_blk →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h₁ refs x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h₁ (S0.usedRefIdxs cA) x_iused →
      ObsFn Obs.W "KernelModeled::ref_projects_from"
        [x_rc, x_r, x_irefs, x_iused, .field (i : F), x_blk] h₁ r h₁' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      Heap.Extends h₁ h₁' ∧
        (r = .field 1 →
          ∃ q cq, UsedRef E₀ A q ∧ recordOf E₀ q = some cq ∧ IsProj cq ∧
            Ix.Cert.ownerOf q cq = Core.ixAddr bb ∧
            (Covered t q → Covered t (Core.ixAddr rb)))
  | [], i, x_rc, x_r, x_irefs, x_iused, x_blk, r, h₁, h₁', h₂, cs,
      hbound, halign, hrc, ext_end, hr, hblk, hrefs, hused, ev, hsub => by
    match Obs.«KernelModeled::ref_projects_from».obs ev with
    | .Nil (he20 := hr0) (he21 := hh) .. =>
      exact ⟨hh ▸ Heap.Extends.refl _, fun h1 => absurd (Value.field.inj (hr0.symm.trans h1)) zero_ne_one⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases hbad
  | q :: rest, i, x_rc, x_r, x_irefs, x_iused, x_blk, r, h₁, h₁', h₂, cs,
      hbound, halign, hrc, ext_end, hr, hblk, hrefs, hused, ev, hsub => by
    have hi : i < 72057594037927936 := by simp at hbound; omega
    have seg_spec : ∀ {x_q x_rest v_seg : SourceValue F} {m_seg : Heap F} {cs_seg : List (Call F)},
        Bytes.RepAddressRef Core.addrTy h₁ q x_q →
        Heap.Extends m_seg h₂ →
        Obs.«KernelModeled::ref_projects_from».Seg1 x_q x_rest x_rc x_r x_irefs x_iused
          (.field (i : F)) x_blk h₁ v_seg m_seg cs_seg →
        (∀ cl ∈ cs_seg, cl ∈ calls) →
        Heap.Extends h₁ m_seg ∧
          (v_seg = .field 1 →
            ∃ cq, UsedRef E₀ A (Core.ixAddr q) ∧ recordOf E₀ (Core.ixAddr q) = some cq ∧
              IsProj cq ∧ Ix.Cert.ownerOf (Core.ixAddr q) cq = Core.ixAddr bb ∧
              (Covered t (Core.ixAddr q) → Covered t (Core.ixAddr rb))) := by
      intro x_q x_rest v_seg m_seg cs_seg hq ext_seg sg hsub_seg
      match sg with
      | .other (ev54 := ev54) (he102 := hv0) (he103 := hh) .. =>
        obtain ⟨hm41, -⟩ := Claim.g_list_has_spec (S0.usedRefIdxs cA) hi hused ev54
        exact ⟨hh ▸ hm41 ▸ Heap.Extends.refl _, fun h1 => absurd (Value.field.inj (hv0.symm.trans h1)) zero_ne_one⟩
      | .n1_other (ev54 := ev54) (ev_crsszbsn := ev_ip) (he_wiyazqbs := hv0)
          (he_rviofgqu := hh) .. =>
        obtain ⟨hm41, -⟩ := Claim.g_list_has_spec (S0.usedRefIdxs cA) hi hused ev54
        subst hm41
        exact ⟨hh ▸ ev_ip.heap_extends, fun h1 => absurd (Value.field.inj (hv0.symm.trans h1)) zero_ne_one⟩
      | .n1_n1 (cs_mxfetwtb := cs_ip) (ev54 := ev54) (ev_crsszbsn := ev_ip)
          (ev_etesurje := ev_cq) (ev_syhqofqg := ev_cr)
          (op_ztslruok := op1) (op_bcpdefgr := op2) (op_iqlapcsn := op3) (hc_rfthzkdb := hcs) .. =>
        obtain ⟨hm41, hhas⟩ := Claim.g_list_has_spec (S0.usedRefIdxs cA) hi hused ev54
        subst hm41
        obtain ⟨ext_ip, hip⟩ := is_projection_of_spec hS hcov hq hblk ev_ip
          (fun cl hcl => hsub_seg cl (by rw [hcs]; simp [hcl]))
        obtain ⟨cq, hcq, hproj_cq, hown_cq, -⟩ := hip rfl
        have ext_cq : Heap.Extends _ h₂ :=
          (ev_cq.heap_extends.trans ev_cr.heap_extends).trans ext_seg
        obtain ⟨hm_cq, hbin_q, hiff_q⟩ :=
          addr_covered_spec_ext hrc ext_cq
            ⟨q, Bytes.repAddressRef_heapMono₂ Core.addrTy ext_ip hq, rfl⟩ ev_cq
        subst hm_cq
        obtain ⟨hm_cr, hbin_r, hiff_r⟩ :=
          addr_covered_spec_ext hrc (ev_cr.heap_extends.trans ext_seg)
            ⟨rb, Bytes.repAddressRef_heapMono₂ Core.addrTy ext_ip hr, rfl⟩ ev_cr
        subst hm_cr
        refine ⟨ext_ip, fun h1 => ?_⟩
        refine ⟨cq, ⟨cA, i, hA, ?_, halign 0 q (by simp)⟩, hcq, hproj_cq, hown_cq, fun hcov_q => ?_⟩
        · rw [← Assembly.usedRefIdxs_eq]
          exact hhas.mp rfl
        · have hq1 := hiff_q.mpr hcov_q
          rcases hbin_r with hr0 | hr1
          · exfalso
            rw [hr0] at op1
            simp only [evalBinOp, sub_zero, Except.ok.injEq] at op1
            rw [hq1, ← op1] at op2
            simp only [evalBinOp, mul_one, Except.ok.injEq] at op2
            rw [← op2] at op3
            simp only [evalBinOp, sub_self, Except.ok.injEq] at op3
            exact absurd (Value.field.inj (op3.symm.trans h1)) zero_ne_one
          · exact hiff_r.mp hr1
    match Obs.«KernelModeled::ref_projects_from».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrefs ld
    | .Cons_n1 (ld12 := ld) (sg113 := sg) (he128 := hr1) (he129 := hh) (hc130 := hcs) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨ext_seg, hseg⟩ := seg_spec hq (hh ▸ ext_end) sg (fun cl hcl => hsub cl (by rw [hcs]; exact hcl))
      refine ⟨hh ▸ ext_seg, fun _ => ?_⟩
      obtain ⟨cq, hu, hcq, hpr, hown, himp⟩ := hseg rfl
      exact ⟨Core.ixAddr q, cq, hu, hcq, hpr, hown, himp⟩
    | .Cons_other (ld12 := ld) (sg113 := sg) (op_ifhibjja := op) (ev140 := ev140)
        (hc181 := hcs) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨ext_seg, -⟩ := seg_spec hq (ev140.heap_extends.trans ext_end) sg
        (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      have hv : _ = Value.field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]; push_cast; rfl
      rw [hv] at ev140
      obtain ⟨ext_rest, hrec⟩ := ref_projects_from_aux hS hcov hA (i := i + 1)
        (by simp at hbound ⊢; omega)
        (fun k q' hget => by
          have := halign (k + 1) q' (by simpa using hget)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
        hrc ext_end
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_seg hr)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_seg hblk)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hused)
        ev140 (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
      exact ⟨ext_seg.trans ext_rest, hrec⟩

private theorem projection_of_ref_block_spec {K : FamRunCtx} {calls cs : List (Call F)}
    {A : _root_.Address} {cA : Ixon.Constant} {refs : List Bytes.Address} {rb : Bytes.Address}
    {x_rc x_r x_irefs x_iused r : SourceValue F} {h₁ h₁' h₂ : Heap F}
    (hS : LoadedReads.RunStore calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored calls K.E₀)
    (hA : recordOf K.E₀ A = some cA)
    (hlen : refs.length < 72057594037927936)
    (hmap : refs.map Core.ixAddr = cA.refs.toList)
    (hrc : Claim.RCLimRep K.t K.bAddr K.lim h₂ x_rc)
    (ext_end : Heap.Extends h₁' h₂)
    (hr : Bytes.RepAddressRef Core.addrTy h₁ rb x_r)
    (hrefs : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h₁ refs x_irefs)
    (hused : RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h₁ (S0.usedRefIdxs cA)
      x_iused)
    (ev : ObsFn Obs.W "KernelModeled::projection_of_ref_block" [x_rc, x_r, x_irefs, x_iused] h₁
      r h₁' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h₁ h₁' ∧ (r = .field 1 → K.ProjOfRef A (Core.ixAddr rb)) := by
  have handleProj : ∀ {m2 m_ci m_pb : Heap F} {cs12 cs_ci cs_pb cs_rpf : List (Call F)}
      {x_c v_ci v_pb : SourceValue F},
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) → (∀ cl ∈ cs_rpf, cl ∈ calls) →
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h₁ x_c m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [x_c] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "KernelModeled::ref_projects_from"
        [x_rc, x_r, x_irefs, x_iused, .field 0, v_pb] m_pb r h₁' cs_rpf →
      Heap.Extends h₁ h₁' ∧ (r = .field 1 → K.ProjOfRef A (Core.ixAddr rb)) := by
    intro m2 m_ci m_pb cs12 cs_ci cs_pb cs_rpf x_c v_ci v_pb hsub12 hsub_ci hsub_rpf
      ev14 ev_ci ev_pb ev_rpf
    obtain ⟨ext1, rawBytes, cr, hlen_r, hh, haddr, -, hexact, hrep_cr, -⟩ :=
      Claim.load_verified_constant_de ⟨rb, hr, rfl⟩ ev14
    have hrec_cr : recordOf K.E₀ (Core.ixAddr rb) = some cr :=
      Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub12 hh) hlen_r (by rw [haddr]; exact hexact)
    have ext_ci := ev_ci.heap_extends
    obtain ⟨hpb_h, hproj, b_own, hown_rep, hown_eq⟩ :=
      projection_block_spec (Core.ixAddr rb) (hrep_cr.mono ext_ci) ev_pb
    subst hpb_h
    have ext12 := ext1.trans ext_ci
    obtain ⟨ext_rpf, hrpf⟩ := ref_projects_from_aux hS hcov hA (i := 0)
      (by simpa using hlen)
      (fun k q hq => by
        rw [Nat.zero_add, ← Array.getElem?_toList, ← hmap, List.getElem?_map, hq]
        rfl)
      hrc ext_end
      (Bytes.repAddressRef_heapMono₂ Core.addrTy ext12 hr) hown_rep
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext12 hrefs)
      (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext12 hused)
      ev_rpf hsub_rpf
    refine ⟨ext12.trans ext_rpf, fun h1 => ?_⟩
    obtain ⟨q, cq, huq, hcq, hpq, hown_q, himp⟩ := hrpf h1
    obtain ⟨cD, hcD, hca⟩ :=
      Claim.proj_member_of_load hS hcov (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hr)
        ev_ci hsub_ci hrec_cr hproj
    rw [← hown_eq, ← hown_q] at hcD hca
    exact ⟨q, cq, cD, huq, hcq, hpq, hcD, hca, himp⟩
  match Obs.«KernelModeled::projection_of_ref_block».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := cs_ci) (cs93 := cs_rpf) (ev14 := ev14)
      (ev_pvplyepc := ev_ci) (ev_bdycolxp := ev_pb) (ev95 := ev_rpf) (hc140 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_rpf
  | .CPrj (cs12 := cs12) (cs_tafpebbo := cs_ci) (cs157 := cs_rpf) (ev14 := ev14)
      (ev_rnaxgwez := ev_ci) (ev_mecagwun := ev_pb) (ev159 := ev_rpf) (hc204 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_rpf
  | .other (ev14 := ev14) (he209 := hr0) (he210 := hh) .. =>
    exact ⟨hh ▸ ev14.heap_extends, fun h1 => absurd (Value.field.inj (hr0.symm.trans h1)) zero_ne_one⟩

/-! ## Dependency paths and witness verification -/

private theorem read_byte_stream {x_s x_b x_rest : SourceValue F} {bs : List UInt8}
    {h h' : Heap F} {cs : List (Call F)} (hs : L1.Stream h bs x_s)
    (ev : ObsFn Obs.W "IxonDeserialize::read_byte" [x_s] h (.tuple [x_b, x_rest]) h' cs) :
    h' = h ∧ ∃ (b : UInt8) (bs' : List UInt8), bs = b :: bs' ∧
      x_b = .field (b.toNat : F) ∧ L1.Stream h bs' x_rest := by
  match Obs.«IxonDeserialize::read_byte».obs ev with
  | .run (ld11 := ld) (he30 := hr) (he45 := hh) .. =>
    injection hr with hpair
    injection hpair with hb hrest
    injection hrest with hrest'
    subst hb hrest' hh
    obtain ⟨b, bs', rfl, hb_rep, hs'⟩ := Lib.rep_cons_of_load hs ld
    exact ⟨rfl, b, bs', rfl, hb_rep, hs'⟩

private theorem field_or_bool_spec {a b c x y : SourceValue F}
    (ha : a = .field 0 ∨ a = .field 1) (hb : b = .field 0 ∨ b = .field 1)
    (op1 : evalBinOp .add a b = .ok x) (op2 : evalBinOp .mul a b = .ok y)
    (op3 : evalBinOp .sub x y = .ok c) :
    (c = .field 0 ∨ c = .field 1) ∧ (c = .field 0 → a = .field 0 ∧ b = .field 0) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp only [evalBinOp, add_zero, mul_zero, Except.ok.injEq] at op1 op2
    rw [← op1, ← op2] at op3
    simp only [evalBinOp, sub_zero, Except.ok.injEq] at op3
    exact ⟨Or.inl op3.symm, fun _ => ⟨rfl, rfl⟩⟩
  · simp only [evalBinOp, zero_add, zero_mul, Except.ok.injEq] at op1 op2
    rw [← op1, ← op2] at op3
    simp only [evalBinOp, sub_zero, Except.ok.injEq] at op3
    exact ⟨Or.inr op3.symm, fun h => absurd (Value.field.inj (op3.trans h)) one_ne_zero⟩
  · simp only [evalBinOp, add_zero, mul_zero, Except.ok.injEq] at op1 op2
    rw [← op1, ← op2] at op3
    simp only [evalBinOp, sub_zero, Except.ok.injEq] at op3
    exact ⟨Or.inr op3.symm, fun h => absurd (Value.field.inj (op3.trans h)) one_ne_zero⟩
  · simp only [evalBinOp, mul_one, Except.ok.injEq] at op1 op2
    rw [← op1, ← op2] at op3
    have h1 : ((1 : F) + 1) - 1 = (1 : F) := by ring
    simp only [evalBinOp, h1, Except.ok.injEq] at op3
    exact ⟨Or.inr op3.symm, fun h => absurd (Value.field.inj (op3.trans h)) one_ne_zero⟩

private theorem walk_path_spec_ext {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀) :
    ∀ (m : Nat) {cur : _root_.Address}
      {x_rc x_cur x_s x_n x_passed x_stop x_s_out x_passed_out : SourceValue F}
      {h h' h_end : Heap F} {cs : List (Call F)},
      cs.length ≤ m →
      Claim.RCLimRep K.t K.bAddr K.lim h_end x_rc →
      Heap.Extends h' h_end →
      S0.addr h x_cur cur →
      (x_passed = .field 0 ∨ x_passed = .field 1) →
      ObsFn Obs.W "KernelModeled::walk_path" [x_rc, x_cur, x_s, x_n, x_passed] h
        (.tuple [x_stop, x_s_out, x_passed_out]) h' cs →
      (∀ cl ∈ cs, cl ∈ K.calls) →
      Heap.Extends h h' ∧
        (∀ bs_in, L1.Stream h bs_in x_s → ∃ bs_out, L1.Stream h' bs_out x_s_out) ∧
        (x_passed_out = .field 0 ∨ x_passed_out = .field 1) ∧
        ∃ stop : _root_.Address, S0.addr h' x_stop stop ∧
          (x_passed_out = .field 0 →
            x_passed = .field 0 ∧ ¬ Covered K.t cur ∧ ¬ Covered K.t stop ∧
              ((x_n = .field 0 ∧ stop = cur) ∨ (x_n ≠ .field 0 ∧ K.DepPath cur stop)))
  | 0, cur, x_rc, x_cur, x_s, x_n, x_passed, x_stop, x_s_out, x_passed_out,
      h, h', h_end, cs, hlen, hrc, ext_end, hcur, hpb, ev, hsub => by
    match Obs.«KernelModeled::walk_path».obs ev with
    | .other (hc323 := hc) .. => simp [hc] at hlen
    | .n0 (hv14 := hn0) (ev_qmmrohoe := ev_cov) (he19 := hr)
        (op_qwpqvqwm := op1) (op_gpazpyfn := op2) (op_bdpndqnl := op3) (he34 := hh) .. =>
      injection hr with hpair
      simp only [List.cons.injEq, and_true] at hpair
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      subst hh
      obtain ⟨hm, hbin_c, hiff_c⟩ := addr_covered_spec_ext hrc ext_end hcur ev_cov
      subst hm
      obtain ⟨hbin_out, hzero⟩ := field_or_bool_spec hpb hbin_c op1 op2 op3
      refine ⟨Heap.Extends.refl _, fun bs_in hst => ⟨bs_in, hst⟩, hbin_out, cur, hcur, fun h0 => ?_⟩
      obtain ⟨hp0, hc0⟩ := hzero h0
      have hnc : ¬ Covered K.t cur := fun hc =>
        absurd (Value.field.inj (hc0.symm.trans (hiff_c.mpr hc))) zero_ne_one
      exact ⟨hp0, hnc, hnc, Or.inl ⟨hn0, rfl⟩⟩
  | m + 1, cur, x_rc, x_cur, x_s, x_n, x_passed, x_stop, x_s_out, x_passed_out,
      h, h', h_end, cs, hlen, hrc, ext_end, hcur, hpb, ev, hsub => by
    match Obs.«KernelModeled::walk_path».obs ev with
    | .n0 (hv14 := hn0) (ev_qmmrohoe := ev_cov) (he19 := hr)
        (op_qwpqvqwm := op1) (op_gpazpyfn := op2) (op_bdpndqnl := op3) (he34 := hh) .. =>
      injection hr with hpair
      simp only [List.cons.injEq, and_true] at hpair
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      subst hh
      obtain ⟨hm, hbin_c, hiff_c⟩ := addr_covered_spec_ext hrc ext_end hcur ev_cov
      subst hm
      obtain ⟨hbin_out, hzero⟩ := field_or_bool_spec hpb hbin_c op1 op2 op3
      refine ⟨Heap.Extends.refl _, fun bs_in hst => ⟨bs_in, hst⟩, hbin_out, cur, hcur, fun h0 => ?_⟩
      obtain ⟨hp0, hc0⟩ := hzero h0
      have hnc : ¬ Covered K.t cur := fun hc =>
        absurd (Value.field.inj (hc0.symm.trans (hiff_c.mpr hc))) zero_ne_one
      exact ⟨hp0, hnc, hnc, Or.inl ⟨hn0, rfl⟩⟩
    | .other (cs86 := cs86) (cs288 := cs288) (hne36 := hne0) (ev53 := ev53) (ev88 := ev88)
        (sg284 := sg) (ev_kkbmepwt := ev_cov) (op_uybassap := op1) (op_riujyiic := op2)
        (op_xgjbnmqg := op3) (ev290 := ev290) (hc323 := hc) .. =>
      have hlen' : cs288.length ≤ m := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have ext1 := ev53.heap_extends
      obtain ⟨ext2, rawBytes, c_cur, hlen_cur, hh_cur, haddr_cur, -, hexact_cur, hrep_cur, -⟩ :=
        Claim.load_verified_constant_de (S0.addr_mono ext1 hcur) ev88
      have hsub86 : ∀ cl ∈ cs86, cl ∈ K.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
      have hrec_cur : recordOf K.E₀ cur = some c_cur :=
        Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub86 hh_cur) hlen_cur
          (by rw [haddr_cur]; exact hexact_cur)
      have hstep : Heap.Extends _ _ ∧ ∃ next : _root_.Address, S0.addr _ _ next ∧
          (UsedRef K.E₀ cur next ∨
            ∃ c, recordOf K.E₀ cur = some c ∧ IsProj c ∧ next = Ix.Cert.ownerOf cur c) := by
        match sg with
        | .n0 (ev116 := ev_pb) .. =>
          obtain ⟨hpb_h, hproj, b_own, hown_rep, hown_eq⟩ :=
            projection_block_spec cur hrep_cur ev_pb
          subst hpb_h
          exact ⟨Heap.Extends.refl _, Ix.Cert.ownerOf cur c_cur, ⟨b_own, hown_rep, hown_eq⟩,
            Or.inr ⟨c_cur, hrec_cur, hproj, rfl⟩⟩
        | .other (hv144 := hmk) (ev213 := ev_idxs) (op235 := op_s1) (ev199 := ev_has)
            (heq243 := hhas1) (op272 := op_s2) (ev249 := ev_lk) .. =>
          obtain ⟨ext_i, hidxs⟩ := Claim.const_idxs_of_spec hrep_cur ev_idxs
          have hsub_eq : _ = _ := Except.ok.inj (op_s1.symm.trans op_s2)
          rw [← hsub_eq] at ev_lk
          have hrf_list := repConstant_refs_eq_local (hmk ▸ hrep_cur)
          obtain ⟨refBs, hrefMap, hrefCore⟩ := repIxonAddrList_to_core hrf_list
          -- Extract field index `idxVal` from `ev_has` and `ev_lk`
          have hex_idx : ∃ k : Nat, _ = Value.field (k : F) ∧
              k ∈ S0.usedRefIdxs c_cur ∧ k < 72057594037927936 := by
            -- `op_s1` gives `v201 = .field f`
            cases hv201 : _ with
            | field f =>
              have hlt_f : f.val < 72057594037927936 := by
                -- From `ev_lk : Lists::lookup`, `f.val < refBs.length = c_cur.refs.size < 2^56`
                have ev_lk' : ObsFn Obs.W (Instance.mk "Lists::lookup" [.ptr (.array .field 32)]).symbol
                    [_, .field f] _ _ _ _ := by
                  rw [Obs.Names.«Lists::lookup<&[Field; 32]>».symbol]
                  simpa [hv201] using ev_lk
                have hhref := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
                  (ext_i.trans ev_has.heap_extends) hrefCore
                obtain ⟨⟨_, hget, -⟩, -⟩ := Lib.lookup_spec ev_lk' hhref
                have hlt_len := (List.getElem?_eq_some_iff.mp hget).1
                have hlen_eq : refBs.length = c_cur.refs.size := by
                  have := congrArg List.length hrefMap
                  simp only [List.length_map, Array.length_toList] at this
                  exact this
                have hsz_lt := refs_size_lt_local hlen_cur hexact_cur
                omega
              have ev_has' : ObsFn Obs.W "KernelClaim::g_list_has"
                  [_, .field ((f.val : Nat) : F)] _ (.field 1) _ _ := by
                simpa [hv201, ZMod.natCast_zmod_val f] using ev_has
              obtain ⟨-, hiff⟩ := Claim.g_list_has_spec (S0.usedRefIdxs c_cur) hlt_f hidxs ev_has'
              exact ⟨f.val, by rw [ZMod.natCast_zmod_val f], hiff.mp rfl, hlt_f⟩
            | tuple _ | construct _ _ _ | ptr _ _ =>
              simp [evalBinOp] at op_s1
              cases _ <;> simp [evalBinOp] at op_s1
          obtain ⟨k, hk_eq, hk_mem, hk_lt⟩ := hex_idx
          have ev_has' : ObsFn Obs.W "KernelClaim::g_list_has"
              [_, .field (k : F)] _ (.field 1) _ _ := by
            rwa [← hk_eq]
          obtain ⟨hm189, -⟩ := Claim.g_list_has_spec (S0.usedRefIdxs c_cur) hk_lt hidxs ev_has'
          subst hm189
          have ev_lk' : ObsFn Obs.W (Instance.mk "Lists::lookup" [.ptr (.array .field 32)]).symbol
              [_, .field (k : F)] _ _ _ _ := by
            rw [Obs.Names.«Lists::lookup<&[Field; 32]>».symbol]
            rwa [← hk_eq]
          obtain ⟨⟨b_next, hget_b, hb_rep⟩, hm_lk⟩ :=
            Lib.lookup_spec ev_lk'
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_i hrefCore)
          subst hm_lk
          have hval_k : ((k : F)).val = k := val_cast_lt_u56 hk_lt
          rw [hval_k] at hget_b
          have hget_c : c_cur.refs[k]? = some (Core.ixAddr b_next) := by
            rw [← Array.getElem?_toList, ← hrefMap, List.getElem?_map, hget_b]; rfl
          exact ⟨ext_i, Core.ixAddr b_next, ⟨b_next, hb_rep, rfl⟩,
            Or.inl ⟨c_cur, k, hrec_cur, by rw [← Assembly.usedRefIdxs_eq]; exact hk_mem, hget_c⟩⟩
      obtain ⟨ext_sg, next, hnext, hstep_rel⟩ := hstep
      have ext_pre := (ext1.trans ext2).trans ext_sg
      obtain ⟨hm_cov, hbin_c, hiff_c⟩ :=
        addr_covered_spec_ext hrc (ev290.heap_extends.trans ext_end)
          (S0.addr_mono ext_pre hcur) ev_cov
      subst hm_cov
      obtain ⟨hbin_p', hzero_p'⟩ := field_or_bool_spec hpb hbin_c op1 op2 op3
      obtain ⟨ext_rec, hs_out, hbin_out, stop, hstop, hrec⟩ :=
        walk_path_spec_ext hS hcov m hlen' hrc ext_end hnext hbin_p' ev290
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      refine ⟨ext_pre.trans ext_rec, fun bs_in hst => ?_, hbin_out, stop, hstop, fun h0 => ?_⟩
      · obtain ⟨bs2, hs2⟩ := get_count_stream hst ev53
        exact hs_out bs2 (L1.Stream.mono (ext2.trans ext_sg) hs2)
      · obtain ⟨hp'_0, hnc_next, hnc_stop, htail⟩ := hrec h0
        obtain ⟨hp0, hc0⟩ := hzero_p' hp'_0
        have hnc_cur : ¬ Covered K.t cur := fun hcc =>
          absurd (Value.field.inj (hc0.symm.trans (hiff_c.mpr hcc))) zero_ne_one
        have hdstep : K.DepStep next cur := ⟨hnc_cur, hnc_next, hstep_rel⟩
        refine ⟨hp0, hnc_cur, hnc_stop, Or.inr ⟨hne0, ?_⟩⟩
        rcases htail with ⟨-, rfl⟩ | ⟨-, hdep⟩
        · exact Relation.TransGen.single hdstep
        · exact Relation.TransGen.tail hdep hdstep

private theorem walk_from_block_spec_ext {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀)
    {B : _root_.Address}
    {x_rc x_blk x_s x_n x_stop x_s_out x_passed_out : SourceValue F}
    {h h' h_end : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep K.t K.bAddr K.lim h_end x_rc)
    (ext_end : Heap.Extends h' h_end)
    (hblk : S0.addr h x_blk B)
    (ev : ObsFn Obs.W "KernelModeled::walk_from_block" [x_rc, x_blk, x_s, x_n] h
      (.tuple [x_stop, x_s_out, x_passed_out]) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ K.calls) :
    Heap.Extends h h' ∧
      (∀ bs_in, L1.Stream h bs_in x_s → ∃ bs_out, L1.Stream h' bs_out x_s_out) ∧
      ∃ stop : _root_.Address, S0.addr h' x_stop stop ∧
        (x_passed_out = .field 0 → K.DepPath B stop) := by
  match Obs.«KernelModeled::walk_from_block».obs ev with
  | .run (cs44 := cs44) (ev25 := ev_iz) (heq40 := hiz0) (ev46 := ev_wp) (hc71 := hc) .. =>
    obtain ⟨hiz_eq, hm15⟩ := Lib.is_zero_spec ev_iz
    subst hm15
    have hne : x_n ≠ .field 0 := by
      intro h0
      rw [h0] at hiz_eq
      simp at hiz_eq
      exact absurd (Value.field.inj (hiz0.symm.trans hiz_eq)) zero_ne_one
    obtain ⟨ext_wp, hs_out, -, stop, hstop, hwp⟩ :=
      walk_path_spec_ext hS hcov cs44.length (Nat.le_refl _) hrc ext_end hblk (Or.inl rfl)
        ev_wp (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    refine ⟨ext_wp, hs_out, stop, hstop, fun h0 => ?_⟩
    rcases (hwp h0).2.2.2 with ⟨hn0, -⟩ | ⟨-, hdep⟩
    · exact absurd hn0 hne
    · exact hdep

private theorem check_witness_spec_ext {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀)
    {B x : _root_.Address} {bs_in : List UInt8}
    {x_rc x_blk x_x x_kind x_s r : SourceValue F}
    {h h' h_end : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep K.t K.bAddr K.lim h_end x_rc)
    (ext_end : Heap.Extends h' h_end)
    (hblk : S0.addr h x_blk B)
    (hx : S0.addr h x_x x)
    (hst : L1.Stream h bs_in x_s)
    (ev : ObsFn Obs.W "KernelModeled::check_witness" [x_rc, x_blk, x_x, x_kind, x_s] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ K.calls) :
    Heap.Extends h h' ∧
      (∃ bs_out, L1.Stream h' bs_out r) ∧
      (K.WitBase B x ∨
        (x_kind = .field 2 ∧
          ∃ cx, recordOf K.E₀ x = some cx ∧ ((∃ rcr, cx.info = .recr rcr) ∨ ∃ p, cx.info = .rPrj p))) := by
  match Obs.«KernelModeled::check_witness».obs ev with
  | .n0 (v15 := v15) (ev28 := ev_ro) (ev69 := ev_iz) (heq84 := hiz0) (op124 := op)
      (ev109 := ev_bra) (heq132 := hbra1) (ev146 := ev_rct) (he164 := hr) (he165 := hh) .. =>
    subst hh hr
    have ext_ro := ev_ro.heap_extends
    obtain ⟨hiz_eq, hm59⟩ := Lib.is_zero_spec ev_iz
    subst hm59
    have hne0 : v15 ≠ Value.field 0 := by
      intro h0
      rw [h0] at hiz_eq
      simp at hiz_eq
      exact absurd (Value.field.inj (hiz0.symm.trans hiz_eq)) zero_ne_one
    have ext_pre : Heap.Extends h h_end :=
      (ev_ro.heap_extends.trans (ev_bra.heap_extends.trans ev_rct.heap_extends)).trans ext_end
    obtain ⟨ro, hro_eq, hof⟩ := role_of_ne_zero_lim_ext hrc ext_pre hx ev_ro hne0
    rw [hro_eq] at op
    simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
    subst op
    rw [hbra1] at ev_bra
    obtain ⟨hm99, hro_mem⟩ := basis_role_allowed_spec ev_bra
    subst hm99
    have ext_all := ext_ro.trans ev_rct.heap_extends
    exact ⟨ext_all, ⟨bs_in, L1.Stream.mono ext_all hst⟩, Or.inl (Or.inl ⟨ro, hro_mem, hof⟩)⟩
  | .n1 (cs_jruoheya := cs_wfb) (ev185 := ev_gc) (ev_lbttumfo := ev_wfb)
      (ev282 := ev_eq) (heq305 := heq1) (ev_kzxwtasl := ev_pm) (ev_scicdnpr := ev_nb)
      (ev_krpcbbcl := ev_ci) (ev_mvspkqrl := ev_acp) (he307 := hr) (he308 := hh)
      (hc309 := hc) .. =>
    subst hh hr
    obtain ⟨bs2, hs2⟩ := get_count_stream hst ev_gc
    have ext_after_wfb : Heap.Extends _ h_end :=
      (ev_eq.heap_extends.trans (ev_pm.heap_extends.trans (ev_nb.heap_extends.trans
        (ev_ci.heap_extends.trans ev_acp.heap_extends)))).trans ext_end
    obtain ⟨ext_wfb, hs_out, stop, hstop, hdep⟩ :=
      walk_from_block_spec_ext hS hcov hrc ext_after_wfb (S0.addr_mono ev_gc.heap_extends hblk)
        ev_wfb (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨bs3, hs3⟩ := hs_out bs2 hs2
    obtain ⟨b_stop, hb_stop, rfl⟩ := hstop
    obtain ⟨b_x, hb_x, rfl⟩ := S0.addr_mono (ev_gc.heap_extends.trans ext_wfb) hx
    obtain ⟨heq_r, hm272⟩ := Lib.address_eq_spec ev_eq hb_stop hb_x
    subst hm272
    have hbs : b_stop = b_x := by
      by_cases h : b_stop = b_x
      · exact h
      · rw [ite_eq_right h] at heq_r
        exact absurd (Value.field.inj (heq1.symm.trans heq_r)) one_ne_zero
    subst hbs
    have ext_mid := ev_pm.heap_extends.trans (ev_nb.heap_extends.trans ev_ci.heap_extends)
    obtain ⟨hm_acp, hpass_or_cov⟩ :=
      assert_covered_past_spec_ext hrc ext_end
        ⟨b_stop, Bytes.repAddressRef_heapMono₂ Core.addrTy ext_mid hb_x, rfl⟩ ev_acp
    subst hm_acp
    have ext_all := ev_gc.heap_extends.trans (ext_wfb.trans ext_mid)
    refine ⟨ext_all, ⟨bs3, L1.Stream.mono ext_mid hs3⟩, Or.inl ?_⟩
    rcases hpass_or_cov with h0 | hcov_x
    · exact Or.inr (Or.inr (Or.inl (hdep h0)))
    · exact Or.inr (Or.inl hcov_x)
  | .n2 (hv314 := hk2) (ev328 := ev_gc) (ev_dpuowbtw := ev_wfb) (ev414 := ev_ccr)
      (ev_yqkzbtyw := ev_acp) (he440 := hr) (he441 := hh) (hc442 := hc) .. =>
    subst hh hr
    obtain ⟨bs2, hs2⟩ := get_count_stream hst ev_gc
    have ext_after_wfb : Heap.Extends _ h_end :=
      (ev_ccr.heap_extends.trans ev_acp.heap_extends).trans ext_end
    obtain ⟨ext_wfb, hs_out, -, -, -⟩ :=
      walk_from_block_spec_ext hS hcov hrc ext_after_wfb (S0.addr_mono ev_gc.heap_extends hblk)
        ev_wfb (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨bs3, hs3⟩ := hs_out bs2 hs2
    have hrec_kind : ∃ cx, recordOf K.E₀ x = some cx ∧
        ((∃ rcr, cx.info = .recr rcr) ∨ ∃ p, cx.info = .rPrj p) := by
      match Obs.«KernelModeled::check_container_rec».obs ev_ccr with
      | .run (cs_ymrayeri := cs_ci) (ev39 := ev39) (ev25 := ev25) (ev_nqhglzzq := ev_ci)
          (ld_hhcwtoqm := hld) (hc96 := hccr) .. =>
        have ext_ci := ev_gc.heap_extends.trans (ext_wfb.trans (ev39.heap_extends.trans ev25.heap_extends))
        obtain ⟨ab, hab, rfl⟩ := S0.addr_mono ext_ci hx
        have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ K.calls := fun cl hcl =>
          hsub cl (by rw [hc]; simp [hccr, hcl])
        obtain ⟨rawBytes, cx, hlen_x, hh_x, haddr_x, hexact_x, -, -⟩ := Claim.get_ci_head hab ev_ci
        have hcx : recordOf K.E₀ (Core.ixAddr ab) = some cx :=
          Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub_ci hh_x) hlen_x
            (by rw [haddr_x]; exact hexact_x)
        exact ⟨cx, hcx, get_ci_loads_rec_is_recr_or_rPrj hS hab ev_ci hsub_ci hld hcx⟩
    have ext_all := ev_gc.heap_extends.trans (ext_wfb.trans (ev_ccr.heap_extends.trans ev_acp.heap_extends))
    exact ⟨ext_all, ⟨bs3, L1.Stream.mono (ev_ccr.heap_extends.trans ev_acp.heap_extends) hs3⟩,
      Or.inr ⟨hk2, hrec_kind⟩⟩
  | .n3 (cs_frlxnmjz := cs_wfb) (cs687 := cs_sg) (cs_gufnlnhk := cs_ci)
      (ev461 := ev_gc1) (ev_ndaajwbz := ev_wfb) (ev547 := ev_gc2) (ev582 := ev_gc3)
      (sg692 := sg) (ev717 := ev_eq) (heq740 := heq1) (ev_gwtfngxo := ev_ci)
      (ev_xxjagmga := ev_acp) (he742 := hr) (he743 := hh) (hc744 := hc) .. =>
    subst hh hr
    obtain ⟨bs2, hs2⟩ := get_count_stream hst ev_gc1
    have ext_sg : Heap.Extends _ _ := by
      match sg with
      | .n0 (ev623 := e) .. => exact e.heap_extends
      | .other (ev650 := e) .. => exact e.heap_extends
    have ext_after_wfb : Heap.Extends _ h_end :=
      (ev_gc2.heap_extends.trans (ev_gc3.heap_extends.trans (ext_sg.trans
        (ev_eq.heap_extends.trans (ev_ci.heap_extends.trans ev_acp.heap_extends))))).trans
        ext_end
    obtain ⟨ext_wfb, hs_out, ib, hib, hdep⟩ :=
      walk_from_block_spec_ext hS hcov hrc ext_after_wfb (S0.addr_mono ev_gc1.heap_extends hblk)
        ev_wfb (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨bs3, hs3⟩ := hs_out bs2 hs2
    obtain ⟨bs4, hs4⟩ := get_count_stream hs3 ev_gc2
    obtain ⟨bs5, hs5⟩ := get_count_stream hs4 ev_gc3
    obtain ⟨b_ib, hb_ib, rfl⟩ := S0.addr_mono (ev_gc2.heap_extends.trans ev_gc3.heap_extends) hib
    have hproj_step : ∃ (info : Ixon.ConstantInfo) (a_p : Bytes.Address),
        ((∃ n, info = .iPrj ⟨n, Core.ixAddr b_ib⟩) ∨
          (∃ ni nc, info = .cPrj ⟨ni, nc, Core.ixAddr b_ib⟩)) ∧
        Bytes.RepAddressRef Core.addrTy _ a_p _ ∧
        Core.ixAddr a_p = Core.projAddr info ∧
        Hashed K.calls (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) := by
      match sg with
      | .n0 (cs621 := cs621) (ev623 := ev_ip) (hc640 := hcs) .. =>
        obtain ⟨-, n, a_p, -, ha_rep, ha_eq, hhash⟩ := compute_iprj_addr_hashed hb_ib ev_ip
        exact ⟨.iPrj ⟨n.toUInt64, Core.ixAddr b_ib⟩, a_p, Or.inl ⟨n.toUInt64, rfl⟩,
          ha_rep, ha_eq, Core.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl])) hhash⟩
      | .other (cs648 := cs648) (ev650 := ev_cp) (hc683 := hcs) .. =>
        obtain ⟨-, ni, nc, a_p, -, -, ha_rep, ha_eq, hhash⟩ := projection_addr_ctor_hashed hb_ib ev_cp
        exact ⟨.cPrj ⟨ni.toUInt64, nc.toUInt64, Core.ixAddr b_ib⟩, a_p,
          Or.inr ⟨ni.toUInt64, nc.toUInt64, rfl⟩,
          ha_rep, ha_eq, Core.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl])) hhash⟩
    obtain ⟨info, a_p, hinfo_kind, hap_rep, hap_eq, hhash_p⟩ := hproj_step
    have ext_to_eq := ev_gc1.heap_extends.trans (ext_wfb.trans
      (ev_gc2.heap_extends.trans (ev_gc3.heap_extends.trans ext_sg)))
    obtain ⟨b_x, hb_x, rfl⟩ := S0.addr_mono ext_to_eq hx
    obtain ⟨heq_r, hm707⟩ := Lib.address_eq_spec ev_eq hap_rep hb_x
    subst hm707
    have hap_eq_bx : a_p = b_x := by
      by_cases h : a_p = b_x
      · exact h
      · rw [ite_eq_right h] at heq_r
        exact absurd (Value.field.inj (heq1.symm.trans heq_r)) one_ne_zero
    subst hap_eq_bx
    have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ K.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨rawBytes, cx, hlen_x, hh_x, haddr_x, hexact_x, -, -⟩ := Claim.get_ci_head hb_x ev_ci
    have hrec_cx : recordOf K.E₀ (Core.ixAddr a_p) = some cx :=
      Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub_ci hh_x) hlen_x
        (by rw [haddr_x]; exact hexact_x)
    have hraw_eq : rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ :=
      hS.hashed_inj (Claim.hashed_mono hsub_ci hh_x) hhash_p (haddr_x.trans hap_eq)
    have hcx_eq : cx = ⟨info, #[], #[], #[], #[]⟩ := by
      have hde_p : Ixon.deConstantExact (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩) =
          .ok ⟨info, #[], #[], #[], #[]⟩ := by
        rcases hinfo_kind with ⟨n, rfl⟩ | ⟨ni, nc, rfl⟩
        · exact Ixon.Verify.deConstantExact_serConstant _ (L1.projConstant_wireWF_iPrj n b_ib)
        · exact Ixon.Verify.deConstantExact_serConstant _ (L1.projConstant_wireWF_cPrj ni nc b_ib)
      rw [hraw_eq] at hexact_x
      exact Except.ok.inj (hexact_x.symm.trans hde_p)
    have hpr_cx : IsProj cx := by
      rw [hcx_eq]
      rcases hinfo_kind with ⟨n, rfl⟩ | ⟨ni, nc, rfl⟩
      · exact Or.inr (Or.inl ⟨⟨n, Core.ixAddr b_ib⟩, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨ni, nc, Core.ixAddr b_ib⟩, rfl⟩))
    have hown_cx : Ix.Cert.ownerOf (Core.ixAddr a_p) cx = Core.ixAddr b_ib := by
      rw [hcx_eq]
      rcases hinfo_kind with ⟨n, rfl⟩ | ⟨ni, nc, rfl⟩ <;> rfl
    obtain ⟨cib, hcib, hca⟩ := Claim.proj_member_of_load hS hcov hb_x ev_ci hsub_ci hrec_cx hpr_cx
    rw [hown_cx] at hcib hca
    obtain ⟨hm_acp, hpass_or_cov⟩ :=
      assert_covered_past_spec_ext hrc ext_end
        ⟨a_p, Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ci.heap_extends hb_x, rfl⟩ ev_acp
    subst hm_acp
    have ext_all := ext_to_eq.trans ev_ci.heap_extends
    refine ⟨ext_all, ⟨bs5, L1.Stream.mono (ext_sg.trans ev_ci.heap_extends) hs5⟩, Or.inl ?_⟩
    rcases hpass_or_cov with h0 | hcov_x
    · exact Or.inr (Or.inr (Or.inr ⟨Core.ixAddr b_ib, cib, hdep h0, hcib, hca⟩))
    · exact Or.inr (Or.inl hcov_x)

/-- **`KernelModeled::check_witnesses` produces a represented list of witness addresses**, each of
which is either a base witness (`WitBase B y`) or a kind-2 container witness whose record is
`.recr` or `.rPrj` (with its `check_witness` call recorded in `cs`). -/
private theorem check_witnesses_spec_ext {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀) :
    ∀ (m : Nat) {B : _root_.Address} {bs_in : List UInt8}
      {x_rc x_blk x_s x_n x_out x_s_out : SourceValue F} {h h' h_end : Heap F}
      {cs : List (Call F)},
      cs.length ≤ m →
      Claim.RCLimRep K.t K.bAddr K.lim h_end x_rc →
      Heap.Extends h' h_end →
      S0.addr h x_blk B →
      L1.Stream h bs_in x_s →
      ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_blk, x_s, x_n] h
        (.tuple [x_out, x_s_out]) h' cs →
      (∀ cl ∈ cs, cl ∈ K.calls) →
      Heap.Extends h h' ∧
        ∃ ws : List Bytes.Address,
          RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' ws x_out ∧
          ∀ w ∈ ws,
            K.WitBase B (Core.ixAddr w) ∨
              (∃ h_w xx_w s_w, Heap.Extends h h_w ∧ S0.addr h_w x_blk B ∧
                S0.addr h_w xx_w (Core.ixAddr w) ∧
                (⟨"KernelModeled::check_witness", [x_rc, x_blk, xx_w, .field 2, s_w], h_w⟩ : Call F) ∈ cs ∧
                ∃ cx, recordOf K.E₀ (Core.ixAddr w) = some cx ∧
                  ((∃ rcr, cx.info = .recr rcr) ∨ ∃ p, cx.info = .rPrj p))
  | 0, B, bs_in, x_rc, x_blk, x_s, x_n, x_out, x_s_out, h, h', h_end, cs,
      hlen, hrc, ext_end, hblk, hst, ev, hsub => by
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .other (hc292 := hc) .. => simp [hc] at hlen
    | .n0 (he19 := hr) (hm29 := hm) (he40 := hh) .. =>
      injection hr with hpair
      simp only [List.cons.injEq, and_true] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      subst hh hm
      exact ⟨Heap.Extends.snoc h _, [], Lib.rep_store_nil h, fun _ hw => by cases hw⟩
  | m + 1, B, bs_in, x_rc, x_blk, x_s, x_n, x_out, x_s_out, h, h', h_end, cs,
      hlen, hrc, ext_end, hblk, hst, ev, hsub => by
    match Obs.«KernelModeled::check_witnesses».obs ev with
    | .n0 (he19 := hr) (hm29 := hm) (he40 := hh) .. =>
      injection hr with hpair
      simp only [List.cons.injEq, and_true] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      subst hh hm
      exact ⟨Heap.Extends.snoc h _, [], Lib.rep_store_nil h, fun _ hw => by cases hw⟩
    | .other (m184 := m184) (cs127 := cs127) (cs194 := cs194) (ev59 := ev_ga) (ev94 := ev_rb)
        (ev_updedcyj := ev_ord) (ev167 := ev_u8) (ev129 := ev_cw) (ev196 := ev_rest)
        (he254 := hr) (hm264 := hm) (he291 := hh) (hc292 := hc) .. =>
      have hlen' : cs194.length ≤ m := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      injection hr with hpair
      simp only [List.cons.injEq, and_true] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      subst hh
      obtain ⟨a_x, bs2, x_a', x_s2', -, hr_ga, ha_rep, hs2, ext_ga, -⟩ :=
        Decl.get_address_spec hst ev_ga
      injection hr_ga with hp_ga
      simp only [List.cons.injEq, and_true] at hp_ga
      obtain ⟨rfl, rfl⟩ := hp_ga
      obtain ⟨hm82, b_kind, bs3, -, -, hs3⟩ := read_byte_stream hs2 ev_rb
      subst hm82
      obtain ⟨-, hm157⟩ := Lib.u8_to_field_spec ev_u8
      subst hm157
      have ext_pre := ext_ga.trans ev_ord.heap_extends
      have ext_snoc : Heap.Extends m184 h' := by rw [hm]; exact Heap.Extends.snoc m184 _
      obtain ⟨ext_cw, ⟨bs4, hs4⟩, hcw_res⟩ :=
        check_witness_spec_ext hS hcov hrc
          ((ev_rest.heap_extends.trans ext_snoc).trans ext_end)
          (S0.addr_mono ext_pre hblk)
          ⟨a_x, Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends ha_rep, rfl⟩
          (L1.Stream.mono ev_ord.heap_extends hs3) ev_cw
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      obtain ⟨ext_rest, ws, hws_rep, hws_spec⟩ :=
        check_witnesses_spec_ext hS hcov m hlen' hrc (ext_snoc.trans ext_end)
          (S0.addr_mono (ext_pre.trans ext_cw) hblk) hs4 ev_rest
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      have ext_all := ext_pre.trans (ext_cw.trans (ext_rest.trans ext_snoc))
      have hcons_rep : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) _
          (a_x :: ws) _ := by
        rw [hm]
        exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy
            (ev_ord.heap_extends.trans (ext_cw.trans ext_rest)) ha_rep)
          hws_rep
      refine ⟨ext_all, a_x :: ws, hcons_rep, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw_rest
      · rcases hcw_res with hwb | ⟨hk2, cx, hcx, hkind⟩
        · exact Or.inl hwb
        · refine Or.inr ⟨_, _, _, ext_pre, S0.addr_mono ext_pre hblk,
            ⟨a_x, Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends ha_rep, rfl⟩,
            ?_, cx, hcx, hkind⟩
          rw [hc, ← hk2]
          simp
      · rcases hws_spec w hw_rest with hwb | ⟨h_w, xx_w, s_w, ext_w, hblk_w, hx_w, hcl_w, hcx⟩
        · exact Or.inl hwb
        · exact Or.inr ⟨h_w, xx_w, s_w, (ext_pre.trans ext_cw).trans ext_w, hblk_w, hx_w,
            by rw [hc]; simp [hcl_w], hcx⟩

/-! ## `BatchGives.familyRefs` -/

private theorem family_refs_go_spec {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀)
    {B : _root_.Address} {cB : Ixon.Constant} {irefs : List Bytes.Address}
    {Wset : List _root_.Address} {idxs : List Nat}
    (hB : recordOf K.E₀ B = some cB)
    (hilen : irefs.length < 72057594037927936)
    (himap : irefs.map Core.ixAddr = cB.refs.toList) :
    ∀ {refs : List Bytes.Address} {i : Nat}
      {x_rc x_refs x_used x_blk x_irefs x_iused x_wset r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      i + refs.length < 72057594037927936 →
      Claim.RCLimRep K.t K.bAddr K.lim h x_rc →
      S0.addr h x_blk B →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h refs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs x_used →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h irefs x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (S0.usedRefIdxs cB) x_iused →
      Claim.RepAddrSet h Wset x_wset →
      ObsFn Obs.W "KernelModeled::family_refs_go"
        [x_rc, x_refs, x_used, .field (i : F), x_blk, x_irefs, x_iused, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ K.calls) →
      Heap.Extends h h' ∧
        ∀ k q, refs[k]? = some q → (i + k) ∈ idxs →
          K.BlockRef B (Core.ixAddr q) ∨ Core.ixAddr q ∈ Wset
  | [], i, x_rc, x_refs, x_used, x_blk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hbound, hrc, hblk, hrefs, hused, hirefs, hiused, hwset, ev, hsub => by
    match Obs.«KernelModeled::family_refs_go».obs ev with
    | .Nil (he23 := hh) .. =>
      exact ⟨hh ▸ Heap.Extends.refl _, fun _ _ hq => by simp at hq⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases hbad
  | q :: rest, i, x_rc, x_refs, x_used, x_blk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hbound, hrc, hblk, hrefs, hused, hirefs, hiused, hwset, ev, hsub => by
    have hi : i < 72057594037927936 := by simp at hbound; omega
    match Obs.«KernelModeled::family_refs_go».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrefs ld
    | .Cons (x_r := x_q) (m385 := m385) (ld12 := ld) (sg392 := sg) (op_gskedpnl := op) (ev398 := ev_rest) (hc463 := hc) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨b_B, hb_B, hix_B⟩ := hblk
      have hseg : Heap.Extends h m385 ∧
          (i ∈ idxs → K.BlockRef B (Core.ixAddr q) ∨ Core.ixAddr q ∈ Wset) := by
        have hproj_same : ∀ {m86 m_ld m_ci m_pb m_eq : Heap F}
            {cs_ld cs_ci cs_pb cs_eq : List (Call F)} {x_c v_ci v_pb : SourceValue F},
            Heap.Extends h m86 →
            (∀ cl ∈ cs_ld, cl ∈ K.calls) → (∀ cl ∈ cs_ci, cl ∈ K.calls) →
            ObsFn Obs.W "Ingress::load_verified_constant" [x_q] m86 x_c m_ld cs_ld →
            ObsFn Obs.W "Ingress::get_ci" [x_q] m_ld v_ci m_ci cs_ci →
            ObsFn Obs.W "KernelModeled::projection_block" [x_c] m_ci v_pb m_pb cs_pb →
            ObsFn Obs.W "Bytes::address_eq" [v_pb, x_blk] m_pb (.field 1) m_eq cs_eq →
            Heap.Extends h m_eq ∧ K.BlockRef B (Core.ixAddr q) := by
          intro m86 m_ld m_ci m_pb m_eq cs_ld cs_ci cs_pb cs_eq x_c v_ci v_pb ext86 hsub_ld hsub_ci
            ev_ld ev_ci ev_pb ev_eq
          have hq86 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext86 hq
          obtain ⟨ext_ld, rawBytes, cr, hlen_r, hh_r, haddr_r, -, hexact_r, hrep_cr, -⟩ :=
            Claim.load_verified_constant_de ⟨q, hq86, rfl⟩ ev_ld
          have hrec_cr : recordOf K.E₀ (Core.ixAddr q) = some cr :=
            Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub_ld hh_r) hlen_r
              (by rw [haddr_r]; exact hexact_r)
          have ext_ci := ev_ci.heap_extends
          obtain ⟨hpb_h, hproj, b_own, hown_rep, hown_eq⟩ :=
            projection_block_spec (Core.ixAddr q) (hrep_cr.mono ext_ci) ev_pb
          subst hpb_h
          obtain ⟨heq_r, heq_h⟩ :=
            Lib.address_eq_spec ev_eq hown_rep
              (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext86.trans (ext_ld.trans ext_ci)) hb_B)
          have hown_B : b_own = b_B := by
            by_cases h' : b_own = b_B
            · exact h'
            · rw [ite_eq_right h'] at heq_r
              exact absurd (Value.field.inj heq_r) one_ne_zero
          subst hown_B
          obtain ⟨cb, hcb, hca⟩ :=
            Claim.proj_member_of_load hS hcov
              (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_ld hq86)
              ev_ci hsub_ci hrec_cr hproj
          rw [← hown_eq, hix_B] at hcb hca
          exact ⟨heq_h ▸ ext86.trans (ext_ld.trans ext_ci), Or.inr (Or.inl ⟨cb, hcb, hca⟩)⟩
        match sg with
        | .other (ev56 := ev56) (hne375 := hne1) (he382 := hh) .. =>
          obtain ⟨hm43, hhas⟩ := Claim.g_list_has_spec idxs hi hused ev56
          exact ⟨hh ▸ hm43 ▸ Heap.Extends.refl _, fun hmem => absurd (hhas.mpr hmem) hne1⟩
        | .n1_n1 (ev56 := ev56) (ev99 := ev99) (he165 := hh) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨hm86, hurh⟩ := used_ref_has_aux (i := 0) (by simpa using hilen) hirefs hiused hq ev99
          obtain ⟨k, -, hk_mem, hk_get⟩ := hurh rfl
          have hget_c : cB.refs[k]? = some (Core.ixAddr q) := by
            rw [← Array.getElem?_toList, ← himap, List.getElem?_map, hk_get]; rfl
          exact ⟨hh ▸ hm86 ▸ Heap.Extends.refl _,
            fun _ => Or.inl (Or.inl ⟨cB, k, hB, by rw [← Assembly.usedRefIdxs_eq]; exact hk_mem, hget_c⟩)⟩
        | .n1_other_IPrj_n1 (cs_zdnxjwry := cs_ld) (cs_qbnwdknq := cs_ci)
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_qgckrtca := ev_ci)
            (ev_vtyrtvpa := ev_pb) (ev_tnredfpp := ev_eq) (he_bzceqiro := hh)
            (hc_zgauihwq := hcs) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨hm86, -⟩ := used_ref_has_aux (i := 0) (by simpa using hilen) hirefs hiused hq ev99
          subst hm86
          obtain ⟨ext_s, hbr⟩ := hproj_same (Heap.Extends.refl _)
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
            ev_ld ev_ci ev_pb ev_eq
          exact ⟨hh ▸ ext_s, fun _ => Or.inl hbr⟩
        | .n1_other_CPrj_n1 (cs_zdnxjwry := cs_ld) (cs_lpudusuv := cs_ci)
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_adpdzihl := ev_ci)
            (ev_jzuzvoks := ev_pb) (ev_glaclyhi := ev_eq) (he_nmfyxnwl := hh)
            (hc_xipxbqsc := hcs) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨hm86, -⟩ := used_ref_has_aux (i := 0) (by simpa using hilen) hirefs hiused hq ev99
          subst hm86
          obtain ⟨ext_s, hbr⟩ := hproj_same (Heap.Extends.refl _)
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
            ev_ld ev_ci ev_pb ev_eq
          exact ⟨hh ▸ ext_s, fun _ => Or.inl hbr⟩
        | .n1_other_IPrj_other_n1 (cs_snsikqdv := cs_prb)
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_qgckrtca := ev_ci)
            (ev_vtyrtvpa := ev_pb) (ev_tnredfpp := ev_eq) (ev_yzpcnxhb := ev_prb)
            (he_zrgpsvav := hh) (hc_azxcvjxu := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans
            (ev_ld.heap_extends.trans (ev_ci.heap_extends.trans
              (ev_pb.heap_extends.trans ev_eq.heap_extends))))
          obtain ⟨ext_prb, hprb⟩ := projection_of_ref_block_spec (K := K) hS hcov hB hilen himap
            (hrc.mono (ext_pre.trans ev_prb.heap_extends)) (Heap.Extends.refl _)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_pre hirefs)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_pre hiused)
            ev_prb (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          exact ⟨hh ▸ ext_pre.trans ext_prb, fun _ => Or.inl (Or.inr (Or.inr (hprb rfl)))⟩
        | .n1_other_CPrj_other_n1 (cs_owbqhnqq := cs_prb)
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_adpdzihl := ev_ci)
            (ev_jzuzvoks := ev_pb) (ev_glaclyhi := ev_eq) (ev_ajdyfujx := ev_prb)
            (he_lgylpqds := hh) (hc_aythwrab := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans
            (ev_ld.heap_extends.trans (ev_ci.heap_extends.trans
              (ev_pb.heap_extends.trans ev_eq.heap_extends))))
          obtain ⟨ext_prb, hprb⟩ := projection_of_ref_block_spec (K := K) hS hcov hB hilen himap
            (hrc.mono (ext_pre.trans ev_prb.heap_extends)) (Heap.Extends.refl _)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_pre hirefs)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_pre hiused)
            ev_prb (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          exact ⟨hh ▸ ext_pre.trans ext_prb, fun _ => Or.inl (Or.inr (Or.inr (hprb rfl)))⟩
        | .n1_other_other_other_n1 (cs_wknojnhr := cs_prb)
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_jlgopmei := ev_prb)
            (he_tzsimcbf := hh) (hc_iowtuhxz := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans ev_ld.heap_extends)
          obtain ⟨ext_prb, hprb⟩ := projection_of_ref_block_spec (K := K) hS hcov hB hilen himap
            (hrc.mono (ext_pre.trans ev_prb.heap_extends)) (Heap.Extends.refl _)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_pre hirefs)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_pre hiused)
            ev_prb (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          exact ⟨hh ▸ ext_pre.trans ext_prb, fun _ => Or.inl (Or.inr (Or.inr (hprb rfl)))⟩
        | .n1_other_IPrj_other_other
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_qgckrtca := ev_ci)
            (ev_vtyrtvpa := ev_pb) (ev_tnredfpp := ev_eq) (ev_yzpcnxhb := ev_prb)
            (ev_vlqtvrdt := ev_mem) (heq_cgphyymq := h1) (he_qwbsdwlv := hh) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans
            (ev_ld.heap_extends.trans (ev_ci.heap_extends.trans
              (ev_pb.heap_extends.trans (ev_eq.heap_extends.trans ev_prb.heap_extends)))))
          obtain ⟨hmem_w, hm_mem⟩ :=
            Claim.addr_set_member_set_spec
              (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
              (hwset.mono ext_pre) ev_mem
          exact ⟨hh ▸ hm_mem ▸ ext_pre, fun _ => Or.inr (hmem_w h1)⟩
        | .n1_other_CPrj_other_other
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_adpdzihl := ev_ci)
            (ev_jzuzvoks := ev_pb) (ev_glaclyhi := ev_eq) (ev_ajdyfujx := ev_prb)
            (ev_evifbzkm := ev_mem) (heq_qygjpayn := h1) (he_vykzghpw := hh) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans
            (ev_ld.heap_extends.trans (ev_ci.heap_extends.trans
              (ev_pb.heap_extends.trans (ev_eq.heap_extends.trans ev_prb.heap_extends)))))
          obtain ⟨hmem_w, hm_mem⟩ :=
            Claim.addr_set_member_set_spec
              (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
              (hwset.mono ext_pre) ev_mem
          exact ⟨hh ▸ hm_mem ▸ ext_pre, fun _ => Or.inr (hmem_w h1)⟩
        | .n1_other_other_other_other
            (ev56 := ev56) (ev99 := ev99) (ev_xluoudzn := ev_ld) (ev_jlgopmei := ev_prb)
            (ev_aamioxen := ev_mem) (heq_siovpfty := h1) (he_mczqspon := hh) .. =>
          have ext_pre := ev56.heap_extends.trans (ev99.heap_extends.trans
            (ev_ld.heap_extends.trans ev_prb.heap_extends))
          obtain ⟨hmem_w, hm_mem⟩ :=
            Claim.addr_set_member_set_spec
              (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
              (hwset.mono ext_pre) ev_mem
          exact ⟨hh ▸ hm_mem ▸ ext_pre, fun _ => Or.inr (hmem_w h1)⟩
      obtain ⟨ext_seg, hq_ok⟩ := hseg
      have hv : _ = Value.field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]; push_cast; rfl
      rw [hv] at ev_rest
      obtain ⟨ext_rest, hrest_ok⟩ := family_refs_go_spec hS hcov hB hilen himap (i := i + 1)
        (by simp at hbound ⊢; omega)
        (hrc.mono ext_seg) (S0.addr_mono ext_seg ⟨b_B, hb_B, hix_B⟩)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hused)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hirefs)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hiused)
        (hwset.mono ext_seg) ev_rest (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      refine ⟨ext_seg.trans ext_rest, fun k q₀ hget hmem => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        exact hq_ok (by simpa using hmem)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hget
        exact hrest_ok k' q₀ hget (by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hmem)

/-- **Discharges `BatchGives.familyRefs`**: every used reference of a scope check's family record
is a reference of its block's closure (`BlockRef`), or a witness of the check (`WitBase` or
`ContWitness`). -/
theorem FamRunCtx.familyRefs_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B rb : _root_.Address} {cs : List (Call F)} (hS : K.ScopeAt B rb cs)
    {x : _root_.Address} (hu : UsedRef K.E₀ rb x) :
    K.BlockRef B x ∨ K.WitBase B x ∨ K.ContWitness cs B x := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev_fam, -, hsub_fam⟩ := hS.1
  match Obs.«KernelModeled::check_family».obs ev_fam with
  | .run (cs342 := cs_ws) (cs1303 := cs_fro)
      (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := ev_ord) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
      (ev344 := ev_ws) (ev403 := ev_asb) (ev435 := ev435) (ev465 := ev465)
      (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817)
      (ev796 := ev796) (ev852 := ev852) (ev_ursqbimm := ev_anr) (ev874 := ev874)
      (ev896 := ev896) (ev960 := ev960) (ev939 := ev939) (ev1011 := ev1011)
      (ev990 := ev990) (ev_edyzsqzv := ev_mv1) (ev_gkddqxhv := ev_cc1)
      (ev_ittpynob := ev_mv2) (ev_biaifgpd := ev_mv3) (ev1203 := ev1203)
      (ev_cwwgzxtj := ev_bfb) (ev1246 := ev1246) (ev_mitevvsv := ev_len)
      (ev_rqpeovbn := ev_iz1) (ev_xrhmaojz := ev_iz2) (ev_whimdwjd := ev_val)
      (ev1305 := ev_fro) (hc1474 := hc_fam) .. =>
    have ext0 := check_family_seg1_extends sg112
    obtain ⟨-, _, hst_rp⟩ := read_payload_stream ev126
    obtain ⟨_, _, _, _, -, hr_ga, -, hs1, -, -⟩ := Decl.get_address_spec hst_rp ev148
    injection hr_ga with hp_ga; injection hp_ga with _ h_s1; injection h_s1 with h_s1'
    subst h_s1'
    obtain ⟨_, hs2⟩ := get_count_stream
      (L1.Stream.mono (ev194.heap_extends.trans ev_ord.heap_extends) hs1) ev231
    obtain ⟨_, _, _, -, -, -, hs3, -⟩ := Decl.get_addrs_spec hs2 ev266
    obtain ⟨bs4, hs4⟩ := get_count_stream hs3 ev309
    have ext_to_ws : Heap.Extends h _ :=
      ext0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
        (ev194.heap_extends.trans (ev_ord.heap_extends.trans
          (ev231.heap_extends.trans (ev266.heap_extends.trans ev309.heap_extends))))))
    have hrc_ws := hrc.mono ext_to_ws
    obtain ⟨ext_ws, ws, hws_rep, hws_spec⟩ :=
      check_witnesses_spec_ext hW.runStore hW.hashedStored cs_ws.length (Nat.le_refl _)
        (hrc_ws.mono ev_ws.heap_extends) (Heap.Extends.refl _)
        (S0.addr_mono ext_to_ws hxb) hs4 ev_ws
        (fun cl hcl => hsub_fam cl (by rw [hc_fam]; simp [hcl]))
    obtain ⟨ext_asb, hwset⟩ := Claim.addr_set_build_spec hws_rep (Claim.RepAddrSet.nil _) ev_asb
    rw [List.append_nil] at hwset
    have ext_asb_fro : Heap.Extends _ _ :=
      ev435.heap_extends.trans (ev465.heap_extends.trans (ev513.heap_extends.trans
        (ev601.heap_extends.trans (ev634.heap_extends.trans (ev664.heap_extends.trans
          (ev686.heap_extends.trans (ev716.heap_extends.trans (ev759.heap_extends.trans
            (ev817.heap_extends.trans (ev796.heap_extends.trans (ev852.heap_extends.trans
              (ev_anr.heap_extends.trans (ev874.heap_extends.trans (ev896.heap_extends.trans
                (ev960.heap_extends.trans (ev939.heap_extends.trans (ev1011.heap_extends.trans
                  (ev990.heap_extends.trans (ev_mv1.heap_extends.trans (ev_cc1.heap_extends.trans
                    (ev_mv2.heap_extends.trans (ev_mv3.heap_extends.trans
                      (ev1203.heap_extends.trans (ev_bfb.heap_extends.trans
                        (ev1246.heap_extends.trans (ev_len.heap_extends.trans
                          (ev_iz1.heap_extends.trans (ev_iz2.heap_extends.trans
                            ev_val.heap_extends))))))))))))))))))))))))))))
    have ext_to_fro := ext_to_ws.trans (ext_ws.trans (ext_asb.trans ext_asb_fro))
    match Obs.«KernelModeled::family_refs_ok».obs ev_fro with
    | .run (cs12 := cs_rb) (cs34 := cs_B) (cs_ijcbjcgc := cs_go)
        (ev14 := ev_rb) (ev36 := ev_B) (ev_ycrqbsja := ev_idx_rb)
        (ev_nhomjxfq := ev_idx_B) (ev_kfwmaaqi := ev_go) (hc222 := hc_fro) .. =>
      obtain ⟨ext_rb, raw_rb, crb, hlen_rb, hh_rb, haddr_rb, -, hexact_rb, hrep_rb, -⟩ :=
        Claim.load_verified_constant_de (S0.addr_mono ext_to_fro hxrb) ev_rb
      have hrec_rb : recordOf K.E₀ rb = some crb :=
        Claim.recordOf_of_hashed hW.hashedStored
          (Claim.hashed_mono (fun cl hcl => hsub_fam cl (by rw [hc_fam]; simp [hc_fro, hcl])) hh_rb)
          hlen_rb (by rw [haddr_rb]; exact hexact_rb)
      obtain ⟨ext_B, raw_B, cB, hlen_B, hh_B, haddr_B, -, hexact_B, hrep_B, -⟩ :=
        Claim.load_verified_constant_de (S0.addr_mono (ext_to_fro.trans ext_rb) hxb) ev_B
      have hrec_B : recordOf K.E₀ B = some cB :=
        Claim.recordOf_of_hashed hW.hashedStored
          (Claim.hashed_mono (fun cl hcl => hsub_fam cl (by rw [hc_fam]; simp [hc_fro, hcl])) hh_B)
          hlen_B (by rw [haddr_B]; exact hexact_B)
      obtain ⟨ext_i1, hused_rb⟩ := Claim.const_idxs_of_spec (hrep_rb.mono ext_B) ev_idx_rb
      obtain ⟨ext_i2, hused_B⟩ := Claim.const_idxs_of_spec (hrep_B.mono ext_i1) ev_idx_B
      have ext_go_pre := ext_rb.trans (ext_B.trans (ext_i1.trans ext_i2))
      obtain ⟨rbRefs, hrbMap, hrbCore⟩ :=
        repIxonAddrList_to_core (repConstant_refs_eq_local hrep_rb)
      obtain ⟨bRefs, hbMap, hbCore⟩ :=
        repIxonAddrList_to_core (repConstant_refs_eq_local hrep_B)
      have hrb_len : rbRefs.length < 72057594037927936 := by
        have := congrArg List.length hrbMap
        simp only [List.length_map, Array.length_toList] at this
        rw [this]; exact refs_size_lt_local hlen_rb hexact_rb
      have hb_len : bRefs.length < 72057594037927936 := by
        have := congrArg List.length hbMap
        simp only [List.length_map, Array.length_toList] at this
        rw [this]; exact refs_size_lt_local hlen_B hexact_B
      obtain ⟨-, hgo⟩ := family_refs_go_spec (K := K) hW.runStore hW.hashedStored hrec_B
        hb_len hbMap (i := 0) (by simpa using hrb_len)
        (hrc.mono (ext_to_fro.trans ext_go_pre))
        (S0.addr_mono (ext_to_fro.trans ext_go_pre) hxb)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          (ext_B.trans (ext_i1.trans ext_i2)) hrbCore)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_i2 hused_rb)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          (ext_i1.trans ext_i2) hbCore)
        hused_B
        (hwset.mono (ext_asb_fro.trans ext_go_pre))
        ev_go (fun cl hcl => hsub_fam cl (by rw [hc_fam]; simp [hc_fro, hcl]))
      obtain ⟨crb', k, hrec', hk_mem, hk_get⟩ := hu
      have hcc : crb' = crb := Option.some.inj (hrec'.symm.trans hrec_rb)
      subst crb'
      have hk_map : (rbRefs.map Core.ixAddr)[k]? = some x := by
        rw [hrbMap, Array.getElem?_toList]; exact hk_get
      rw [List.getElem?_map] at hk_map
      cases hq : rbRefs[k]? with
      | none => simp [hq] at hk_map
      | some q =>
        simp only [hq, Option.map_some, Option.some.injEq] at hk_map
        subst hk_map
        have hk_s0 : k ∈ S0.usedRefIdxs crb := by
          rw [Assembly.usedRefIdxs_eq]; exact hk_mem
        rcases hgo k q hq (by simpa using hk_s0) with hbr | hmem_w
        · exact Or.inl hbr
        · rw [List.mem_map] at hmem_w
          obtain ⟨w, hw_rev, hw_eq⟩ := hmem_w
          have hw_in : w ∈ ws := List.mem_reverse.mp hw_rev
          rw [← hw_eq]
          rcases hws_spec w hw_in with hwb | ⟨h_w, xx_w, s_w, ext_w, hblk_w, hx_w, hcl_w, -⟩
          · exact Or.inr (Or.inl hwb)
          · exact Or.inr (Or.inr ⟨h_w, rc, xb, xx_w, s_w, hrc_ws.mono ext_w, hblk_w, hx_w,
              by rw [hc_fam]; simp [hcl_w]⟩)

/-! ## `BatchGives.adviceRefs` -/

private theorem projection_of_advice_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {S : List _root_.Address} {rb : Bytes.Address} {x_r x_aset r : SourceValue F}
    {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hr : Bytes.RepAddressRef Core.addrTy h rb x_r)
    (hseen : Claim.RepAddrSet h S x_aset)
    (ev : ObsFn Obs.W "KernelModeled::projection_of_advice" [x_r, x_aset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      (r = .field 1 →
        ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
          ConstAddrOf blk cblk (Core.ixAddr rb)) := by
  have handleProj : ∀ {m2 m_ci m_pb : Heap F} {cs12 cs_ci cs_pb cs_mem : List (Call F)}
      {x_c v_ci v_pb : SourceValue F},
      (∀ cl ∈ cs12, cl ∈ calls) → (∀ cl ∈ cs_ci, cl ∈ calls) →
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h x_c m2 cs12 →
      ObsFn Obs.W "Ingress::get_ci" [x_r] m2 v_ci m_ci cs_ci →
      ObsFn Obs.W "KernelModeled::projection_block" [x_c] m_ci v_pb m_pb cs_pb →
      ObsFn Obs.W "KernelClaim::addr_set_member" [v_pb, x_aset] m_pb r h' cs_mem →
      Heap.Extends h h' ∧
        (r = .field 1 →
          ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
            ConstAddrOf blk cblk (Core.ixAddr rb)) := by
    intro m2 m_ci m_pb cs12 cs_ci cs_pb cs_mem x_c v_ci v_pb hsub12 hsub_ci ev14 ev_ci ev_pb ev_mem
    obtain ⟨ext1, rawBytes, cr, hlen, hh, haddr, -, hexact, hrep_cr, -⟩ :=
      Claim.load_verified_constant_de ⟨rb, hr, rfl⟩ ev14
    have hrec_cr : recordOf E₀ (Core.ixAddr rb) = some cr :=
      Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub12 hh) hlen (by rw [haddr]; exact hexact)
    have ext_ci := ev_ci.heap_extends
    obtain ⟨hpb_h, hproj, b_own, hown_rep, hown_eq⟩ :=
      projection_block_spec (Core.ixAddr rb) (hrep_cr.mono ext_ci) ev_pb
    subst hpb_h
    obtain ⟨hmem_s, hh_m⟩ :=
      Claim.addr_set_member_set_spec hown_rep (hseen.mono (ext1.trans ext_ci)) ev_mem
    refine ⟨hh_m ▸ ext1.trans ext_ci, fun h1 => ?_⟩
    obtain ⟨cblk, hcblk, hca⟩ :=
      Claim.proj_member_of_load hS hcov (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hr)
        ev_ci hsub_ci hrec_cr hproj
    rw [← hown_eq] at hcblk hca
    exact ⟨Core.ixAddr b_own, cblk, hmem_s h1, hcblk, hca⟩
  match Obs.«KernelModeled::projection_of_advice».obs ev with
  | .IPrj (cs12 := cs12) (cs_skilefqi := cs_ci) (ev14 := ev14) (ev_pvplyepc := ev_ci)
      (ev109 := ev_pb) (ev95 := ev_mem) (hc125 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_mem
  | .CPrj (cs12 := cs12) (cs_tafpebbo := cs_ci) (ev14 := ev14) (ev_rnaxgwez := ev_ci)
      (ev158 := ev_pb) (ev144 := ev_mem) (hc174 := hc) .. =>
    exact handleProj
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      ev14 ev_ci ev_pb ev_mem
  | .other (ev14 := ev14) (he179 := hr0) (he180 := hh) .. =>
    exact ⟨hh ▸ ev14.heap_extends, fun h1 => absurd (Value.field.inj (hr0.symm.trans h1)) zero_ne_one⟩

private theorem advice_refs_ok_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {S Wset : List _root_.Address} {idxs : List Nat}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) :
    ∀ {refs : List Bytes.Address} {i : Nat}
      {x_refs x_used x_aset x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      i + refs.length < 72057594037927936 →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h refs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs x_used →
      Claim.RepAddrSet h S x_aset →
      Claim.RepAddrSet h Wset x_wset →
      ObsFn Obs.W "KernelModeled::advice_refs_ok"
        [x_refs, x_used, .field (i : F), x_aset, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      Heap.Extends h h' ∧
        ∀ k q, refs[k]? = some q → (i + k) ∈ idxs →
          Core.ixAddr q ∈ S ∨ Core.ixAddr q ∈ Wset ∨
            ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
              ConstAddrOf blk cblk (Core.ixAddr q)
  | [], i, x_refs, x_used, x_aset, x_wset, r, h, h', cs,
      hbound, hrefs, hused, hseen, hwset, ev, hsub => by
    match Obs.«KernelModeled::advice_refs_ok».obs ev with
    | .Nil (he23 := hh) .. => exact ⟨hh ▸ Heap.Extends.refl _, fun _ _ hq => by simp at hq⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld
      cases hbad
  | q :: rest, i, x_refs, x_used, x_aset, x_wset, r, h, h', cs,
      hbound, hrefs, hused, hseen, hwset, ev, hsub => by
    have hi : i < 72057594037927936 := by simp at hbound; omega
    match Obs.«KernelModeled::advice_refs_ok».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrefs ld
    | .Cons (m291 := m291) (ld12 := ld) (sg298 := sg) (op337 := op) (ev304 := ev_rest) (hc353 := hc) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      have hseg : Heap.Extends h m291 ∧
          (i ∈ idxs → Core.ixAddr q ∈ S ∨ Core.ixAddr q ∈ Wset ∨
            ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
              ConstAddrOf blk cblk (Core.ixAddr q)) := by
        match sg with
        | .other (ev56 := ev56) (hne281 := hne1) (he288 := hh) .. =>
          obtain ⟨hm43, hhas⟩ := Claim.g_list_has_spec idxs hi hused ev56
          exact ⟨hh ▸ hm43 ▸ Heap.Extends.refl _, fun hmem => absurd (hhas.mpr hmem) hne1⟩
        | .n1_n1 (ev56 := ev56) (ev99 := ev_mem) (he150 := hh) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨hmem_s, hm86⟩ := Claim.addr_set_member_set_spec hq hseen ev_mem
          exact ⟨hh ▸ hm86 ▸ Heap.Extends.refl _, fun _ => Or.inl (hmem_s rfl)⟩
        | .n1_other_n1 (ev56 := ev56) (ev99 := ev_ms) (ev170 := ev_mw) (he221 := hh) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨-, hm86⟩ := Claim.addr_set_member_set_spec hq hseen ev_ms
          subst hm86
          obtain ⟨hmem_w, hm157⟩ := Claim.addr_set_member_set_spec hq hwset ev_mw
          exact ⟨hh ▸ hm157 ▸ Heap.Extends.refl _, fun _ => Or.inr (Or.inl (hmem_w rfl))⟩
        | .n1_other_other (cs230 := cs_pa) (ev56 := ev56) (ev99 := ev_ms) (ev170 := ev_mw)
            (ev232 := ev_pa) (heq275 := h1) (he279 := hh) (hc280 := hcs) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          obtain ⟨-, hm86⟩ := Claim.addr_set_member_set_spec hq hseen ev_ms
          subst hm86
          obtain ⟨-, hm157⟩ := Claim.addr_set_member_set_spec hq hwset ev_mw
          subst hm157
          obtain ⟨ext_pa, hpa⟩ := projection_of_advice_spec hS hcov hq hseen ev_pa
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          exact ⟨hh ▸ ext_pa, fun _ => Or.inr (Or.inr (hpa h1))⟩
      obtain ⟨ext_seg, hq_ok⟩ := hseg
      have hv : _ = Value.field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]; push_cast; rfl
      rw [hv] at ev_rest
      obtain ⟨ext_rest, hrest_ok⟩ := advice_refs_ok_spec hS hcov (i := i + 1)
        (by simp at hbound ⊢; omega)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hused)
        (hseen.mono ext_seg) (hwset.mono ext_seg)
        ev_rest (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      refine ⟨ext_seg.trans ext_rest, fun k q₀ hget hmem => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        exact hq_ok (by simpa using hmem)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hget
        exact hrest_ok k' q₀ hget (by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hmem)

private theorem check_advice_record_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {S Wset : List _root_.Address} {ab : Bytes.Address}
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (ha : Bytes.RepAddressRef Core.addrTy h ab x_a)
    (hseen : Claim.RepAddrSet h S x_aset)
    (hwset : Claim.RepAddrSet h Wset x_wset)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      ((∀ c, recordOf E₀ (Core.ixAddr ab) = some c → ¬ IsProj c) ∨
        ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
          ConstAddrOf blk cblk (Core.ixAddr ab)) ∧
      ∀ x, UsedRef E₀ (Core.ixAddr ab) x →
        x ∈ S ∨ x ∈ Wset ∨
          ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧ ConstAddrOf blk cblk x := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (m945 := m945) (cs12 := cs12) (cs947 := cs947) (cs_dkogjupv := cs_aro)
      (ev_yqjbwijz := ev_ord) (ev14 := ev14) (sg952 := sg) (ev_lawbyzgo := ev_idx)
      (ev_bilbznow := ev_aro) (ev_ozxzdina := ev_idx2) (ev_tnqzszcy := ev_safe)
      (hc1011 := hc) .. =>
    have ext0 := ev_ord.heap_extends
    have ha0 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext0 ha
    obtain ⟨ext1, rawBytes, ca, hlen_a, hh_a, haddr_a, -, hexact_a, hrep_a, -⟩ :=
      Claim.load_verified_constant_de ⟨ab, ha0, rfl⟩ ev14
    have hrec_a : recordOf E₀ (Core.ixAddr ab) = some ca :=
      Claim.recordOf_of_hashed hcov
        (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh_a)
        hlen_a (by rw [haddr_a]; exact hexact_a)
    have hseg : Heap.Extends m2 m945 ∧
        ((∀ c, recordOf E₀ (Core.ixAddr ab) = some c → ¬ IsProj c) ∨
          ∃ blk cblk, blk ∈ S ∧ recordOf E₀ blk = some cblk ∧
            ConstAddrOf blk cblk (Core.ixAddr ab)) := by
      have hnotProj : ∀ hnp : ¬ IsProj ca,
          (∀ c, recordOf E₀ (Core.ixAddr ab) = some c → ¬ IsProj c) := by
        intro hnp c hc'
        have e : c = ca := Option.some.inj (hc'.symm.trans hrec_a)
        subst e; exact hnp
      obtain ⟨infoVal, _, _, _, _, hmk, hinfo_rep, -, -, -, -⟩ := hrep_a
      injection hmk with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hinfo_eq := hargs.1
      have hnoProj_of_tag : ∀ tag args,
          infoVal = .construct "Ixon::ConstantInfo" tag args →
          tag ≠ "DPrj" → tag ≠ "IPrj" → tag ≠ "CPrj" → tag ≠ "RPrj" →
          ¬ IsProj ca := by
        intro tag args hv h1 h2 h3 h4 hp
        rw [hv] at hinfo_rep
        rcases hp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩
        · rw [h] at hinfo_rep; obtain ⟨_, he, -⟩ := hinfo_rep
          exact h1 (Value.construct.inj he).2.1
        · rw [h] at hinfo_rep; obtain ⟨_, he, -⟩ := hinfo_rep
          exact h2 (Value.construct.inj he).2.1
        · rw [h] at hinfo_rep; obtain ⟨_, he, -⟩ := hinfo_rep
          exact h3 (Value.construct.inj he).2.1
        · rw [h] at hinfo_rep; obtain ⟨_, he, -⟩ := hinfo_rep
          exact h4 (Value.construct.inj he).2.1
      match sg with
      | .Defn_Definition_Safe (hv81 := hv) (ev210 := ev_rc) .. =>
        exact ⟨ev_rc.heap_extends, Or.inl (hnotProj (hnoProj_of_tag _ _ (hinfo_eq.trans hv)
          (by decide) (by decide) (by decide) (by decide)))⟩
      | .Defn_Definition_other (heq258 := h01) .. => exact absurd (Value.field.inj h01) zero_ne_one
      | .Defn_Theorem (hv81 := hv) (ev321 := ev_rc) .. =>
        exact ⟨ev_rc.heap_extends, Or.inl (hnotProj (hnoProj_of_tag _ _ (hinfo_eq.trans hv)
          (by decide) (by decide) (by decide) (by decide)))⟩
      | .Defn_Opaque (heq372 := h01) .. => exact absurd (Value.field.inj h01) zero_ne_one
      | .Recr (hv403 := hv) (ev553 := e1) (ev540 := e2) (ev574 := e3) .. =>
        exact ⟨e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends),
          Or.inl (hnotProj (hnoProj_of_tag _ _ (hinfo_eq.trans hv)
            (by decide) (by decide) (by decide) (by decide)))⟩
      | .Muts (hv598 := hv) (ev629 := e1) (ev649 := e2) (ev683 := e3) (ev723 := e4)
          (ev744 := e5) .. =>
        exact ⟨e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans
          (e4.heap_extends.trans e5.heap_extends))),
          Or.inl (hnotProj (hnoProj_of_tag _ _ (hinfo_eq.trans hv)
            (by decide) (by decide) (by decide) (by decide)))⟩
      | .IPrj (cs_sopfkvlz := cs_ci) (ev836 := ev_pb) (ev822 := ev_mem) (heq858 := h1)
          (ev_gjbqzffr := ev_ci) (he862 := hh) (hc863 := hcs) .. =>
        obtain ⟨hm_pb, hproj, b_own, hown_rep, hown_eq⟩ :=
          projection_block_spec (Core.ixAddr ab) hrep_a ev_pb
        subst hm_pb
        obtain ⟨hmem_s, hm_mem⟩ :=
          Claim.addr_set_member_set_spec hown_rep (hseen.mono (ext0.trans ext1)) ev_mem
        subst hm_mem
        obtain ⟨cblk, hcblk, hca⟩ :=
          Claim.proj_member_of_load hS hcov
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 ha0) ev_ci
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl])) hrec_a hproj
        rw [← hown_eq] at hcblk hca
        exact ⟨hh ▸ ev_ci.heap_extends, Or.inr ⟨Core.ixAddr b_own, cblk, hmem_s h1, hcblk, hca⟩⟩
      | .CPrj (cs_xamhzxrj := cs_ci) (ev915 := ev_pb) (ev901 := ev_mem) (heq937 := h1)
          (ev_wwojrrlm := ev_ci) (he941 := hh) (hc942 := hcs) .. =>
        obtain ⟨hm_pb, hproj, b_own, hown_rep, hown_eq⟩ :=
          projection_block_spec (Core.ixAddr ab) hrep_a ev_pb
        subst hm_pb
        obtain ⟨hmem_s, hm_mem⟩ :=
          Claim.addr_set_member_set_spec hown_rep (hseen.mono (ext0.trans ext1)) ev_mem
        subst hm_mem
        obtain ⟨cblk, hcblk, hca⟩ :=
          Claim.proj_member_of_load hS hcov
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 ha0) ev_ci
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl])) hrec_a hproj
        rw [← hown_eq] at hcblk hca
        exact ⟨hh ▸ ev_ci.heap_extends, Or.inr ⟨Core.ixAddr b_own, cblk, hmem_s h1, hcblk, hca⟩⟩
    obtain ⟨ext_sg, hkind_a⟩ := hseg
    obtain ⟨ext_idx, hused_a⟩ := Claim.const_idxs_of_spec (hrep_a.mono ext_sg) ev_idx
    obtain ⟨aRefs, haMap, haCore⟩ := repIxonAddrList_to_core (repConstant_refs_eq_local hrep_a)
    have ha_len : aRefs.length < 72057594037927936 := by
      have := congrArg List.length haMap
      simp only [List.length_map, Array.length_toList] at this
      rw [this]; exact refs_size_lt_local hlen_a hexact_a
    have ext_to_aro := ext0.trans (ext1.trans (ext_sg.trans ext_idx))
    obtain ⟨ext_aro, haro⟩ := advice_refs_ok_spec hS hcov (i := 0) (by simpa using ha_len)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) (ext_sg.trans ext_idx) haCore)
      hused_a (hseen.mono ext_to_aro) (hwset.mono ext_to_aro)
      ev_aro (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    have ext_all := ext_to_aro.trans (ext_aro.trans (ev_idx2.heap_extends.trans ev_safe.heap_extends))
    refine ⟨ext_all, hkind_a, fun x hu => ?_⟩
    obtain ⟨ca', k, hrec', hk_mem, hk_get⟩ := hu
    have hcc : ca' = ca := Option.some.inj (hrec'.symm.trans hrec_a)
    subst ca'
    have hk_map : (aRefs.map Core.ixAddr)[k]? = some x := by
      rw [haMap, Array.getElem?_toList]; exact hk_get
    rw [List.getElem?_map] at hk_map
    cases hq : aRefs[k]? with
    | none => simp [hq] at hk_map
    | some q =>
      simp only [hq, Option.map_some, Option.some.injEq] at hk_map
      subst hk_map
      have hk_s0 : k ∈ S0.usedRefIdxs ca := by
        rw [Assembly.usedRefIdxs_eq]; exact hk_mem
      exact haro k q hq (by simpa using hk_s0)

private theorem check_advice_records_prefix_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {Wset : List _root_.Address}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) :
    ∀ (rest pre : List Bytes.Address) {S : List _root_.Address}
      {x_rc x_adv x_seen x_wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h rest x_adv →
      Claim.RepAddrSet h S x_seen →
      (∀ z, z ∈ S ↔ ∃ j < pre.length, ∃ b', pre[j]? = some b' ∧ Core.ixAddr b' = z) →
      (∀ j b', j < pre.length → pre[j]? = some b' →
        (∀ c, recordOf E₀ (Core.ixAddr b') = some c → ¬ IsProj c) ∨
        ∃ j' b'', j' < j ∧ pre[j']? = some b'' ∧
          ∃ c'', recordOf E₀ (Core.ixAddr b'') = some c'' ∧
            ConstAddrOf (Core.ixAddr b'') c'' (Core.ixAddr b')) →
      Claim.RepAddrSet h Wset x_wset →
      ObsFn Obs.W "KernelModeled::check_advice_records" [x_rc, x_adv, x_seen, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ (k : Nat) (b : Bytes.Address), rest[k]? = some b →
        ∀ x, UsedRef E₀ (Core.ixAddr b) x →
          (∃ j b', j < pre.length + k ∧ (pre ++ rest)[j]? = some b' ∧ Core.ixAddr b' = x ∧
              ∀ c, recordOf E₀ x = some c → ¬ IsProj c) ∨
          (∃ j b' c', j < pre.length + k ∧ (pre ++ rest)[j]? = some b' ∧
              recordOf E₀ (Core.ixAddr b') = some c' ∧ ConstAddrOf (Core.ixAddr b') c' x) ∨
          x ∈ Wset
  | [], pre, S, x_rc, x_adv, x_seen, x_wset, r, h, h', cs,
      _, _, _, _, _, _, _, k, b, hk => by simp at hk
  | a :: rest', pre, S, x_rc, x_adv, x_seen, x_wset, r, h, h', cs,
      hadv, hseen, hS_iff, hpre_inv, hwset, ev, hsub, k, b, hk => by
    match Obs.«KernelModeled::check_advice_records».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hadv ld
    | .Cons (cs100 := cs_car) (cs138 := cs_rest) (ld12 := ld)
        (ev_mfihupbr := ev_ms) (ev_xzbngsxs := ev_mw) (ev102 := ev_car)
        (ev170 := ev_ins) (ev140 := ev_rest) (hc201 := hc) .. =>
      obtain ⟨a', rest'', heq, ha, hrest⟩ := Lib.rep_cons_of_load hadv ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨-, hm1⟩ := Claim.addr_set_member_set_spec ha hseen ev_ms
      subst hm1
      obtain ⟨-, hm2⟩ := Claim.addr_set_member_set_spec ha hwset ev_mw
      subst hm2
      obtain ⟨ext_car, ha_kind, ha_refs⟩ :=
        check_advice_record_spec hS hcov ha hseen hwset ev_car
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        intro x hu
        rcases ha_refs x hu with hx_S | hx_W | ⟨blk, cblk, hblk_S, hcblk, hca⟩
        · obtain ⟨j, hj, b', hb', rfl⟩ := (hS_iff x).mp hx_S
          have hget_app : (pre ++ a :: rest')[j]? = some b' := by
            rw [List.getElem?_append_left hj]; exact hb'
          rcases hpre_inv j b' hj hb' with hnp | ⟨j', b'', hj', hb'', c'', hc'', hca''⟩
          · exact Or.inl ⟨j, b', by omega, hget_app, rfl, hnp⟩
          · have hget_app' : (pre ++ a :: rest')[j']? = some b'' := by
              rw [List.getElem?_append_left (Nat.lt_trans hj' hj)]; exact hb''
            exact Or.inr (Or.inl ⟨j', b'', c'', by omega, hget_app', hc'', hca''⟩)
        · exact Or.inr (Or.inr hx_W)
        · obtain ⟨j, hj, b', hb', rfl⟩ := (hS_iff blk).mp hblk_S
          have hget_app : (pre ++ a :: rest')[j]? = some b' := by
            rw [List.getElem?_append_left hj]; exact hb'
          exact Or.inr (Or.inl ⟨j, b', cblk, by omega, hget_app, hcblk, hca⟩)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        rw [← Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol] at ev_ins
        obtain ⟨ext_ins, hseen'⟩ :=
          Claim.rbtree_set_insert_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_car ha) (hseen.mono ext_car) ev_ins
        have ext_step := ext_car.trans ext_ins
        have hS'_iff : ∀ z, z ∈ Core.ixAddr a :: S ↔
            ∃ j < (pre ++ [a]).length, ∃ b', (pre ++ [a])[j]? = some b' ∧ Core.ixAddr b' = z := by
          intro z
          simp only [List.mem_cons, List.length_append, List.length_singleton]
          constructor
          · rintro (rfl | hz)
            · exact ⟨pre.length, by omega, a, by simp, rfl⟩
            · obtain ⟨j, hj, b', hb', rfl⟩ := (hS_iff z).mp hz
              exact ⟨j, by omega, b', by rw [List.getElem?_append_left hj]; exact hb', rfl⟩
          · rintro ⟨j, hj, b', hb', rfl⟩
            by_cases hlt : j < pre.length
            · rw [List.getElem?_append_left hlt] at hb'
              exact Or.inr ((hS_iff _).mpr ⟨j, hlt, b', hb', rfl⟩)
            · have heqj : j = pre.length := by omega
              subst heqj
              simp at hb'
              subst hb'
              exact Or.inl rfl
        have hpre'_inv : ∀ j b', j < (pre ++ [a]).length → (pre ++ [a])[j]? = some b' →
            (∀ c, recordOf E₀ (Core.ixAddr b') = some c → ¬ IsProj c) ∨
            ∃ j' b'', j' < j ∧ (pre ++ [a])[j']? = some b'' ∧
              ∃ c'', recordOf E₀ (Core.ixAddr b'') = some c'' ∧
                ConstAddrOf (Core.ixAddr b'') c'' (Core.ixAddr b') := by
          intro j b' hj hb'
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hlt : j < pre.length
          · rw [List.getElem?_append_left hlt] at hb'
            rcases hpre_inv j b' hlt hb' with hnp | ⟨j', b'', hj', hb'', c'', hc'', hca''⟩
            · exact Or.inl hnp
            · exact Or.inr ⟨j', b'', hj',
                by rw [List.getElem?_append_left (Nat.lt_trans hj' hlt)]; exact hb'',
                c'', hc'', hca''⟩
          · have heqj : j = pre.length := by omega
            subst heqj
            simp at hb'
            subst hb'
            rcases ha_kind with hnp | ⟨blk, cblk, hblk_S, hcblk, hca⟩
            · exact Or.inl hnp
            · obtain ⟨j', hj', b'', hb'', rfl⟩ := (hS_iff blk).mp hblk_S
              exact Or.inr ⟨j', b'', hj',
                by rw [List.getElem?_append_left hj']; exact hb'', cblk, hcblk, hca⟩
        have hrec := check_advice_records_prefix_spec hS hcov rest' (pre ++ [a])
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_step hrest)
          hseen' hS'_iff hpre'_inv (hwset.mono ext_step) ev_rest
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) k' b hk
        intro x hu
        have hlist_eq : (pre ++ [a]) ++ rest' = pre ++ a :: rest' := by simp
        have hlen_eq : (pre ++ [a]).length + k' = pre.length + (k' + 1) := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [hlist_eq, hlen_eq] at hrec
        exact hrec x hu

/-- **Discharges `BatchGives.adviceRefs`**: every used reference of the `k`-th advice record of a
scope check's own list is an earlier listed non-projection record, a constant address of an earlier
listed record, or a witness of the check. -/
theorem FamRunCtx.adviceRefs_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B rb : _root_.Address} {cs : List (Call F)} {advAs : List Bytes.Address}
    (hS : K.ScopeAt B rb cs)
    (hown : FamilyCallOwn K.calls K.bAddr K.t B rb K.lim cs advAs)
    {k : Nat} {b : Bytes.Address} (hk : advAs[k]? = some b)
    {x : _root_.Address} (hu : UsedRef K.E₀ (Core.ixAddr b) x) :
    (∃ j b', j < k ∧ advAs[j]? = some b' ∧ Core.ixAddr b' = x ∧
        ∀ c, recordOf K.E₀ x = some c → ¬ IsProj c) ∨
    (∃ j b' c', j < k ∧ advAs[j]? = some b' ∧ recordOf K.E₀ (Core.ixAddr b') = some c' ∧
        ConstAddrOf (Core.ixAddr b') c' x) ∨
    K.WitBase B x ∨ K.ContWitness cs B x := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, -, -, hfoa, -, hsub_fam⟩ := hown
  obtain ⟨-, m_ws, x_s4, x_nw, x_outside, x_s5, m_ws', cs_ws, ⟨bs4, hs4⟩, ev_ws,
    wset, m_asb, cs_asb, ev_asb, m_adv, m_adv', x_advice, v_adv, cs_adv, ev_adv,
    ext_h_ws, ext_asb_adv, advRep, sub_ws, -, sub_adv⟩ := hfoa
  have hrc_ws := hrc.mono ext_h_ws
  obtain ⟨ext_ws, ws, hws_rep, hws_spec⟩ :=
    check_witnesses_spec_ext hW.runStore hW.hashedStored cs_ws.length (Nat.le_refl _)
      (hrc_ws.mono ev_ws.heap_extends) (Heap.Extends.refl _)
      (S0.addr_mono ext_h_ws hxb) hs4 ev_ws (fun cl hcl => hsub_fam cl (sub_ws cl hcl))
  obtain ⟨ext_asb, hwset⟩ := Claim.addr_set_build_spec hws_rep (Claim.RepAddrSet.nil _) ev_asb
  rw [List.append_nil] at hwset
  have hrec := check_advice_records_prefix_spec hW.runStore hW.hashedStored advAs []
    advRep (Claim.RepAddrSet.nil m_adv) (by simp) (by intro _ _ hj; simp at hj)
    (hwset.mono ext_asb_adv) ev_adv (fun cl hcl => hsub_fam cl (sub_adv cl hcl)) k b hk x hu
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hrec
  rcases hrec with h1 | h2 | hmem_w
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · rw [List.mem_map] at hmem_w
    obtain ⟨w, hw_rev, hw_eq⟩ := hmem_w
    have hw_in : w ∈ ws := List.mem_reverse.mp hw_rev
    rw [← hw_eq]
    rcases hws_spec w hw_in with hwb | ⟨h_w, xx_w, s_w, ext_w, hblk_w, hx_w, hcl_w, -⟩
    · exact Or.inr (Or.inr (Or.inl hwb))
    · exact Or.inr (Or.inr (Or.inr ⟨h_w, rc, xb, xx_w, s_w, hrc_ws.mono ext_w, hblk_w, hx_w,
        sub_ws _ hcl_w⟩))

/-! ## `rec_family_block`, `check_const` on recursor projections, and `BatchGives.contWitness` -/

/-- Unconditional raw recursor representation from `Ingress::get_ci` on a standalone `.recr` or
`.rPrj` record. -/
theorem get_ci_of_rec_raw_uncond {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {ab : Bytes.Address} {x_r ptr v : SourceValue F} {h h' : Heap F}
    {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hab : Bytes.RepAddressRef Core.addrTy h ab x_r)
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_r] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v)
    (hc : recordOf E₀ (Core.ixAddr ab) = some c) :
    (∀ rc, c.info = .recr rc →
      ∃ blobs, L1.RawRecrValRep c.refs.toList [Core.ixAddr ab] c.univs.toList c.sharing.toList
        blobs h' rc (Core.ixAddr ab) 0 v) ∧
    (∀ idx blk, c.info = .rPrj ⟨idx, blk⟩ →
      ∃ cb ms rc blobs, recordOf E₀ blk = some cb ∧ cb.info = .muts ms ∧
        ms[idx.toNat]? = some (.recr rc) ∧
        L1.RawRecrValRep cb.refs.toList (L1.blockRecurAddrs blk ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' rc blk idx.toNat v) := by
  have match_wrong : ∀ {cs12 : List (Call F)} {m2 : Heap F} {x_c : SourceValue F},
      (∀ cl ∈ cs12, cl ∈ calls) →
      ObsFn Obs.W "Ingress::load_verified_constant" [x_r] h x_c m2 cs12 →
      ∃ c', c' = c ∧ L1.RepConstant m2 c' x_c := by
    intro cs12 m2 x_c hsub12 ev14
    obtain ⟨-, _, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    have hcc : c' = c :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
        (Core.hashed_mono hsub12 hh) haddr hexact
    exact ⟨c', hcc, cRep⟩
  constructor
  · intro rc hrc
    match Obs.«Ingress::get_ci».obs ev with
    | .Recr (cs12 := cs12) (ev14 := ev14) (hm951 := hm951) (hm973 := hm973)
        (he981 := he981) (hm980 := hm980) (ev1056 := ev1056) (ev987 := ev987)
        (hc1071 := hcs) .. =>
      have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨ext1, rawList, c', -, hhash, haddr, hexact, -, -, -, -, hbd32, -, cRep⟩ :=
        L1.load_verified_constant_decode_bounded hab ev14
      have hcc : c' = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
          (Core.hashed_mono hsub12 hhash) haddr hexact
      subst c'
      obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
      rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
      subst infoVal shPtr rfPtr unPtr bdPtr
      obtain ⟨rc', hc_info, hrc_rep⟩ := L1.repConstantInfo_recr_inv hinfo
      have hrc_eq : rc' = rc := Ixon.ConstantInfo.recr.inj (hc_info.symm.trans hrc)
      subst rc'
      have ext2a : Heap.Extends _ _ := by rw [hm973]; exact Heap.Extends.snoc _ _
      have ext2b : Heap.Extends _ _ := by rw [hm951]; exact Heap.Extends.snoc _ _
      have ext2 := ext2a.trans ext2b
      have hnil965 : RepList Names.«Lists::Node<&[Field; 32]>» L1.RepIxonAddressRef _ []
          (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») _) := by
        rw [hm973]; exact Lib.rep_store_nil _
      have ha965 : L1.RepIxonAddressRef _ (Core.ixAddr ab) x_r :=
        (L1.core_to_repIxonAddressRef hab).mono (ext1.trans ext2a)
      have hrecs : RepList L1.addressListEnum L1.RepIxonAddressRef _ [Core.ixAddr ab]
          (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») _) := by
        rw [hm951, L1.addressListEnum_eq]
        exact Lib.rep_store_cons L1.repIxonAddressRef_heapMono₂ ha965 hnil965
      obtain ⟨ext3, htbl⟩ :=
        L1.binder_table_spec (hbd.mono Deserialize.repBinderBlock_heapMono₂ ext2) hbd32 ev1056
      have ext23 := ext2.trans ext3
      have ev987' : ObsFn Obs.W "Convert::convert_recursor"
          [_, x_r, .field ((0 : Nat) : F), _, _, _, _, _, .field 0] _ _ _ _ := by
        simpa using ev987
      obtain ⟨ext4, blobs, -, hraw⟩ :=
        L1.convert_recursor_spec
          (hrc_rep.mono ext23)
          ((L1.core_to_repIxonAddressRef hab).mono (ext1.trans ext23))
          (by decide)
          (Deserialize.RepShareVec.mono ext23 hsh)
          (hrf.mono L1.repIxonAddressRef_heapMono₂ ext23)
          (hrecs.mono L1.repIxonAddressRef_heapMono₂ ext3)
          (hun.mono Deserialize.repUnivPtr_heapMono₂ ext23)
          htbl ev987'
      rw [he981, hm980] at hld
      have hv_eq : _ = v := Except.ok.inj ((Claim.loadValue_snoc_self _ _).symm.trans hld)
      subst hv_eq
      rw [hm980]
      exact ⟨blobs, hraw.mono (Heap.Extends.snoc _ _) (fun _ hm => hm)⟩
    | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hcs) ..
    | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hcs) ..
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hcs) .. =>
      exfalso
      obtain ⟨c', rfl, cRep⟩ := match_wrong (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) ev14
      obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
      rw [hrc] at hinfo
      obtain ⟨rv, hrv, -⟩ := hinfo
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
      rw [← hc_eq.2.2.1] at hrv
      simp at hrv
  · intro idx blk hrprj
    match Obs.«Ingress::get_ci».obs ev with
    | .RPrj (cs12 := cs12) (cs894 := cs894) (ev14 := ev14) (ev917 := ev917) (ev896 := ev896)
        (hc926 := hcs) .. =>
      have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hsub894 : ∀ cl ∈ cs894, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨-, _, c', -, hhash, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
        L1.load_verified_constant_decode_bounded hab ev14
      have hcc : c' = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
          (Core.hashed_mono hsub12 hhash) haddr hexact
      subst c'
      obtain ⟨infoVal, _, _, _, _, hc_mk, hinfo, -, -, -, -⟩ := cRep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_mk
      rcases hc_mk with ⟨_, _, hinfo_eq, _, _, _, _⟩
      subst infoVal
      obtain ⟨p, hp_eq, hx_idx, hblk_ix⟩ := L1.repConstantInfo_rPrj_inv hinfo
      have hp_val : p = ⟨idx, blk⟩ := Ixon.ConstantInfo.rPrj.inj (hp_eq.symm.trans hrprj)
      subst hp_val
      subst hx_idx
      obtain ⟨hidx56, hv898, hm907⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value _ idx) ev917
      subst hv898 hm907
      obtain ⟨b_blk, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
      obtain ⟨-, -, blkBytes, cb, ms, rc, blobs, v',
        hhash_blk, haddr_blk, hexact_blk, hcb_info, hmc_get, hld', hraw⟩ :=
        get_ci_rprj_raw_uncond hb_rep ev896
      have hv_eq : v' = v := Except.ok.inj (hld'.symm.trans hld)
      subst hv_eq
      obtain ⟨_, c0, -, hh0, haddr0, hexact0, -, hgh⟩ := Claim.get_ci_head hab ev
      have hc0_eq : c0 = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
          (Core.hashed_mono hsub hh0) haddr0 hexact0
      subst c0
      obtain ⟨cb', ms', _, hbl, -⟩ := hgh.rPrj idx blk hrprj
      obtain ⟨hrec_cb', -⟩ := (hbl.mono hsub).stored hcov
      have hcb_eq : cb = cb' :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans (hb_eq ▸ hrec_cb'))
          (Core.hashed_mono hsub894 hhash_blk) haddr_blk hexact_blk
      subst cb
      have hidx_val : ((idx.toNat : F)).val = idx.toNat := val_cast_lt_u56 hidx56
      rw [hidx_val] at hmc_get hraw
      rw [hb_eq] at hraw
      exact ⟨cb', ms, rc, blobs, hrec_cb', hcb_info,
        by rw [← Array.getElem?_toList]; exact hmc_get, hraw⟩
    | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hcs) ..
    | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hcs) ..
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
      exfalso
      obtain ⟨c', rfl, cRep⟩ := match_wrong (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) ev14
      obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
      rw [hrprj] at hinfo
      obtain ⟨pv, hpv, -⟩ := hinfo
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
      rw [← hc_eq.2.2.1] at hpv
      simp at hpv

private theorem lastDom_unique (c : Ixon.Constant) :
    ∀ n₁ n₂ {e d₁ d₂ : Ixon.Expr},
      Binding.FamilyOf.lastDom c n₁ e = some d₁ →
      Binding.FamilyOf.lastDom c n₂ e = some d₂ → d₁ = d₂
  | 0, _, _, _, _, h1, _ => by simp [Binding.FamilyOf.lastDom] at h1
  | _, 0, _, _, _, _, h2 => by simp [Binding.FamilyOf.lastDom] at h2
  | n₁ + 1, n₂ + 1, e, d₁, d₂, h1, h2 => by
    unfold Binding.FamilyOf.lastDom at h1 h2
    cases hnd : Binding.FamilyOf.node c e with
    | all d b =>
      rw [hnd] at h1 h2
      dsimp only at h1 h2
      cases hb : Binding.FamilyOf.node c b with
      | all _ _ =>
        rw [hb] at h1 h2
        exact lastDom_unique c n₁ n₂ h1 h2
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ =>
        rw [hb] at h1 h2
        exact Option.some.inj (h1.symm.trans h2)
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at h1; cases h1

private theorem spineHead_unique (c : Ixon.Constant) :
    ∀ n₁ n₂ {e : Ixon.Expr},
      (∀ f a, Binding.FamilyOf.spineHead c n₁ e ≠ .app f a) →
      (∀ f a, Binding.FamilyOf.spineHead c n₂ e ≠ .app f a) →
      Binding.FamilyOf.spineHead c n₁ e = Binding.FamilyOf.spineHead c n₂ e
  | n₁, n₂, e, h1, h2 => by
    cases hnd : Binding.FamilyOf.node c e with
    | app f a =>
      cases n₁ with
      | zero =>
        simp only [Binding.FamilyOf.spineHead, hnd] at h1
        exact (h1 f a rfl).elim
      | succ n₁' =>
        cases n₂ with
        | zero =>
          simp only [Binding.FamilyOf.spineHead, hnd] at h2
          exact (h2 f a rfl).elim
        | succ n₂' =>
          simp only [Binding.FamilyOf.spineHead, hnd] at h1 h2 ⊢
          exact spineHead_unique c n₁' n₂' h1 h2
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
    | letE _ _ _ _ _ | share _ =>
      have hconst : ∀ n, Binding.FamilyOf.spineHead c n e = Binding.FamilyOf.node c e := by
        intro n
        cases n with
        | zero => rfl
        | succ n' => simp [Binding.FamilyOf.spineHead, hnd]
      rw [hconst n₁, hconst n₂]

private theorem get_ci_loads_induct_is_iprj {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {ab : Bytes.Address} {ap ptr x_blk : SourceValue F} {h h' : Heap F}
    {w0 w1 w2 w3 w4 w5 w7 : SourceValue F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hab : Bytes.RepAddressRef Core.addrTy h ab ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [w0, w1, w2, w3, w4, w5, x_blk, w7])) :
    ∃ (c : Ixon.Constant) (idx : UInt64) (blk : _root_.Address) (b_blk : Bytes.Address)
      (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      recordOf E₀ (Core.ixAddr ab) = some c ∧ c.info = .iPrj ⟨idx, blk⟩ ∧
      Bytes.RepAddressRef Core.addrTy h' b_blk x_blk ∧ Core.ixAddr b_blk = blk ∧
      recordOf E₀ blk = some cb ∧ cb.info = .muts ms ∧ ms[idx.toNat]? = some (.indc ind) := by
  obtain ⟨rawBytes, c, hlen, hh, haddr, hexact, -, hhead⟩ := Claim.get_ci_head hab ev
  have hc : recordOf E₀ (Core.ixAddr ab) = some c :=
    Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub hh) hlen (by rw [haddr]; exact hexact)
  cases hinfo : c.info with
  | iPrj p =>
    obtain ⟨idx, blk⟩ := p
    obtain ⟨cb, ms, ind, hbl, hmem, -, _, _, _, _, x_blk', b_blk, hld', hb_rep, hb_eq⟩ :=
      hhead.iPrj idx blk hinfo
    have hargs := (Value.construct.inj (Except.ok.inj (hld'.symm.trans hld))).2.2
    simp only [List.cons.injEq, and_true] at hargs
    have hx_eq : x_blk' = x_blk := hargs.2.2.2.2.2.2.1
    subst hx_eq
    obtain ⟨hcb, hms⟩ := (hbl.mono hsub).stored hcov
    exact ⟨c, idx, blk, b_blk, cb, ms, ind, hc, hinfo, hb_rep, hb_eq, hcb, hms,
      by rw [← Array.getElem?_toList]; exact hmem⟩
  | muts ms => exact (hhead.notMuts ms hinfo).elim
  | axio ax =>
    obtain ⟨_, _, hl⟩ := hhead.axio ax hinfo
    exact absurd (Value.construct.inj (Except.ok.inj (hl.symm.trans hld))).2.1 (by decide)
  | quot q =>
    obtain ⟨_, _, hl⟩ := hhead.quot q hinfo
    exact absurd (Value.construct.inj (Except.ok.inj (hl.symm.trans hld))).2.1 (by decide)
  | cPrj p =>
    obtain ⟨idx, cidx, blk⟩ := p
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, -, -⟩ :=
      hhead.cPrj idx cidx blk hinfo
    exact absurd (Value.construct.inj (Except.ok.inj (hl.symm.trans hld))).2.1 (by decide)
  | rPrj p =>
    obtain ⟨idx, blk⟩ := p
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, -, -⟩ :=
      hhead.rPrj idx blk hinfo
    exact absurd (Value.construct.inj (Except.ok.inj (hl.symm.trans hld))).2.1 (by decide)
  | recr rc =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hl⟩ := hhead.recr rc hinfo
    exact absurd (Value.construct.inj (Except.ok.inj (hl.symm.trans hld))).2.1 (by decide)
  | defn d =>
    exfalso
    match Obs.«Ingress::get_ci».obs ev with
    | .Defn_n0 (hm218 := hm) (he219 := he) (ev225 := ev_cd) .. =>
      rw [he, hm] at hld
      have hv := Except.ok.inj ((Claim.loadValue_snoc_self _ _).symm.trans hld)
      rw [hv] at ev_cd
      match Obs.«Convert::convert_definition».obs ev_cd with
      | .Definition (he242 := h) .. | .Opaque (he329 := h) .. | .Theorem (he373 := h) .. =>
        exact absurd (Value.construct.inj h).2.1 (by decide)
    | .Defn_other (hm339 := hm) (he340 := he) (ev346 := ev_cd) .. =>
      rw [he, hm] at hld
      have hv := Except.ok.inj ((Claim.loadValue_snoc_self _ _).symm.trans hld)
      rw [hv] at ev_cd
      match Obs.«Convert::convert_definition».obs ev_cd with
      | .Definition (he242 := h) .. | .Opaque (he329 := h) .. | .Theorem (he373 := h) .. =>
        exact absurd (Value.construct.inj h).2.1 (by decide)
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hcs) ..
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
      obtain ⟨-, _, c', -, hh', haddr', hexact', -, -, -, -, -, -, cRep⟩ :=
        L1.load_verified_constant_decode_bounded hab ev14
      have hcc := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
        (Core.hashed_mono (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hh') haddr' hexact'
      subst c'
      obtain ⟨infoVal, _, _, _, _, hmk, hiRep, -, -, -, -⟩ := cRep
      rw [hinfo] at hiRep
      obtain ⟨dv, hdv, -⟩ := hiRep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rw [← hmk.2.2.1] at hdv; simp at hdv
  | dPrj p =>
    exfalso
    match Obs.«Ingress::get_ci».obs ev with
    | .DPrj (ev650 := ev_dp) .. =>
      match Obs.«Ingress::get_ci_dprj».obs ev_dp with
      | .run (he230 := he) (hm229 := hm) (ev236 := ev_cd) .. =>
        rw [he, hm] at hld
        have hv := Except.ok.inj ((Claim.loadValue_snoc_self _ _).symm.trans hld)
        rw [hv] at ev_cd
        match Obs.«Convert::convert_definition».obs ev_cd with
        | .Definition (he242 := h) .. | .Opaque (he329 := h) .. | .Theorem (he373 := h) .. =>
          exact absurd (Value.construct.inj h).2.1 (by decide)
    | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hcs) ..
    | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hcs) ..
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hcs) ..
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
      obtain ⟨-, _, c', -, hh', haddr', hexact', -, -, -, -, -, -, cRep⟩ :=
        L1.load_verified_constant_decode_bounded hab ev14
      have hcc := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
        (Core.hashed_mono (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hh') haddr' hexact'
      subst c'
      obtain ⟨infoVal, _, _, _, _, hmk, hiRep, -, -, -, -⟩ := cRep
      rw [hinfo] at hiRep
      obtain ⟨pv, hpv, -⟩ := hiRep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rw [← hmk.2.2.1] at hpv; simp at hpv

/-- **`KernelModeled::rec_family_block` specification**: extracts the inductive block `ib`, the
motive-0 carrier `t0`, and proves both that `t0` is a motive-0 carrier of the recursor record
(giving `UsedRef` for `.rPrj` blocks and determinism across calls!) and that `ib` has an `.indc`
member. -/
theorem rec_family_block_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {x : _root_.Address} {x_rec r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hx : S0.addr h x_rec x)
    (ev : ObsFn Obs.W "KernelModeled::rec_family_block" [x_rec] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      ∃ (cx : Ixon.Constant) (ib_b : Bytes.Address) (cib : Ixon.Constant)
        (ms : Array Ixon.MutConst) (j : UInt64) (ind : Ixon.Inductive)
        (t0 : _root_.Address) (ct0 : Ixon.Constant),
        recordOf E₀ x = some cx ∧
        Bytes.RepAddressRef Core.addrTy h' ib_b r ∧
        recordOf E₀ (Core.ixAddr ib_b) = some cib ∧ cib.info = .muts ms ∧
        ms[j.toNat]? = some (.indc ind) ∧
        recordOf E₀ t0 = some ct0 ∧ ct0.info = .iPrj ⟨j, Core.ixAddr ib_b⟩ ∧
        ((∃ rc n, cx.info = .recr rc ∧ Binding.FamilyOf.motiveCarrierAt cx rc 0 n = some t0) ∨
          (∃ idx a ca rs rc n, cx.info = .rPrj ⟨idx, a⟩ ∧ recordOf E₀ a = some ca ∧
            ca.info = .muts rs ∧ rs[idx.toNat]? = some (.recr rc) ∧
            Binding.FamilyOf.motiveCarrierAt ca rc 0 n = some t0 ∧ UsedRef E₀ a t0)) := by
  obtain ⟨ab, hab, rfl⟩ := hx
  match Obs.«KernelModeled::rec_family_block».obs ev with
  | .run (cs16 := cs16) (cs174 := cs174) (cs196 := cs196) (cs266 := cs266)
      (ev18 := ev_ci) (ld12 := ld_rec) (ev110 := ev_peel) (ld138 := ld_for)
      (ev176 := ev_ldom) (ev198 := ev_sp) (ld232 := ld_const) (ev268 := ev_ci_t0)
      (ld262 := ld_ind) (he331 := hr) (he332 := hh) (hc333 := hc) .. =>
    have hsub16 : ∀ cl ∈ cs16, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    have hsub266 : ∀ cl ∈ cs266, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨rawX, cx, hlenX, hhX, haddrX, hexactX, -, -⟩ := Claim.get_ci_head hab ev_ci
    have hcx : recordOf E₀ (Core.ixAddr ab) = some cx :=
      Claim.recordOf_of_hashed hcov (Claim.hashed_mono hsub16 hhX) hlenX
        (by rw [haddrX]; exact hexactX)
    have hrec_raw := get_ci_of_rec_raw_uncond hS hcov hab ev_ci hsub16 ld_rec hcx
    -- Factor out the common motive-0 carrier extraction given `L1.RawRecrValRep`
    have extract_carrier : ∀ {cHost : Ixon.Constant} {recurAddrs : List _root_.Address}
        {rc : Ixon.Recursor} {blkAddr : _root_.Address} {recIdx : Nat}
        {blobs : List (_root_.Address × ByteArray)},
        L1.RawRecrValRep cHost.refs.toList recurAddrs cHost.univs.toList cHost.sharing.toList
          blobs _ rc blkAddr recIdx _ →
        ∃ (n : Nat) (t0_b : Bytes.Address),
          Binding.FamilyOf.motiveCarrierAt cHost rc 0 n = some (Core.ixAddr t0_b) ∧
          Bytes.RepAddressRef Core.addrTy _ t0_b _ := by
      intro cHost recurAddrs rc blkAddr recIdx blobs hraw
      obtain ⟨-, hnp56, -, -, -, -, tyPtr, rulesPtr, blkPtr, _, -, -, hv_eq, rawTy, -⟩ := hraw
      injection hv_eq with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨_, rfl, rfl, _⟩ := hargs
      obtain ⟨hm98, -, b1, e1, hpeel, raw1⟩ := peel_n_foralls_raw rc.params.toNat hnp56 rawTy ev_peel
      subst hm98
      obtain ⟨b2, em, -, hnd1, raw_m, -⟩ := rawConvExpr_forall_inv raw1 ld_for
      obtain ⟨hm164, -, n1, b3, ed, hldom, raw_d⟩ :=
        last_binder_dom_raw_aux cs174.length (Nat.le_refl _) raw_m ev_ldom
      subst hm164
      obtain ⟨ext_sp, -, n2, b4, raw_hd, hns_hd⟩ :=
        collect_spine_raw_aux cs196.length (Nat.le_refl _) raw_d ev_sp
      obtain ⟨rIdx, uIdxs, t0, t0_b, hnd_hd, href_t0, hix_t0, ht0_rep⟩ :=
        rawConvExpr_const_inv raw_hd ld_const
      rw [node_of_not_share hns_hd] at hnd_hd
      -- Match fuel `n := max n1 n2`? Even cleaner: `lastDom` and `spineHead` are monotone in fuel!
      -- Prove fuel monotonicity for `lastDom` and `spineHead` right here.
      have hldom_mono : ∀ k₁ k₂ e d, k₁ ≤ k₂ →
          Binding.FamilyOf.lastDom cHost k₁ e = some d →
          Binding.FamilyOf.lastDom cHost k₂ e = some d := by
        intro k₁
        induction k₁ with
        | zero => intro _ _ _ _ h; simp [Binding.FamilyOf.lastDom] at h
        | succ k₁ ih =>
          intro k₂ e d hle h
          obtain ⟨k₂', rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
          unfold Binding.FamilyOf.lastDom at h ⊢
          cases hnd : Binding.FamilyOf.node cHost e with
          | all d' b' =>
            rw [hnd] at h ⊢; dsimp only at h ⊢
            cases hb' : Binding.FamilyOf.node cHost b' with
            | all _ _ =>
              rw [hb'] at h ⊢
              exact ih k₂' b' d (by omega) h
            | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _
            | lam _ _ | letE _ _ _ _ _ | share _ =>
              rw [hb'] at h ⊢; exact h
          | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _
          | lam _ _ | letE _ _ _ _ _ | share _ =>
            rw [hnd] at h; cases h
      have hsp_mono : ∀ k₁ k₂ e, k₁ ≤ k₂ →
          (∀ f a, Binding.FamilyOf.spineHead cHost k₁ e ≠ .app f a) →
          Binding.FamilyOf.spineHead cHost k₂ e = Binding.FamilyOf.spineHead cHost k₁ e := by
        intro k₁
        induction k₁ with
        | zero =>
          intro k₂ e _ hne
          simp only [Binding.FamilyOf.spineHead] at hne ⊢
          cases k₂ with
          | zero => rfl
          | succ k₂' =>
            unfold Binding.FamilyOf.spineHead
            cases hnd : Binding.FamilyOf.node cHost e with
            | app f a => exact (hne f a hnd).elim
            | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _
            | all _ _ | letE _ _ _ _ _ | share _ => rfl
        | succ k₁ ih =>
          intro k₂ e hle hne
          obtain ⟨k₂', rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
          unfold Binding.FamilyOf.spineHead at hne ⊢
          cases hnd : Binding.FamilyOf.node cHost e with
          | app f a =>
            rw [hnd] at hne ⊢
            exact ih k₂' f (by omega) hne
          | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _
          | all _ _ | letE _ _ _ _ _ | share _ =>
            rw [hnd]
      let nf := max n1 n2
      have hldom_nf := hldom_mono n1 nf em ed (Nat.le_max_left _ _) hldom
      have hsp_nf : Binding.FamilyOf.spineHead cHost nf ed = .ref rIdx uIdxs := by
        rw [hsp_mono n2 nf ed (Nat.le_max_right _ _) (by rw [hnd_hd]; intro _ _ h; cases h), hnd_hd]
      have hmot : Binding.FamilyOf.motiveCarrierAt cHost rc 0 nf = some (Core.ixAddr t0_b) := by
        unfold Binding.FamilyOf.motiveCarrierAt
        rw [Nat.add_zero, hpeel]
        simp only [bind, Option.bind, Binding.FamilyOf.domOf, hnd1, hldom_nf,
          Binding.FamilyOf.refHeadAt, hsp_nf, ← hix_t0]
        exact href_t0
      exact ⟨nf, t0_b, hmot, ht0_rep⟩
    rcases get_ci_loads_rec_is_recr_or_rPrj hS hab ev_ci hsub16 ld_rec hcx with
      ⟨rc, hrc⟩ | ⟨⟨idx, a⟩, hrprj⟩
    · obtain ⟨blobs, hraw⟩ := hrec_raw.1 rc hrc
      obtain ⟨nf, t0_b, hmot, ht0_rep⟩ := extract_carrier hraw
      obtain ⟨ct0, j, blk, ib_b, cib, ms, ind, hct0, hct0_info, hib_rep, hib_eq, hcib, hms, hmj⟩ :=
        get_ci_loads_induct_is_iprj hS hcov ht0_rep ev_ci_t0 hsub266 ld_ind
      subst hr hh hib_eq
      exact ⟨ev_ci.heap_extends.trans (ev_peel.heap_extends.trans (ev_ldom.heap_extends.trans
        (ev_sp.heap_extends.trans ev_ci_t0.heap_extends))),
        cx, ib_b, cib, ms, j, ind, Core.ixAddr t0_b, ct0, hcx, hib_rep, hcib, hms, hmj,
        hct0, hct0_info, Or.inl ⟨rc, nf, hrc, hmot⟩⟩
    · obtain ⟨ca, rs, rc, blobs, hca, hca_muts, hca_k, hraw⟩ := hrec_raw.2 idx a hrprj
      obtain ⟨nf, t0_b, hmot, ht0_rep⟩ := extract_carrier hraw
      obtain ⟨ct0, j, blk, ib_b, cib, ms, ind, hct0, hct0_info, hib_rep, hib_eq, hcib, hms, hmj⟩ :=
        get_ci_loads_induct_is_iprj hS hcov ht0_rep ev_ci_t0 hsub266 ld_ind
      subst hr hh hib_eq
      have hu_t0 : UsedRef E₀ a (Core.ixAddr t0_b) :=
        motiveCarrierAt_usedRef hca hca_muts hca_k hmot
      exact ⟨ev_ci.heap_extends.trans (ev_peel.heap_extends.trans (ev_ldom.heap_extends.trans
        (ev_sp.heap_extends.trans ev_ci_t0.heap_extends))),
        cx, ib_b, cib, ms, j, ind, Core.ixAddr t0_b, ct0, hcx, hib_rep, hcib, hms, hmj,
        hct0, hct0_info, Or.inr ⟨idx, a, ca, rs, rc, nf, hrprj, hca, hca_muts, hca_k, hmot, hu_t0⟩⟩

private theorem motiveCarrierAt_unique (c : Ixon.Constant) (rc : Ixon.Recursor) (i n₁ n₂ : Nat)
    {a₁ a₂ : _root_.Address}
    (h1 : Binding.FamilyOf.motiveCarrierAt c rc i n₁ = some a₁)
    (h2 : Binding.FamilyOf.motiveCarrierAt c rc i n₂ = some a₂) : a₁ = a₂ := by
  unfold Binding.FamilyOf.motiveCarrierAt at h1 h2
  cases hp : Binding.FamilyOf.peel c (rc.params.toNat + i) rc.typ with
  | none => rw [hp] at h1; simp at h1
  | some e =>
    rw [hp] at h1 h2; dsimp only [bind, Option.bind] at h1 h2
    cases hd : Binding.FamilyOf.domOf c e with
    | none => rw [hd] at h1; simp at h1
    | some m =>
      rw [hd] at h1 h2; dsimp only [bind, Option.bind] at h1 h2
      cases hl1 : Binding.FamilyOf.lastDom c n₁ m with
      | none => rw [hl1] at h1; simp at h1
      | some d₁ =>
        cases hl2 : Binding.FamilyOf.lastDom c n₂ m with
        | none => rw [hl2] at h2; simp at h2
        | some d₂ =>
          have hd_eq : d₁ = d₂ := lastDom_unique c n₁ n₂ hl1 hl2
          subst hd_eq
          rw [hl1] at h1; rw [hl2] at h2; dsimp only [bind, Option.bind] at h1 h2
          unfold Binding.FamilyOf.refHeadAt at h1 h2
          have hna1 : ∀ f a, Binding.FamilyOf.spineHead c n₁ d₁ ≠ .app f a := by
            intro f a he; rw [he] at h1; cases h1
          have hna2 : ∀ f a, Binding.FamilyOf.spineHead c n₂ d₁ ≠ .app f a := by
            intro f a he; rw [he] at h2; cases h2
          have hsp_eq := spineHead_unique c n₁ n₂ hna1 hna2
          rw [hsp_eq] at h1
          exact Option.some.inj (h1.symm.trans h2)

/-- **`KernelModeled::rec_family_block` is deterministic** in the run's store: two calls on the
same recursor address return the same family block address. -/
theorem rec_family_block_det {calls cs₁ cs₂ : List (Call F)} {E₀ : Ixon.Env}
    {x ib₁ ib₂ : _root_.Address} {xa₁ xa₂ r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hx₁ : S0.addr h₁ xa₁ x) (hx₂ : S0.addr h₂ xa₂ x)
    (ev₁ : ObsFn Obs.W "KernelModeled::rec_family_block" [xa₁] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn Obs.W "KernelModeled::rec_family_block" [xa₂] h₂ r₂ h₂' cs₂)
    (hsub₁ : ∀ cl ∈ cs₁, cl ∈ calls) (hsub₂ : ∀ cl ∈ cs₂, cl ∈ calls)
    (hr₁ : S0.addr h₁' r₁ ib₁) (hr₂ : S0.addr h₂' r₂ ib₂) :
    ib₁ = ib₂ := by
  obtain ⟨-, cx₁, ib_b₁, -, -, j₁, -, t0₁, ct0₁, hcx₁, hib₁_rep, -, -, -, hct0₁, hct0₁_info, hk₁⟩ :=
    rec_family_block_spec hS hcov hx₁ ev₁ hsub₁
  obtain ⟨-, cx₂, ib_b₂, -, -, j₂, -, t0₂, ct0₂, hcx₂, hib₂_rep, -, -, -, hct0₂, hct0₂_info, hk₂⟩ :=
    rec_family_block_spec hS hcov hx₂ ev₂ hsub₂
  have hcx_eq : cx₁ = cx₂ := Option.some.inj (hcx₁.symm.trans hcx₂)
  subst cx₂
  have ht0_eq : t0₁ = t0₂ := by
    rcases hk₁ with ⟨rc₁, n₁, hinfo₁, hmot₁⟩ | ⟨idx₁, a₁, ca₁, rs₁, rc₁, n₁, hinfo₁, hca₁, hms₁, hmk₁, hmot₁, -⟩
    · rcases hk₂ with ⟨rc₂, n₂, hinfo₂, hmot₂⟩ | ⟨_, _, _, _, _, _, hinfo₂, -⟩
      · have hrc : rc₁ = rc₂ := Ixon.ConstantInfo.recr.inj (hinfo₁.symm.trans hinfo₂)
        subst rc₂
        exact motiveCarrierAt_unique cx₁ rc₁ 0 n₁ n₂ hmot₁ hmot₂
      · rw [hinfo₁] at hinfo₂; cases hinfo₂
    · rcases hk₂ with ⟨_, _, hinfo₂, -⟩ | ⟨idx₂, a₂, ca₂, rs₂, rc₂, n₂, hinfo₂, hca₂, hms₂, hmk₂, hmot₂, -⟩
      · rw [hinfo₁] at hinfo₂; cases hinfo₂
      · have hp := Ixon.ConstantInfo.rPrj.inj (hinfo₁.symm.trans hinfo₂)
        injection hp with hidx_eq ha_eq
        subst hidx_eq ha_eq
        have hca_eq : ca₁ = ca₂ := Option.some.inj (hca₁.symm.trans hca₂)
        subst ca₂
        have hrs_eq : rs₁ = rs₂ := Ixon.ConstantInfo.muts.inj (hms₁.symm.trans hms₂)
        subst rs₂
        have hrc_eq : rc₁ = rc₂ := Ixon.MutConst.recr.inj (Option.some.inj (hmk₁.symm.trans hmk₂))
        subst rc₂
        exact motiveCarrierAt_unique ca₁ rc₁ 0 n₁ n₂ hmot₁ hmot₂
  subst t0₂
  have hct_eq : ct0₁ = ct0₂ := Option.some.inj (hct0₁.symm.trans hct0₂)
  subst ct0₂
  have hib_eq : Core.ixAddr ib_b₁ = Core.ixAddr ib_b₂ := by
    have hp := Ixon.ConstantInfo.iPrj.inj (hct0₁_info.symm.trans hct0₂_info)
    injection hp
  obtain ⟨b1, hb1, rfl⟩ := hr₁
  obtain ⟨b2, hb2, rfl⟩ := hr₂
  have heq1 : b1 = ib_b₁ := Bytes.repAddressRef_inj hb1 hib₁_rep
  have heq2 : b2 = ib_b₂ := Bytes.repAddressRef_inj hb2 hib₂_rep
  rw [heq1, heq2]
  exact hib_eq

private theorem is_muts_block_of_muts {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {x_a r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (ha : S0.addr h x_a a)
    (hc : recordOf E₀ a = some c) (hms : c.info = .muts ms)
    (ev : ObsFn Obs.W "KernelCheck::is_muts_block" [x_a] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧ r = .field 1 := by
  match Obs.«KernelCheck::is_muts_block».obs ev with
  | .Muts (ev14 := ev14) (he90 := hr) (he91 := hh) .. =>
    exact ⟨hh ▸ ev14.heap_extends, hr⟩
  | .other (cs12 := cs12) (ev14 := ev14) (hne93 := hne) (hc99 := hcs) .. =>
    exfalso
    obtain ⟨-, _, c', -, hh, haddr, -, hexact, hrep, -⟩ := Claim.load_verified_constant_de ha ev14
    have hcc : c' = c :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
        (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])) hh) haddr hexact
    subst c'
    obtain ⟨infoVal, _, _, _, _, hmk, hinfo, -, -, -, -⟩ := hrep
    rw [hms] at hinfo
    obtain ⟨mv, hmv, -⟩ := hinfo
    injection hmk with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1] at hmv
    exact hne [mv] rfl hmv

private theorem peel_n_foralls_raw_any {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr} :
    ∀ (m : Nat) {blobs : List (_root_.Address × ByteArray)} {e : Ixon.Expr}
      {h h' : Heap F} {x_e x_n r : SourceValue F} {cs : List (Call F)},
      cs.length ≤ m →
      L1.RawConvExpr refs recurAddrs univs sharing blobs h e x_e →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [x_e, x_n] h r h' cs →
      h' = h ∧ ∃ blobs' e', L1.RawConvExpr refs recurAddrs univs sharing blobs' h e' r
  | 0, blobs, e, h, h', x_e, x_n, r, cs, hlen, hraw, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, blobs, e, hraw⟩
    | .other (hc83 := hc) .. => simp [hc] at hlen
  | m + 1, blobs, e, h, h', x_e, x_n, r, cs, hlen, hraw, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, blobs, e, hraw⟩
    | .other (cs59 := cs59) (ld51 := hld) (ev61 := ev_rec) (hc83 := hc) .. =>
      have hlen' : cs59.length ≤ m := by
        rw [hc] at hlen; simp only [List.length_cons] at hlen; omega
      obtain ⟨blobs1, _, body, -, -, rawBody⟩ := rawConvExpr_forall_inv hraw hld
      exact peel_n_foralls_raw_any m hlen' rawBody ev_rec

/-- **`KernelCheck::check_const` on any recursor projection record `.rPrj ⟨idx, a⟩` takes the
modeled `Rec_other` arm**: `a` is a `RecBlock`, `block_is_modeled` answers non-zero on its family
inductive block `ib`, `check_family [rc, ib, a]` runs inside `check_const`, and `a` uses `t0`
(an `.iPrj` of `ib`). Reused by both `BatchGives.contWitness` and `BatchGives.recArm`. -/
theorem rprj_check_const_rec_other {calls cs₁ cs₂ : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr x a : _root_.Address} {lim : Option Nat}
    {cx : Ixon.Constant} {idx : UInt64}
    {rc xx ptr v_ci r : SourceValue F} {h h₁ h₂ : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hx : S0.addr h xx x)
    (hcx : recordOf E₀ x = some cx) (hrprj : cx.info = .rPrj ⟨idx, a⟩)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [xx] h ptr h₁ cs₁)
    (hld : loadValue h₁ ptr = .ok v_ci)
    (ev_chk : ObsFn Obs.W "KernelCheck::check_const" [rc, v_ci, xx] h₁ r h₂ cs₂)
    (hsub₁ : ∀ cl ∈ cs₁, cl ∈ calls) (hsub₂ : ∀ cl ∈ cs₂, cl ∈ calls) :
    RecBlock E₀ a ∧
      ∃ (ca : Ixon.Constant) (ib t0 : _root_.Address) (cib ct0 : Ixon.Constant)
        (ms_ib : Array Ixon.MutConst) (j : UInt64) (ind : Ixon.Inductive)
        (cs_fam : List (Call F))
        (m_bm m_bm' : Heap F) (xb_bm v_bm : SourceValue F) (cs_bm : List (Call F)),
        recordOf E₀ a = some ca ∧ ConstAddrOf a ca x ∧
        recordOf E₀ ib = some cib ∧ cib.info = .muts ms_ib ∧ ms_ib[j.toNat]? = some (.indc ind) ∧
        recordOf E₀ t0 = some ct0 ∧ ct0.info = .iPrj ⟨j, ib⟩ ∧ UsedRef E₀ a t0 ∧
        (∃ m_rfb m_rfb' r_rfb cs_rfb, S0.addr m_rfb xx x ∧ S0.addr m_rfb' r_rfb ib ∧
          ObsFn Obs.W "KernelModeled::rec_family_block" [xx] m_rfb r_rfb m_rfb' cs_rfb ∧
          ∀ cl ∈ cs_rfb, cl ∈ cs₂) ∧
        Heap.Extends h₁ m_bm ∧ S0.addr m_bm xb_bm ib ∧
        ObsFn Obs.W "KernelModeled::block_is_modeled" [xb_bm] m_bm v_bm m_bm' cs_bm ∧
        v_bm ≠ .field 0 ∧ (∀ cl ∈ cs_bm, cl ∈ cs₂) ∧
        FamilyCallAtLim calls bAddr t ib a lim cs_fam ∧ (∀ cl ∈ cs_fam, cl ∈ cs₂) := by
  obtain ⟨ab, hab, rfl⟩ := hx
  obtain ⟨rawX, cx', -, hhX, haddrX, hexactX, -, hhead⟩ := Claim.get_ci_head hab ev_ci
  have hcc : cx' = cx :=
    hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcx)
      (Claim.hashed_mono hsub₁ hhX) haddrX hexactX
  subst cx'
  obtain ⟨ca, rs, rc_m, hbl, hmem_rc, _, _, _, _, _, _, _, _, x_blk, b_a, hld_rec, hba_rep, hba_eq⟩ :=
    hhead.rPrj idx a hrprj
  have hv_eq : v_ci = .construct "KernelTypes::KConstantInfo" "Rec" _ :=
    Except.ok.inj (hld.symm.trans hld_rec)
  obtain ⟨hca, hca_muts⟩ := (hbl.mono hsub₁).stored hcov
  have hmem_arr : rs[idx.toNat]? = some (.recr rc_m) := by
    rw [← Array.getElem?_toList]; exact hmem_rc
  have hca_pos : 0 < rs.size := by
    have := (Array.getElem?_eq_some_iff.mp hmem_arr).1; omega
  have hca_const : ConstAddrOf a ca (Core.ixAddr ab) := by
    obtain ⟨ca', hca', hca_of⟩ :=
      Claim.proj_member_of_load hS hcov hab ev_ci hsub₁ hcx
        (Or.inr (Or.inr (Or.inr ⟨⟨idx, a⟩, hrprj⟩)))
    have hown : Ix.Cert.ownerOf (Core.ixAddr ab) cx = a := by simp [Ix.Cert.ownerOf, hrprj]
    rw [hown] at hca' hca_of
    have e : ca' = ca := Option.some.inj (hca'.symm.trans hca)
    subst e; exact hca_of
  have ext_ci := ev_ci.heap_extends
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom (hv22 := hv) .. | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
  | .Induct_other_other (hv1240 := hv) ..
  | .Ctor_n0 (hv1989 := hv) .. | .Ctor_other_n0 (hv1989 := hv) ..
  | .Ctor_other_other (hv1989 := hv) .. =>
    rw [hv_eq] at hv; exact absurd (Value.construct.inj hv).2.1 (by decide)
  | .Rec_n0 (cs2940 := cs_cbk) (cs3066 := cs_crm) (hv2727 := hv)
      (ev14 := e1) (ev2801 := e2) (hm2865 := hm) (ev2838 := e3) (ev2882 := e4)
      (ev2912 := e5) (ev2942 := ev_cbk) (ev2964 := ev_rfb) (ev2986 := ev_bm)
      (ev3068 := ev_crm) (hc3093 := hc) .. =>
    exfalso
    rw [hv_eq] at hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    have hx_rb : x_blk = _ := hargs.2.2.2.2.2.2.2.2.2.1
    have ext_cbk : Heap.Extends h₁ _ :=
      e1.heap_extends.trans (e2.heap_extends.trans ((hm ▸ Heap.Extends.snoc _ _).trans
        (e3.heap_extends.trans (e4.heap_extends.trans e5.heap_extends))))
    have hrec_a_at : Ix.Cert.recordAt E₀ a = some ca :=
      (hS.recordOf_eq_recordAt a).symm.trans hca
    have hunif := Claim.check_block_member_kinds_uniform hS hrec_a_at hca_muts
      ⟨b_a, hx_rb ▸ Bytes.repAddressRef_heapMono₂ Core.addrTy ext_cbk hba_rep, hba_eq⟩
      ev_cbk (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl]))
    have hall_rec : ∀ m ∈ rs.toList, ∃ r, m = .recr r := by
      rcases hunif with hd | hi | hr
      · obtain ⟨d, hd⟩ := hd (.recr rc_m) (List.mem_of_getElem? hmem_rc); cases hd
      · obtain ⟨i, hi⟩ := hi (.recr rc_m) (List.mem_of_getElem? hmem_rc); cases hi
      · exact hr
    -- Inside `check_recursor_member`, `is_muts_block` on both `a` and `parent_blk` answers 1,
    -- forcing `a = parent_blk`, which contradicts `parent_blk` having an `.indc` member!
    match Obs.«KernelCheck::check_recursor_member».obs ev_crm with
    | .run (cs140 := cs_p) (cs276 := cs_m1) (cs290 := cs_m2) (hv15 := hv_crm)
        (ev85 := ev_r2p) (ev142 := ev_ci_p) (ld136 := ld_p) (ev233 := ev_bm_p)
        (ev278 := ev_m1) (ev292 := ev_m2) (op272 := op_mul1) (ev314 := ev_aeq)
        (op308 := op_sub) (op264 := op_mul2) (heq357 := h0) (hc898 := hc_crm) .. =>
      rw [hv_eq] at hv_crm
      injection hv_crm with _ _ hargs'
      simp only [List.cons.injEq, and_true] at hargs'
      have hx_rb' : x_blk = _ := hargs'.2.2.2.2.2.2.2.2.2.1
      have ext_to_crm := ext_cbk.trans (ev_cbk.heap_extends.trans
        (ev_rfb.heap_extends.trans ev_bm.heap_extends))
      have hv72_addr : ∃ b72 : Bytes.Address, Bytes.RepAddressRef Core.addrTy _ b72 _ := by
        obtain ⟨ca', rs', rc', blobs', -, -, -, hraw_rec⟩ :=
          (get_ci_of_rec_raw_uncond hS hcov hab ev_ci hsub₁ hld hcx).2 idx a hrprj
        obtain ⟨-, -, -, -, -, -, tyPtr, _, _, _, -, -, hv_raw, rawTy, -⟩ := hraw_rec
        rw [hv_eq] at hv_raw
        injection hv_raw with _ _ hargs_r
        simp only [List.cons.injEq, and_true] at hargs_r
        have hty_eq : tyPtr = _ := hargs_r.2.1.symm.trans hargs'.2.1
        rw [hty_eq] at rawTy
        have rawTy_crm := L1.rawConvExpr_heapMono ext_to_crm rawTy
        match Obs.«KernelCheck::rec_to_parent_addr».obs ev_r2p with
        | .run (cs48 := cs48) (cs115 := cs115) (ev50 := ev_peel) (ld78 := ld_for)
            (ev117 := ev_sp) (ld154 := ld_const) (he174 := hr_r2p) (he175 := hh_r2p) .. =>
          obtain ⟨hm38, _, _, raw1⟩ :=
            peel_n_foralls_raw_any cs48.length (Nat.le_refl _) rawTy_crm ev_peel
          subst hm38
          obtain ⟨_, _, _, -, rawMaj, -⟩ := rawConvExpr_forall_inv raw1 ld_for
          obtain ⟨-, -, _, _, rawHd, -⟩ :=
            collect_spine_raw_aux cs115.length (Nat.le_refl _) rawMaj ev_sp
          obtain ⟨_, _, _, t0_b, -, -, -, ht0_rep⟩ := rawConvExpr_const_inv rawHd ld_const
          subst hr_r2p hh_r2p
          exact ⟨t0_b, ht0_rep⟩
      obtain ⟨b72, hb72⟩ := hv72_addr
      obtain ⟨-, j_p, blk_p, b_p, cp, msp, indp, -, -, hbp_rep, hbp_eq, hcp, hmsp, hmj⟩ :=
        get_ci_loads_induct_is_iprj hS hcov hb72 ev_ci_p
          (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hc_crm, hcl])) ld_p
      subst hbp_eq
      have ext_m1 := ext_to_crm.trans (ev_r2p.heap_extends.trans
        (ev_ci_p.heap_extends.trans ev_bm_p.heap_extends))
      have ha_m1 : Bytes.RepAddressRef Core.addrTy _ b_a _ :=
        hx_rb' ▸ Bytes.repAddressRef_heapMono₂ Core.addrTy ext_m1 hba_rep
      obtain ⟨ext_m1', hm1_eq⟩ :=
        is_muts_block_of_muts hS ⟨b_a, ha_m1, hba_eq⟩ hca hca_muts ev_m1
          (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hc_crm, hcl]))
      have hp_m2 := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (ev_bm_p.heap_extends.trans ext_m1') hbp_rep
      obtain ⟨ext_m2', hm2_eq⟩ :=
        is_muts_block_of_muts hS ⟨b_p, hp_m2, rfl⟩ hcp hmsp ev_m2
          (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hc_crm, hcl]))
      obtain ⟨haeq, -⟩ := Lib.address_eq_spec ev_aeq
        (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_m1'.trans ext_m2') ha_m1)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_m2' hp_m2)
      have hba_bp : b_a = b_p := by
        by_cases he : b_a = b_p
        · exact he
        · rw [ite_eq_right he] at haeq
          rw [hm1_eq, hm2_eq] at op_mul1
          simp only [evalBinOp, mul_one, Except.ok.injEq] at op_mul1
          subst op_mul1
          rw [haeq] at op_sub
          simp only [evalBinOp, sub_zero, Except.ok.injEq] at op_sub
          subst op_sub
          simp only [evalBinOp, mul_one, Except.ok.injEq] at op_mul2
          exact absurd (Value.field.inj (op_mul2.symm.trans h0)) one_ne_zero
      subst hba_bp
      rw [hba_eq] at hcp
      have hcp_eq : cp = ca := Option.some.inj (hcp.symm.trans hca)
      subst cp
      have hmsp_eq : msp = rs := Ixon.ConstantInfo.muts.inj (hmsp.symm.trans hca_muts)
      subst msp
      have hmem_ind : .indc indp ∈ rs.toList := by
        rw [← Array.getElem?_toList] at hmj
        exact List.mem_of_getElem? hmj
      obtain ⟨r', hr'⟩ := hall_rec (.indc indp) hmem_ind
      cases hr'
  | .Rec_other (cs2940 := cs_cbk) (cs2962 := cs_rfb) (cs2984 := cs_bm) (cs3155 := cs_fam)
      (hv2727 := hv) (ev14 := e1) (ev2801 := e2) (hm2865 := hm) (ev2838 := e3)
      (ev2882 := e4) (ev2912 := e5) (ev2942 := ev_cbk) (ev2964 := ev_rfb)
      (ev2986 := ev_bm) (hne3094 := hbm_ne0) (ev3157 := ev_cf) (hc3182 := hc) .. =>
    rw [hv_eq] at hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    have hx_rb : x_blk = _ := hargs.2.2.2.2.2.2.2.2.2.1
    have ext_cbk : Heap.Extends h₁ _ :=
      e1.heap_extends.trans (e2.heap_extends.trans ((hm ▸ Heap.Extends.snoc _ _).trans
        (e3.heap_extends.trans (e4.heap_extends.trans e5.heap_extends))))
    have hrec_a_at : Ix.Cert.recordAt E₀ a = some ca :=
      (hS.recordOf_eq_recordAt a).symm.trans hca
    have hunif := Claim.check_block_member_kinds_uniform hS hrec_a_at hca_muts
      ⟨b_a, hx_rb ▸ Bytes.repAddressRef_heapMono₂ Core.addrTy ext_cbk hba_rep, hba_eq⟩
      ev_cbk (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl]))
    have hall_rec : ∀ m ∈ rs.toList, ∃ r, m = .recr r := by
      rcases hunif with hd | hi | hr
      · obtain ⟨d, hd⟩ := hd (.recr rc_m) (List.mem_of_getElem? hmem_rc); cases hd
      · obtain ⟨i, hi⟩ := hi (.recr rc_m) (List.mem_of_getElem? hmem_rc); cases hi
      · exact hr
    have hRB : RecBlock E₀ a := ⟨ca, rs, hca, hca_muts, hca_pos, hall_rec⟩
    have ext_to_rfb := ext_cbk.trans ev_cbk.heap_extends
    obtain ⟨ext_rfb, cx₂, ib_b, cib, ms_ib, j, ind, t0, ct0, hcx₂, hib_rep, hcib, hms_ib, hmj,
        hct0, hct0_info, hk_rfb⟩ :=
      rec_family_block_spec hS hcov
        ⟨ab, Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_ci.trans ext_to_rfb) hab, rfl⟩
        ev_rfb (fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl]))
    have hcx₂_eq : cx₂ = cx := Option.some.inj (hcx₂.symm.trans hcx)
    subst cx₂
    have hu_t0 : UsedRef E₀ a t0 := by
      rcases hk_rfb with ⟨_, _, hbad, -⟩ | ⟨_, a', _, _, _, _, hrprj', -, -, -, -, hu⟩
      · rw [hrprj] at hbad; cases hbad
      · have hp := Ixon.ConstantInfo.rPrj.inj (hrprj.symm.trans hrprj')
        injection hp with _ ha_eq; subst ha_eq; exact hu
    have ext_to_bm := ext_to_rfb.trans ext_rfb
    have ext_to_cf := ext_to_bm.trans ev_bm.heap_extends
    have hfc : FamilyCallAtLim calls bAddr t (Core.ixAddr ib_b) a lim cs_fam :=
      ⟨_, _, rc, _, _, r,
        hrc.mono (ext_ci.trans ext_to_cf),
        ⟨ib_b, Bytes.repAddressRef_heapMono₂ Core.addrTy ev_bm.heap_extends hib_rep, rfl⟩,
        ⟨b_a, hx_rb ▸ Bytes.repAddressRef_heapMono₂ Core.addrTy ext_to_cf hba_rep, hba_eq⟩,
        ev_cf,
        hsub₂ _ (by rw [hc]; simp),
        fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl])⟩
    exact ⟨hRB, ca, Core.ixAddr ib_b, t0, cib, ct0, ms_ib, j, ind, cs_fam,
      _, _, _, _, cs_bm, hca, hca_const, hcib, hms_ib, hmj, hct0, hct0_info, hu_t0,
      ⟨_, _, _, cs_rfb,
        ⟨ab, Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_ci.trans ext_to_rfb) hab, rfl⟩,
        ⟨ib_b, hib_rep, rfl⟩, ev_rfb, fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl])⟩,
      ext_to_bm, ⟨ib_b, hib_rep, rfl⟩, ev_bm, hbm_ne0,
      fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl]),
      hfc, fun cl hcl => hsub₂ cl (by rw [hc]; simp [hcl])⟩

private theorem container_refs_ok_spec {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀)
    {ib : _root_.Address} {cib : Ixon.Constant} {irefs : List Bytes.Address}
    {Wset : List _root_.Address} {idxs : List Nat}
    (hib : recordOf K.E₀ ib = some cib)
    (hilen : irefs.length < 72057594037927936)
    (himap : irefs.map Core.ixAddr = cib.refs.toList) :
    ∀ {refs : List Bytes.Address} {i : Nat}
      {x_rc x_refs x_used x_self x_iblk x_irefs x_iused x_wset r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      i + refs.length < 72057594037927936 →
      Claim.RCLimRep K.t K.bAddr K.lim h x_rc →
      S0.addr h x_iblk ib →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h refs x_refs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs x_used →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h irefs x_irefs →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (S0.usedRefIdxs cib) x_iused →
      Claim.RepAddrSet h Wset x_wset →
      ObsFn Obs.W "KernelModeled::container_refs_ok"
        [x_rc, x_refs, x_used, .field (i : F), x_self, x_iblk, x_irefs, x_iused, x_wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ K.calls) →
      Heap.Extends h h' ∧
        ∀ k q, refs[k]? = some q → (i + k) ∈ idxs →
          K.BlockRef ib (Core.ixAddr q) ∨
            (Core.ixAddr q ∈ Wset ∧
              ∃ cq, recordOf K.E₀ (Core.ixAddr q) = some cq ∧
                (∀ rcr, cq.info ≠ .recr rcr) ∧ (∀ p, cq.info ≠ .rPrj p))
  | [], i, x_rc, x_refs, x_used, x_self, x_iblk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hbound, hrc, hiblk, hrefs, hused, hirefs, hiused, hwset, ev, hsub => by
    match Obs.«KernelModeled::container_refs_ok».obs ev with
    | .Nil (he23 := hh) .. => exact ⟨hh ▸ Heap.Extends.refl _, fun _ _ hq => by simp at hq⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld; cases hbad
  | q :: rest, i, x_rc, x_refs, x_used, x_self, x_iblk, x_irefs, x_iused, x_wset, r, h, h', cs,
      hbound, hrc, hiblk, hrefs, hused, hirefs, hiused, hwset, ev, hsub => by
    have hi : i < 72057594037927936 := by simp at hbound; omega
    match Obs.«KernelModeled::container_refs_ok».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrefs ld
    | .Cons (m385 := m385) (ld12 := ld) (sg392 := sg) (op_gskedpnl := op) (ev398 := ev_rest) (hc463 := hc) .. =>
      obtain ⟨q', rest', heq, hq, hrest⟩ := Lib.rep_cons_of_load hrefs ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨b_ib, hb_ib, hix_ib⟩ := hiblk
      have hseg : Heap.Extends h m385 ∧
          (i ∈ idxs → K.BlockRef ib (Core.ixAddr q) ∨
            (Core.ixAddr q ∈ Wset ∧
              ∃ cq, recordOf K.E₀ (Core.ixAddr q) = some cq ∧
                (∀ rcr, cq.info ≠ .recr rcr) ∧ (∀ p, cq.info ≠ .rPrj p))) := by
        match sg with
        | .other (ev56 := ev56) (hne375 := hne1) (he382 := hh) .. =>
          obtain ⟨hm43, hhas⟩ := Claim.g_list_has_spec idxs hi hused ev56
          exact ⟨hh ▸ hm43 ▸ Heap.Extends.refl _, fun hmem => absurd (hhas.mpr hmem) hne1⟩
        | .n1_other_other_other_n1_Recr (heq_jwmirhum := h01) ..
        | .n1_other_other_other_n1_RPrj (heq_rbmskoff := h01) ..
        | .n1_other_other_other_other (heq_siovpfty := h01) .. =>
          exact absurd (Value.field.inj h01) zero_ne_one
        | .n1_n1 (ev56 := ev56) (ev_tojkhkzc := ev_eq) (ev99 := ev_urh) (he165 := hh) .. =>
          obtain ⟨hm43, -⟩ := Claim.g_list_has_spec idxs hi hused ev56
          subst hm43
          have ext_eq := ev_eq.heap_extends
          obtain ⟨hm86, hurh⟩ := used_ref_has_aux (i := 0) (by simpa using hilen)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_eq hirefs)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_eq hiused)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_eq hq) ev_urh
          obtain ⟨k, -, hk_mem, hk_get⟩ := hurh rfl
          have hget_c : cib.refs[k]? = some (Core.ixAddr q) := by
            rw [← Array.getElem?_toList, ← himap, List.getElem?_map, hk_get]; rfl
          exact ⟨hh ▸ hm86 ▸ ext_eq,
            fun _ => Or.inl (Or.inl ⟨cib, k, hib, by rw [← Assembly.usedRefIdxs_eq]; exact hk_mem, hget_c⟩)⟩
        | .n1_other_n1 (cs183 := cs_ip) (ev56 := ev56) (ev_tojkhkzc := ev_eq) (ev99 := ev_urh)
            (ev185 := ev_ip) (he236 := hh) (hc237 := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev_eq.heap_extends.trans ev_urh.heap_extends)
          obtain ⟨ext_ip, hip⟩ := is_projection_of_spec hS hcov
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hb_ib)
            ev_ip (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          obtain ⟨-, -, -, -, c_ib', hc_ib', hca⟩ := hip rfl
          rw [hix_ib] at hc_ib' hca
          exact ⟨hh ▸ ext_pre.trans ext_ip, fun _ => Or.inl (Or.inr (Or.inl ⟨c_ib', hc_ib', hca⟩))⟩
        | .n1_other_other_n1 (cs254 := cs_prb) (ev56 := ev56) (ev_tojkhkzc := ev_eq)
            (ev99 := ev_urh) (ev185 := ev_ip) (ev256 := ev_prb) (he315 := hh) (hc316 := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev_eq.heap_extends.trans
            (ev_urh.heap_extends.trans ev_ip.heap_extends))
          obtain ⟨ext_prb, hprb⟩ := projection_of_ref_block_spec (K := K) hS hcov hib hilen himap
            (hrc.mono (ext_pre.trans ev_prb.heap_extends)) (Heap.Extends.refl _)
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_pre hirefs)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_pre hiused)
            ev_prb (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl]))
          exact ⟨hh ▸ ext_pre.trans ext_prb, fun _ => Or.inl (Or.inr (Or.inr (hprb rfl)))⟩
        | .n1_other_other_other_n1_other (cs_nlmkvjrk := cs_ld) (ev56 := ev56)
            (ev_tojkhkzc := ev_eq) (ev99 := ev_urh) (ev185 := ev_ip) (ev256 := ev_prb)
            (ev_ntfvqzva := ev_mem) (ev_eauaaxrq := ev_ld) (hne_qzgodjon := hne_recr)
            (hne_vgdvhltn := hne_rprj) (he_nqrzigtc := hh) (hc_xkxroafj := hcs) .. =>
          have ext_pre := ev56.heap_extends.trans (ev_eq.heap_extends.trans
            (ev_urh.heap_extends.trans (ev_ip.heap_extends.trans ev_prb.heap_extends)))
          obtain ⟨hmem_w, hm_mem⟩ := Claim.addr_set_member_set_spec
            (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq) (hwset.mono ext_pre) ev_mem
          subst hm_mem
          obtain ⟨ext_ld, rawQ, cq, hlenQ, hhQ, haddrQ, -, hexactQ, hrepQ, -⟩ :=
            Claim.load_verified_constant_de ⟨q, Bytes.repAddressRef_heapMono₂ Core.addrTy ext_pre hq, rfl⟩ ev_ld
          have hrec_q : recordOf K.E₀ (Core.ixAddr q) = some cq :=
            Claim.recordOf_of_hashed hcov
              (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcs, hcl])) hhQ)
              hlenQ (by rw [haddrQ]; exact hexactQ)
          obtain ⟨infoVal, _, _, _, _, hmk, hiRep, -, -, -, -⟩ := hrepQ
          injection hmk with _ _ hargs
          simp only [List.cons.injEq] at hargs
          have hno_recr : ∀ rcr, cq.info ≠ .recr rcr := by
            intro rcr hinfo; rw [hinfo] at hiRep; obtain ⟨rv, hrv, -⟩ := hiRep
            rw [← hargs.1] at hrv; exact hne_recr [rv] rfl hrv
          have hno_rprj : ∀ p, cq.info ≠ .rPrj p := by
            intro p hinfo; rw [hinfo] at hiRep; obtain ⟨pv, hpv, -⟩ := hiRep
            rw [← hargs.1] at hpv; exact hne_rprj [pv] rfl hpv
          exact ⟨hh ▸ ext_pre.trans ext_ld,
            fun _ => Or.inr ⟨hmem_w rfl, cq, hrec_q, hno_recr, hno_rprj⟩⟩
      obtain ⟨ext_seg, hq_ok⟩ := hseg
      have hv : _ = Value.field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]; push_cast; rfl
      rw [hv] at ev_rest
      obtain ⟨ext_rest, hrest_ok⟩ := container_refs_ok_spec hS hcov hib hilen himap (i := i + 1)
        (by simp at hbound ⊢; omega)
        (hrc.mono ext_seg) (S0.addr_mono ext_seg ⟨b_ib, hb_ib, hix_ib⟩)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hused)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_seg hirefs)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_seg hiused)
        (hwset.mono ext_seg) ev_rest (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      refine ⟨ext_seg.trans ext_rest, fun k q₀ hget hmem => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst hget
        exact hq_ok (by simpa using hmem)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hget
        exact hrest_ok k' q₀ hget (by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hmem)

private theorem container_recs_refs_standalone_refs_spec {K : FamRunCtx}
    (hS : LoadedReads.RunStore K.calls K.E₀)
    (hcov : LoadedReads.HashedRecordsStored K.calls K.E₀)
    {x ib : _root_.Address} {cx : Ixon.Constant} {rcr : Ixon.Recursor}
    {Wset : List _root_.Address}
    (hcx : recordOf K.E₀ x = some cx) (hrcr : cx.info = .recr rcr)
    (hib_det : ∀ {xa r_ib : SourceValue F} {hh₁ hh₂ : Heap F} {cs_r : List (Call F)},
      S0.addr hh₁ xa x →
      ObsFn Obs.W "KernelModeled::rec_family_block" [xa] hh₁ r_ib hh₂ cs_r →
      (∀ cl ∈ cs_r, cl ∈ K.calls) → S0.addr hh₂ r_ib ib) :
    ∀ (elems : List (SourceValue F)) {h h' : Heap F} {rc xs wset r xx : SourceValue F}
      {cs : List (Call F)},
      RepList Core.addrListEnum (fun _ a b => a = b) h elems xs →
      xx ∈ elems →
      Claim.RCLimRep K.t K.bAddr K.lim h rc →
      S0.addr h xx x →
      Claim.RepAddrSet h Wset wset →
      ObsFn Obs.W "KernelModeled::container_recs_refs" [rc, xs, wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ K.calls) →
      ∀ y, UsedRef K.E₀ x y →
        K.BlockRef ib y ∨
          (y ∈ Wset ∧ ∃ cy, recordOf K.E₀ y = some cy ∧
            (∀ r', cy.info ≠ .recr r') ∧ (∀ p, cy.info ≠ .rPrj p)) := by
  intro elems
  induction elems with
  | nil => intro _ _ _ _ _ _ _ _ _ hmem; cases hmem
  | cons el rest ih =>
    intro h h' rc xs wset r xx cs hrep hmem hrc hx hwset ev hsub
    match Obs.«KernelModeled::container_recs_refs».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons_Recr (cs53 := cs53) (cs142 := cs142) (cs172 := cs172) (ld12 := ld)
        (ev55 := ev_ld) (ev144 := ev_crc) (ev174 := ev_rest) (hc191 := hc) .. =>
      obtain ⟨el', rest', heq, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection heq with h1 h2; subst h1 h2
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · -- Head is `xx`: unpack `ev_crc : container_refs_check`!
        obtain ⟨ext_ld, rawX, cx', hlenX, hhX, haddrX, -, hexactX, hrepX, -⟩ :=
          Claim.load_verified_constant_de hx ev_ld
        have hcc : cx' = cx :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcx)
            (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hhX) haddrX hexactX
        subst cx'
        match Obs.«KernelModeled::container_refs_check».obs ev_crc with
        | .run (cs12 := cs_rfb) (cs34 := cs_ib) (cs_pwnfsnzi := cs_cro)
            (ev14 := ev_rfb) (ev36 := ev_ib) (hv59 := hv_mk) (ev_iroawuwo := ev_ix)
            (ev_yqrkylod := ev_iib) (ev_wymffvuv := ev_cro) (hc222 := hc_crc) .. =>
          have hib_addr : S0.addr _ _ ib :=
            hib_det (S0.addr_mono ext_ld hx) ev_rfb
              (fun cl hcl => hsub cl (by rw [hc]; simp [hc_crc, hcl]))
          obtain ⟨ext_ib, rawIb, cib, hlenIb, hhIb, haddrIb, -, hexactIb, hrepIb, -⟩ :=
            Claim.load_verified_constant_de hib_addr ev_ib
          have hrec_ib : recordOf K.E₀ ib = some cib :=
            Claim.recordOf_of_hashed hcov
              (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hc_crc, hcl])) hhIb)
              hlenIb (by rw [haddrIb]; exact hexactIb)
          have ext_to_ix := ev_rfb.heap_extends.trans ext_ib
          obtain ⟨ext_ix, hused_x⟩ := Claim.const_idxs_of_spec (hrepX.mono ext_to_ix) ev_ix
          obtain ⟨ext_iib, hused_ib⟩ := Claim.const_idxs_of_spec (hrepIb.mono ext_ix) ev_iib
          obtain ⟨xRefs, hxMap, hxCore⟩ := repIxonAddrList_to_core (repConstant_refs_eq_local hrepX)
          obtain ⟨ibRefs, hibMap, hibCore⟩ := repIxonAddrList_to_core (repConstant_refs_eq_local hrepIb)
          have hx_len : xRefs.length < 72057594037927936 := by
            have := congrArg List.length hxMap
            simp only [List.length_map, Array.length_toList] at this
            rw [this]; exact refs_size_lt_local hlenX hexactX
          have hib_len : ibRefs.length < 72057594037927936 := by
            have := congrArg List.length hibMap
            simp only [List.length_map, Array.length_toList] at this
            rw [this]; exact refs_size_lt_local hlenIb hexactIb
          have ext_cro_pre := ext_ld.trans (ext_to_ix.trans (ext_ix.trans ext_iib))
          obtain ⟨-, hcro⟩ := container_refs_ok_spec (K := K) hS hcov hrec_ib hib_len hibMap
            (i := 0) (by simpa using hx_len)
            (hrc.mono ext_cro_pre) (S0.addr_mono (ext_ib.trans (ext_ix.trans ext_iib)) hib_addr)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
              (ext_to_ix.trans (ext_ix.trans ext_iib)) hxCore)
            (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext_iib hused_x)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
              (ext_ix.trans ext_iib) hibCore)
            hused_ib (hwset.mono ext_cro_pre)
            ev_cro (fun cl hcl => hsub cl (by rw [hc]; simp [hc_crc, hcl]))
          intro y hu
          obtain ⟨cx'', k, hrec'', hk_mem, hk_get⟩ := hu
          have hcc'' : cx'' = cx := Option.some.inj (hrec''.symm.trans hcx)
          subst cx''
          have hk_map : (xRefs.map Core.ixAddr)[k]? = some y := by
            rw [hxMap, Array.getElem?_toList]; exact hk_get
          rw [List.getElem?_map] at hk_map
          cases hq : xRefs[k]? with
          | none => simp [hq] at hk_map
          | some q =>
            simp only [hq, Option.map_some, Option.some.injEq] at hk_map
            subst hk_map
            exact hcro k q hq (by rw [Nat.zero_add, Assembly.usedRefIdxs_eq]; exact hk_mem)
      · have ext_step := ev_ld.heap_extends.trans ev_crc.heap_extends
        exact ih (RepLinkedList.mono (fun _ _ _ _ _ e => e) ext_step hrestRep) hmemRest
          (hrc.mono ext_step) (S0.addr_mono ext_step hx) (hwset.mono ext_step) ev_rest
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    | .Cons_RPrj (cs53 := cs53) (ld12 := ld) (ev55 := ev_ld) (ev_fvuqobfi := e1)
        (ev_vyniyqbz := e2) (ev210 := e3) (ev266 := ev_rest) (hc283 := hc) .. =>
      obtain ⟨el', rest', heq, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection heq with h1 h2; subst h1 h2
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · exfalso
        obtain ⟨-, _, cx', -, hhX, haddrX, -, hexactX, hrepX, -⟩ :=
          Claim.load_verified_constant_de hx ev_ld
        have hcc : cx' = cx :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcx)
            (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hhX) haddrX hexactX
        subst cx'
        obtain ⟨infoVal, _, _, _, _, hmk, hiRep, -, -, -, -⟩ := hrepX
        rw [hrcr] at hiRep
        obtain ⟨rv, hrv, -⟩ := hiRep
        injection hmk with _ _ hargs
        simp only [List.cons.injEq] at hargs
        rw [← hargs.1] at hrv; simp at hrv
      · have ext_step := ev_ld.heap_extends.trans (e1.heap_extends.trans
          (e2.heap_extends.trans e3.heap_extends))
        exact ih (RepLinkedList.mono (fun _ _ _ _ _ e => e) ext_step hrestRep) hmemRest
          (hrc.mono ext_step) (S0.addr_mono ext_step hx) (hwset.mono ext_step) ev_rest
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    | .Cons_other (cs53 := cs53) (ld12 := ld) (ev55 := ev_ld) (hne192 := hneRecr)
        (ev295 := ev_rest) (hc312 := hc) .. =>
      obtain ⟨el', rest', heq, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection heq with h1 h2; subst h1 h2
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · exfalso
        obtain ⟨-, _, cx', -, hhX, haddrX, -, hexactX, hrepX, -⟩ :=
          Claim.load_verified_constant_de hx ev_ld
        have hcc : cx' = cx :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcx)
            (Claim.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hhX) haddrX hexactX
        subst cx'
        obtain ⟨infoVal, _, _, _, _, hmk, hiRep, -, -, -, -⟩ := hrepX
        rw [hrcr] at hiRep
        obtain ⟨rv, hrv, -⟩ := hiRep
        injection hmk with _ _ hargs
        simp only [List.cons.injEq] at hargs
        rw [← hargs.1] at hrv
        exact hneRecr [rv] rfl hrv
      · exact ih (RepLinkedList.mono (fun _ _ _ _ _ e => e) ev_ld.heap_extends hrestRep) hmemRest
          (hrc.mono ev_ld.heap_extends) (S0.addr_mono ev_ld.heap_extends hx)
          (hwset.mono ev_ld.heap_extends) ev_rest
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))

/-- **Discharges `BatchGives.contWitness`**: every container witness of a scope check bound to no
walked role eliminates a non-empty inductive block `ib` reached from `B` by a dependency path, has
its `check_container_rec` among the check's calls, closes standalone references against `ib` and
non-kind-2 witnesses, and otherwise belongs to a recursor block whose family check with `ib` is
among the scope check's calls. -/
theorem FamRunCtx.contWitness_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B rb : _root_.Address} {cs : List (Call F)} {x : _root_.Address}
    (hS : K.ScopeAt B rb cs) (hwit : K.ContWitness cs B x) (hncov : ¬ Covered K.t x) :
    ∃ ib, K.DepPath B ib ∧ IndBlock K.E₀ ib ∧ ContainerRecCheckIn cs K.bAddr K.t K.lim x ∧
      (∀ cx, recordOf K.E₀ x = some cx → Standalone cx →
        ∀ y, UsedRef K.E₀ x y → K.BlockRef ib y ∨ K.WitBase B y) ∧
      ((∃ cx, recordOf K.E₀ x = some cx ∧ Standalone cx) ∨
        ∃ a ca cs', recordOf K.E₀ a = some ca ∧ ConstAddrOf a ca x ∧ RecBlock K.E₀ a ∧
          FamilyCallAtLim K.calls K.bAddr K.t ib a K.lim cs' ∧ ∀ cl ∈ cs', cl ∈ cs) := by
  obtain ⟨h₀, h₀', rc₀, xb₀, xrb₀, r₀, -, -, -, ev_fam, -, hsub_fam⟩ := hS.1
  obtain ⟨h_w, rc_w, xb_w, xx_w, s_w, hrc_w, hxb_w, hxx_w, hcl_w⟩ := hwit
  obtain ⟨m_rp, v_rp, m_rp', cs_rp, ev_rp, m_ws, x_s4, x_nw, ev_pre_ws, x_outside, x_s5,
    m_ws', cs_ws, ev_ws, wset, m_asb, cs_asb, ev_asb, v_cr, m_cr, cs_cr, ev_cr,
    v_w, m_w, cs_w, ev_w, ext_rp_ws, ext_ws_w, ext_w_ws', sub_ws, sub_asb, sub_cr, sub_w,
    elems, outsideRep, memOutside⟩ := obsFn_check_witness_enclosing_family ev_fam hcl_w
  -- Pull `S0.addr m_ws xb_w B` back from `hxb_w` via `ev_rp`'s initial `loadValue m_rp xb_w`!
  have hxb_ws : S0.addr m_ws xb_w B := by
    obtain ⟨b_B, hb_B, hix_B⟩ := hxb_w
    have hld_rp : ∃ v, loadValue m_rp xb_w = .ok v := by
      match Obs.«KernelModeled::read_payload».obs ev_rp with
      | .Nil (ld11 := ld) .. | .other (ld11 := ld) .. => exact ⟨_, ld⟩
    obtain ⟨v_rp0, hld_rp0⟩ := hld_rp
    exact ⟨b_B, repAddressRef_pullback ext_ws_w (ext_rp_ws.loadValue_eq hld_rp0) hb_B, hix_B⟩
  -- Build `L1.Stream m_ws bs4 x_s4` from `ev_rp` + `ev_pre_ws`!
  have hs4_ws : ∃ bs4 : List UInt8, L1.Stream m_ws bs4 x_s4 := by
    obtain ⟨x_rb', x_s1', m_ga, cs_ga, x_na', x_s2', m_gc1, cs_gc1, m_gc1', x_adv', x_s3',
      m_gas, cs_gas, cs_gc2, ev_ga, ext_ga, ev_gc1, ev_gas, ev_gc2⟩ := ev_pre_ws
    obtain ⟨-, _, hst_rp⟩ := read_payload_stream ev_rp
    obtain ⟨_, _, _, _, -, hr_ga, -, hs1, -, -⟩ := Decl.get_address_spec hst_rp ev_ga
    injection hr_ga with hp_ga; injection hp_ga with _ hs1_eq; injection hs1_eq with hs1_eq'
    subst hs1_eq'
    obtain ⟨_, hs2⟩ := get_count_stream (L1.Stream.mono ext_ga hs1) ev_gc1
    obtain ⟨_, _, _, -, -, -, hs3, -⟩ := Decl.get_addrs_spec hs2 ev_gas
    exact get_count_stream hs3 ev_gc2
  obtain ⟨bs4, hs4⟩ := hs4_ws
  -- Run `check_witnesses_spec_ext` on `ev_ws` using `hrc_ws' = hrc_w.mono (ev_w.heap_extends.trans ext_w_ws')`!
  have hrc_ws' := hrc_w.mono (ev_w.heap_extends.trans ext_w_ws')
  obtain ⟨ext_ws, ws, hws_rep, hws_spec⟩ :=
    check_witnesses_spec_ext (K := K) hW.runStore hW.hashedStored cs_ws.length (Nat.le_refl _)
      hrc_ws' (Heap.Extends.refl _) hxb_ws hs4 ev_ws
      (fun cl hcl => hsub_fam cl (sub_ws cl hcl))
  obtain ⟨ext_asb, hwset⟩ := Claim.addr_set_build_spec hws_rep (Claim.RepAddrSet.nil _) ev_asb
  rw [List.append_nil] at hwset
  -- Now unpack `ev_w` (kind = 2)!
  match Obs.«KernelModeled::check_witness».obs ev_w with
  | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
  | .n1 (hv171 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
  | .n3 (hv447 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
  | .n2 (cs_gfiphqsh := cs_wfb) (cs412 := cs_ccr) (ev328 := ev_gc) (ev_dpuowbtw := ev_wfb)
      (ev414 := ev_ccr) (ev_yqkzbtyw := ev_acp) (he441 := hh_w) (hc442 := hcw) .. =>
    have hsub_w_cs : ∀ cl ∈ cs_w, cl ∈ cs := fun cl hcl => sub_ws cl (sub_w cl hcl)
    have hsub_w : ∀ cl ∈ cs_w, cl ∈ K.calls := fun cl hcl => hsub_fam cl (hsub_w_cs cl hcl)
    have ext_to_acp := ev_gc.heap_extends.trans (ev_wfb.heap_extends.trans ev_ccr.heap_extends)
    obtain ⟨hm_acp, hpass_or_cov⟩ :=
      assert_covered_past_spec_ext (hrc_w.mono (ext_to_acp.trans ev_acp.heap_extends))
        (Heap.Extends.refl _) (S0.addr_mono ext_to_acp hxx_w) ev_acp
    have hpass0 : _ = Value.field 0 := by
      rcases hpass_or_cov with h0 | hcov_x
      · exact h0
      · exact (hncov hcov_x).elim
    obtain ⟨ext_wfb, -, ib, hib_addr, hdep_fn⟩ :=
      walk_from_block_spec_ext (K := K) hW.runStore hW.hashedStored
        (hrc_w.mono (ev_gc.heap_extends.trans ev_wfb.heap_extends)) (Heap.Extends.refl _)
        (S0.addr_mono ev_gc.heap_extends hxb_w) ev_wfb
        (fun cl hcl => hsub_w cl (by rw [hcw]; simp [hcl]))
    have hdep : K.DepPath B ib := hdep_fn hpass0
    have ext_to_ccr := ev_gc.heap_extends.trans ext_wfb
    have hccr_in : ContainerRecCheckIn cs K.bAddr K.t K.lim x :=
      ⟨_, _, rc_w, xx_w, _, _, cs_ccr, hrc_w.mono ext_to_ccr, S0.addr_mono ext_to_ccr hxx_w,
        ev_ccr, fun cl hcl => hsub_w_cs cl (by rw [hcw]; simp [hcl])⟩
    match Obs.«KernelModeled::check_container_rec».obs ev_ccr with
    | .run (cs37 := cs37) (cs_ymrayeri := cs_ci) (cs73 := cs73)
        (ev39 := ev39) (ev25 := ev25) (heq61 := heq_ib)
        (ev_nqhglzzq := ev_ci) (ld_hhcwtoqm := ld_rec) (ev75 := ev75) (hc96 := hccr) .. =>
      have hsub37 : ∀ cl ∈ cs37, cl ∈ K.calls := fun cl hcl =>
        hsub_w cl (by rw [hcw]; simp [hccr, hcl])
      have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ K.calls := fun cl hcl =>
        hsub_w cl (by rw [hcw]; simp [hccr, hcl])
      have hsub73_cs : ∀ cl ∈ cs73, cl ∈ cs := fun cl hcl =>
        hsub_w_cs cl (by rw [hcw]; simp [hccr, hcl])
      obtain ⟨ext39, cx, ib_b, cib, ms, j, ind, -, -, hcx, hib_b_rep, hcib, hms, hmj, -, -, -⟩ :=
        rec_family_block_spec hW.runStore hW.hashedStored (S0.addr_mono ext_to_ccr hxx_w)
          ev39 hsub37
      obtain ⟨ib_b2, hib2_rep, hib2_ix⟩ := S0.addr_mono ext39 hib_addr
      obtain ⟨haeq, hm25⟩ := Lib.address_eq_spec ev25 hib_b_rep hib2_rep
      have hib_b_eq : ib_b = ib_b2 := by
        by_cases he : ib_b = ib_b2
        · exact he
        · rw [ite_eq_right he] at haeq
          exact absurd (Value.field.inj (heq_ib.symm.trans haeq)) one_ne_zero
      subst hib_b_eq
      subst hib2_ix
      -- Prove `IndBlock K.E₀ (Core.ixAddr ib_b)` from `dep_top` + `hW.uniform`!
      have hTib : K.Top (Core.ixAddr ib_b) := (dep_top hW hdep hS.2.1).1
      have hpos : 0 < ms.size := by
        have := (Array.getElem?_eq_some_iff.mp hmj).1; omega
      have hmem_ind : .indc ind ∈ ms.toList := by
        rw [← Array.getElem?_toList] at hmj; exact List.mem_of_getElem? hmj
      have hall_ind : ∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i := by
        rcases hW.uniform (Core.ixAddr ib_b) cib ms hTib hcib hms with hd | hi | hr
        · obtain ⟨d, hd⟩ := hd (.indc ind) hmem_ind; cases hd
        · exact hi
        · obtain ⟨r', hr'⟩ := hr (.indc ind) hmem_ind; cases hr'
      have hInd : IndBlock K.E₀ (Core.ixAddr ib_b) := ⟨cib, ms, hcib, hms, hpos, hall_ind⟩
      -- Split on whether `cx` is standalone `.recr` or projection `.rPrj`
      have ext_to_ci := ext_to_ccr.trans (ext39.trans ev25.heap_extends)
      obtain ⟨ab_x, hab_x, hix_x⟩ := S0.addr_mono ext_to_ci hxx_w
      have hkind := get_ci_loads_rec_is_recr_or_rPrj hW.runStore hab_x ev_ci hsub_ci ld_rec
        (hix_x.symm ▸ hcx)
      refine ⟨Core.ixAddr ib_b, hdep, hInd, hccr_in, ?_, ?_⟩
      · -- Standalone-refs conjunct
        intro cx' hcx' hStand y hu
        have hce : cx' = cx := Option.some.inj (hcx'.symm.trans hcx)
        subst hce
        rcases hkind with ⟨rcr, hrcr⟩ | ⟨p, hrprj⟩
        · have hib_det : ∀ {xa r_ib : SourceValue F} {hh₁ hh₂ : Heap F} {cs_r : List (Call F)},
              S0.addr hh₁ xa x →
              ObsFn Obs.W "KernelModeled::rec_family_block" [xa] hh₁ r_ib hh₂ cs_r →
              (∀ cl ∈ cs_r, cl ∈ K.calls) → S0.addr hh₂ r_ib (Core.ixAddr ib_b) := by
            intro xa r_ib hh₁ hh₂ cs_r hxa ev_r hsub_r
            obtain ⟨-, -, ib_r, -, -, -, -, -, -, -, hib_r_rep, -⟩ :=
              rec_family_block_spec hW.runStore hW.hashedStored hxa ev_r hsub_r
            have heq_ib' := rec_family_block_det hW.runStore hW.hashedStored
              hxa (S0.addr_mono ext_to_ccr hxx_w) ev_r ev39 hsub_r hsub37
              ⟨ib_r, hib_r_rep, rfl⟩ ⟨ib_b, hib_b_rep, rfl⟩
            exact ⟨ib_r, hib_r_rep, heq_ib'⟩
          have hrefs := container_recs_refs_standalone_refs_spec (K := K)
            hW.runStore hW.hashedStored hcx hrcr hib_det elems
            (RepLinkedList.mono (fun _ _ _ _ _ e => e) ext_asb outsideRep) memOutside
            (hrc_ws'.mono ext_asb)
            (S0.addr_mono (ev_w.heap_extends.trans (ext_w_ws'.trans ext_asb)) hxx_w)
            hwset ev_cr (fun cl hcl => hsub_fam cl (sub_cr cl hcl)) y hu
          rcases hrefs with hbr | ⟨hy_mem, cy, hcy, hno_recr, hno_rprj⟩
          · exact Or.inl hbr
          · rw [List.mem_map] at hy_mem
            obtain ⟨w, hw_rev, hw_eq⟩ := hy_mem
            have hw_in : w ∈ ws := List.mem_reverse.mp hw_rev
            rw [← hw_eq] at hcy ⊢
            rcases hws_spec w hw_in with hwb | ⟨-, -, -, -, -, -, -, cx₂, hcx₂, hrec_or_rprj⟩
            · exact Or.inr hwb
            · exfalso
              have heq_cy : cx₂ = cy := Option.some.inj (hcx₂.symm.trans hcy)
              subst heq_cy
              rcases hrec_or_rprj with ⟨r', hr'⟩ | ⟨p', hp'⟩
              · exact hno_recr r' hr'
              · exact hno_rprj p' hp'
        · exact (standalone_not_proj hStand (Or.inr (Or.inr (Or.inr ⟨p, hrprj⟩)))).elim
      · -- Standalone vs `.rPrj` container witness
        rcases hkind with ⟨rcr, hrcr⟩ | ⟨⟨idx, a⟩, hrprj⟩
        · exact Or.inl ⟨cx, hcx, Or.inr (Or.inl ⟨rcr, hrcr⟩)⟩
        · right
          match Obs.«KernelClaim::run_check».obs ev75 with
          | .run (cs15 := cs15) (cs29 := cs29) (ev17 := ev17) (ld11 := ld11)
              (ev31 := ev31) (hc56 := hc56) .. =>
            have hsub15 : ∀ cl ∈ cs15, cl ∈ K.calls := fun cl hcl =>
              hsub_fam cl (hsub73_cs cl (by rw [hc56]; simp [hcl]))
            have hsub29_cs : ∀ cl ∈ cs29, cl ∈ cs := fun cl hcl =>
              hsub73_cs cl (by rw [hc56]; simp [hcl])
            have hsub29 : ∀ cl ∈ cs29, cl ∈ K.calls := fun cl hcl => hsub_fam cl (hsub29_cs cl hcl)
            have ext_to_rc := ext_to_ci.trans ev_ci.heap_extends
            obtain ⟨hRB, ca, ib', -, -, -, -, -, -, cs_fam, -, -, -, -, -,
                hca, hca_const, -, -, -, -, -, -,
                ⟨_, _, _, cs_rfb', hx_rfb', hib'_rfb, ev_rfb', hsub_rfb'⟩,
                -, -, -, -, -, hfc, hsub_cf⟩ :=
              rprj_check_const_rec_other hW.runStore hW.hashedStored
                (hrc_w.mono ext_to_rc) (S0.addr_mono ext_to_rc hxx_w)
                hcx hrprj ev17 ld11 ev31 hsub15 hsub29
            have hib'_eq : ib' = Core.ixAddr ib_b :=
              rec_family_block_det hW.runStore hW.hashedStored
                hx_rfb' (S0.addr_mono ext_to_ccr hxx_w) ev_rfb' ev39
                (fun cl hcl => hsub29 cl (hsub_rfb' cl hcl)) hsub37
                hib'_rfb ⟨ib_b, hib_b_rep, rfl⟩
            subst hib'_eq
            exact ⟨a, ca, cs_fam, hca, hca_const, hRB, hfc, fun cl hcl => hsub29_cs cl (hsub_cf cl hcl)⟩

end IxVM.Refinement.Typing
