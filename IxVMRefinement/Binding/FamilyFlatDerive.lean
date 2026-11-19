import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Binding.FamilyReconZeta
import IxVMRefinement.Binding.BlockElimSpec
import IxVMRefinement.Binding.FamilyOfCall
import IxVMRefinement.FamilyAlias.CheckFamilyReads
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4

/-! # The derived flattened family of a block, read off an observed family check

`KernelModeled::check_family` builds the flattened family of the record it is handed
(`KernelCheck::build_flat_block`), derives the flattened family of the block from the block's
constructors (`KernelModeled::check_nested_aux`: `nested_walk` from the entries of the block's own
types, `flat_reals`), and asserts that the two lists are the same entries in the same order
(`aux_all_in`). This module reads that comparison on exact entries (`FlatEntryRepExact`):

* `aux_entry_in_spec` (`KernelModeled::aux_entry_in`): the answer is `FamilyFlat.auxEntryIn`;
* `aux_all_in_spec` (`KernelModeled::aux_all_in`): the answer is `1` exactly when the two
  represented lists are equal, entry by entry: the same address, the same kind, syntactically the
  same parameters and the same levels (the circuit's `spec_params_zeta_eq` reads a `let` as its
  reduct, which is how an exact term represents one, so on exact terms it decides equality);
* `flat_reals_spec` (`KernelModeled::flat_reals`): the entries that are not auxiliaries, in order;
* `NestedWalkSpec`: the reading of `KernelModeled::nested_walk` this module takes;
* `check_nested_aux_spec` (`KernelModeled::check_nested_aux`): `nestedWalk` from the entries of
  the block's own types answers the whole list;
* `originals_not_aux`, `originals_filter_append`, `FlatOriginals`, `flatOriginals_of_append`,
  `derivedFlatAt_of_walk`: the block's own entries of a flattened family that lists the block's
  types and then auxiliaries are the block's types, so a walk from them that answers the whole
  list is the derivation `derivedFlatAt`;
* **`blockDerivedFlat_of_checks`**: an observed `check_nested_aux` on the flattened family `es`
  of a block, at the block's elimination offset (`BlockElim`, which `block_elim_blockElim` reads
  off the observed `block_elim`), gives `BlockDerivedFlat`;
* `CheckFamilyFlatChain`, `checkFamily_flatChain`: the events of an observed
  `KernelModeled::check_family` between `block_elim` and `family_refs_ok` (`build_flat_block`,
  `check_nested_aux`, the length of the flattened family and the completeness assertion), at
  their heaps, over the chain `CheckFamilyChain` of the same call;
* `CheckFamilyFlatChain.validates_one`, `CheckFamilyFlatChain.length_eq`: under a group's
  validation the record has one recursor per entry of the flattened family;
* **`blockDerivedFlat_of_checkFamily`**: `BlockDerivedFlat` from the chain and those events.

Taken, not proved here: the reading of `nested_walk` (`NestedWalkSpec`), and of
`build_flat_block` that the returned list represents entries `es` whose own entries are the
block's types at the offset (`FlatOriginals`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry FlatView auxEntryIn nestedWalk originals
  derivedFlatAt membersAt BlockElim BlockDerivedFlat)
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Consistency (Bounded)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Field arithmetic on flags -/

private theorem field_mul_ite {p q : Prop} [Decidable p] [Decidable q] {v : SourceValue F}
    (op : evalBinOp .mul (.field (if p then 1 else 0) : SourceValue F)
      (.field (if q then 1 else 0)) = .ok v) :
    v = .field (if p ∧ q then 1 else 0) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem ite_field_eq_one {p : Prop} [Decidable p]
    (h : (.field (if p then 1 else 0) : SourceValue F) = .field 1) : p := by
  by_contra hp
  rw [ite_eq_right hp] at h
  exact absurd (Value.field.inj h) (by decide)

private theorem ite_field_ne_one {p : Prop} [Decidable p]
    (h : (.field (if p then 1 else 0) : SourceValue F) ≠ .field 1) : ¬ p := by
  intro hp
  rw [ite_eq_left hp] at h
  exact h rfl

/-- The difference of two flags is zero exactly when they are the same flag. -/
private theorem auxVal_sub {a b : Bool} {v : SourceValue F}
    (op : evalBinOp .sub (auxVal a) (auxVal b) = .ok v) : v = .field 0 ↔ a = b := by
  simp only [evalBinOp, auxVal] at op
  injection op with hv
  rw [← hv]
  cases a <;> cases b <;> simp

theorem FlatEntry.ext' {d e : FlatEntry} (ha : d.addr = e.addr) (hx : d.aux = e.aux)
    (hp : d.params = e.params) (hl : d.levels = e.levels) : d = e := by
  cases d
  cases e
  simp only at ha hx hp hl
  subst ha hx hp hl
  rfl

/-! ## `aux_entry_in` -/

/-- **`KernelModeled::aux_entry_in`** answers whether the entries hold an auxiliary with the
address, the parameters and the levels (`FamilyFlat.auxEntryIn`). -/
theorem aux_entry_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (es : List FlatEntry) {a : Bytes.Address} {sp : List KExpr} {us : List KLevel}
      {xflat xa xsp xus r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::aux_entry_in" [xflat, xa, xsp, xus] h r h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepKLevelList h us xus →
      r = .field (if auxEntryIn es (ixAddr a) sp us then 1 else 0) := by
  intro es
  induction es with
  | nil =>
    intro a sp us xflat xa xsp xus r h h' cs ev _ hes _ _ _
    match Obs.«KernelModeled::aux_entry_in».obs ev with
    | .Nil (he20 := hr) .. => rw [hr]; rfl
    | .Cons_n1_n1 (ld12 := ld) .. | .Cons_n1_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro a sp us xflat xa xsp xus r h h' cs ev hbnd hes ra rsp rus
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::aux_entry_in».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1_n1 (m77 := m1) (m131 := m2) (ld12 := ld) (ev99 := evaeq) (op92 := op1)
        (ev_caflkvhk := evp) (ev164 := evl) (op136 := op2) (he185 := hr) (hc187 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      subst hv1
      have hfirst := ite_field_eq_one ((field_mul_ite op1).symm.trans rfl)
      have hx := spec_params_zeta_eq_exact hinj hsp rsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      obtain ⟨hy, -⟩ := level_list_struct_eq_exact (hou.mono evp.heap_extends)
        (rus.mono evp.heap_extends) evl
      subst hx hy
      have hsecond := ite_field_eq_one ((field_mul_ite op2).symm.trans rfl)
      have haux : e.aux = true := hfirst.1
      have haddr : e.addr = ixAddr a := by rw [← hae, hfirst.2]
      rw [hr]
      simp [auxEntryIn, haux, haddr, hsecond.1, hsecond.2]
    | .Cons_n1_other (m77 := m1) (m121 := m3) (m131 := m2) (ld12 := ld) (ev99 := evaeq)
        (op92 := op1) (ev_caflkvhk := evp) (ev164 := evl) (op136 := op2) (hne188 := hne)
        (ev197 := evrec) (hc230 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      subst hv1
      have hx := spec_params_zeta_eq_exact hinj hsp rsp
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      obtain ⟨hy, rfl⟩ := level_list_struct_eq_exact (hou.mono evp.heap_extends)
        (rus.mono evp.heap_extends) evl
      subst hx hy
      have hv := field_mul_ite op2
      subst hv
      have hsecond := ite_field_ne_one hne
      have ext := evp.heap_extends
      have hrec := ih evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext hes') (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
        (tmOExactList_mono ext rsp) (rus.mono ext)
      rw [hrec]
      have hno : (e.params == sp && e.levels == us) = false := by
        cases hb : (e.params == sp && e.levels == us)
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact absurd hb hsecond
      have hno' : (e.aux && e.addr == ixAddr a && e.params == sp && e.levels == us) = false := by
        rw [Bool.and_assoc, hno, Bool.and_false]
      simp [auxEntryIn, List.any_cons, hno']
    | .Cons_other (m77 := m1) (ld12 := ld) (ev99 := evaeq) (op92 := op1) (hne231 := hne)
        (ev240 := evrec) (hc273 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae ra
      subst hv1
      have hv := field_mul_ite op1
      subst hv
      have hfirst := ite_field_ne_one hne
      have hrec := ih evrec (sub fun c hc' => by rw [hc]; simp [hc']) hes' ra rsp rus
      rw [hrec]
      have hno : (e.aux && e.addr == ixAddr a) = false := by
        cases hb : (e.aux && e.addr == ixAddr a)
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact absurd ⟨hb.1, ixAddr_inj (hae.trans hb.2)⟩ hfirst
      have hno' : (e.aux && e.addr == ixAddr a && e.params == sp && e.levels == us) = false := by
        rw [hno, Bool.false_and, Bool.false_and]
      simp [auxEntryIn, List.any_cons, hno']

/-! ## `aux_all_in` -/

/-- **`KernelModeled::aux_all_in`** answers `1` exactly when the two represented lists of entries
are equal: entry by entry the same address, the same kind, the same parameters and the same
levels. -/
theorem aux_all_in_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (ds es : List FlatEntry) {xd xf r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::aux_all_in" [xd, xf] h r h' cs →
      Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h ds xd →
      RepList flatListEnum (FlatEntryRepExact κ) h es xf →
      (r = .field 1 ∧ ds = es) ∨ (r = .field 0 ∧ ds ≠ es) := by
  intro ds
  induction ds with
  | nil =>
    intro es xd xf r h h' cs ev _ hds hes
    match Obs.«KernelModeled::aux_all_in».obs ev with
    | .Nil_Nil (ld_neljdsge := ld2) (he_kudvonoa := hr) .. =>
      obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hes ld2
      exact .inl ⟨hr, rfl⟩
    | .Nil_other (ld_neljdsge := ld2) (hne_nazlygkb := hne) (he_bwthzoys := hr) .. =>
      refine .inr ⟨hr, ?_⟩
      cases es with
      | nil =>
        cases hes with
        | nil cell =>
          have hld := Lib.load_enum_cell cell
          rw [ld2] at hld
          injection hld with hv
          exact absurd hv (hne [] rfl)
      | cons _ _ => simp
    | .Cons_Nil (ld12 := ld) .. | .Cons_Cons_n1 (ld12 := ld) ..
    | .Cons_Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld
      cases hcons
  | cons d ds ih =>
    intro es xd xf r h h' cs ev hbnd hds hes
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelModeled::aux_all_in».obs ev with
    | .Nil_Nil (ld12 := ld) .. | .Nil_other (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hds ld
    | .Cons_Nil (ld_uplwbryy := ld2) (he_igwiafed := hr) .. =>
      obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hes ld2
      exact .inr ⟨hr, by simp⟩
    | .Cons_Cons_n1 (v_grufbhou := vk) (m_szacviej := m0) (ld12 := ld1) (ld_uplwbryy := ld2)
        (sg_ifmfdpfc := sg) (ev_woqiuyxz := evaeq) (op_wetvvjfd := op1) (ev_dfliojir := evp)
        (op_yjodglud := op2) (ev_wxxbloog := evl) (op_hcqhjrdx := op3) (ev_zzxrtlvt := evrec)
        (hc_llamfqbn := hc) .. =>
      obtain ⟨d', ds', h1, hd', hds'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld1
      injection h1 with e1 e2; subst e1 e2
      obtain ⟨e, es', rfl, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld2
      obtain ⟨xa1, xp1, xl1, ad, htup, rad, had, hsp1, hou1⟩ := hd'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨xa2, xp2, xl2, ae, htup, rae, hae, hsp2, hou2⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hk, rfl⟩ : vk = .field (if d.aux = e.aux then 1 else 0) ∧ m0 = h := by
        cases sg with
        | n0 op hr hh _ => exact ⟨by rw [hr, ite_eq_left ((auxVal_sub op).mp rfl)], hh⟩
        | other v op hne hr hh _ =>
          exact ⟨by rw [hr, ite_eq_right (fun e => hne ((auxVal_sub op).mpr e))], hh⟩
      subst hk
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rad rae
      subst hv1
      have hv2 := field_mul_ite op1
      subst hv2
      have hx := spec_params_zeta_eq_exact hinj hsp1 hsp2
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      subst hx
      have hv3 := field_mul_ite op2
      subst hv3
      obtain ⟨hy, rfl⟩ := level_list_struct_eq_exact (hou1.mono evp.heap_extends)
        (hou2.mono evp.heap_extends) evl
      subst hy
      have hall := ite_field_eq_one (field_mul_ite op3).symm
      have hde : d = e :=
        FlatEntry.ext' (by rw [← had, ← hae, hall.1.1.1]) hall.1.1.2 hall.1.2 hall.2
      subst hde
      have hrec := ih es' evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono evp.heap_extends hds') (flatList_mono evp.heap_extends hes')
      rcases hrec with ⟨h1, rfl⟩ | ⟨h0, hne⟩
      · exact .inl ⟨h1, rfl⟩
      · exact .inr ⟨h0, fun heq => hne (List.cons.inj heq).2⟩
    | .Cons_Cons_other (v_grufbhou := vk) (m_szacviej := m0) (ld12 := ld1) (ld_uplwbryy := ld2)
        (sg_ifmfdpfc := sg) (ev_woqiuyxz := evaeq) (op_wetvvjfd := op1) (ev_dfliojir := evp)
        (op_yjodglud := op2) (ev_wxxbloog := evl) (op_hcqhjrdx := op3) (hne_gpnzqlow := hne)
        (he_cjmqmowm := hr) (hc_jqpmhazn := hc) .. =>
      obtain ⟨d', ds', h1, hd', hds'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hds ld1
      injection h1 with e1 e2; subst e1 e2
      obtain ⟨e, es', rfl, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld2
      obtain ⟨xa1, xp1, xl1, ad, htup, rad, had, hsp1, hou1⟩ := hd'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨xa2, xp2, xl2, ae, htup, rae, hae, hsp2, hou2⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hk, rfl⟩ : vk = .field (if d.aux = e.aux then 1 else 0) ∧ m0 = h := by
        cases sg with
        | n0 op hr hh _ => exact ⟨by rw [hr, ite_eq_left ((auxVal_sub op).mp rfl)], hh⟩
        | other v op hne hr hh _ =>
          exact ⟨by rw [hr, ite_eq_right (fun e => hne ((auxVal_sub op).mpr e))], hh⟩
      subst hk
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rad rae
      subst hv1
      have hv2 := field_mul_ite op1
      subst hv2
      have hx := spec_params_zeta_eq_exact hinj hsp1 hsp2
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      subst hx
      have hv3 := field_mul_ite op2
      subst hv3
      obtain ⟨hy, rfl⟩ := level_list_struct_eq_exact (hou1.mono evp.heap_extends)
        (hou2.mono evp.heap_extends) evl
      subst hy
      have hv4 := field_mul_ite op3
      subst hv4
      have hnot := ite_field_ne_one hne
      refine .inr ⟨hr, ?_⟩
      intro heq
      injection heq with hde _
      subst hde
      exact hnot ⟨⟨⟨ixAddr_inj (had.trans hae.symm), rfl⟩, rfl⟩, rfl⟩

/-! ## `flat_reals` -/

/-- **`KernelModeled::flat_reals`** returns the entries that are not auxiliaries, in order. -/
theorem flat_reals_spec {κ : _root_.Address → KKey} :
    ∀ (es : List FlatEntry) {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::flat_reals" [xflat] h r h' cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList flatListEnum (FlatEntryRepExact κ) h' (es.filter fun e => !e.aux) r := by
  intro es
  induction es with
  | nil =>
    intro xflat r h h' cs ev hes
    match Obs.«KernelModeled::flat_reals».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      rw [hr, hm]
      exact .nil (by simp)
    | .Cons_n0 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro xflat r h h' cs ev hes
    match Obs.«KernelModeled::flat_reals».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n0 (v108 := v) (m117 := m1) (ld12 := ld) (he103 := hr) (hm102 := hm)
        (ev127 := evrec) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with e1 e2; subst e1 e2
      have haux : e.aux = false := by
        obtain ⟨xa, xps, xls, a, htup, -⟩ := he'
        injection htup with hl; injection hl with _ hl; injection hl with h2 _
        exact auxVal_eq_zero.mp h2.symm
      have hrec := ih evrec hes'
      have ext1 : Heap.Extends h m1 := evrec.heap_extends
      have ext2 : Heap.Extends m1 h' := by rw [hm]; exact Heap.Extends.snoc _ _
      rw [List.filter_cons_of_pos (by simp [haux]), hr]
      refine .cons ?_ (he'.mono (ext1.trans ext2)) (flatList_mono ext2 hrec)
      rw [hm]
      simp
    | .Cons_other (x_is_aux := xaux) (ld12 := ld) (hne137 := hne) (ev146 := evrec) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with e1 e2; subst e1 e2
      have haux : e.aux = true := by
        obtain ⟨xa, xps, xls, a, htup, -⟩ := he'
        injection htup with hl; injection hl with _ hl; injection hl with h2 _
        cases hx : e.aux
        · exact absurd (h2.trans (auxVal_eq_zero.mpr hx)) hne
        · rfl
      rw [List.filter_cons_of_neg (by simp [haux])]
      exact ih evrec hes'

/-! ## `check_nested_aux` -/

/-- **The reading of `KernelModeled::nested_walk` taken here**: a call among the calls `root`,
with its own calls, on the block `B` and represented entries `acc`, from position `0`, returns
the represented result of the model's walk `nestedWalk` over the readings `V` at some fuel. -/
def NestedWalkSpec (κ : _root_.Address → KKey) (V : FlatView) (B : _root_.Address)
    (root : List (Call F)) : Prop :=
  ∀ {b : Bytes.Address} {acc : List FlatEntry} {xb xacc r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)},
    Bytes.RepAddressRef addrTy h b xb → ixAddr b = B →
    RepList flatListEnum (FlatEntryRepExact κ) h acc xacc →
    ObsFn W "KernelModeled::nested_walk" [xb, xacc, .field 0] h r h' cs →
    (⟨"KernelModeled::nested_walk", [xb, xacc, .field 0], h⟩ : Call F) ∈ root →
    (∀ c ∈ cs, c ∈ root) →
    ∃ (n : Nat) (ds : List FlatEntry), nestedWalk V B n 0 acc = some ds ∧
      RepList flatListEnum (FlatEntryRepExact κ) h' ds r

/-- **`KernelModeled::check_nested_aux`** on the represented entries `es`: the model's walk from
the entries of `es` that are not auxiliaries answers `es` itself, at some fuel. -/
theorem check_nested_aux_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {V : FlatView} {B : _root_.Address} {root : List (Call F)}
    (nested_walk : NestedWalkSpec κ V B root) (bd : Bounded root)
    {b : Bytes.Address} {es : List FlatEntry} {xb xflat r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (hb : Bytes.RepAddressRef addrTy h b xb) (hB : ixAddr b = B)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (ev : ObsFn W "KernelModeled::check_nested_aux" [xb, xflat] h r h' cs) :
    ∃ n, nestedWalk V B n 0 (es.filter fun e => !e.aux) = some es := by
  match Obs.«KernelModeled::check_nested_aux».obs ev with
  | .run (ev36 := evR) (ev14 := evW) (ev75 := evC1) (ev95 := evC2) (ev129 := evA)
      (heq152 := h1) (hc157 := hc) .. =>
    have hreals := flat_reals_spec _ evR hes
    obtain ⟨n, ds, hwalk, hds⟩ :=
      nested_walk (Bytes.repAddressRef_heapMono₂ addrTy evR.heap_extends hb) hB hreals evW
        (hroot _ (by rw [hc]; simp)) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
    have ext : Heap.Extends _ _ := evC1.heap_extends.trans evC2.heap_extends
    have ext0 : Heap.Extends h _ := evR.heap_extends.trans (evW.heap_extends.trans ext)
    have hall := aux_all_in_spec hinj ds es evA
      (RomBound.bounded_mono bd fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (flatList_mono ext hds) (flatList_mono ext0 hes)
    have hde : ds = es := by
      rcases hall with ⟨-, hde⟩ | ⟨h0, -⟩
      · exact hde
      · exact absurd (Value.field.inj (h0.symm.trans h1)) (by decide)
    subst hde
    exact ⟨n, hwalk⟩

/-! ## From the walk to the derivation -/

/-- The entries `originals` lists are the block's own: none is an auxiliary. -/
theorem originals_not_aux {V : FlatView} {off : Nat} :
    ∀ (ms : List _root_.Address) (os : List FlatEntry), originals V off ms = some os →
      ∀ e ∈ os, e.aux = false := by
  intro ms
  induction ms with
  | nil =>
    intro os h e he
    simp only [originals, Option.some.injEq] at h
    subst h
    cases he
  | cons a as ih =>
    intro os h e he
    simp only [originals] at h
    cases hc : V.ci a with
    | none => simp [hc] at h
    | some x =>
      cases x with
      | none => simp [hc] at h
      | some i =>
        simp only [hc] at h
        cases ho : originals V off as with
        | none => simp [ho] at h
        | some os' =>
          simp only [ho, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp he with rfl | he'
          · rfl
          · exact ih os' ho e he'

/-- **The block's own entries of a flattened family that lists the block's types and then
auxiliaries are the block's types.** -/
theorem originals_filter_append {V : FlatView} {off : Nat} {ms : List _root_.Address}
    {os xs : List FlatEntry} (ho : originals V off ms = some os)
    (hx : ∀ e ∈ xs, e.aux = true) : (os ++ xs).filter (fun e => !e.aux) = os := by
  rw [List.filter_append]
  have h1 : os.filter (fun e => !e.aux) = os :=
    List.filter_eq_self.mpr fun e he => by simp [originals_not_aux ms os ho e he]
  have h2 : xs.filter (fun e => !e.aux) = [] :=
    List.filter_eq_nil_iff.mpr fun e he => by simp [hx e he]
  rw [h1, h2, List.append_nil]

/-- **The block's own entries of `es` are the block's types at the offset `off`**: the entries of
`es` that are not auxiliaries are what `build_flat_originals` lists of the block `B` in the store
`E₀` (`FamilyFlat.originals` over the block's members). -/
def FlatOriginals (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address) (off : Nat)
    (es : List FlatEntry) : Prop :=
  ∃ ms, membersAt E₀ B = some ms ∧
    originals (FlatView.ofStore t E₀) off ms = some (es.filter fun e => !e.aux)

/-- A flattened family that lists the block's types and then auxiliaries has the block's types
as its own entries. -/
theorem flatOriginals_of_append {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B : _root_.Address}
    {off : Nat} {ms : List _root_.Address} {os xs : List FlatEntry}
    (hm : membersAt E₀ B = some ms)
    (ho : originals (FlatView.ofStore t E₀) off ms = some os)
    (hx : ∀ e ∈ xs, e.aux = true) : FlatOriginals t E₀ B off (os ++ xs) :=
  ⟨ms, hm, by rw [originals_filter_append ho hx]; exact ho⟩

/-- **A walk from the block's own entries that answers the whole list is the derivation.** -/
theorem derivedFlatAt_of_walk {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B : _root_.Address}
    {off n : Nat} {es : List FlatEntry} (horig : FlatOriginals t E₀ B off es)
    (hw : nestedWalk (FlatView.ofStore t E₀) B n 0 (es.filter fun e => !e.aux) = some es) :
    derivedFlatAt (FlatView.ofStore t E₀) B off n = some es := by
  obtain ⟨ms, hm, ho⟩ := horig
  have hm' : (FlatView.ofStore t E₀).members B = some ms := hm
  unfold derivedFlatAt
  simp only [hm', ho]
  exact hw

/-- **The flattened family a family check compares is the one derived from the block.** An
observed `KernelModeled::check_nested_aux` on the block `B` and the represented entries `es`,
whose own entries are the block's types at the offset `off` (`FlatOriginals`), with `off` the
block's elimination offset (`BlockElim`, which `block_elim_blockElim` reads off the observed
`KernelModeled::block_elim`): `es` is the flattened family derived from `B` at `off`. -/
theorem blockDerivedFlat_of_checks {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B : _root_.Address} {off : Nat}
    {root : List (Call F)}
    (nested_walk : NestedWalkSpec κ (FlatView.ofStore t E₀) B root) (bd : Bounded root)
    (helim : BlockElim t E₀ B off)
    {b : Bytes.Address} {es : List FlatEntry} {xb xflat r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (hb : Bytes.RepAddressRef addrTy h b xb) (hB : ixAddr b = B)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (horig : FlatOriginals t E₀ B off es)
    (ev : ObsFn W "KernelModeled::check_nested_aux" [xb, xflat] h r h' cs) :
    BlockDerivedFlat t E₀ B off es := by
  obtain ⟨n, hw⟩ := check_nested_aux_spec hinj nested_walk bd hroot hb hB hes ev
  exact ⟨helim, n, derivedFlatAt_of_walk horig hw⟩

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry FlatView BlockElim BlockDerivedFlat indTypeAt
  defnValAt keyAddr)
open IxVM.Refinement.Binding.FamilyRecon (GuardDefnAnswers GuardIndAnswers NestedWalkSpec
  FlatOriginals FlatEntryRepExact flatListEnum blockDerivedFlat_of_checks natCast_inj_small)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The events of a family check the derivation is read off -/

/-- **The flat-block events of an observed `KernelModeled::check_family`**, between its
`block_elim` and its `family_refs_ok` (the heaps `C.m1191` and `C.mRefs` of the chain `C`): the
flattened family read off the record (`build_flat_block` at the offset `C.uo`), its comparison
with the family derived from the block (`check_nested_aux`), its length, and the completeness
assertion (the record has one recursor per entry, `complete`, or is empty outside a group's
validation, `emptyOk`; their disjunction is asserted). -/
structure CheckFamilyFlatChain {rc b rb : SourceValue F} {h_in h_out : Heap F}
    {calls : List (Call F)} (C : CheckFamilyChain rc b rb h_in h_out calls) where
  flat : SourceValue F
  mFlat : Heap F
  evFlat : SubCall calls "KernelCheck::build_flat_block" [rb, b, C.uo] C.m1191 flat mFlat
  vNested : SourceValue F
  mNested : Heap F
  evNested : SubCall calls "KernelModeled::check_nested_aux" [b, flat] mFlat vNested mNested
  nFlat : SourceValue F
  mLenFlat : Heap F
  evLenFlat : SubCall calls Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [flat] mNested nFlat mLenFlat
  diff : SourceValue F
  opDiff : evalBinOp .sub C.nRecs nFlat = .ok diff
  complete : SourceValue F
  mComplete : Heap F
  evComplete : SubCall calls "Fields::is_zero" [diff] mLenFlat complete mComplete
  empty : SourceValue F
  mEmpty : Heap F
  evEmpty : SubCall calls "Fields::is_zero" [C.nRecs] mComplete empty mEmpty
  validates : SourceValue F
  evValidates : SubCall calls "KernelRoles::rc_validates_group" [rc] mEmpty validates C.mRefs
  notValidates : SourceValue F
  opNot : evalBinOp .sub (.field 1 : SourceValue F) validates = .ok notValidates
  emptyOk : SourceValue F
  opEmptyOk : evalBinOp .mul empty notValidates = .ok emptyOk
  sum : SourceValue F
  opSum : evalBinOp .add complete emptyOk = .ok sum
  prod : SourceValue F
  opProd : evalBinOp .mul complete emptyOk = .ok prod
  opOr : evalBinOp .sub sum prod = .ok (.field 1)

private theorem callSub_of_eq' {xs calls : List (Call F)} (h : calls = xs) : CallSub xs calls := by
  subst h
  exact fun _ h => h

private def peelCall {calls rest cs : List (Call F)} {f : String}
    {args : List (SourceValue F)} {h₁ h₂ : Heap F} {v : SourceValue F}
    (h : CallSub (⟨f, args, h₁⟩ :: (cs ++ rest)) calls)
    (ev : ObsFn Obs.W f args h₁ v h₂ cs) :
    SubCall calls f args h₁ v h₂ ×' CallSub rest calls :=
  ⟨⟨cs, ev, h _ List.mem_cons_self,
      fun cl hcl => h cl (List.mem_cons_of_mem _ (List.mem_append_left rest hcl))⟩,
   fun cl hcl => h cl (List.mem_cons_of_mem _ (List.mem_append_right cs hcl))⟩

private def peelLast {calls cs : List (Call F)} {f : String}
    {args : List (SourceValue F)} {h₁ h₂ : Heap F} {v : SourceValue F}
    (h : CallSub (⟨f, args, h₁⟩ :: cs) calls)
    (ev : ObsFn Obs.W f args h₁ v h₂ cs) :
    SubCall calls f args h₁ v h₂ :=
  ⟨cs, ev, h _ List.mem_cons_self, fun cl hcl => h cl (List.mem_cons_of_mem _ hcl)⟩

/-- **The heap-chained reading of an observed `KernelModeled::check_family`, with its flat-block
events.** -/
theorem checkFamily_flatChain {rc b rb r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_family" [rc, b, rb] h r h' calls) :
    ∃ C : CheckFamilyChain rc b rb h h' calls, Nonempty (CheckFamilyFlatChain C) := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (sg112 := sg) (ev126 := e126) (ev148 := e148) (ev194 := e194) (heq217 := q217)
      (ev_yqjbwijz := eOrd) (ev231 := e231) (ev266 := e266) (ev309 := e309) (ev344 := e344)
      (ev403 := e403) (ev435 := e435) (ev465 := e465) (ev513 := e513) (ev601 := e601)
      (ev634 := e634) (heq650 := q650) (ev664 := e664) (ev686 := e686) (ev716 := e716)
      (ev759 := e759) (ev817 := e817) (ev796 := e796) (ev852 := e852) (ev_ursqbimm := eNoRole)
      (ev_srfmazjk := eNoTypeRole) (ev874 := e874) (ev896 := e896) (ev960 := e960)
      (ev939 := e939) (ev1011 := e1011)
      (ev990 := e990) (ev_edyzsqzv := eTysV) (ev_gkddqxhv := eLater) (ev_ittpynob := eCtorsV)
      (ev_biaifgpd := eRecsV) (ev1203 := eElim) (ev_cwwgzxtj := eFlat) (ev1246 := eNest)
      (ev_mitevvsv := eLenF) (op_jmfoqaec := oDiff) (ev_rqpeovbn := eZ1) (ev_xrhmaojz := eZ2)
      (ev_whimdwjd := eValG) (op_qfbltjlu := oNot) (op_cnutjuwu := oEmptyOk)
      (op_ymhwloon := oSum) (op_mvhbzaru := oProd) (op_zaucahqq := oOr) (heq_sujkqzii := qOr)
      (ev1305 := eRefs) (ev1343 := eChk) (ld1465 := lS9) (he1473 := hEqH) (hc1474 := hc) .. =>
    subst q217 q650 hEqH qOr
    have h0 := callSub_of_eq' hc
    have hSubSeg : CallSub _ calls := fun cl hcl => h0 cl (List.mem_append_left _ hcl)
    have hr : CallSub _ calls := fun cl hcl => h0 cl (List.mem_append_right _ hcl)
    let s126 := (peelCall hr e126).1
    let hr := (peelCall hr e126).2
    let ⟨s148, hr⟩ := peelCall hr e148
    let ⟨s194, hr⟩ := peelCall hr e194
    let ⟨sOrd, hr⟩ := peelCall hr eOrd
    let ⟨s231, hr⟩ := peelCall hr e231
    let ⟨s266, hr⟩ := peelCall hr e266
    let ⟨s309, hr⟩ := peelCall hr e309
    let ⟨s344, hr⟩ := peelCall hr e344
    let ⟨s403, hr⟩ := peelCall hr e403
    let ⟨s435, hr⟩ := peelCall hr e435
    let ⟨s465, hr⟩ := peelCall hr e465
    let ⟨s513, hr⟩ := peelCall hr e513
    let ⟨s601, hr⟩ := peelCall hr e601
    let ⟨s634, hr⟩ := peelCall hr e634
    let ⟨s664, hr⟩ := peelCall hr e664
    let ⟨s686, hr⟩ := peelCall hr e686
    let ⟨s716, hr⟩ := peelCall hr e716
    let ⟨s759, hr⟩ := peelCall hr e759
    let ⟨s817, hr⟩ := peelCall hr e817
    let ⟨s796, hr⟩ := peelCall hr e796
    let ⟨s852, hr⟩ := peelCall hr e852
    let ⟨sNoRole, hr⟩ := peelCall hr eNoRole
    let ⟨sNoTypeRole, hr⟩ := peelCall hr eNoTypeRole
    let ⟨s874, hr⟩ := peelCall hr e874
    let ⟨s896, hr⟩ := peelCall hr e896
    let ⟨s960, hr⟩ := peelCall hr e960
    let ⟨s939, hr⟩ := peelCall hr e939
    let ⟨s1011, hr⟩ := peelCall hr e1011
    let ⟨s990, hr⟩ := peelCall hr e990
    let ⟨sTysV, hr⟩ := peelCall hr eTysV
    let ⟨sLater, hr⟩ := peelCall hr eLater
    let ⟨sCtorsV, hr⟩ := peelCall hr eCtorsV
    let ⟨sRecsV, hr⟩ := peelCall hr eRecsV
    let ⟨sElim, hr⟩ := peelCall hr eElim
    let ⟨sFlat, hr⟩ := peelCall hr eFlat
    let ⟨sNest, hr⟩ := peelCall hr eNest
    let ⟨sLenF, hr⟩ := peelCall hr eLenF
    let ⟨sZ1, hr⟩ := peelCall hr eZ1
    let ⟨sZ2, hr⟩ := peelCall hr eZ2
    let ⟨sValG, hr⟩ := peelCall hr eValG
    let ⟨sRefs, hr⟩ := peelCall hr eRefs
    let sChk := peelLast hr eChk
    exact
      ⟨{ vSeg := _, m105 := _, cs107 := _, sg112 := sg
         subSeg := hSubSeg
         payload := _, m114 := _, evReadPayload := s126
         callsRest := _, callsPrefix := hc
         xRb := _, s1 := _, m136 := _, evGetRb := s148
         m184 := _, evRbEq := s194
         vOrd := _, mOrd := _, evInOrder := sOrd
         nAdv := _, s2 := _, m219 := _, evCountAdv := s231
         advList := _, s3 := _, m254 := _, evGetAdv := s266
         nWit := _, s4 := _, m297 := _, evCountWit := s309
         outside := _, s5 := _, m332 := _, evCheckWit := s344
         wset := _, m391 := _, evWset := s403
         vCont := _, m423 := _, evContRefs := s435
         aset := _, m453 := _, evCheckAdv := s465
         members := _, wSh := _, wRf := _, wUn := _, wBd := _, m501 := _, evLoadBlk := s513
         nInd := _, m589 := _, evLenMem := s601
         m624 := _, evIndcCnt := s634
         np := _, m652 := _, evNParams := s664
         tys := _, m674 := _, evTypes := s686
         tyM := _, s6 := _, m704 := _, evTypeMods := s716
         ctors := _, m747 := _, evCtors := s759
         nCtors := _, m807 := _, evLenCtors := s817
         ctorM := _, s7 := _, m784 := _, evCtorMods := s796
         recs := _, m840 := _, evRecs := s852
         vNoRole := _, mNoRole := _, evNoRole := sNoRole
         vNoTypeRole := _, mNoTypeRole := _, evNoTypeRole := sNoTypeRole
         nRecs := _, m862 := _, evLenRecs := s874
         recM := _, s8 := _, m884 := _, evRecMods := s896
         ctorRec := _, m950 := _, evSrcTail := s960
         src := _, m927 := _, evSrc := s939
         ctorRecM := _, m1001 := _, evDstTail := s1011
         dst := _, m978 := _, evDst := s990
         vTysVal := _, mTysVal := _, evTysVal := sTysV
         later := _, mLater := _, evLater := sLater
         vCtorsVal := _, mCtorsVal := _, evCtorsVal := sCtorsV
         vRecsVal := _, mRecsVal := _, evRecsVal := sRecsV
         bnl := _, uo := _, m1191 := _, evBlockElim := sElim
         mRefs := _, extAfterElim := sFlat.extends.trans (sNest.extends.trans (sLenF.extends.trans
           (sZ1.extends.trans (sZ2.extends.trans sValG.extends))))
         vRefs := _, m1293 := _, evRefsOk := sRefs
         s9 := _, evCheckRecs := sChk
         ldS9Nil := lS9 },
       ⟨{ flat := _, mFlat := _, evFlat := sFlat
          vNested := _, mNested := _, evNested := sNest
          nFlat := _, mLenFlat := _, evLenFlat := sLenF
          diff := _, opDiff := oDiff
          complete := _, mComplete := _, evComplete := sZ1
          empty := _, mEmpty := _, evEmpty := sZ2
          validates := _, evValidates := sValG
          notValidates := _, opNot := oNot
          emptyOk := _, opEmptyOk := oEmptyOk
          sum := _, opSum := oSum
          prod := _, opProd := oProd
          opOr := oOr }⟩⟩

/-! ## What the events give -/

private abbrev flatEntryTy : Generic.Ty :=
  .tuple [.ptr (.array .field 32), .field,
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]),
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])])]

theorem CheckFamilyChain.ext_in_m1191 {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (C : CheckFamilyChain rc b rb h h' calls) :
    Heap.Extends h C.m1191 :=
  (check_family_seg1_extends C.sg112).trans (C.ext_m105_m453.trans (C.ext_m453_m978.trans
    (C.evTysVal.extends.trans (C.evLater.extends.trans (C.evCtorsVal.extends.trans
      (C.evRecsVal.extends.trans C.evBlockElim.extends))))))

theorem CheckFamilyFlatChain.ext_in_mFlat {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {C : CheckFamilyChain rc b rb h h' calls}
    (X : CheckFamilyFlatChain C) : Heap.Extends h X.mFlat :=
  C.ext_in_m1191.trans X.evFlat.extends

theorem CheckFamilyFlatChain.ext_mFlat_mEmpty {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {C : CheckFamilyChain rc b rb h h' calls}
    (X : CheckFamilyFlatChain C) : Heap.Extends X.mFlat X.mEmpty :=
  X.evNested.extends.trans (X.evLenFlat.extends.trans
    (X.evComplete.extends.trans X.evEmpty.extends))

/-- **Under a group's validation the context answers that it validates a group**
(`rc_validates_group_spec` at the heap of the family check's own call). -/
theorem CheckFamilyFlatChain.validates_one {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {C : CheckFamilyChain rc b rb h h' calls}
    (X : CheckFamilyFlatChain C) {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {n : Nat}
    (hn : n < 77) (hrc : Claim.RCLimRep t bAddr (some n) h rc) : X.validates = .field 1 :=
  (IxVM.Refinement.Binding.rc_validates_group_spec hn
    (hrc.mono (X.ext_in_mFlat.trans X.ext_mFlat_mEmpty)) X.evValidates.obs).1

/-- **Completeness of the family record under a group's validation**: when the context validates
a group (`X.validates = 1`), the record's recursor count `n` is the length of the flattened
family, on any representation of it as a list. The bounds keep the two counts apart in the
field. -/
theorem CheckFamilyFlatChain.length_eq {rc b rb : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {C : CheckFamilyChain rc b rb h h' calls}
    (X : CheckFamilyFlatChain C) {α : Type} {R : Heap F → α → SourceValue F → Prop}
    {xs : List α} {n : Nat} (hvg : X.validates = .field 1)
    (hn : C.nRecs = .field (n : F)) (hnlt : n < 18446744069414584321)
    (hxs : RepList flatListEnum R X.mNested xs X.flat)
    (hlen : xs.length < 18446744069414584321) : xs.length = n := by
  have hxs' : RepList (Instance.mk "Lists::Node" [flatEntryTy]).symbol R X.mNested xs X.flat := by
    rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]
    exact hxs
  have evLen' : ObsFn Obs.W (Instance.mk "Lists::length" [flatEntryTy]).symbol
      [X.flat] X.mNested X.nFlat X.mLenFlat X.evLenFlat.cs := by
    rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]
    exact X.evLenFlat.obs
  obtain ⟨hflen, -⟩ := Lib.Lists.length_spec evLen' hxs'
  obtain ⟨hc, -⟩ := Lib.is_zero_spec X.evComplete.obs
  obtain ⟨he, -⟩ := Lib.is_zero_spec X.evEmpty.obs
  have h0 := X.opDiff
  have h1 := X.opNot
  have h2 := X.opEmptyOk
  have h3 := X.opSum
  have h4 := X.opProd
  have h5 := X.opOr
  rw [hvg] at h1
  simp only [evalBinOp, sub_self, Except.ok.injEq] at h1
  rw [← h1, he] at h2
  simp only [evalBinOp, mul_zero, Except.ok.injEq] at h2
  rw [← h2, hc] at h3 h4
  simp only [evalBinOp, add_zero, mul_zero, Except.ok.injEq] at h3 h4
  rw [← h3, ← h4] at h5
  simp only [evalBinOp, sub_zero, Except.ok.injEq] at h5
  have hd : X.diff = .field 0 := by
    by_contra hne
    rw [ite_eq_right hne] at h5
    exact absurd (Value.field.inj h5) (by decide)
  rw [hn, hflen, hd] at h0
  simp only [evalBinOp, Except.ok.injEq] at h0
  have hz : ((n : Nat) : F) - ((xs.length : Nat) : F) = 0 := Value.field.inj h0
  exact (natCast_inj_small hnlt hlen (sub_eq_zero.mp hz)).symm

/-- **`BlockDerivedFlat` from an observed family check.** On the chain `C` of an observed
`KernelModeled::check_family` of the block `B` with its flat-block events `X`, over a block record
of the run's store, the store reads `block_elim` makes (`GuardDefnAnswers`, `GuardIndAnswers`)
and the reading of `nested_walk` (`NestedWalkSpec`): the offset `block_elim` returns is the
block's elimination offset `off`, and the entries `es` the returned flattened family represents,
whose own entries are the block's types at `off` (`FlatOriginals`), are the flattened family
derived from `B` at `off`. -/
theorem blockDerivedFlat_of_checkFamily {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    (hka : ∀ a, keyAddr t (κ a) = some a)
    (hD : GuardDefnAnswers κ (defnValAt t E₀) calls)
    (hI : GuardIndAnswers κ (indTypeAt t E₀) calls)
    (nested_walk : NestedWalkSpec κ (FlatView.ofStore t E₀) B calls)
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {rc xb xrb : SourceValue F} {h h' : Heap F} {cs : List (Call F)} (hsub : CallSub cs calls)
    (C : CheckFamilyChain rc xb xrb h h' cs) (X : CheckFamilyFlatChain C)
    {bB : Bytes.Address} (hbB : Bytes.RepAddressRef addrTy h bB xb) (hb : ixAddr bB = B)
    {es : List FlatEntry}
    (hes : RepList flatListEnum (FlatEntryRepExact κ) X.mFlat es X.flat)
    (horig : ∀ off : Nat, C.uo = .field (off : F) → BlockElim t E₀ B off →
      FlatOriginals t E₀ B off es) :
    ∃ off : Nat, C.uo = .field (off : F) ∧ BlockDerivedFlat t E₀ B off es := by
  subst hb
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  obtain ⟨msPtr, hxm, hlist, -⟩ := Decl.load_block_info hS
    (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
    (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)) hB.record hB.muts
  have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
  rw [← hxe] at hlist
  have ext_501_652 : Heap.Extends C.m501 C.m652 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans C.evNParams.extends)
  have hmems652 : Core.Specs.Callees.MembersRep C.m652 ms.toList C.members :=
    Route.membersRep_of_repMutConstList (hlist.mono L1.repMutConst_heapMono₂ ext_501_652)
  have hb652 : Bytes.RepAddressRef addrTy C.m652 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_652)) hbB
  obtain ⟨-, typeAs, htA, htypes⟩ := L1.build_recur_addrs_spec hmems652 hb652 C.evTypes.obs
  have ext_674 : Heap.Extends C.m674 C.mRecsVal :=
    C.evTypeMods.extends.trans (C.evCtors.extends.trans (C.evLenCtors.extends.trans
      (C.evCtorMods.extends.trans (C.evRecs.extends.trans (C.evNoRole.extends.trans
        (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans (C.evRecMods.extends.trans
          (C.evSrcTail.extends.trans (C.evSrc.extends.trans (C.evDstTail.extends.trans
            (C.evDst.extends.trans (C.evTysVal.extends.trans (C.evLater.extends.trans
              (C.evCtorsVal.extends.trans C.evRecsVal.extends)))))))))))))))
  obtain ⟨a0, restAs, ind0, off, -, -, -, -, -, helim, huo⟩ :=
    block_elim_blockElim hka hD hI hbd hS hB hms_u64
      (fun cl hcl => hsub cl (C.evBlockElim.sub cl hcl)) htypes
      (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext_674 htA)
      C.evBlockElim.obs
  exact ⟨off, huo, blockDerivedFlat_of_checks hinj nested_walk hbd helim
    (fun c hc => hsub c (X.evNested.sub c hc))
    (Bytes.repAddressRef_heapMono₂ addrTy X.ext_in_mFlat hbB) rfl hes (horig off huo helim)
    X.evNested.obs⟩

end IxVM.Refinement.Typing.FamilyAlias
