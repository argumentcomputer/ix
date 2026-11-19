import IxVMRefinement.Binding.FamilyReconSites
import IxVMRefinement.Obs.KernelCheck12

/-! # Flattened family entries and recursive-field classification on `TmOExact`

This module refines the flattened-family lookup and field-classification helpers of `KernelCheck`
directly on `TmOExact` and `RepKLevelList` (without `NoLetTele` or `MatchStructFaithful`):

* `flatListEnum`, `fieldListEnum`, `RepNatField`, `FlatEntryRepExact`;
* `flat_member_at_spec`: `KernelCheck::flat_member_at`;
* `spec_params_dom_prefix_match_spec`: `KernelCheck::spec_params_dom_prefix_match` (`specPrefix`);
* `flat_find_matching_spec`: `KernelCheck::flat_find_matching` (`flatFindMatching`);
* `is_rec_field_peel_spec`: `KernelCheck::is_rec_field_peel` (`isRecField`);
* `walk_fields_classify_spec` and `walk_fields_classify_nil_spec`:
  `KernelCheck::walk_fields_classify` (`fieldsClassify`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry)
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Exact flat-entry and field-list representations -/

/-- The list enum of a flattened family's entries. -/
abbrev flatListEnum : String :=
  Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»

/-- The list enum of field-encoded naturals (`Lists::Node<Field>`). -/
abbrev fieldListEnum : String := Obs.Names.«Lists::Node<Field>»

/-- Representation of a small natural as a field value (heap-independent). -/
def RepNatField (_ : Heap F) (n : Nat) (v : SourceValue F) : Prop :=
  v = .field (n : F)

theorem repNatField_heapMono₂ : HeapMono₂ RepNatField :=
  fun _ _ _ _ _ h => h

theorem fieldList_mono {h₁ h₂ : Heap F} {ns : List Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hl : RepList fieldListEnum RepNatField h₁ ns p) :
    RepList fieldListEnum RepNatField h₂ ns p :=
  repList_heapMono₂ fieldListEnum repNatField_heapMono₂ ext hl

/-- **A flattened family's entry as the circuit holds it, with exact terms and exact levels.** -/
def FlatEntryRepExact (κ : _root_.Address → KKey) (h : Heap F) (e : FlatEntry)
    (p : SourceValue F) : Prop :=
  ∃ (xa xps xls : SourceValue F) (a : Bytes.Address), p = .tuple [xa, auxVal e.aux, xps, xls] ∧
    Bytes.RepAddressRef addrTy h a xa ∧ ixAddr a = e.addr ∧
    RepList kexprListEnum (TmOExact κ) h e.params xps ∧ RepKLevelList h e.levels xls

theorem FlatEntryRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {e : FlatEntry}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (h : FlatEntryRepExact κ h₁ e p) :
    FlatEntryRepExact κ h₂ e p := by
  obtain ⟨xa, xps, xls, a, rfl, ra, ha, hps, hls⟩ := h
  exact ⟨xa, xps, xls, a, rfl, Bytes.repAddressRef_heapMono₂ addrTy ext ra, ha,
    tmOExactList_mono ext hps, hls.mono ext⟩

theorem flatEntryRepExact_heapMono₂ {κ : _root_.Address → KKey} :
    HeapMono₂ (FlatEntryRepExact κ) :=
  fun _ _ _ _ ext h => h.mono ext

theorem flatList_mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {es : List FlatEntry}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (hl : RepList flatListEnum (FlatEntryRepExact κ) h₁ es p) :
    RepList flatListEnum (FlatEntryRepExact κ) h₂ es p :=
  repList_heapMono₂ flatListEnum flatEntryRepExact_heapMono₂ ext hl

/-! ## `flat_member_at` -/

/-- **`KernelCheck::flat_member_at(flat, pos)`** at a position inside the list is the entry
there; no allocation. -/
theorem flat_member_at_spec {κ : _root_.Address → KKey} :
    ∀ (es : List FlatEntry) (pos : Nat) {xflat r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, pos < es.length → pos < 9223372036854775808 →
      ObsFn W "KernelCheck::flat_member_at" [xflat, .field (pos : F)] h r h' cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      h' = h ∧ ∃ e, es[pos]? = some e ∧ FlatEntryRepExact κ h e r := by
  intro es
  induction es with
  | nil => intro pos _ _ _ _ _ hlt; exact absurd hlt (Nat.not_lt_zero _)
  | cons e es ih =>
    intro pos xflat r h h' cs hlt hpos ev hes
    rcases Obs.«KernelCheck::flat_member_at».obs ev with
      ⟨m₁, m₂, m₃, ld, -⟩ | ⟨x_m, x_rest, ld, hv, rfl, rfl, -⟩ |
      ⟨x_m, x_rest, cs₁, v₁, ld, hne, op, ev₁, -⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    · obtain ⟨z, zs, hzs, hz, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      rw [← hz1] at hz
      have hp : pos = 0 := field_natCast_eq_zero (by omega) hv
      subst hp
      exact ⟨rfl, e, rfl, hz⟩
    · obtain ⟨z, zs, hzs, -, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      rw [← hz2] at hzs'
      have hp : pos ≠ 0 := field_natCast_ne_zero (by omega) hne
      obtain rfl := binop_sub_one_nat (by omega) op
      obtain ⟨hh, e', he', hr⟩ := ih (pos - 1) (by simp at hlt; omega) (by omega) ev₁ hzs'
      refine ⟨hh, e', ?_, hr⟩
      obtain ⟨p, rfl⟩ : ∃ p, pos = p + 1 := ⟨pos - 1, by omega⟩
      simpa using he'

/-! ## `spec_params_dom_prefix_match` and `flat_find_matching` -/

/-- **`KernelCheck::spec_params_dom_prefix_match`** decides `specPrefix sp args liftBy`
bidirectionally on `TmOExact` when `κ` is injective. -/
theorem spec_params_dom_prefix_match_spec {κ : _root_.Address → KKey}
    (hinj : Function.Injective κ) {liftBy : Nat} (hlift : liftBy < 4611686018427387904) :
    ∀ (sp args : List KExpr) {xsp xargs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::spec_params_dom_prefix_match"
        [xsp, xargs, .field (liftBy : F)] h r h' cs →
      IxVM.Consistency.Bounded cs →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepList kexprListEnum (TmOExact κ) h args xargs →
      r = .field (if specPrefix sp args liftBy then 1 else 0) := by
  intro sp
  induction sp with
  | nil =>
    intro args xsp xargs r h h' cs ev _ hsp _
    match Obs.«KernelCheck::spec_params_dom_prefix_match».obs ev with
    | .Nil (he20 := hr) .. => rw [hr]; rfl
    | .Cons_Nil (ld12 := ld) .. | .Cons_Cons_n1 (ld12 := ld) ..
    | .Cons_Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsp ld
      cases hcons
  | cons s sr ih =>
    intro args xsp xargs r h h' cs ev hbnd hsp hargs
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    match Obs.«KernelCheck::spec_params_dom_prefix_match».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hsp ld
    | .Cons_Nil (ld51 := ld2) (he59 := hr) .. =>
      obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hargs ld2
      rw [hr]; rfl
    | .Cons_Cons_n1 (x_s := xs) (x_sr := xsr) (x_a := xa) (x_ar := xar) (v79 := vl)
        (m80 := m1) (cs90 := cs1) (m117 := m2) (cs_noorzezv := cs2) (cs154 := cs3)
        (ld12 := ld1) (ld51 := ld2) (ev92 := evl) (ev_vzplvuse := eveq)
        (ev156 := evrec) (hc181 := hc) .. =>
      obtain ⟨s', sr', h1, hs, hsr⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsp ld1
      injection h1 with hs' hsr'; subst hs' hsr'
      obtain ⟨a, ar, rfl, ha, har⟩ := IxVM.Refinement.Core.RepList.cons_of_load hargs ld2
      have evl' : ObsFn W "KernelSubst::expr_lift"
          [xs, .field (liftBy : F), .field ((0 : Nat) : F)] h vl m1 cs1 := by simpa using evl
      have hvl := expr_lift_tmOExact hlift (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) hs evl'
      have heq := kexpr_zeta_struct_eq_exact hinj hvl (ha.mono evl.heap_extends)
        (sub fun c hc' => by rw [hc]; simp [hc']) eveq
      have hsame : s.liftLooseBVars liftBy 0 = a := by
        by_contra hne; rw [ite_eq_right hne] at heq
        exact absurd (Value.field.inj heq) (by decide)
      have ext12 := evl.heap_extends.trans eveq.heap_extends
      have hrec := ih ar evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (tmOExactList_mono ext12 hsr) (tmOExactList_mono ext12 har)
      rw [hrec]
      simp [specPrefix, hsame]
    | .Cons_Cons_other (x_s := xs) (x_sr := xsr) (x_a := xa) (x_ar := xar) (v79 := vl)
        (m80 := m1) (cs90 := cs1) (v116 := veq) (m117 := m2) (cs_noorzezv := cs2)
        (ld12 := ld1) (ld51 := ld2) (ev92 := evl) (ev_vzplvuse := eveq)
        (hne182 := hne) (he186 := hr) (hc188 := hc) .. =>
      subst hr
      obtain ⟨s', sr', h1, hs, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hsp ld1
      injection h1 with hs' hsr'; subst hs' hsr'
      obtain ⟨a, ar, rfl, ha, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hargs ld2
      have evl' : ObsFn W "KernelSubst::expr_lift"
          [xs, .field (liftBy : F), .field ((0 : Nat) : F)] h vl m1 cs1 := by simpa using evl
      have hvl := expr_lift_tmOExact hlift (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) hs evl'
      have heq := kexpr_zeta_struct_eq_exact hinj hvl (ha.mono evl.heap_extends)
        (sub fun c hc' => by rw [hc]; simp [hc']) eveq
      have hdiff : s.liftLooseBVars liftBy 0 ≠ a := fun h => by
        rw [ite_eq_left h] at heq; exact hne heq
      have hbf : (s.liftLooseBVars liftBy 0 == a) = false := beq_eq_false_iff_ne.mpr hdiff
      simp [specPrefix, hbf]

private theorem field_mul_bool_flat {b₁ b₂ : Bool} {v : SourceValue F}
    (op : evalBinOp .mul (.field (if b₁ then 1 else 0)) (.field (if b₂ then 1 else 0)) = .ok v) :
    v = .field (if (b₁ && b₂) then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> (simp only [evalBinOp, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, ↓reduceIte] at op ⊢; injection op with hv; rw [← hv]; simp)

/-- **`KernelCheck::flat_find_matching`** computes `flatFindMatching` shifted by `pos`
bidirectionally on `FlatEntryRepExact` when `κ` is injective. -/
theorem flat_find_matching_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {liftBy : Nat} (hlift : liftBy < 4611686018427387904) :
    ∀ (es : List FlatEntry) (pos : Nat)
      {a : Bytes.Address} {us : List KLevel} {args : List KExpr}
      {xflat xca xus xargs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::flat_find_matching"
        [xflat, xca, xus, xargs, .field (liftBy : F), .field (pos : F)] h r h' cs →
      IxVM.Consistency.Bounded cs →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h a xca →
      RepKLevelList h us xus →
      RepList kexprListEnum (TmOExact κ) h args xargs →
      match flatFindMatching es (ixAddr a) us args liftBy with
      | some k => r = .tuple [.field 1, .field ((pos + k : Nat) : F)]
      | none => r = .tuple [.field 0, .field 0] := by
  intro es
  induction es with
  | nil =>
    intro pos a us args xflat xca xus xargs r h h' cs ev _ hes _ _ _
    match Obs.«KernelCheck::flat_find_matching».obs ev with
    | .Nil (he24 := hr) .. => rw [hr]; rfl
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro pos a us args xflat xca xus xargs r h h' cs ev hbnd hes rca rus rargs
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    have evalEntry :
        ∀ {xrest xm xaux xsp xou v1 m1 cs1 v2 m2 cs2 vout : SourceValue F → Prop},
          True := fun {_ _ _ _ _ _ _ _ _ _ _ _} => trivial
    match Obs.«KernelCheck::flat_find_matching».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1 (x_rest := xrest) (x_member_addr := xm) (x_is_aux := xaux) (x_sp := xsp)
        (x_ou := xou) (v93 := v1) (m94 := m1) (cs104 := cs1) (v175 := v2) (m176 := m2)
        (cs178 := cs2) (ld12 := ld) (ev106 := evaeq) (sg183 := sg) (op200 := opm)
        (he211 := hr) (hc226 := hc) .. =>
      subst hr
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae rca
      have haddr_eq : (if ae = a then (1 : F) else 0) = if e.addr == ixAddr a then 1 else 0 := by
        rw [← hae]
        by_cases h : ae = a
        · subst h; simp
        · have hne : ixAddr ae ≠ ixAddr a := fun heq => h (ixAddr_inj heq)
          rw [ite_eq_right h, beq_eq_false_iff_ne.mpr hne]; rfl
      rw [haddr_eq] at hv1; subst hv1
      have hv2 : v2 = .field (if (!e.aux || (specPrefix e.params args liftBy && e.levels == us))
          then 1 else 0) := by
        cases sg with
        | n0 hv0 hr2 _ _ =>
          have haux : e.aux = false := auxVal_eq_zero.mp hv0
          rw [hr2, haux]; rfl
        | other x1 y2 m12 cs_p cs_l hne0 evp evl op_pl hc_s =>
          have haux : e.aux = true := by
            cases h : e.aux
            · exact (hne0 (auxVal_eq_zero.mpr h)).elim
            · rfl
          have b_p : IxVM.Consistency.Bounded cs_p :=
            sub fun c hc' => by rw [hc, hc_s]; simp [hc']
          have hx1 := spec_params_dom_prefix_match_spec hinj hlift e.params args evp b_p hsp rargs
          obtain ⟨hy2, -⟩ := level_list_struct_eq_exact (hou.mono evp.heap_extends)
            (rus.mono evp.heap_extends) evl
          have hl_eq : (if e.levels = us then (1 : F) else 0) = if e.levels == us then 1 else 0 := by
            by_cases h : e.levels = us
            · subst h; simp
            · rw [ite_eq_right h, beq_eq_false_iff_ne.mpr h]; rfl
          rw [hl_eq] at hy2
          subst hx1 hy2
          have hm := field_mul_bool_flat op_pl
          rw [haux]; simpa using hm
      subst hv2
      have hmul := field_mul_bool_flat opm
      have hpred : (e.addr == ixAddr a &&
          (!e.aux || (specPrefix e.params args liftBy && e.levels == us))) = true := by
        cases hp : (e.addr == ixAddr a &&
            (!e.aux || (specPrefix e.params args liftBy && e.levels == us)))
        · rw [hp] at hmul; exact absurd (Value.field.inj hmul) (by decide)
        · rfl
      unfold flatFindMatching
      simp [List.findIdx?_cons, hpred]
    | .Cons_other (x_rest := xrest) (x_member_addr := xm) (x_is_aux := xaux) (x_sp := xsp)
        (x_ou := xou) (v93 := v1) (m94 := m1) (cs104 := cs1) (v175 := v2) (m176 := m2)
        (cs178 := cs2) (v184 := vout) (cs234 := cs3) (v_zlvrmwlu := vpos1)
        (ld12 := ld) (ev106 := evaeq) (sg183 := sg) (op200 := opm) (hne227 := hne1)
        (op_epyjxidj := op1) (ev236 := evrec) (hc285 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae rca
      have haddr_eq : (if ae = a then (1 : F) else 0) = if e.addr == ixAddr a then 1 else 0 := by
        rw [← hae]
        by_cases h : ae = a
        · subst h; simp
        · have hne : ixAddr ae ≠ ixAddr a := fun heq => h (ixAddr_inj heq)
          rw [ite_eq_right h, beq_eq_false_iff_ne.mpr hne]; rfl
      rw [haddr_eq] at hv1; subst hv1
      have hseg : v2 = .field (if (!e.aux || (specPrefix e.params args liftBy && e.levels == us))
          then 1 else 0) ∧ Heap.Extends m1 m2 := by
        cases sg with
        | n0 hv0 hr2 hh2 _ =>
          have haux : e.aux = false := auxVal_eq_zero.mp hv0
          subst hh2; rw [hr2, haux]; exact ⟨rfl, Heap.Extends.refl _⟩
        | other x1 y2 m12 cs_p cs_l hne0 evp evl op_pl hc_s =>
          have haux : e.aux = true := by
            cases h : e.aux
            · exact (hne0 (auxVal_eq_zero.mpr h)).elim
            · rfl
          have b_p : IxVM.Consistency.Bounded cs_p :=
            sub fun c hc' => by rw [hc, hc_s]; simp [hc']
          have hx1 := spec_params_dom_prefix_match_spec hinj hlift e.params args evp b_p hsp rargs
          obtain ⟨hy2, hh_l⟩ := level_list_struct_eq_exact (hou.mono evp.heap_extends)
            (rus.mono evp.heap_extends) evl
          have hl_eq : (if e.levels = us then (1 : F) else 0) = if e.levels == us then 1 else 0 := by
            by_cases h : e.levels = us
            · subst h; simp
            · rw [ite_eq_right h, beq_eq_false_iff_ne.mpr h]; rfl
          rw [hl_eq] at hy2
          subst hx1 hy2 hh_l
          have hm := field_mul_bool_flat op_pl
          rw [haux]
          exact ⟨by simpa using hm, evp.heap_extends⟩
      obtain ⟨hv2, ext2⟩ := hseg
      subst hv2
      have hmul := field_mul_bool_flat opm
      have hpred : (e.addr == ixAddr a &&
          (!e.aux || (specPrefix e.params args liftBy && e.levels == us))) = false := by
        cases hp : (e.addr == ixAddr a &&
            (!e.aux || (specPrefix e.params args liftBy && e.levels == us)))
        · rfl
        · rw [hp] at hmul; exact (hne1 hmul).elim
      obtain rfl := binop_add_one_nat op1
      have hrec := ih (pos + 1) evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (flatList_mono ext2 hes') (Bytes.repAddressRef_heapMono₂ addrTy ext2 rca)
        (rus.mono ext2) (tmOExactList_mono ext2 rargs)
      unfold flatFindMatching at hrec ⊢
      simp only [List.findIdx?_cons, hpred]
      cases hfi : List.findIdx? (fun e => e.addr == ixAddr a &&
          (!e.aux || (specPrefix e.params args liftBy && e.levels == us))) es with
      | none => rw [hfi] at hrec; exact hrec
      | some k =>
        rw [hfi] at hrec
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hrec

/-! ## `is_rec_field_peel` -/

/-- **`KernelCheck::is_rec_field_peel`** computes `isRecField V es liftBy E` exactly on
`TmOExact` when `κ` is injective and `AddrOf κ V` holds (with zero no-let premise). -/
theorem is_rec_field_peel_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {V : ReconView} (hA : AddrOf κ V) {liftBy : Nat} (hlift : liftBy < 4611686018427387904)
    {es : List FlatEntry} {E : KExpr} {xty xflat r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_rec_field_peel"
      [xty, xflat, .field (liftBy : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : TmOExact κ h E xty)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat) :
    match isRecField V es liftBy E with
    | some m => r = .tuple [.field 1, .field (m : F)]
    | none => r = .tuple [.field 0, .field 0] := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::is_rec_field_peel».obs ev with
  | .Forall (x_body := xbody) (cs40 := cs1) (ld12 := ld) (ev42 := e1) (hc67 := hc) .. =>
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    have hrec := is_rec_field_peel_spec hinj hA hlift e1
      (sub fun c hc' => by rw [hc]; simp [hc']) hB hes
    simpa [isRecField, peelAll] using hrec
  | .Let (x_v := xv) (x_b := xb) (v_wqlgkxlw := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_itgiedpj := cs2) (ld12 := ld)
      (ev_gemvpjgn := e1) (ev_zkphyhvi := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V0, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact is_rec_field_peel_spec hinj hA hlift e2
      (sub fun c hc' => by rw [hc]; simp [hc']) hv' (flatList_mono e1.heap_extends hes)
  | .other_Const (v1 := v) (m73 := m1) (cs_jssmsurq := cs1) (x_head := xhd) (x_args := xargs)
      (x_caddr := xca) (x_us := xus) (cs144 := cs2) (ld12 := ld) (hne68 := hnf)
      (hne_ttotnwna := hnl) (ev_ygzmqkmf := evsp) (ld122 := ldh) (ev146 := evfm)
      (hc186 := hc) .. =>
    have hpeel := peelAll_of_not_forall_not_let hE ld hnf hnl
    obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec hE
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, us, hfn_eq, rca, rus⟩ := TmOExact.const_of_load hfn ldh
    have evfm' : ObsFn W "KernelCheck::flat_find_matching"
        [xflat, xca, xus, xargs, .field (liftBy : F), .field ((0 : Nat) : F)] m1 r h' cs2 := by
      simpa using evfm
    have hfm := flat_find_matching_spec hinj hlift es 0 evfm'
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (flatList_mono evsp.heap_extends hes) rca rus hargs
    simp only [isRecField, hpeel, hfn_eq, hA (ixAddr ca)]
    simpa using hfm
  | .other_other (v1 := v) (m73 := m1) (cs_jssmsurq := cs1) (x_head := xhd) (x_args := xargs)
      (v111 := vh) (ld12 := ld) (hne68 := hnf) (hne_ttotnwna := hnl) (ev_ygzmqkmf := evsp)
      (ld122 := ldh) (hne187 := hneC) (he195 := hr) (hc209 := hc) .. =>
    subst hr
    have hpeel := peelAll_of_not_forall_not_let hE ld hnf hnl
    obtain ⟨hfn, hnlh, -⟩ := collect_spine_zeta_spec hE
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    unfold isRecField
    rw [hpeel]
    cases hf : E.getAppFn with
    | const ck cus => exact (tmOExact_not_const hfn hnlh ldh hneC ck cus hf).elim
    | _ => rfl
termination_by cs.length

/-! ## `walk_fields_classify` -/

private theorem reverse_kexpr_spec {κ : _root_.Address → KKey} {xs : List KExpr}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (TmOExact κ) h xs l) :
    RepList kexprListEnum (TmOExact κ) h' xs.reverse r := by
  have hrev := Lib.Lists.reverse_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (tmOExact_heapMono₂ (κ := κ))
    (by rw [Obs.Names.«Lists::reverse<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hrev

private theorem reverse_field_spec {ns : List Nat}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::reverse<Field>» [l] h r h' cs)
    (hl : RepList fieldListEnum RepNatField h ns l) :
    RepList fieldListEnum RepNatField h' ns.reverse r := by
  have hrev := Lib.Lists.reverse_spec (t := .field) repNatField_heapMono₂
    (by rw [Obs.Names.«Lists::reverse<Field>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<Field>».symbol]; exact hl)
  rwa [Obs.Names.«Lists::Node<Field>».symbol] at hrev

/-- **`KernelCheck::walk_fields_classify`** with accumulators refines `fieldsClassify V f es
liftBy fidx E` at every large enough fuel, on `TmOExact` (stepping through any `Let` nodes),
preserving `AddrIn S κ`. -/
theorem walk_fields_classify_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop}
    {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {V : ReconView} (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V)
    (hI : IndAnswers rootCalls S κ V) (hC : CtorOfAnswers rootCalls S V)
    (hM : ModeledAnswers rootCalls S V)
    {es : List FlatEntry} {liftBy : Nat} :
    ∀ {E : KExpr} {fidx : Nat}
      {domsAcc normAcc : List KExpr} {recAcc recMemAcc : List Nat}
      {xrc xty xflat xdoms xrec xrecmem xnorm xtys r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      liftBy + fidx + (peelAll E).1.length < 4611686018427387904 →
      ObsFn W "KernelCheck::walk_fields_classify"
        [xrc, xty, xflat, xdoms, xrec, xrecmem, xnorm, .field (fidx : F),
          .field (liftBy : F), xtys] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ rootCalls) →
      TmOExact κ h E xty → AddrIn S κ E →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList kexprListEnum (TmOExact κ) h domsAcc xdoms →
      RepList fieldListEnum RepNatField h recAcc xrec →
      RepList fieldListEnum RepNatField h recMemAcc xrecmem →
      RepList kexprListEnum (TmOExact κ) h normAcc xnorm →
      Heap.Extends h h' ∧
      ∃ (xds xri xrm xret xns : SourceValue F)
        (ds ns : List KExpr) (ri rm : List Nat) (ret : KExpr),
        r = .tuple [xds, xri, xrm, xret, xns] ∧
        RepList kexprListEnum (TmOExact κ) h' (domsAcc.reverse ++ ds) xds ∧
        RepList fieldListEnum RepNatField h' (recAcc.reverse ++ ri) xri ∧
        RepList fieldListEnum RepNatField h' (recMemAcc.reverse ++ rm) xrm ∧
        TmOExact κ h' ret xret ∧
        RepList kexprListEnum (TmOExact κ) h' (normAcc.reverse ++ ns) xns ∧
        (∀ D ∈ ds, AddrIn S κ D) ∧ AddrIn S κ ret ∧ (∀ N ∈ ns, AddrIn S κ N) ∧
        Eventually fun f => fieldsClassify V f es liftBy fidx E = some (ds, ri, rm, ret, ns) := by
  intro E fidx domsAcc normAcc recAcc recMemAcc xrc xty xflat xdoms xrec xrecmem xnorm xtys r
    h h' cs hbound ev hbnd hsub hE hEin hes hdoms hrec hrecmem hnorm
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have rsub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → ∀ c ∈ cs', c ∈ rootCalls :=
    fun hs c hc => hsub c (hs c hc)
  have hext : Heap.Extends h h' := ObsFn.heap_extends ev
  match Obs.«KernelCheck::walk_fields_classify».obsx ev with
  | .Forall_n1_bind (x_dom := xdom) (x_body := xbody) (v36 := vnd) (m37 := m1) (cs47 := cs1)
      (m75 := m2) (cs85 := cs2) (v90 := vlb) (m122 := m3) (m153 := m4) (m184 := m5)
      (x_mem_idx := xmem) (m243 := m6) (m274 := m7) (cs307 := cs3) (v317 := vf1)
      (ld12 := ld) (ev49 := evw) (op118 := oplb) (ev87 := evrecf) (hm132 := hm3)
      (hm163 := hm4) (hm194 := hm5) (hm253 := hm6) (hm284 := hm7) (op382 := opf1)
      (ev309 := evnext) (hc398 := hc) .. =>
    subst hm3 hm4 hm5 hm6 hm7
    obtain ⟨D, B, ℓ, rfl, hD1, hB, -⟩ := TmOExact.forallE_of_load hE ld
    obtain ⟨ext1, nd, ⟨aw, haw⟩, hnd, hndIn⟩ := whnf_tele_spec hA hD hI hC hM (cs1.length + 1)
      (Nat.lt_succ_self _) evw (sub fun c hc' => by rw [hc]; simp [hc'])
      (rsub fun c hc' => by rw [hc]; simp [hc']) hD1 hEin.1
    obtain rfl := binop_add_nat oplb
    have hrf := is_rec_field_peel_spec hinj hA (by simp [peelAll] at hbound; omega) evrecf
      (sub fun c hc' => by rw [hc]; simp [hc']) hnd (flatList_mono ext1 hes)
    cases hrf_eq : isRecField V es (liftBy + fidx) nd with
    | none =>
      rw [hrf_eq] at hrf
      injection hrf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    | some m =>
      rw [hrf_eq] at hrf
      injection hrf with hp; injection hp with _ hp2; injection hp2 with hmem
      subst hmem
      have ext2 := evrecf.heap_extends
      have ext12 := ext1.trans ext2
      let h3 := m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]
      let h4 := h3 ++ [.construct kexprListEnum "Cons" [vnd, xnorm]]
      let h5 := h4 ++ [.construct kexprListEnum "Cons" [xdom, xtys]]
      let h6 := h5 ++ [.construct fieldListEnum "Cons" [.field (fidx : F), xrec]]
      let h7 := h6 ++ [.construct fieldListEnum "Cons" [.field (m : F), xrecmem]]
      have ext3 : Heap.Extends m2 h3 := Heap.Extends.snoc _ _
      have ext4 : Heap.Extends h3 h4 := Heap.Extends.snoc _ _
      have ext5 : Heap.Extends h4 h5 := Heap.Extends.snoc _ _
      have ext6 : Heap.Extends h5 h6 := Heap.Extends.snoc _ _
      have ext7 : Heap.Extends h6 h7 := Heap.Extends.snoc _ _
      have hdoms' : RepList kexprListEnum (TmOExact κ) h3 (D :: domsAcc) _ :=
        Lib.rep_store_cons tmOExact_heapMono₂ (hD1.mono ext12) (tmOExactList_mono ext12 hdoms)
      have hnorm' : RepList kexprListEnum (TmOExact κ) h4 (nd :: normAcc) _ :=
        Lib.rep_store_cons tmOExact_heapMono₂ (hnd.mono (ext2.trans ext3))
          (tmOExactList_mono (ext12.trans ext3) hnorm)
      have hrec' : RepList fieldListEnum RepNatField h6 (fidx :: recAcc) _ :=
        Lib.rep_store_cons repNatField_heapMono₂ rfl
          (fieldList_mono (ext12.trans (ext3.trans (ext4.trans ext5))) hrec)
      have hrecmem' : RepList fieldListEnum RepNatField h7 (m :: recMemAcc) _ :=
        Lib.rep_store_cons repNatField_heapMono₂ rfl
          (fieldList_mono (ext12.trans (ext3.trans (ext4.trans (ext5.trans ext6)))) hrecmem)
      have extAll : Heap.Extends h h7 :=
        ext12.trans (ext3.trans (ext4.trans (ext5.trans (ext6.trans ext7))))
      obtain rfl := binop_add_one_nat opf1
      have hlt : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨-, xds, xri, xrm, xret, xns, ds, ns, ri, rm, ret, hr, h1, h2, h3, h4, h5,
          hdsIn, hretIn, hnsIn, ⟨ab, hab⟩⟩ :=
        walk_fields_classify_spec hinj hA hD hI hC hM
          (by simp only [peelAll, List.length_cons] at hbound; omega)
          evnext (sub fun c hc' => by rw [hc]; simp [hc'])
          (rsub fun c hc' => by rw [hc]; simp [hc'])
          (hB.mono extAll) hEin.2 (flatList_mono extAll hes)
          (tmOExactList_mono (ext4.trans (ext5.trans (ext6.trans ext7))) hdoms')
          (fieldList_mono ext7 hrec') hrecmem'
          (tmOExactList_mono (ext5.trans (ext6.trans ext7)) hnorm')
      refine ⟨hext, xds, xri, xrm, xret, xns, D :: ds, nd :: ns, fidx :: ri, m :: rm, ret, hr,
        by simpa using h1, by simpa using h2, by simpa using h3, h4, by simpa using h5,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hEin.1; exact hdsIn X hm),
        hretIn,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hndIn; exact hnsIn X hm),
        ⟨max aw ab, fun f hf => ?_⟩⟩
      simp only [fieldsClassify, haw f f (by omega) (by omega), hab f (by omega), hrf_eq]
  | .Forall_other (x_dom := xdom) (x_body := xbody) (v36 := vnd) (m37 := m1) (cs47 := cs1)
      (v74 := vrf) (m75 := m2) (cs85 := cs2) (v90 := vlb) (m122 := m3) (m153 := m4) (m184 := m5)
      (cs405 := cs3) (v415 := vf1) (ld12 := ld) (ev49 := evw) (op118 := oplb) (ev87 := evrecf)
      (hm132 := hm3) (hm163 := hm4) (hm194 := hm5) (op480 := opf1) (ev407 := evnext)
      (hc496 := hc) (hnt0 := hnt) .. =>
    subst hm3 hm4 hm5
    obtain ⟨D, B, ℓ, rfl, hD1, hB, -⟩ := TmOExact.forallE_of_load hE ld
    obtain ⟨ext1, nd, ⟨aw, haw⟩, hnd, hndIn⟩ := whnf_tele_spec hA hD hI hC hM (cs1.length + 1)
      (Nat.lt_succ_self _) evw (sub fun c hc' => by rw [hc]; simp [hc'])
      (rsub fun c hc' => by rw [hc]; simp [hc']) hD1 hEin.1
    obtain rfl := binop_add_nat oplb
    have hrf := is_rec_field_peel_spec hinj hA (by simp [peelAll] at hbound; omega) evrecf
      (sub fun c hc' => by rw [hc]; simp [hc']) hnd (flatList_mono ext1 hes)
    cases hrf_eq : isRecField V es (liftBy + fidx) nd with
    | some m =>
      rw [hrf_eq] at hrf
      exact (hnt (.field (m : F)) hrf).elim
    | none =>
      have ext2 := evrecf.heap_extends
      have ext12 := ext1.trans ext2
      let h3 := m2 ++ [.construct kexprListEnum "Cons" [xdom, xdoms]]
      let h4 := h3 ++ [.construct kexprListEnum "Cons" [vnd, xnorm]]
      let h5 := h4 ++ [.construct kexprListEnum "Cons" [xdom, xtys]]
      have ext3 : Heap.Extends m2 h3 := Heap.Extends.snoc _ _
      have ext4 : Heap.Extends h3 h4 := Heap.Extends.snoc _ _
      have ext5 : Heap.Extends h4 h5 := Heap.Extends.snoc _ _
      have hdoms' : RepList kexprListEnum (TmOExact κ) h3 (D :: domsAcc) _ :=
        Lib.rep_store_cons tmOExact_heapMono₂ (hD1.mono ext12) (tmOExactList_mono ext12 hdoms)
      have hnorm' : RepList kexprListEnum (TmOExact κ) h4 (nd :: normAcc) _ :=
        Lib.rep_store_cons tmOExact_heapMono₂ (hnd.mono (ext2.trans ext3))
          (tmOExactList_mono (ext12.trans ext3) hnorm)
      have extAll : Heap.Extends h h5 := ext12.trans (ext3.trans (ext4.trans ext5))
      obtain rfl := binop_add_one_nat opf1
      have hlt : cs3.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨-, xds, xri, xrm, xret, xns, ds, ns, ri, rm, ret, hr, h1, h2, h3, h4, h5,
          hdsIn, hretIn, hnsIn, ⟨ab, hab⟩⟩ :=
        walk_fields_classify_spec hinj hA hD hI hC hM
          (by simp only [peelAll, List.length_cons] at hbound; omega)
          evnext (sub fun c hc' => by rw [hc]; simp [hc'])
          (rsub fun c hc' => by rw [hc]; simp [hc'])
          (hB.mono extAll) hEin.2 (flatList_mono extAll hes)
          (tmOExactList_mono (ext4.trans ext5) hdoms')
          (fieldList_mono extAll hrec) (fieldList_mono extAll hrecmem)
          (tmOExactList_mono ext5 hnorm')
      refine ⟨hext, xds, xri, xrm, xret, xns, D :: ds, nd :: ns, ri, rm, ret, hr,
        by simpa using h1, h2, h3, h4, by simpa using h5,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hEin.1; exact hdsIn X hm),
        hretIn,
        (fun X hX => by rcases List.mem_cons.mp hX with rfl | hm; exact hndIn; exact hnsIn X hm),
        ⟨max aw ab, fun f hf => ?_⟩⟩
      simp only [fieldsClassify, haw f f (by omega) (by omega), hab f (by omega), hrf_eq]
  | .Let (x_v := xv) (x_b := xb) (v_rjvjoyoq := v') (m_jfbjeidy := m')
      (cs_swwhkahe := cs1) (cs_wgevuyab := cs2) (ld12 := ld)
      (ev_gfkycmwo := e1) (ev_wojvmxdy := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V0, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have ext1 := e1.heap_extends
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨-, res⟩ := walk_fields_classify_spec hinj hA hD hI hC hM hbound e2
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (rsub fun c hc' => by rw [hc]; simp [hc']) hv' hEin
      (flatList_mono ext1 hes) (tmOExactList_mono ext1 hdoms)
      (fieldList_mono ext1 hrec) (fieldList_mono ext1 hrecmem) (tmOExactList_mono ext1 hnorm)
    exact ⟨hext, res⟩
  | .other (v1 := v) (v503 := xds) (v504 := xri) (v505 := xrm) (v507 := xns)
      (m510 := m1) (m530 := m2) (m550 := m3) (m577 := m4) (ld12 := ld)
      (hne497 := hnf) (hne_ttotnwna := hnl) (he508 := hr) (ev520 := evr1)
      (ev540 := evr2) (ev560 := evr3) (ev587 := evr4) (he596 := hh) .. =>
    subst hr hh
    have hds := reverse_kexpr_spec evr1 hdoms
    have hri := reverse_field_spec evr2 (fieldList_mono evr1.heap_extends hrec)
    have ext12 := evr1.heap_extends.trans evr2.heap_extends
    have hrm := reverse_field_spec evr3 (fieldList_mono ext12 hrecmem)
    have ext123 := ext12.trans evr3.heap_extends
    have hns := reverse_kexpr_spec evr4 (tmOExactList_mono ext123 hnorm)
    have hfc : ∀ f, fieldsClassify V f es liftBy fidx E = some ([], [], [], E, []) := by
      intro f
      cases hE' : E with
      | forallE D B m =>
        exact (tmOExact_not_forall hE ⟨v, ld, hnl⟩ ld hnf D B m hE').elim
      | _ => rfl
    refine ⟨hext, xds, xri, xrm, xty, xns, [], [], [], [], E, rfl,
      by simpa using tmOExactList_mono (evr2.heap_extends.trans (evr3.heap_extends.trans evr4.heap_extends)) hds,
      by simpa using fieldList_mono (evr3.heap_extends.trans evr4.heap_extends) hri,
      by simpa using fieldList_mono evr4.heap_extends hrm,
      hE.mono (ext123.trans evr4.heap_extends),
      by simpa using hns,
      (fun _ hm => nomatch hm), hEin, (fun _ hm => nomatch hm),
      Eventually.always hfc⟩
termination_by _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs => cs.length

/-- **`KernelCheck::walk_fields_classify`** starting from empty accumulators and `fidx = 0`. -/
theorem walk_fields_classify_nil_spec {rootCalls : List (Call F)} {S : _root_.Address → Prop}
    {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {V : ReconView} (hA : AddrOf κ V) (hD : DefnAnswers rootCalls S κ V)
    (hI : IndAnswers rootCalls S κ V) (hC : CtorOfAnswers rootCalls S V)
    (hM : ModeledAnswers rootCalls S V)
    {es : List FlatEntry} {liftBy : Nat} {E : KExpr}
    {xrc xty xflat xdoms xrec xrecmem xnorm xtys r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbound : liftBy + (peelAll E).1.length < 4611686018427387904)
    (ev : ObsFn W "KernelCheck::walk_fields_classify"
      [xrc, xty, xflat, xdoms, xrec, xrecmem, xnorm, .field 0, .field (liftBy : F), xtys] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hsub : ∀ c ∈ cs, c ∈ rootCalls)
    (hE : TmOExact κ h E xty) (hEin : AddrIn S κ E)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (hdoms : RepList kexprListEnum (TmOExact κ) h [] xdoms)
    (hrec : RepList fieldListEnum RepNatField h [] xrec)
    (hrecmem : RepList fieldListEnum RepNatField h [] xrecmem)
    (hnorm : RepList kexprListEnum (TmOExact κ) h [] xnorm) :
    Heap.Extends h h' ∧
    ∃ (xds xri xrm xret xns : SourceValue F)
      (ds ns : List KExpr) (ri rm : List Nat) (ret : KExpr),
      r = .tuple [xds, xri, xrm, xret, xns] ∧
      RepList kexprListEnum (TmOExact κ) h' ds xds ∧
      RepList fieldListEnum RepNatField h' ri xri ∧
      RepList fieldListEnum RepNatField h' rm xrm ∧
      TmOExact κ h' ret xret ∧
      RepList kexprListEnum (TmOExact κ) h' ns xns ∧
      (∀ D ∈ ds, AddrIn S κ D) ∧ AddrIn S κ ret ∧ (∀ N ∈ ns, AddrIn S κ N) ∧
      Eventually fun f => fieldsClassify V f es liftBy 0 E = some (ds, ri, rm, ret, ns) := by
  have ev' : ObsFn W "KernelCheck::walk_fields_classify"
      [xrc, xty, xflat, xdoms, xrec, xrecmem, xnorm, .field ((0 : Nat) : F),
        .field (liftBy : F), xtys] h r h' cs := by simpa using ev
  simpa using walk_fields_classify_spec hinj hA hD hI hC hM (by omega) ev' hbnd hsub hE hEin hes
    hdoms hrec hrecmem hnorm

end IxVM.Refinement.Binding.FamilyRecon
