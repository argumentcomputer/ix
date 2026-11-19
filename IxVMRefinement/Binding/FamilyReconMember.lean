import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Binding.FamilyReconLocal
import IxVMRefinement.Binding.PayloadCoreSpecs
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelCheck8
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.KernelCheck10
import IxVMRefinement.Obs.KernelRoles1

/-! # A member of the family record against the reconstruction

`KernelCheck::check_recursor_canonical_at` locates a recursor's major type in the flattened
family (`flat_find_pos_kind`, `flat_find_pos`), lists the record's peer recursors
(`build_peer_recs`), and compares the recursor with the reconstruction at that position
(`canonical_rules_at_pos`).

* `flat_find_pos_spec`, `flat_find_pos_kind_spec`: the two searches are `flatFindPos` and
  `flatFindPosKind`, the first entry at an address, and of a kind with given parameters and levels.
* `FlatDistinct`, `MembersSeparate`, `derivedFlatAt_distinct`: two entries of a derived family at
  one address are both auxiliaries with different parameters or levels, where the view lists the
  block's types once each and no type of another block among them.
* `flatFindPosKind_aux`, `flatFindPosKind_own_none`, `flatFindPosKind_own`, `flatFindPos_own`,
  `FlatDistinct.no_earlier_match`: among different entries the searches find an entry at its own
  position, and the first recursor matching an entry is the entry's own.
* `canonical_rules_at_pos_spec`: under a group's validation the declared type is the reconstructed
  type at the position (`kexpr_struct_eq_tmOExact`) and the rules follow the reconstructed bodies.
* `check_recursor_canonical_at_spec`: the position found is the entry's, so the same of the whole
  member check. `memberRecon_of_canonical`: `MemberRecon` at the semantic equality of levels.
* `recTypeAt_major`, `major_head_of_canonical`: the declared type's major premise is over the
  entry it was compared at, at the entry's levels. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Consistency (blockSelf)
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr ExprLvEq)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Positions in the flattened family -/

/-- **`flat_find_pos`**: the first entry at the address. -/
def flatFindPos (es : List FlatEntry) (a : _root_.Address) : Option Nat :=
  es.findIdx? fun e => e.addr == a

/-- **`flat_find_pos_kind`**: the first entry at the address of the kind `aux`, and at an
auxiliary with the parameters and the levels. -/
def flatFindPosKind (es : List FlatEntry) (a : _root_.Address) (aux : Bool) (sp : List KExpr)
    (us : List KLevel) : Option Nat :=
  es.findIdx? fun e =>
    e.addr == a && (e.aux == aux) && (!aux || (e.params == sp && e.levels == us))

private theorem addr_beq_field {ae a : Bytes.Address} {e : FlatEntry} (hae : ixAddr ae = e.addr) :
    (if ae = a then (1 : F) else 0) = if e.addr == ixAddr a then 1 else 0 := by
  rw [← hae]
  by_cases h : ae = a
  · subst h; simp
  · have hne : ixAddr ae ≠ ixAddr a := fun heq => h (ixAddr_inj heq)
    rw [ite_eq_right h, beq_eq_false_iff_ne.mpr hne]; rfl

/-- **`KernelCheck::flat_find_pos`** computes `flatFindPos` shifted by `pos`; no allocation. -/
theorem flat_find_pos_spec {κ : _root_.Address → KKey} :
    ∀ (es : List FlatEntry) (pos : Nat) {a : Bytes.Address}
      {xflat xa r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)},
      ObsFn W "KernelCheck::flat_find_pos" [xflat, xa, .field (pos : F)] h r h' cs →
      (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h a xa →
      h' = h ∧
      match flatFindPos es (ixAddr a) with
      | some k => r = .tuple [.field 1, .field ((pos + k : Nat) : F)]
      | none => r = .tuple [.field 0, .field 0] := by
  intro es
  induction es with
  | nil =>
    intro pos a xflat xa r h h' cs root ev _ hes _
    match Obs.«KernelCheck::flat_find_pos».obs ev with
    | .Nil (he24 := hr) (he37 := hh) .. => exact ⟨hh, by rw [hr]; rfl⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro pos a xflat xa r h h' cs root ev hroot hes rca
    match Obs.«KernelCheck::flat_find_pos».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1 (ld12 := ld) (ev106 := evaeq) (he131 := hr) (he145 := hh) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl
      subst h1
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae rca
      rw [addr_beq_field hae] at hv1
      have hpred : (e.addr == ixAddr a) = true := by
        cases hp : (e.addr == ixAddr a)
        · rw [hp] at hv1; exact absurd (Value.field.inj hv1) (by decide)
        · rfl
      refine ⟨hh, ?_⟩
      unfold flatFindPos
      simp [List.findIdx?_cons, hpred, hr]
    | .Cons_other (ld12 := ld) (ev106 := evaeq) (hne147 := hne1) (op187 := op1)
        (ev156 := evrec) (hc189 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨xm', xsp', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl
      subst h1
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae rca
      rw [addr_beq_field hae] at hv1
      have hpred : (e.addr == ixAddr a) = false := by
        cases hp : (e.addr == ixAddr a)
        · rfl
        · rw [hp] at hv1; exact (hne1 hv1).elim
      obtain rfl := binop_add_one_nat op1
      obtain ⟨hh, hrec⟩ := ih (pos + 1) evrec
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hes' rca
      refine ⟨hh, ?_⟩
      unfold flatFindPos at hrec ⊢
      simp only [List.findIdx?_cons, hpred]
      cases hfi : List.findIdx? (fun e => e.addr == ixAddr a) es with
      | none => rw [hfi] at hrec; exact hrec
      | some k =>
        rw [hfi] at hrec
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hrec

private theorem field_mul_bool' {b₁ b₂ : Bool} {v : SourceValue F}
    (op : evalBinOp .mul (.field (if b₁ then 1 else 0)) (.field (if b₂ then 1 else 0)) = .ok v) :
    v = .field (if (b₁ && b₂) then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> (simp only [evalBinOp, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, ↓reduceIte] at op ⊢; injection op with hv; rw [← hv]; simp)

private theorem aux_sub_eq {a b : Bool} {v : SourceValue F}
    (op : evalBinOp .sub (auxVal a) (auxVal b) = .ok v) :
    v = .field 0 ↔ b = a := by
  cases a <;> cases b <;>
    (simp only [auxVal, evalBinOp, Except.ok.injEq] at op; subst op; simp)

/-- **`KernelCheck::flat_find_pos_kind`** computes `flatFindPosKind` shifted by `pos` on
`FlatEntryRepExact` when `κ` is injective. -/
theorem flat_find_pos_kind_spec {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (es : List FlatEntry) (pos : Nat) {a : Bytes.Address} {aux : Bool} {sp : List KExpr}
      {us : List KLevel} {xflat xa xsp xus r : SourceValue F} {h h' : Heap F}
      {cs root : List (Call F)},
      ObsFn W "KernelCheck::flat_find_pos_kind"
        [xflat, xa, auxVal aux, xsp, xus, .field (pos : F)] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Bytes.RepAddressRef addrTy h a xa →
      RepList kexprListEnum (TmOExact κ) h sp xsp →
      RepKLevelList h us xus →
      Heap.Extends h h' ∧
      match flatFindPosKind es (ixAddr a) aux sp us with
      | some k => r = .tuple [.field 1, .field ((pos + k : Nat) : F)]
      | none => r = .tuple [.field 0, .field 0] := by
  intro es
  induction es with
  | nil =>
    intro pos a aux sp us xflat xa xsp xus r h h' cs root ev _ _ hes _ _ _
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (he24 := hr) (he37 := hh) .. =>
      subst hh; exact ⟨Heap.Extends.refl _, by rw [hr]; rfl⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, hcons, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hcons
  | cons e es ih =>
    intro pos a aux sp us xflat xa xsp xus r h h' cs root ev hbnd hroot hes rca rsp rus
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    -- the three factors of one entry
    have entry : ∀ {xm xaux xsp' xou v1 v2 v3 : SourceValue F} {m1 m2 m3 : Heap F}
        {cs1 cs2 cs3 : List (Call F)} {xrest : SourceValue F},
        FlatEntryRepExact κ h e (.tuple [xm, xaux, xsp', xou]) →
        ObsFn W "Bytes::address_eq" [xm, xa] h v1 m1 cs1 →
        «Obs».«KernelCheck::flat_find_pos_kind».Seg1 v1 xm xaux xsp' xou
          (.tuple [xm, xaux, xsp', xou]) xrest xflat xa (auxVal aux) xsp xus (.field (pos : F))
          m1 v2 m2 cs2 →
        «Obs».«KernelCheck::flat_find_pos_kind».Seg2 v2 v1 xm xaux xsp' xou
          (.tuple [xm, xaux, xsp', xou]) xrest xflat xa (auxVal aux) xsp xus (.field (pos : F))
          m2 v3 m3 cs3 →
        (∀ c ∈ cs3, c ∈ cs) →
        v1 = .field (if e.addr == ixAddr a then 1 else 0) ∧
        v2 = .field (if e.aux == aux then 1 else 0) ∧
        v3 = .field (if (!aux || (e.params == sp && e.levels == us)) then 1 else 0) ∧
        Heap.Extends h m3 := by
      intro xm xaux xsp' xou v1 v2 v3 m1 m2 m3 cs1 cs2 cs3 xrest he' evaeq sg1 sg2 hcs3
      obtain ⟨xm', xsp'', xou', ae, htup, rae, hae, hsp, hou⟩ := he'
      injection htup with hl; injection hl with h1 hl; injection hl with h2 hl
      injection hl with h3 hl; injection hl with h4
      subst h1 h2 h3 h4
      obtain ⟨hv1, rfl⟩ := Lib.address_eq_spec evaeq rae rca
      rw [addr_beq_field hae] at hv1
      have hv2 : v2 = .field (if e.aux == aux then 1 else 0) ∧ m2 = m1 := by
        cases sg1 with
        | n0 op hr hh _ =>
          have := (aux_sub_eq op).mp rfl
          rw [hr, this]; simp [hh]
        | other v op hne hr hh _ =>
          have hne' : e.aux ≠ aux := fun heq => hne ((aux_sub_eq op).mpr heq)
          rw [hr, beq_eq_false_iff_ne.mpr hne']; simp [hh]
      obtain ⟨hv2, rfl⟩ := hv2
      refine ⟨hv1, hv2, ?_⟩
      cases sg2 with
      | n1 x1 y2 m12 cs_p cs_l hv evp evl op_pl hc_s =>
        have haux : aux = true := auxVal_eq_one.mp hv
        have b_p : IxVM.Consistency.Bounded cs_p :=
          sub fun c hc' => hcs3 c (by rw [hc_s]; simp [hc'])
        have hx1 := spec_params_zeta_eq_exact hinj hsp rsp b_p evp
        obtain ⟨hy2, hh_l⟩ := level_list_struct_eq_exact (hou.mono evp.heap_extends)
          (rus.mono evp.heap_extends) evl
        have hp_eq : (if e.params = sp then (1 : F) else 0) =
            if e.params == sp then 1 else 0 := by
          by_cases hq : e.params = sp
          · subst hq; simp
          · rw [ite_eq_right hq, beq_eq_false_iff_ne.mpr hq]; rfl
        have hl_eq : (if e.levels = us then (1 : F) else 0) = if e.levels == us then 1 else 0 := by
          by_cases hq : e.levels = us
          · subst hq; simp
          · rw [ite_eq_right hq, beq_eq_false_iff_ne.mpr hq]; rfl
        rw [hp_eq] at hx1
        rw [hl_eq] at hy2
        subst hx1 hy2 hh_l
        have hm := field_mul_bool' op_pl
        rw [haux]
        exact ⟨by simpa using hm, evp.heap_extends⟩
      | other hne hr hh _ =>
        have haux : aux = false := by
          cases hq : aux
          · rfl
          · exact (hne (auxVal_eq_one.mpr hq)).elim
        subst hh
        rw [hr, haux]
        exact ⟨rfl, Heap.Extends.refl _⟩
    match Obs.«KernelCheck::flat_find_pos_kind».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_n1 (ld12 := ld) (ev105 := evaeq) (sg163 := sg1) (sg216 := sg2) (op241 := op1)
        (op233 := op2) (he253 := hr) (he267 := hh) (hc268 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨hv1, hv2, hv3, ext⟩ := entry he' evaeq sg1 sg2
        (fun c hc' => by rw [hc]; simp [hc'])
      subst hv1 hv2 hv3 hh
      have hm1 := field_mul_bool' op1
      subst hm1
      have hm2 := field_mul_bool' op2
      have hpred : (e.addr == ixAddr a && (e.aux == aux) &&
          (!aux || (e.params == sp && e.levels == us))) = true := by
        cases hp : (e.addr == ixAddr a && (e.aux == aux) &&
            (!aux || (e.params == sp && e.levels == us)))
        · rw [hp] at hm2; exact absurd (Value.field.inj hm2) (by decide)
        · rfl
      refine ⟨ext, ?_⟩
      unfold flatFindPosKind
      simp [List.findIdx?_cons, hpred, hr]
    | .Cons_other (ld12 := ld) (ev105 := evaeq) (sg163 := sg1) (sg216 := sg2) (op241 := op1)
        (op233 := op2) (hne269 := hne1) (op_epyjxidj := opp) (ev278 := evrec) (hc327 := hc) .. =>
      obtain ⟨e', es', h1, he', hes'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection h1 with he1 hes1; subst he1 hes1
      obtain ⟨hv1, hv2, hv3, ext⟩ := entry he' evaeq sg1 sg2
        (fun c hc' => by rw [hc]; simp [hc'])
      subst hv1 hv2 hv3
      have hm1 := field_mul_bool' op1
      subst hm1
      have hm2 := field_mul_bool' op2
      have hpred : (e.addr == ixAddr a && (e.aux == aux) &&
          (!aux || (e.params == sp && e.levels == us))) = false := by
        cases hp : (e.addr == ixAddr a && (e.aux == aux) &&
            (!aux || (e.params == sp && e.levels == us)))
        · rfl
        · rw [hp] at hm2; exact (hne1 hm2).elim
      obtain rfl := binop_add_one_nat opp
      obtain ⟨ext', hrec⟩ := ih (pos + 1) evrec (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (flatList_mono ext hes') (Bytes.repAddressRef_heapMono₂ addrTy ext rca)
        (tmOExactList_mono ext rsp) (rus.mono ext)
      refine ⟨ext.trans ext', ?_⟩
      unfold flatFindPosKind at hrec ⊢
      simp only [List.findIdx?_cons, hpred]
      cases hfi : List.findIdx? (fun e => e.addr == ixAddr a && (e.aux == aux) &&
          (!aux || (e.params == sp && e.levels == us))) es with
      | none => rw [hfi] at hrec; exact hrec
      | some k =>
        rw [hfi] at hrec
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using hrec

/-! ## The entries of a derived family differ -/

/-- **Two entries at one address are both auxiliaries, with different parameters or levels.** -/
def FlatDistinct (es : List FlatEntry) : Prop :=
  ∀ (i j : Nat) (ei ej : FlatEntry), i < j → es[i]? = some ei → es[j]? = some ej →
    ei.addr = ej.addr →
    ei.aux = true ∧ ej.aux = true ∧ (ei.params ≠ ej.params ∨ ei.levels ≠ ej.levels)

/-- **The view lists the block's types once each, and no type of another block among them.** -/
structure MembersSeparate (V : FlatView) (B : _root_.Address) : Prop where
  nodup : ∀ ms, V.members B = some ms → ms.Nodup
  apart : ∀ b ms msb, (b == B) = false → V.members B = some ms → V.members b = some msb →
    ∀ a ∈ msb, a ∉ ms

/-- An address a nested occurrence's block lists. -/
def AuxAddr (V : FlatView) (B : _root_.Address) (a : _root_.Address) : Prop :=
  ∃ b ms, (b == B) = false ∧ V.members b = some ms ∧ a ∈ ms

/-- The entries after `os` are auxiliaries at addresses of other blocks, pairwise different. -/
def AuxTail (V : FlatView) (B : _root_.Address) (os acc : List FlatEntry) : Prop :=
  ∃ auxs, acc = os ++ auxs ∧ (∀ e ∈ auxs, e.aux = true ∧ AuxAddr V B e.addr) ∧ auxs.Nodup

theorem auxEntryIn_of_mem {acc : List FlatEntry} {m : _root_.Address} {sp : List KExpr}
    {us : List KLevel} (h : (⟨m, true, sp, us⟩ : FlatEntry) ∈ acc) :
    auxEntryIn acc m sp us = true := by
  unfold auxEntryIn
  rw [List.any_eq_true]
  exact ⟨_, h, by simp⟩

theorem addBlockMembers_auxTail {V : FlatView} {B : _root_.Address} {os : List FlatEntry}
    {sp : List KExpr} {us : List KLevel} :
    ∀ (ms : List _root_.Address) (acc : List FlatEntry), (∀ m ∈ ms, AuxAddr V B m) →
      AuxTail V B os acc → AuxTail V B os (addBlockMembers ms sp us acc) := by
  intro ms
  induction ms with
  | nil => intro acc _ hacc; exact hacc
  | cons m ms ih =>
    intro acc hms hacc
    simp only [addBlockMembers]
    apply ih _ (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))
    by_cases hin : auxEntryIn acc m sp us = true
    · rw [ite_eq_left hin]; exact hacc
    · rw [ite_eq_right hin]
      obtain ⟨auxs, rfl, hall, hnd⟩ := hacc
      refine ⟨auxs ++ [⟨m, true, sp, us⟩], by rw [List.append_assoc], ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hall e he
        · rw [List.mem_singleton] at he
          subst he
          exact ⟨rfl, hms m List.mem_cons_self⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro hab
        subst hab
        exact hin (auxEntryIn_of_mem (List.mem_append_right _ ha))

section Thread

variable {V : FlatView} {B : _root_.Address} {I : List FlatEntry → Prop}

theorem scanList_inv {rec : KExpr → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ x acc r, I acc → rec x acc = some r → I r) :
    ∀ (l : List KExpr) (acc r : List FlatEntry), I acc → scanList rec l acc = some r → I r := by
  intro l
  induction l with
  | nil =>
    intro acc r hacc h
    simp only [scanList, Option.some.injEq] at h
    subst h; exact hacc
  | cons x xs ih =>
    intro acc r hacc h
    simp only [scanList] at h
    cases hx : rec x acc with
    | none => simp [hx] at h
    | some a =>
      simp only [hx] at h
      exact ih a r (hr x acc a hacc hx) h

theorem appCase_inv
    (hstep : ∀ b ms sp us acc, (b == B) = false → V.members b = some ms → I acc →
      I (addBlockMembers ms sp us acc))
    {rec : KExpr → Nat → List FlatEntry → Option (List FlatEntry)}
    (hr : ∀ e d acc r, I acc → rec e d acc = some r → I r)
    {hd : KExpr} {args : List KExpr} {d : Nat} {acc r : List FlatEntry} (hacc : I acc)
    (h : appCase rec V B hd args d acc = some r) : I r := by
  have hs : ∀ acc r, I acc → scanList (fun x acc => rec x d acc) args acc = some r → I r :=
    fun acc r => scanList_inv (fun x acc r => hr x d acc r) args acc r
  unfold appCase at h
  cases hk : constOf hd with
  | none =>
    simp only [hk] at h
    cases h1 : rec hd d acc with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      exact hs a r (hr hd d acc a hacc h1) h
  | some p =>
    obtain ⟨c, us⟩ := p
    simp only [hk] at h
    cases ha : V.addr c with
    | none => simp [ha] at h
    | some ca =>
      simp only [ha] at h
      cases hc : V.ci ca with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none =>
          simp only [hc] at h
          exact hs acc r hacc h
        | some i =>
          simp only [hc] at h
          cases hn : nestedAt V B i args with
          | none => simp [hn] at h
          | some b =>
            cases b with
            | false =>
              simp only [hn] at h
              exact hs acc r hacc h
            | true =>
              simp only [hn] at h
              cases hm : V.members i.blk with
              | none => simp [hm] at h
              | some ms =>
                simp only [hm] at h
                cases hl : occParamsLower (args.take i.np) d with
                | none => simp [hl] at h
                | some sp =>
                  simp only [hl, Option.some.injEq] at h
                  subst h
                  have hb : (i.blk == B) = false := by
                    unfold nestedAt at hn
                    cases hbb : (i.blk == B || decide (args.length < i.np)) with
                    | true => simp [hbb] at hn
                    | false =>
                      simp only [Bool.or_eq_false_iff] at hbb
                      exact hbb.1
                  exact hstep i.blk ms sp us acc hb hm hacc

theorem occScanF_inv
    (hstep : ∀ b ms sp us acc, (b == B) = false → V.members b = some ms → I acc →
      I (addBlockMembers ms sp us acc)) :
    ∀ (n : Nat) (e : KExpr) (d : Nat) (acc r : List FlatEntry), I acc →
      occScanF V B n e d acc = some r → I r := by
  intro n
  induction n with
  | zero => intro e d acc r _ h; simp [occScanF] at h
  | succ n ih =>
    intro e d acc r hacc h
    simp only [occScanF] at h
    cases hm : mentions V B e with
    | none => simp [hm] at h
    | some b =>
      cases b with
      | false =>
        simp only [hm, Option.some.injEq] at h
        subst h; exact hacc
      | true =>
        simp only [hm] at h
        cases e with
        | app f a =>
          simp only at h
          exact appCase_inv hstep ih hacc h
        | lam t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact ih b (d + 1) a1 r (ih t d acc a1 hacc h1) h
        | forallE t b m =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            exact ih b (d + 1) a1 r (ih t d acc a1 hacc h1) h
        | letE t v b l =>
          simp only at h
          cases h1 : occScanF V B n t d acc with
          | none => simp [h1] at h
          | some a1 =>
            simp only [h1] at h
            cases h2 : occScanF V B n v d a1 with
            | none => simp [h2] at h
            | some a2 =>
              simp only [h2] at h
              exact ih b (d + 1) a2 r (ih v d a1 a2 (ih t d acc a1 hacc h1) h2) h
        | proj s i x =>
          simp only at h
          exact ih x d acc r hacc h
        | bvar _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | fvar _ _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | sort _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | const _ _ => simp only [Option.some.injEq] at h; subst h; exact hacc
        | lit _ => simp only [Option.some.injEq] at h; subst h; exact hacc

theorem ctorsLoop_inv
    (hstep : ∀ b ms sp us acc, (b == B) = false → V.members b = some ms → I acc →
      I (addBlockMembers ms sp us acc))
    (i : IndInfo) (aux : Bool) (sp : List KExpr) (us : List KLevel) :
    ∀ (cs : List Nat) (acc r : List FlatEntry), I acc →
      ctorsLoop V B i aux sp us cs acc = some r → I r := by
  intro cs
  induction cs with
  | nil =>
    intro acc r hacc h
    simp only [ctorsLoop, Option.some.injEq] at h
    subst h; exact hacc
  | cons c cs ih =>
    intro acc r hacc h
    simp only [ctorsLoop] at h
    cases h1 : ctorScan V B i aux sp us acc c with
    | none => simp [h1] at h
    | some a =>
      simp only [h1] at h
      refine ih a r ?_ h
      unfold ctorScan at h1
      cases hc : V.ctorType i.blk i.idx c with
      | none => simp [hc] at h1
      | some cty =>
        simp only [hc] at h1
        cases hb : ctorBody aux i.np sp (exprInstLevels us cty) with
        | none => simp [hb] at h1
        | some body =>
          simp only [hb] at h1
          exact occScanF_inv hstep _ body 0 acc a hacc h1

theorem nestedWalk_inv
    (hstep : ∀ b ms sp us acc, (b == B) = false → V.members b = some ms → I acc →
      I (addBlockMembers ms sp us acc)) :
    ∀ (n i : Nat) (acc r : List FlatEntry), I acc → nestedWalk V B n i acc = some r → I r := by
  intro n
  induction n with
  | zero => intro i acc r _ h; simp [nestedWalk] at h
  | succ n ih =>
    intro i acc r hacc h
    simp only [nestedWalk] at h
    cases hi : acc[i]? with
    | none =>
      simp only [hi, Option.some.injEq] at h
      subst h; exact hacc
    | some e =>
      simp only [hi] at h
      cases hc : V.ci e.addr with
      | none => simp [hc] at h
      | some x =>
        cases x with
        | none => simp [hc] at h
        | some info =>
          simp only [hc] at h
          cases hs : ctorsScan V B info e.aux e.params e.levels acc with
          | none => simp [hs] at h
          | some a =>
            simp only [hs] at h
            exact ih (i + 1) a r
              (ctorsLoop_inv hstep info e.aux e.params e.levels _ acc a hacc hs) h

end Thread

theorem originals_shape {V : FlatView} {off : Nat} :
    ∀ (as : List _root_.Address) (os : List FlatEntry), originals V off as = some os →
      os.map (·.addr) = as ∧ ∀ e ∈ os, e.aux = false := by
  intro as
  induction as with
  | nil =>
    intro os h
    simp only [originals, Option.some.injEq] at h
    subst h; exact ⟨rfl, by simp⟩
  | cons a as ih =>
    intro os h
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
          obtain ⟨h1, h2⟩ := ih os' ho
          refine ⟨by simp [h1], ?_⟩
          intro e he
          rcases List.mem_cons.mp he with he | he
          · subst he; rfl
          · exact h2 e he

/-- **The flattened family derived from a block whose types the view lists apart has different
entries**: the block's own types are at different addresses, no auxiliary is at one of them, and
two auxiliaries at one address differ in their parameters or levels (`add_block_members` adds an
auxiliary only when `aux_entry_in` finds none with its type, parameters and levels). -/
theorem derivedFlatAt_distinct {V : FlatView} {B : _root_.Address} (hsep : MembersSeparate V B)
    {off n : Nat} {es : List FlatEntry} (h : derivedFlatAt V B off n = some es) :
    FlatDistinct es := by
  unfold derivedFlatAt at h
  cases hm : V.members B with
  | none => simp [hm] at h
  | some ms =>
    simp only [hm] at h
    cases ho : originals V off ms with
    | none => simp [ho] at h
    | some os =>
      simp only [ho] at h
      obtain ⟨hmap, hnaux⟩ := originals_shape ms os ho
      have hI : AuxTail V B os es :=
        nestedWalk_inv (I := AuxTail V B os)
          (fun b msb sp us acc hb hmb hacc =>
            addBlockMembers_auxTail msb acc (fun m hm' => ⟨b, msb, hb, hmb, hm'⟩) hacc)
          n 0 os es ⟨[], by simp, by simp, List.nodup_nil⟩ h
      obtain ⟨auxs, rfl, hall, hnd⟩ := hI
      have hlen : os.length = ms.length := by rw [← hmap, List.length_map]
      have haddr : ∀ (i : Nat) (e : FlatEntry), os[i]? = some e → ms[i]? = some e.addr := by
        intro i e hi
        rw [← hmap, List.getElem?_map, hi]; rfl
      intro i j ei ej hij hi hj hadd
      by_cases hjo : j < os.length
      · -- both among the block's own types
        rw [List.getElem?_append_left hjo] at hj
        rw [List.getElem?_append_left (by omega)] at hi
        have h1 := haddr i ei hi
        have h2 := haddr j ej hj
        rw [hadd] at h1
        have hilt : i < ms.length := by omega
        have hjlt : j < ms.length := by omega
        rw [List.getElem?_eq_getElem hilt] at h1
        rw [List.getElem?_eq_getElem hjlt] at h2
        have := (List.Nodup.getElem_inj_iff (hsep.nodup ms hm)).mp
          ((Option.some.inj h1).trans (Option.some.inj h2).symm)
        omega
      · rw [List.getElem?_append_right (by omega)] at hj
        obtain ⟨hjaux, b, msb, hb, hmb, hjm⟩ := hall ej (List.mem_of_getElem? hj)
        by_cases hio : i < os.length
        · -- one of the block's own types and an auxiliary
          rw [List.getElem?_append_left hio] at hi
          have h1 := haddr i ei hi
          exact absurd (hadd ▸ List.mem_of_getElem? h1) (hsep.apart b ms msb hb hm hmb _ hjm)
        · rw [List.getElem?_append_right (by omega)] at hi
          obtain ⟨hiaux, -⟩ := hall ei (List.mem_of_getElem? hi)
          refine ⟨hiaux, hjaux, ?_⟩
          by_contra hcon
          have hp : ei.params = ej.params := by
            by_contra hne; exact hcon (Or.inl hne)
          have hl : ei.levels = ej.levels := by
            by_contra hne; exact hcon (Or.inr hne)
          have heq : ei = ej := by
            cases ei; cases ej; simp_all
          have hilt : i - os.length < auxs.length := (List.getElem?_eq_some_iff.mp hi).1
          have hjlt : j - os.length < auxs.length := (List.getElem?_eq_some_iff.mp hj).1
          rw [List.getElem?_eq_getElem hilt] at hi
          rw [List.getElem?_eq_getElem hjlt] at hj
          have := (List.Nodup.getElem_inj_iff hnd).mp
            ((Option.some.inj hi).trans (heq.trans (Option.some.inj hj).symm))
          omega

/-! ## The position of an entry among different entries -/

theorem findIdx?_eq_some_of {α : Type} {p : α → Bool} :
    ∀ {es : List α} {k : Nat} {e : α}, es[k]? = some e → p e = true →
      (∀ (j : Nat) (ej : α), j < k → es[j]? = some ej → p ej = false) →
      es.findIdx? p = some k
  | [], k, e, hk, _, _ => by simp at hk
  | x :: xs, 0, e, hk, hp, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp [List.findIdx?_cons, hp]
  | x :: xs, k + 1, e, hk, hp, hlt => by
    have hx : p x = false := hlt 0 x (by omega) rfl
    have hk' : xs[k]? = some e := by simpa using hk
    have ih := findIdx?_eq_some_of (es := xs) hk' hp
      (fun j ej hj hej => hlt (j + 1) ej (by omega) (by simpa using hej))
    simp [List.findIdx?_cons, hx, ih]

theorem findIdx?_eq_none_of {α : Type} {p : α → Bool} :
    ∀ {es : List α}, (∀ (j : Nat) (ej : α), es[j]? = some ej → p ej = false) →
      es.findIdx? p = none
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = false := h 0 x rfl
    have ih := findIdx?_eq_none_of (es := xs)
      (fun j ej hej => h (j + 1) ej (by simpa using hej))
    simp [List.findIdx?_cons, hx, ih]

/-- Two entries of a family of different entries at one address, the first not an auxiliary or
the two with one parameters and levels, are at one position. -/
theorem FlatDistinct.eq_pos {es : List FlatEntry} (hd : FlatDistinct es) {j k : Nat}
    {ej e : FlatEntry} (hj : es[j]? = some ej) (hk : es[k]? = some e) (ha : ej.addr = e.addr)
    (hne : ¬ (ej.aux = true ∧ e.aux = true ∧ (ej.params ≠ e.params ∨ ej.levels ≠ e.levels))) :
    j = k := by
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · exact absurd (hd j k ej e hlt hj hk ha) hne
  · exact heq
  · obtain ⟨h1, h2, h3⟩ := hd k j e ej hgt hk hj ha.symm
    exact absurd ⟨h2, h1, h3.imp (fun h => fun h' => h h'.symm) (fun h => fun h' => h h'.symm)⟩ hne

/-- **An auxiliary entry is found at its own position by its kind** (`flat_find_pos_kind`). -/
theorem flatFindPosKind_aux {es : List FlatEntry} (hd : FlatDistinct es) {k : Nat}
    {e : FlatEntry} (hk : es[k]? = some e) (he : e.aux = true) :
    flatFindPosKind es e.addr true e.params e.levels = some k := by
  unfold flatFindPosKind
  refine findIdx?_eq_some_of hk (by simp [he]) ?_
  intro j ej hj hej
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hcon
  obtain ⟨⟨ha, -⟩, hp, hl⟩ := hcon
  have := hd.eq_pos hej hk ha (fun h => h.2.2.elim (fun h' => h' hp) (fun h' => h' hl))
  omega

/-- **One of the block's own types is found by no auxiliary's kind.** -/
theorem flatFindPosKind_own_none {es : List FlatEntry} (hd : FlatDistinct es) {k : Nat}
    {e : FlatEntry} (hk : es[k]? = some e) (he : e.aux = false) (sp : List KExpr)
    (us : List KLevel) : flatFindPosKind es e.addr true sp us = none := by
  unfold flatFindPosKind
  refine findIdx?_eq_none_of ?_
  intro j ej hej
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hcon
  obtain ⟨⟨ha, hjaux⟩, -⟩ := hcon
  have hjk := hd.eq_pos hej hk ha (fun h => by rw [he] at h; exact absurd h.2.1 (by decide))
  subst hjk
  rw [hk] at hej
  obtain rfl := Option.some.inj hej
  rw [he] at hjaux
  exact absurd hjaux (by decide)

/-- **One of the block's own types is found at its own position by its kind.** -/
theorem flatFindPosKind_own {es : List FlatEntry} (hd : FlatDistinct es) {k : Nat}
    {e : FlatEntry} (hk : es[k]? = some e) (he : e.aux = false) (sp : List KExpr)
    (us : List KLevel) : flatFindPosKind es e.addr false sp us = some k := by
  unfold flatFindPosKind
  refine findIdx?_eq_some_of hk (by simp [he]) ?_
  intro j ej hj hej
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  simp only [Bool.not_false, Bool.true_or, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hcon
  have := hd.eq_pos hej hk hcon.1 (fun h => by rw [he] at h; exact absurd h.2.1 (by decide))
  omega

/-- **One of the block's own types is the first entry at its address** (`flat_find_pos`). -/
theorem flatFindPos_own {es : List FlatEntry} (hd : FlatDistinct es) {k : Nat}
    {e : FlatEntry} (hk : es[k]? = some e) (he : e.aux = false) :
    flatFindPos es e.addr = some k := by
  unfold flatFindPos
  refine findIdx?_eq_some_of hk (by simp) ?_
  intro j ej hj hej
  by_contra hcon
  rw [Bool.not_eq_false, beq_iff_eq] at hcon
  have := hd.eq_pos hej hk hcon (fun h => by rw [he] at h; exact absurd h.2.1 (by decide))
  omega

/-- **The first recursor matching an entry is the entry's own**: where recursor `j` matches an
entry only at the address of entry `j`, and matches an auxiliary only at entry `j`'s parameters
and levels when entry `j` is an auxiliary, no recursor before `k` matches entry `k` of a family
of different entries. -/
theorem FlatDistinct.no_earlier_match {es : List FlatEntry} (hd : FlatDistinct es)
    {p : Nat → FlatEntry → Bool}
    (hsound : ∀ (j : Nat) (e ej : FlatEntry), es[j]? = some ej → p j e = true →
      ej.addr = e.addr ∧
        (e.aux = true → ej.aux = true → ej.params = e.params ∧ ej.levels = e.levels))
    {k : Nat} {e : FlatEntry} (hk : es[k]? = some e) (j : Nat) (hj : j < k) : p j e = false := by
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  have hklt : k < es.length := (List.getElem?_eq_some_iff.mp hk).1
  have hjlt : j < es.length := by omega
  obtain ⟨ha, hpl⟩ := hsound j e es[j] (List.getElem?_eq_getElem hjlt) hcon
  have := hd.eq_pos (List.getElem?_eq_getElem hjlt) hk ha
    (fun h => h.2.2.elim (fun h' => h' (hpl h.2.1 h.1).1) (fun h' => h' (hpl h.2.1 h.1).2))
  omega

/-! ## A member against the reconstruction at a position -/

/-- **`KernelCheck::kexpr_struct_eq` returning `1` on two open exact terms**: the terms are
equal, levels included. -/
theorem kexpr_struct_eq_tmOExact {κ : _root_.Address → KKey} {Ea Eb : KExpr}
    {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : TmOExact κ h Ea pa) (hb : TmOExact κ h Eb pb)
    (ev : ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs) : Ea = Eb := by
  obtain ⟨ka, ra⟩ := ha
  obtain ⟨kb, rb⟩ := hb
  exact IxVM.Refinement.Decl.kexpr_struct_eq_one
    (tmExact_depth_le ra (max ka kb) (Nat.le_max_left _ _))
    (tmExact_depth_le rb (max ka kb) (Nat.le_max_right _ _)) ev

theorem flat_length' {R : Heap F → FlatEntry → SourceValue F → Prop} {xs : List FlatEntry}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [l] h r h' cs)
    (hl : RepList flatListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec
    (t := .tuple [.ptr (.array .field 32), .field,
      .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]),
      .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])])]) (R := R)
    (by rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

/-- **`KernelCheck::canonical_rules_at_pos` under a group's validation**
(`rc_validates_group(rc) = 1`), at the position `k` of the flattened family `es`: the declared
type `ty` is the reconstructed type at `k` (`build_rec_type`, compared by `kexpr_struct_eq`; the
arm that accepts the full consumption of the reconstruction asserts `rc_validates_group(rc) = 0`),
and every stored rule follows the reconstructed body (`populate_rules`, `compare_rules`) at the
constructors before `k` (`ctors_before_pos`). The builders' and the comparison's results are
taken at this call's arguments, on any heap extending the call's. -/
theorem canonical_rules_at_pos_spec {κ : _root_.Address → KKey} {V : ReconView}
    {es : List FlatEntry} {fop : List Nat} {off nP nMot nMin nl k : Nat} {ty : KExpr}
    {peers : List _root_.Address} {stored : List (Nat × Nat × KExpr)} {self : IndData}
    {ba : Bytes.Address} {NF : _root_.Address → Nat → Nat → Nat → Prop}
    {x_rc x_flat x_nc x_pblk x_pidx x_np x_lvls x_peers x_fop x_rules x_ty x_pty
      x_pnl x_pni x_elim x_uo x_form r : SourceValue F} {h h' : Heap F}
    {cs root : List (Call F)}
    (ev : ObsFn W "KernelCheck::canonical_rules_at_pos"
      [x_rc, x_flat, .field (k : F), x_nc, x_pblk, x_pidx, x_np, .field (nMot : F), .field (nMin : F), x_lvls, x_peers,
        x_fop, x_rules, x_ty, x_pty, x_pnl, x_pni, x_elim, x_uo, x_form] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es x_flat)
    (hk : k < es.length) (hlen : es.length < 2 ^ 39)
    (hnMot : nMot < 4294967296) (hnMin : nMin < 4294967296)
    (hty : TmOExact κ h ty x_ty)
    (rc_validates_group : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelRoles::rc_validates_group" [x_rc] m v m' cs' → Heap.Extends h m →
      v = .field 1)
    (build_rec_type : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, x_np, x_pni, x_elim, x_uo, x_flat, x_fop, .field (k : F)]
        m v m' cs' → Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ R, TmOExact κ m' R v ∧
        Eventually fun f => recTypeAt V f es off nP k = some R)
    (build_all_minors : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors"
        [x_rc, x_flat, x_fop, x_np, .field (es.length : F), x_np, x_elim] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ Ms, RepList kexprListEnum (TmOExact κ) m' Ms v ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (rules_at_pos : ∀ {h₀ h₁ h₂ h₃ : Heap F} {vcb vcanon v w x_aux x_sp x_ou : SourceValue F}
      {cs₁ cs₂ cs₃ : List (Call F)} (e : FlatEntry) (Ms : List KExpr),
      ObsFn W "KernelCheck::ctors_before_pos" [x_flat, .field (k : F), .field 0] h₀ vcb h₁ cs₁ →
      ObsFn W "KernelCheck::populate_rules"
        [x_rc, x_nc, vcb, x_pblk, x_pidx, x_np, .field (nMot : F), .field (nMin : F), x_ou,
          x_lvls, x_flat, x_peers, x_fop, x_aux, x_sp, .field 0, x_elim] h₁ vcanon h₂ cs₂ →
      ObsFn W "KernelCheck::compare_rules"
        [x_rules, vcanon, x_np, .field (nMot : F), .field (nMin : F), x_pblk, x_pidx, x_nc,
          .field 0, x_elim, x_ty, vcb] h₂ v h₃ cs₃ →
      Heap.Extends h h₀ → IxVM.Consistency.Bounded cs₂ → IxVM.Consistency.Bounded cs₃ →
      (∀ c ∈ cs₁, c ∈ root) → (∀ c ∈ cs₂, c ∈ root) → (∀ c ∈ cs₃, c ∈ root) →
      es[k]? = some e → FlatEntryRepExact κ h₀ e (.tuple [w, x_aux, x_sp, x_ou]) →
      nMot = es.length → nMin = Ms.length →
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) →
      Heap.Extends h₀ h₁ ∧ Heap.Extends h₁ h₂ ∧ Heap.Extends h₂ h₃ ∧
        ∃ (cbk : Nat) (bodies : List KExpr), ctorsBefore V es k = some cbk ∧
          (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
          stored.length ≤ self.nctors ∧
          ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
            ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
              ∃ cb, bodies[c]? = some cb ∧
                RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb) :
    Heap.Extends h h' ∧
    ∃ (Ms : List KExpr) (cbk : Nat) (bodies : List KExpr),
      nMot = es.length ∧ nMin = Ms.length ∧
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
      (Eventually fun f => recTypeAt V f es off nP k = some ty) ∧
      ctorsBefore V es k = some cbk ∧
      (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
      stored.length ≤ self.nctors ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
          ∃ cb, bodies[c]? = some cb ∧
            RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::canonical_rules_at_pos».obs ev with
  | .run (m2 := m2) (m60 := m60) (v59 := v59) (v259 := v259) (m_uszksxrg := m3) (m224 := m224) (m261 := m261)
      (m246 := m246) (v384 := v384) (m385 := m385) (v421 := v421) (m422 := m422)
      (ev15 := evMem) (ev72 := evBRT) (sg_xtajopni := sg) (ev236 := evLen1) (ev271 := evBAM)
      (ev258 := evLen2) (heq355 := heqMot) (heq383 := heqMin) (ev397 := evCBP) (ev434 := evPR) (ev_fswvniux := evCR) (hc671 := hc) .. =>
    obtain ⟨hm2, e, hek, he⟩ := flat_member_at_spec es k hk (by omega) evMem hes
    have ext0 : Heap.Extends h m2 := hm2 ▸ Heap.Extends.refl _
    have ext1 : Heap.Extends h m60 := ext0.trans (ObsFn.heap_extends evBRT)
    obtain ⟨-, R, hR, hRec⟩ := build_rec_type evBRT ext0
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
    -- the declared type is the reconstruction
    have hsg : R = ty ∧ Heap.Extends m60 m3 := by
      refine ⟨?_, ?_⟩
      · cases sg with
        | n1_n1 _ _ evEq _ _ _ _ => exact kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        | n1_other_n1 _ _ _ _ evEq _ _ _ _ _ =>
          exact kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        | n1_other_other _ _ _ _ _ evEq _ _ _ _ _ _ _ =>
          exact kexpr_struct_eq_tmOExact hR (hty.mono ext1) evEq
        | other _ _ _ _ _ _ _ _ _ _ _ _ _ evEq _ evVG hvg0 _ _ _ _ _ _ _ _ =>
          have h1 := rc_validates_group evVG (ext1.trans (ObsFn.heap_extends evEq))
          rw [hvg0] at h1
          exact absurd (Value.field.inj h1) (by decide)
      · cases sg with
        | n1_n1 _ _ evEq _ _ hh _ => subst hh; exact ObsFn.heap_extends evEq
        | n1_other_n1 _ _ _ _ evEq _ evW _ hh _ =>
          subst hh; exact (ObsFn.heap_extends evEq).trans (ObsFn.heap_extends evW)
        | n1_other_other _ _ _ _ _ evEq _ evW _ _ _ hh _ =>
          subst hh; exact (ObsFn.heap_extends evEq).trans (ObsFn.heap_extends evW)
        | other _ _ _ _ _ _ _ _ _ _ _ _ _ evEq _ evVG _ evW _ _ evZ _ _ hh _ =>
          subst hh
          exact (ObsFn.heap_extends evEq).trans ((ObsFn.heap_extends evVG).trans
            ((ObsFn.heap_extends evW).trans (ObsFn.heap_extends evZ)))
    obtain ⟨hRty, ext2⟩ := hsg
    subst hRty
    obtain ⟨hv223, hm224⟩ := flat_length' evLen1 (flatList_mono (ext1.trans ext2) hes)
    subst hv223 hm224
    have hnMotEq : nMot = es.length :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqMot)
    obtain ⟨-, Ms, hMs, hMsE⟩ := build_all_minors evBAM (ext1.trans ext2)
      (sub fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc']))
    have hMsLen : Ms.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (show (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [v259], m261⟩ : Call F) ∈ cs
          by rw [hc]; simp) (by simp) hMs
    obtain ⟨hv245, -⟩ := kexpr_length evLen2 hMs
    subst hv245
    have hnMinEq : nMin = Ms.length :=
      natCast_inj_small (by omega) (by omega) (Value.field.inj heqMin)
    have ext3 : Heap.Extends h m246 :=
      ext1.trans (ext2.trans ((ObsFn.heap_extends evBAM).trans (ObsFn.heap_extends evLen2)))
    obtain ⟨-, -, -, cbk, bodies, hrest⟩ := rules_at_pos e Ms evCBP evPR evCR ext3
      (sub fun c hc' => by rw [hc]; simp [hc']) (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hek (he.mono ext3) hnMotEq hnMinEq hMsE
    exact ⟨Ms, cbk, bodies, hnMotEq, hnMinEq, hMsE, hRec, hrest⟩

/-! ## The whole member check -/

/-- **What `check_recursor_canonical_at` hands `canonical_rules_at_pos`**: the flattened family
(`build_flat_block`), the peer recursors' addresses (`build_peer_recs`), the entries' parameter
counts (`build_flat_own_params`), the recursor's level parameters (`build_rec_lvls_list`) and the
elimination level. -/
structure CanonArgs (κ : _root_.Address → KKey) (V : ReconView) (es : List FlatEntry)
    (peers : List _root_.Address) (fop : List Nat) (off nl : Nat) (h : Heap F)
    (x_flat x_peers x_fop x_lvls x_elim : SourceValue F) : Prop where
  flat : RepList flatListEnum (FlatEntryRepExact κ) h es x_flat
  peers : ∃ as : List Bytes.Address,
    RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) h as x_peers ∧
      as.map ixAddr = peers
  fopEq : flatOwnParams V es = some fop
  fop : RepList fieldListEnum RepNatField h fop x_fop
  lvls : RepKLevelList h ((List.range nl).map Ix.Kernel.Level.param) x_lvls
  elim : RepKLevel h (elimLevel off) x_elim

theorem CanonArgs.mono {κ : _root_.Address → KKey} {V : ReconView} {es : List FlatEntry}
    {peers : List _root_.Address} {fop : List Nat} {off nl : Nat} {h h' : Heap F}
    {x_flat x_peers x_fop x_lvls x_elim : SourceValue F} (ext : Heap.Extends h h')
    (a : CanonArgs κ V es peers fop off nl h x_flat x_peers x_fop x_lvls x_elim) :
    CanonArgs κ V es peers fop off nl h' x_flat x_peers x_fop x_lvls x_elim := by
  obtain ⟨as, has, hmap⟩ := a.peers
  exact ⟨flatList_mono ext a.flat,
    ⟨as, repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext has, hmap⟩,
    a.fopEq, fieldList_mono ext a.fop, a.lvls.mono ext, a.elim.mono ext⟩

private theorem is_muts_block_bool {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_muts_block" [x] h r h' cs) :
    ∃ b : Bool, r = .field (if b then 1 else 0) := by
  match Obs.«KernelCheck::is_muts_block».obs ev with
  | .Muts (he90 := hr) .. => exact ⟨true, hr⟩
  | .other (he97 := hr) .. => exact ⟨false, hr⟩

private theorem one_sub_bool {b : Bool} {v : SourceValue F}
    (op : evalBinOp .sub (.field 1) (.field (if b then (1 : F) else 0)) = .ok v) :
    v = .field (if (!b) then 1 else 0) := by
  cases b <;> (simp only [evalBinOp, Except.ok.injEq] at op; subst op; simp)

private theorem field_nat_eq_one {off : Nat} (hoff : off ≤ 1) :
    (.field (off : F) : SourceValue F) = .field 1 ↔ off = 1 := by
  interval_cases off <;> simp

/-- **`KernelCheck::check_recursor_canonical_at` under a group's validation**, on recursor `k`
of a family record whose major premise is over entry `k` of a flattened family `es` of different
entries: the position it finds for the major premise's type is `k` (`flat_find_pos_kind` at an
auxiliary, whose parameters and levels the recursor's type gives; `flat_find_pos` at one of the
block's own types), so `canonical_rules_at_pos` compares the recursor with the reconstruction at
`k`: its declared type is the reconstructed one and its rules follow the reconstructed bodies.
The record's builders and the comparison are taken at this call's arguments. -/
theorem check_recursor_canonical_at_spec {κ : _root_.Address → KKey}
    (hinj : Function.Injective κ) {V : ReconView} {es : List FlatEntry} (hd : FlatDistinct es)
    {off nP nI nMot nMin nl k : Nat} {e : FlatEntry} (hek : es[k]? = some e) {ty : KExpr}
    {peers : List _root_.Address} {stored : List (Nat × Nat × KExpr)} {self : IndData}
    {ba : Bytes.Address} {NF : _root_.Address → Nat → Nat → Nat → Prop}
    {arb apb apar : Bytes.Address}
    {x_rc x_ty x_rules x_k x_uns x_rb x_idx x_pnl x_pty x_pnp x_pni x_nc x_w x_pblk x_pidx
      x_addr x_par x_bnl x_form r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)}
    (ev : ObsFn W "KernelCheck::check_recursor_canonical_at"
      [x_rc,
        .construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx],
        x_addr,
        .construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx],
        x_par, .field (off : F), x_bnl, x_form] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hoff : off ≤ 1) (hnl : nl < 4294967296)
    (hnMot : nMot < 4294967296) (hnMin : nMin < 4294967296)
    (hty : TmOExact κ h ty x_ty)
    (hpar : Bytes.RepAddressRef addrTy h apar x_par) (hpar_eq : ixAddr apar = e.addr)
    (hrb : Bytes.RepAddressRef addrTy h arb x_rb)
    (hpb : Bytes.RepAddressRef addrTy h apb x_pblk)
    (haux : e.aux = true → arb ≠ apb)
    (rc_validates_group : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelRoles::rc_validates_group" [x_rc] m v m' cs' → Heap.Extends h m →
      v = .field 1)
    (is_muts_block : e.aux = true → ∀ {m m' : Heap F} {x v : SourceValue F}
      {cs' : List (Call F)}, x = x_rb ∨ x = x_pblk →
      ObsFn W "KernelCheck::is_muts_block" [x] m v m' cs' → Heap.Extends h m →
      (∀ c ∈ cs', c ∈ root) → v = .field 1)
    (build_flat_block : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_flat_block" [x_rb, x_pblk, .field (off : F)] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) m' es v)
    (build_peer_recs : ∀ {m m' : Heap F} {v x_flat : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_peer_recs" [x_flat, x_rb, x_addr] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) m es x_flat →
      ∃ as : List Bytes.Address,
        RepList IxVM.Refinement.Core.addrListEnum (Bytes.RepAddressRef addrTy) m' as v ∧
          as.map ixAddr = peers)
    (build_flat_own_params : ∀ {m m' : Heap F} {v x_flat : SourceValue F}
      {cs' : List (Call F)},
      ObsFn W "KernelCheck::build_flat_own_params" [x_flat] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) m es x_flat →
      Heap.Extends m m' ∧ ∃ ns, flatOwnParams V es = some ns ∧
        RepList fieldListEnum RepNatField m' ns v)
    (extract_aux_spec_params_from_rec : ∀ {m m' : Heap F} {v : SourceValue F}
      {cs' : List (Call F)},
      ObsFn W "KernelCheck::extract_aux_spec_params_from_rec"
        [.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx], x_pnp] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      ∃ sp, RepList kexprListEnum (TmOExact κ) m' sp v ∧ (e.aux = true → sp = e.params))
    (extract_aux_occ_us : ∀ {m m' : Heap F} {v : SourceValue F} {cs' : List (Call F)},
      ObsFn W "KernelCheck::extract_aux_occ_us"
        [.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]] m v m' cs' →
      Heap.Extends h m → IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      ∃ us, RepKLevelList m' us v ∧ (e.aux = true → us = e.levels))
    (build_rec_type : ∀ {m m' : Heap F} {v x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::build_rec_type"
        [x_rc, x_pty, x_pnl, .field (nP : F), x_pni, x_elim, .field (off : F), x_flat, x_fop,
          .field (k : F)] m v m' cs' →
      CanonArgs κ V es peers fop off nl m x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ R, TmOExact κ m' R v ∧
        Eventually fun f => recTypeAt V f es off nP k = some R)
    (build_all_minors : ∀ {m m' : Heap F} {v x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::build_all_minors"
        [x_rc, x_flat, x_fop, .field (nP : F), .field (es.length : F), .field (nP : F), x_elim]
        m v m' cs' →
      CanonArgs κ V es peers fop off nl m x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs' → (∀ c ∈ cs', c ∈ root) →
      Heap.Extends m m' ∧ ∃ Ms, RepList kexprListEnum (TmOExact κ) m' Ms v ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (rules_at_pos : ∀ {h₀ h₁ h₂ h₃ : Heap F}
      {vcb vcanon v w x_aux x_sp x_ou x_flat x_peers x_fop x_lvls x_elim : SourceValue F}
      {cs₁ cs₂ cs₃ : List (Call F)} {fop : List Nat} (Ms : List KExpr),
      ObsFn W "KernelCheck::ctors_before_pos" [x_flat, .field (k : F), .field 0] h₀ vcb h₁ cs₁ →
      ObsFn W "KernelCheck::populate_rules"
        [x_rc, x_nc, vcb, x_pblk, x_pidx, .field (nP : F), .field (nMot : F), .field (nMin : F),
          x_ou, x_lvls, x_flat, x_peers, x_fop, x_aux, x_sp, .field 0, x_elim] h₁ vcanon h₂ cs₂ →
      ObsFn W "KernelCheck::compare_rules"
        [x_rules, vcanon, .field (nP : F), .field (nMot : F), .field (nMin : F), x_pblk, x_pidx,
          x_nc, .field 0, x_elim, x_ty, vcb] h₂ v h₃ cs₃ →
      Heap.Extends h h₀ →
      CanonArgs κ V es peers fop off nl h₀ x_flat x_peers x_fop x_lvls x_elim →
      IxVM.Consistency.Bounded cs₂ → IxVM.Consistency.Bounded cs₃ →
      (∀ c ∈ cs₁, c ∈ root) → (∀ c ∈ cs₂, c ∈ root) → (∀ c ∈ cs₃, c ∈ root) →
      FlatEntryRepExact κ h₀ e (.tuple [w, x_aux, x_sp, x_ou]) →
      nMot = es.length → nMin = Ms.length →
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) →
      Heap.Extends h₀ h₁ ∧ Heap.Extends h₁ h₂ ∧ Heap.Extends h₂ h₃ ∧
        ∃ (cbk : Nat) (bodies : List KExpr), ctorsBefore V es k = some cbk ∧
          (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
          stored.length ≤ self.nctors ∧
          ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
            ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
              ∃ cb, bodies[c]? = some cb ∧
                RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb) :
    Heap.Extends h h' ∧
    ∃ (fop : List Nat) (Ms : List KExpr) (cbk : Nat) (bodies : List KExpr),
      flatOwnParams V es = some fop ∧ nMot = es.length ∧ nMin = Ms.length ∧
      (Eventually fun f =>
        allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
      (Eventually fun f => recTypeAt V f es off nP k = some ty) ∧
      ctorsBefore V es k = some cbk ∧
      (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
      stored.length ≤ self.nctors ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
          ∃ cb, bodies[c]? = some cb ∧
            RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have hklt : k < es.length := (List.getElem?_eq_some_iff.mp hek).1
  -- everything up to the position, shared by the two arms that reach `canonical_rules_at_pos`
  have common : ∀ {x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx'
      x_pnl' x_pty' x_pnp' x_pni' x_nc' x_w' x_pblk' x_pidx' v209 v218 v247 v285 v323 x361 y362
      x353 y398 y354 v345 v477 v_so v486 : SourceValue F}
      {m210 m219 m248 m286 m324 m363 m355 m346 m478 m_yr m487 : Heap F}
      {cs212 cs229 cs258 cs296 cs334 cs372 cs386 cs408 cs480 cs_jq cs497 : List (Call F)},
      (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx] : SourceValue F) =
        .construct "KernelTypes::KConstantInfo" "Rec"
          [x_nlvls, x_ty', x_n_p, x_n_i, x_n_mot, x_n_min, x_rules', x_k', x_uns', x_rb',
            x_idx'] →
      (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx] : SourceValue F) =
        .construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl', x_pty', x_pnp', x_pni', x_nc', x_w', x_pblk', x_pidx'] →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX1 x_pnl' x_pty' x_pnp' x_pni' x_nc'
        x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb'
        x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl x_form h v209 m210 cs212 →
      ObsFn W "KernelCheck::build_rec_lvls_list" [x_nlvls, .field 0] m210 v218 m219 cs229 →
      ObsFn W "KernelCheck::build_flat_block" [x_rb', x_pblk', .field (off : F)]
        m219 v247 m248 cs258 →
      ObsFn W "KernelCheck::build_peer_recs" [v247, x_rb', x_addr] m248 v285 m286 cs296 →
      ObsFn W "KernelCheck::build_flat_own_params" [v247] m286 v323 m324 cs334 →
      ObsFn W "KernelCheck::is_muts_block" [x_rb'] m324 x361 m363 cs372 →
      ObsFn W "KernelCheck::is_muts_block" [x_pblk'] m363 y362 m355 cs386 →
      evalBinOp .mul x361 y362 = .ok x353 →
      ObsFn W "Bytes::address_eq" [x_rb', x_pblk'] m355 y398 m346 cs408 →
      evalBinOp .sub (.field 1) y398 = .ok y354 →
      evalBinOp .mul x353 y354 = .ok v345 →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX2 v345 v323 v285 v247 v218 v209
        x_pnl' x_pty' x_pnp' x_pni' x_nc' x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i x_n_mot
        x_n_min x_rules' x_k' x_uns' x_rb' x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl x_form m346 v477 m478 cs480 →
      «Obs».«KernelCheck::check_recursor_canonical_at».SegX_aowwkmcx v477 v345 v323 v285 v247
        v218 v209 x_pnl' x_pty' x_pnp' x_pni' x_nc' x_pblk' x_pidx' x_nlvls x_ty' x_n_p x_n_i
        x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx' x_rc
        (.construct "KernelTypes::KConstantInfo" "Rec"
          [.field (nl : F), x_ty, .field (nP : F), .field (nI : F), .field (nMot : F),
            .field (nMin : F), x_rules, x_k, x_uns, x_rb, x_idx]) x_addr
        (.construct "KernelTypes::KConstantInfo" "Induct"
          [x_pnl, x_pty, x_pnp, x_pni, x_nc, x_w, x_pblk, x_pidx])
        x_par (.field (off : F)) x_bnl x_form m478 v_so m_yr cs_jq →
      ObsFn W "KernelCheck::flat_find_pos_kind" [v247, x_par, v345, v477, v_so, .field 0]
        m_yr v486 m487 cs497 →
      (∀ c ∈ cs212 ++ cs229 ++ cs258 ++ cs296 ++ cs334 ++ cs372 ++ cs386 ++ cs408 ++ cs480 ++
          cs_jq ++ cs497, c ∈ cs) →
      (⟨"KernelCheck::build_flat_own_params", [v247], m286⟩ : Call F) ∈ cs →
      (x_ty' = x_ty ∧ x_n_p = .field (nP : F) ∧ x_n_mot = .field (nMot : F) ∧
          x_n_min = .field (nMin : F) ∧ x_rules' = x_rules ∧ x_pty' = x_pty ∧ x_pnl' = x_pnl ∧
          x_pni' = x_pni ∧ x_nc' = x_nc ∧ x_pblk' = x_pblk ∧ x_pidx' = x_pidx) ∧
        Heap.Extends h m487 ∧ es.length < 2 ^ 39 ∧
        (∃ fop, CanonArgs κ V es peers fop off nl m487 v247 v285 v323 v218 v209) ∧
        ∃ (aux' : Bool) (sp : List KExpr) (us : List KLevel),
          (e.aux = true → aux' = true ∧ sp = e.params ∧ us = e.levels) ∧
          match flatFindPosKind es e.addr aux' sp us with
          | some j => v486 = .tuple [.field 1, .field ((j : Nat) : F)]
          | none => v486 = .tuple [.field 0, .field 0] := by
    intro x_nlvls x_ty' x_n_p x_n_i x_n_mot x_n_min x_rules' x_k' x_uns' x_rb' x_idx'
      x_pnl' x_pty' x_pnp' x_pni' x_nc' x_w' x_pblk' x_pidx' v209 v218 v247 v285 v323 x361 y362
      x353 y398 y354 v345 v477 v_so v486 m210 m219 m248 m286 m324 m363 m355 m346 m478 m_yr m487
      cs212 cs229 cs258 cs296 cs334 cs372 cs386 cs408 cs480 cs_jq cs497
      hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3 sg2 sg3 evK hsubs hmemFop
    injection hrec with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl, -, -, rfl, -⟩ := hargs
    injection hind with _ _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := hargs
    have hin : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs212 ++ cs229 ++ cs258 ++ cs296 ++
        cs334 ++ cs372 ++ cs386 ++ cs408 ++ cs480 ++ cs_jq ++ cs497) → ∀ c ∈ cs', c ∈ cs :=
      fun hs c hc' => hsubs c (hs c hc')
    -- the elimination level
    have helim : RepKLevel m210 (elimLevel off) v209 ∧ Heap.Extends h m210 := by
      cases sg1 with
      | n1 hv hr hm _ =>
        have ho : off = 1 := (field_nat_eq_one hoff).mp hv
        subst hr hm ho
        refine ⟨?_, Heap.Extends.snoc _ _⟩
        have := (RepKLevel.allocParam h (n := 0) (by decide)).1
        simpa [elimLevel] using this
      | other hne hr hm _ =>
        have ho : off ≠ 1 := fun ho => hne ((field_nat_eq_one hoff).mpr ho)
        subst hr hm
        refine ⟨?_, Heap.Extends.snoc _ _⟩
        have := (RepKLevel.allocZero h).1
        simpa [elimLevel, ho] using this
    obtain ⟨helim, e1⟩ := helim
    have hlv := IxVM.Refinement.Decl.build_rec_lvls_list_spec hnl evL
    have e2 : Heap.Extends h m219 := e1.trans (ObsFn.heap_extends evL)
    have hflat := build_flat_block evF e2 (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
    have e3 : Heap.Extends h m248 := e2.trans (ObsFn.heap_extends evF)
    obtain ⟨as, has, hmap⟩ := build_peer_recs evP e3 (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc')) hflat
    have x1 : Heap.Extends m248 m286 := ObsFn.heap_extends evP
    have x2 : Heap.Extends m286 m324 := ObsFn.heap_extends evFop
    obtain ⟨-, fop, hfopEq, hfopRep⟩ := build_flat_own_params evFop (e3.trans x1)
      (sub (hin fun c hc' => by simp [hc']))
      (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc')) (flatList_mono x1 hflat)
    have x3 : Heap.Extends m324 m363 := ObsFn.heap_extends evM1
    have x4 : Heap.Extends m363 m355 := ObsFn.heap_extends evM2
    have e7 : Heap.Extends h m355 := e3.trans (x1.trans (x2.trans (x3.trans x4)))
    have hflat286 := flatList_mono x1 hflat
    have hlen : es.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd hmemFop (by simp) hflat286
    -- whether the recursor is an auxiliary's
    obtain ⟨b1, rfl⟩ := is_muts_block_bool evM1
    obtain ⟨b2, rfl⟩ := is_muts_block_bool evM2
    have hx353 := field_mul_bool' op1
    subst hx353
    obtain ⟨hy398, hm346⟩ := Lib.address_eq_spec evAeq
      (Bytes.repAddressRef_heapMono₂ addrTy e7 hrb) (Bytes.repAddressRef_heapMono₂ addrTy e7 hpb)
    subst hm346
    have hy398' : y398 = .field (if decide (arb = apb) then 1 else 0) := by
      rw [hy398]; by_cases hq : arb = apb <;> simp [hq]
    subst hy398'
    have hy354 := one_sub_bool op2
    subst hy354
    have hv345 := field_mul_bool' op3
    have haux' : e.aux = true → (b1 && b2 && !decide (arb = apb)) = true := by
      intro hea
      have h1 := is_muts_block hea (Or.inl rfl) evM1
        (e3.trans (x1.trans x2)) (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
      have h2 := is_muts_block hea (Or.inr rfl) evM2
        (e3.trans (x1.trans (x2.trans x3)))
        (fun c hc' => hroot c (hin (fun c hc' => by simp [hc']) c hc'))
      have hb1 : b1 = true := by
        cases b1
        · exact absurd (Value.field.inj h1) (by decide)
        · rfl
      have hb2 : b2 = true := by
        cases b2
        · exact absurd (Value.field.inj h2) (by decide)
        · rfl
      simp [hb1, hb2, haux hea]
    -- the recursor's parameters and levels
    have hsp : ∃ sp, RepList kexprListEnum (TmOExact κ) m478 sp v477 ∧
        (e.aux = true → sp = e.params) ∧ Heap.Extends m346 m478 := by
      cases sg2 with
      | n1 cs444 hv evX hc' =>
        subst hc'
        have hs444 : ∀ c ∈ cs444, c ∈ cs := hin (fun c hcc => by simp [hcc])
        obtain ⟨sp, hsp, hspe⟩ := extract_aux_spec_params_from_rec evX e7 (sub hs444)
          (fun c hcc => hroot c (hs444 c hcc))
        exact ⟨sp, hsp, hspe, ObsFn.heap_extends evX⟩
      | other hne hr hm _ =>
        subst hr hm
        refine ⟨[], .nil (by simp), ?_, Heap.Extends.snoc _ _⟩
        intro hea
        rw [hv345, haux' hea] at hne
        exact absurd rfl hne
    obtain ⟨sp, hsp, hspe, x6⟩ := hsp
    have hus : ∃ us, RepKLevelList m_yr us v_so ∧ (e.aux = true → us = e.levels) ∧
        Heap.Extends m478 m_yr := by
      cases sg3 with
      | n1 csj hv evX hc' =>
        subst hc'
        have hsj : ∀ c ∈ csj, c ∈ cs := hin (fun c hcc => by simp [hcc])
        obtain ⟨us, hus, huse⟩ := extract_aux_occ_us evX (e7.trans x6) (sub hsj)
          (fun c hcc => hroot c (hsj c hcc))
        exact ⟨us, hus, huse, ObsFn.heap_extends evX⟩
      | other hne hr hm _ =>
        subst hr hm
        rw [← IxVM.Refinement.Levels.klevelList_names]
        refine ⟨[], .nil (by simp), ?_, Heap.Extends.snoc _ _⟩
        intro hea
        rw [hv345, haux' hea] at hne
        exact absurd rfl hne
    obtain ⟨us, hus, huse, x7⟩ := hus
    have e9 : Heap.Extends h m_yr := e7.trans (x6.trans x7)
    have ext248 : Heap.Extends m248 m_yr := x1.trans (x2.trans (x3.trans (x4.trans (x6.trans x7))))
    have evK' : ObsFn W "KernelCheck::flat_find_pos_kind"
        [v247, x_par, auxVal (b1 && b2 && !decide (arb = apb)), v477, v_so,
          .field ((0 : Nat) : F)] m_yr v486 m487 cs497 := by
      have h0 : (.field 0 : SourceValue F) = .field ((0 : Nat) : F) := by simp
      rw [hv345, h0] at evK; exact evK
    obtain ⟨x8, hfind⟩ := flat_find_pos_kind_spec hinj es 0 evK'
      (sub (hin fun c hc' => by simp [hc'])) (root := cs497) (fun c hc' => hc')
      (flatList_mono ext248 hflat) (Bytes.repAddressRef_heapMono₂ addrTy e9 hpar)
      (tmOExactList_mono x7 hsp) hus
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, e9.trans x8, hlen, ?_,
      (b1 && b2 && !decide (arb = apb)), sp, us,
      fun hea => ⟨haux' hea, hspe hea, huse hea⟩, ?_⟩
    · have ext286 : Heap.Extends m286 m487 :=
        x2.trans (x3.trans (x4.trans (x6.trans (x7.trans x8))))
      exact ⟨fop, flatList_mono (ext248.trans x8) hflat,
        ⟨as, repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ addrTy) ext286 has, hmap⟩,
        hfopEq, fieldList_mono (x3.trans (x4.trans (x6.trans (x7.trans x8)))) hfopRep,
        hlv.mono ((ObsFn.heap_extends evF).trans (ext248.trans x8)),
        helim.mono ((ObsFn.heap_extends evL).trans ((ObsFn.heap_extends evF).trans
          (ext248.trans x8)))⟩
    · rw [hpar_eq] at hfind
      cases hf : flatFindPosKind es e.addr (b1 && b2 && !decide (arb = apb)) sp us with
      | none => rw [hf] at hfind; exact hfind
      | some j => rw [hf] at hfind; simpa using hfind
  -- the position is `k`, and the comparison there
  have finish : ∀ {x_self_pos v209 v218 v247 v285 v323 : SourceValue F} {m : Heap F}
      {cs' : List (Call F)} {fop : List Nat},
      ObsFn W "KernelCheck::canonical_rules_at_pos"
        [x_rc, v247, x_self_pos, x_nc, x_pblk, x_pidx, .field (nP : F), .field (nMot : F),
          .field (nMin : F), v218, v285, v323, x_rules, x_ty, x_pty, x_pnl, x_pni, v209,
          .field (off : F), x_form] m r h' cs' →
      x_self_pos = .field (k : F) → Heap.Extends h m → es.length < 2 ^ 39 →
      CanonArgs κ V es peers fop off nl m v247 v285 v323 v218 v209 → (∀ c ∈ cs', c ∈ cs) →
      ∃ (fop : List Nat) (Ms : List KExpr) (cbk : Nat) (bodies : List KExpr),
        flatOwnParams V es = some fop ∧ nMot = es.length ∧ nMin = Ms.length ∧
        (Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms) ∧
        (Eventually fun f => recTypeAt V f es off nP k = some ty) ∧
        ctorsBefore V es k = some cbk ∧
        (Eventually fun f => ruleBodiesAt V f es off nP nMot nMin nl k peers = some bodies) ∧
        stored.length ≤ self.nctors ∧
        ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
          ru.1 = c ∧ c < self.nctors ∧ NF (ixAddr ba) self.idx c ru.2.1 ∧
            ∃ cb, bodies[c]? = some cb ∧
              RuleFollows ty nP nMot nMin (cbk + c) ru.2.1 (elimLevel off) ru.2.2 cb := by
    intro x_self_pos v209 v218 v247 v285 v323 m cs' fop evC hpos ext hlen args hcs'
    subst hpos
    obtain ⟨Ms, cbk, bodies, h1, h2, h3, h4⟩ :=
      (canonical_rules_at_pos_spec (root := root) (fop := fop) (self := self) (ba := ba)
      (NF := NF) (stored := stored) (peers := peers) (nl := nl) evC (sub hcs')
      (fun c hc' => hroot c (hcs' c hc')) args.flat hklt hlen hnMot hnMin (hty.mono ext)
      (fun evv ext' => rc_validates_group evv (ext.trans ext'))
      (fun evv ext' hb hr => build_rec_type evv (args.mono ext') hb hr)
      (fun evv ext' hb hr => build_all_minors evv (args.mono ext') hb hr)
      (fun e' Ms ev1 ev2 ev3 ext' hb2 hb3 hr1 hr2 hr3 he' hrep hm1 hm2 hms => by
        rw [hek] at he'
        obtain rfl := Option.some.inj he'
        exact rules_at_pos Ms ev1 ev2 ev3 (ext.trans ext') (args.mono ext') hb2 hb3 hr1 hr2 hr3
          hrep hm1 hm2 hms)).2
    exact ⟨fop, Ms, cbk, bodies, args.fopEq, h1, h2, h3, h4⟩
  match Obs.«KernelCheck::check_recursor_canonical_at».obsx ev with
  | .Induct_n1_bind (hv15 := hrec) (hv86 := hind) (sg217 := sg1) (ev231 := evL) (ev260 := evF)
      (ev298 := evP) (ev336 := evFop) (ev374 := evM1) (ev388 := evM2) (op368 := op1)
      (ev410 := evAeq) (op404 := op2) (op360 := op3) (sg485 := sg2) (sg_berdancy := sg3)
      (ev499 := evK) (ev572 := evC) (hc725 := hc) .. =>
    obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ext, hlen, ⟨fop, args⟩, aux', sp,
        us, hauxe, hfind⟩ := common hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3
      sg2 sg3 evK (fun c hc' => by
        rw [hc]
        simp only [List.mem_append, List.mem_cons] at hc' ⊢
        rcases hc' with (((((((((( h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
          simp [h]) (by rw [hc]; simp)
    refine finish evC ?_ ext hlen args (fun c hc' => by rw [hc]; simp [hc'])
    cases hea : e.aux with
    | true =>
      obtain ⟨rfl, rfl, rfl⟩ := hauxe hea
      rw [flatFindPosKind_aux hd hek hea] at hfind
      injection hfind with hl; injection hl with _ hl; injection hl with hl
    | false =>
      cases aux' with
      | true =>
        rw [flatFindPosKind_own_none hd hek hea] at hfind
        injection hfind with hl; injection hl with hl
        exact absurd (Value.field.inj hl) (by decide)
      | false =>
        rw [flatFindPosKind_own hd hek hea] at hfind
        injection hfind with hl; injection hl with _ hl; injection hl with hl
  | .Induct_other (v247 := vflat) (m487 := m487) (m730 := m730) (cs741 := cs741)
      (x_self_pos := xpos) (hv15 := hrec) (hv86 := hind) (sg217 := sg1) (ev231 := evL)
      (ev260 := evF) (ev298 := evP) (ev336 := evFop) (ev374 := evM1) (ev388 := evM2)
      (op368 := op1) (ev410 := evAeq) (op404 := op2) (op360 := op3) (sg485 := sg2)
      (sg_berdancy := sg3) (ev499 := evK) (ev743 := evFP) (ev790 := evC) (hc943 := hc)
      (hnt0 := hnt) .. =>
    obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ext, hlen, ⟨fop, args⟩, aux', sp,
        us, hauxe, hfind⟩ := common hrec hind sg1 evL evF evP evFop evM1 evM2 op1 evAeq op2 op3
      sg2 sg3 evK (fun c hc' => by
        rw [hc]
        simp only [List.mem_append, List.mem_cons] at hc' ⊢
        rcases hc' with (((((((((( h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;>
          simp [h]) (by rw [hc]; simp)
    have evFP' : ObsFn W "KernelCheck::flat_find_pos" [vflat, x_par, .field ((0 : Nat) : F)]
        m487 (.tuple [.field 1, xpos]) m730 cs741 := by
      have h0 : (.field 0 : SourceValue F) = .field ((0 : Nat) : F) := by simp
      rw [h0] at evFP; exact evFP
    obtain ⟨hm730, hpos⟩ := flat_find_pos_spec es 0 evFP' (root := cs) (fun c hc' => by
      rw [hc]; simp [hc']) args.flat (Bytes.repAddressRef_heapMono₂ addrTy ext hpar)
    subst hm730
    refine finish evC ?_ ext hlen args (fun c hc' => by rw [hc]; simp [hc'])
    rw [hpar_eq] at hpos
    cases hea : e.aux with
    | true =>
      obtain ⟨rfl, rfl, rfl⟩ := hauxe hea
      rw [flatFindPosKind_aux hd hek hea] at hfind
      exact absurd hfind (hnt _)
    | false =>
      cases aux' with
      | true =>
        rw [flatFindPos_own hd hek hea] at hpos
        injection hpos with hl; injection hl with _ hl; injection hl with hl
        simpa using hl
      | false =>
        rw [flatFindPosKind_own hd hek hea] at hfind
        exact absurd hfind (hnt _)
  | .other (hne944 := hne) .. => exact absurd rfl (hne _ rfl)

/-! ## The member-level form -/

/-- **A recursor of the family record is `MemberRecon` at its position from what its check
gives** (`check_recursor_canonical_at_spec`, at the store's readings, the recursor's own counts
and the record's recursors as the peers): its type in the canonical reading is the reconstructed
type itself, so the two are related at the semantic equality of levels, and its rules, in the
canonical reading, follow the reconstructed bodies. -/
theorem memberRecon_of_canonical {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {rb : _root_.Address}
    {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {es : List FlatEntry} {off k : Nat}
    {r : Ixon.Recursor} {ty : KExpr} {stored : List (Nat × Nat × KExpr)}
    (hty : loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
      (mutsRoot rs k) r.typ = some ty)
    (hrules : ∀ (c : Nat) (ru : Ixon.RecursorRule), r.rules[c]? = some ru →
      ∃ (rhs : KExpr) (cidx : Nat),
        loadedAt t (fun x => E.blobs.get? x) crb (blockSelf t rb rs) r.lvls.toNat
          (mutsRoot rs k + 1 + ((c : Nat) : IxVM.F)) ru.rhs = some rhs ∧
        stored[c]? = some (cidx, ru.fields.toNat, rhs))
    (hcanon : ∃ (cbk : Nat) (bodies : List KExpr),
      (Eventually fun f =>
        recTypeAt (ReconView.ofStore t E) f es off r.params.toNat k = some ty) ∧
      ctorsBefore (ReconView.ofStore t E) es k = some cbk ∧
      (Eventually fun f =>
        ruleBodiesAt (ReconView.ofStore t E) f es off r.params.toNat r.motives.toNat
          r.minors.toNat r.lvls.toNat k (recAddrs rb rs) = some bodies) ∧
      ∀ (c : Nat) (ru : Nat × Nat × KExpr), stored[c]? = some ru →
        ∃ cb, bodies[c]? = some cb ∧
          RuleFollows ty r.params.toNat r.motives.toNat r.minors.toNat (cbk + c) ru.2.1
            (elimLevel off) ru.2.2 cb) :
    ∃ fuel, MemberRecon ExprLvEq t E rb crb rs es off fuel k r := by
  obtain ⟨cbk, bodies, ⟨a₁, h₁⟩, hcb, ⟨a₂, h₂⟩, hfol⟩ := hcanon
  refine ⟨max a₁ a₂, ty, ty, bodies, cbk, hty, h₁ _ (Nat.le_max_left _ _),
    IxVM.Refinement.Core.ExprLvEq.refl ty, h₂ _ (Nat.le_max_right _ _), hcb, ?_⟩
  intro c ru hru
  obtain ⟨rhs, cidx, hrhs, hrule⟩ := hrules c ru hru
  obtain ⟨cb, hcbd, hrf⟩ := hfol c _ hrule
  exact ⟨rhs, cb, hrhs, hcbd, hrf⟩

/-! ## The major premise of the reconstructed type -/

theorem peelForalls_wrapForalls (b : KExpr) (dl : KLevel) :
    ∀ (ds : List KExpr) (n : Nat),
      peelForalls (ds.length + n) (wrapForalls b ds dl) = peelForalls n b
  | [], n => by simp [wrapForalls]
  | d :: ds, n => by
    have ih := peelForalls_wrapForalls b dl ds n
    have hlen : (d :: ds).length + n = (ds.length + n) + 1 := by simp; omega
    rw [hlen]
    simpa [wrapForalls, peelForalls] using ih

theorem getAppFn_appSpine : ∀ (args : List KExpr) (head : KExpr),
    Ix.Kernel.Expr.getAppFn (appSpine head args) = Ix.Kernel.Expr.getAppFn head
  | [], _ => rfl
  | a :: as, head => by
    show Ix.Kernel.Expr.getAppFn (appSpine (.app head a) as) = _
    rw [getAppFn_appSpine as (.app head a)]
    rfl

theorem collectDoms_length_le' {V : ReconView} {f : Nat} :
    ∀ (n : Nat) (ty : KExpr) (p : List KExpr × KExpr),
      collectDoms V f n ty = some p → p.1.length ≤ n
  | 0, ty, p, h => by
    simp only [collectDoms, Option.some.injEq] at h
    subst h
    simp
  | n + 1, ty, p, h => by
    simp only [collectDoms] at h
    cases hb : binderOf V f ty with
    | none => rw [hb] at h; cases h
    | some o =>
      cases o with
      | none =>
        rw [hb] at h
        simp only [Option.some.injEq] at h
        subst h
        simp
      | some t =>
        obtain ⟨dd, bb, mm⟩ := t
        rw [hb] at h
        dsimp only at h
        cases hc : collectDoms V f n bb with
        | none => rw [hc] at h; cases h
        | some q =>
          rw [hc] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have := collectDoms_length_le' n bb q hc
          simp
          omega

theorem allMotives_length {V : ReconView} {f : Nat} {elim : KLevel} {nrp : Nat} :
    ∀ (es : List FlatEntry) (j : Nat) (ms : List KExpr),
      allMotives V f elim nrp es j = some ms → ms.length = es.length
  | [], j, ms, h => by
    simp only [allMotives, Option.some.injEq] at h
    subst h; rfl
  | e :: es, j, ms, h => by
    simp only [allMotives] at h
    cases hi : V.ind e.addr with
    | none => simp [hi] at h
    | some o =>
      cases o with
      | none => simp [hi] at h
      | some i =>
        simp only [hi] at h
        cases hm : motiveType V f e.addr i.ty i.np i.ni e.levels elim nrp e.aux e.params with
        | none => simp [hm] at h
        | some mt =>
          simp only [hm] at h
          cases hr : allMotives V f elim nrp es (j + 1) with
          | none => simp [hr] at h
          | some rest =>
            simp only [hr, Option.map_some, Option.some.injEq] at h
            subst h
            simp [allMotives_length es (j + 1) rest hr]

/-- **The major premise of the reconstructed type at entry `k` is over entry `k`**: where the
reconstructed type has a binder after `nP` parameters, one motive for each entry, the
reconstructed minor premises and `nI` binders, `nI` at least entry `k`'s index count, that
binder's domain is headed by entry `k`'s type at entry `k`'s levels. -/
theorem recTypeAt_major {V : ReconView} {f : Nat} {es : List FlatEntry} {off nP nI k : Nat}
    {R d : KExpr} {ek : FlatEntry} {self : IndData} {fop : List Nat} {Ms : List KExpr}
    (h : recTypeAt V f es off nP k = some R) (hek : es[k]? = some ek)
    (hself : V.ind ek.addr = some (some self)) (hfop : flatOwnParams V es = some fop)
    (hMs : allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (hni : self.ni ≤ nI)
    (hd : binderDomAfter (nP + es.length + Ms.length + nI) R = some d) :
    Ix.Kernel.Expr.getAppFn d = .const (V.key ek.addr) ek.levels := by
  unfold recTypeAt at h
  simp only [hek] at h
  cases h0 : es[0]? with
  | none => simp [h0] at h
  | some e0 =>
    simp only [h0] at h
    cases hp : V.ind e0.addr with
    | none => simp [hp] at h
    | some o =>
      cases o with
      | none => simp [hp] at h
      | some prim =>
        simp only [hp, hself] at h
        cases hc1 : collectDoms V f nP (exprInstLevels
            ((List.range prim.nl).map fun i => Ix.Kernel.Level.param (off + i)) prim.ty) with
        | none => simp [hc1] at h
        | some pd =>
          obtain ⟨paramDoms, pr⟩ := pd
          simp only [hc1] at h
          cases hmo : allMotives V f (elimLevel off) nP es 0 with
          | none => simp [hmo] at h
          | some motDoms =>
            simp only [hmo, hfop, hMs] at h
            cases hpm : peelMotiveParams nP ek.aux ek.params self.np 0
                (exprInstLevels ek.levels self.ty) with
            | none => simp [hpm] at h
            | some selfAfter =>
              simp only [hpm] at h
              cases hc2 : collectDoms V f self.ni selfAfter with
              | none => simp [hc2] at h
              | some id =>
                obtain ⟨idxRaw, ir⟩ := id
                simp only [hc2, Option.some.injEq] at h
                subst h
                have hpl : paramDoms.length ≤ nP := collectDoms_length_le' nP _ _ hc1
                have hil : idxRaw.length ≤ self.ni := collectDoms_length_le' self.ni _ _ hc2
                have hml : motDoms.length = es.length := allMotives_length es 0 motDoms hmo
                have hli : (liftIndices idxRaw (es.length + Ms.length)).length = idxRaw.length := by
                  simp [liftIndices]
                obtain ⟨δ, hδ⟩ : ∃ δ, nP + es.length + Ms.length + nI =
                    paramDoms.length + (motDoms.length + (Ms.length +
                      ((liftIndices idxRaw (es.length + Ms.length)).length + δ))) :=
                  ⟨nP + nI - paramDoms.length - idxRaw.length, by rw [hml, hli]; omega⟩
                unfold binderDomAfter at hd
                rw [hδ, peelForalls_wrapForalls, peelForalls_wrapForalls, peelForalls_wrapForalls,
                  peelForalls_wrapForalls] at hd
                cases δ with
                | zero =>
                  simp only [peelForalls, Option.some.injEq] at hd
                  subst hd
                  unfold appBVarsDown
                  rw [getAppFn_appSpine]
                  cases ek.aux with
                  | true =>
                    simp only [ite_true, specParamsLifted]
                    rw [getAppFn_appSpine]; rfl
                  | false =>
                    simp only [Bool.false_eq_true, ite_false, appBVarsDec]
                    rw [getAppFn_appSpine]; rfl
                | succ δ =>
                  cases δ with
                  | zero => simp [peelForalls] at hd
                  | succ δ => simp [peelForalls] at hd

/-- **The declared type's major premise is over the entry the check compared it at**: what
`check_recursor_canonical_at_spec` gives of a recursor with `nP` parameters, `nMot` motives,
`nMin` minors and `nI` indices (the motive and minor counts are the reconstruction's, the declared
type is the reconstructed type at `k`) makes the binder after its parameters, motives, minors and
indices one over entry `k`'s type at entry `k`'s levels. At one of the block's own types these are
the levels `build_flat_originals` writes, which no reading of the record gives. -/
theorem major_head_of_canonical {V : ReconView} {es : List FlatEntry}
    {off nP nMot nMin nI k : Nat} {ty d : KExpr} {ek : FlatEntry} {self : IndData}
    {fop : List Nat} {Ms : List KExpr} (hek : es[k]? = some ek)
    (hself : V.ind ek.addr = some (some self)) (hfop : flatOwnParams V es = some fop)
    (hMot : nMot = es.length) (hMin : nMin = Ms.length)
    (hMs : Eventually fun f =>
      allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    (hR : Eventually fun f => recTypeAt V f es off nP k = some ty) (hni : self.ni ≤ nI)
    (hd : binderDomAfter (nP + nMot + nMin + nI) ty = some d) :
    Ix.Kernel.Expr.getAppFn d = .const (V.key ek.addr) ek.levels := by
  obtain ⟨a₁, h₁⟩ := hMs
  obtain ⟨a₂, h₂⟩ := hR
  subst hMot hMin
  exact recTypeAt_major (h₂ (max a₁ a₂) (Nat.le_max_right _ _)) hek hself hfop
    (h₁ (max a₁ a₂) (Nat.le_max_left _ _)) hni hd

end IxVM.Refinement.Binding.FamilyRecon
