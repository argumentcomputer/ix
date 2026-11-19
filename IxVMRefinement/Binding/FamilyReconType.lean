import IxVMRefinement.Binding.FamilyReconFlat
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelCheck5
import IxVMRefinement.Obs.KernelCheck10
import IxVMRefinement.Obs.KernelCheck12

/-! # The reconstructed recursor type on `TmOExact`: motives and assembly

The type side of the reconstruction (`KernelCheck::build_rec_type`), each function read as the
model's (`FamilyReconModel`) on open exact terms, at every large enough fuel of head normalization:

* `build_major_args_for_member_spec`, `build_major_args_for_self_spec`: the major premise's
  parameter arguments (`majorParams`, `appBVarsDec`, or `specParamsLifted` at an auxiliary);
* `build_motive_type_flat_spec` (`motiveType`);
* `build_all_motives_walk_spec`, `build_all_motives_spec` (`allMotives`);
* `build_flat_own_params_spec` (`flatOwnParams`);
* `build_rec_type_from_spec`, `build_rec_type_spec` (`recTypeAt`), from the reading of
  `build_all_minors` (`allMinors`) as a hypothesis.

The circuit skips an entry of the flattened family that is no inductive type where the model has
no value, so the family statements are over families whose every entry is one (`AllInd`), and
whose every entry's parameters are instantiated by a recursor parameter or a parameter of the
entry (`ParamsFit`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry exprInstLevels)
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum addrTy ixAddr
  Resolved klevelListEnum_eq)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open IxVM (F)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Families the reconstruction is total on -/

/-- Every entry of the family is an inductive type of the view. -/
def AllInd (V : ReconView) (es : List FlatEntry) : Prop :=
  ∀ e ∈ es, ∃ d, V.ind e.addr = some (some d)

/-- **An entry's parameters fit a recursor over `nrp` parameters**: each parameter of the entry's
type is instantiated by a parameter of the entry (at an auxiliary) or by one of the recursor's
(`subst_param_for` builds `bvar (nrp - 1 - j)` in the field). -/
def ParamsFit (V : ReconView) (nrp : Nat) (e : FlatEntry) : Prop :=
  ∀ d, V.ind e.addr = some (some d) →
    ∀ i, i < d.np → ¬ (e.aux = true ∧ i < e.params.length) → i < nrp

theorem AllInd.tail {V : ReconView} {e : FlatEntry} {es : List FlatEntry}
    (h : AllInd V (e :: es)) : AllInd V es :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

section

variable {κ : _root_.Address → KKey}

/-! ## The major premise's parameter arguments -/

/-- **`KernelCheck::build_major_args_for_member(head, nrp, depth, is_aux, ps)`**: the head applied
to the recursor's parameters under `depth` binders (`majorParams`), or at an auxiliary to the
entry's parameters lifted by `depth` (`specParamsLifted`). -/
theorem build_major_args_for_member_spec {nrp depth : Nat} {aux : Bool} {Ps : List KExpr}
    (hnd : nrp + depth < 9223372036854775808) (hd : depth < 4611686018427387904)
    {xh xps r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)} {H : KExpr}
    (ev : ObsFn W "KernelCheck::build_major_args_for_member"
      [xh, .field (nrp : F), .field (depth : F), auxVal aux, xps] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hH : TmOExact κ h H xh) (hP : RepList kexprListEnum (TmOExact κ) h Ps xps) :
    Heap.Extends h h' ∧
      TmOExact κ h' (if aux then specParamsLifted H Ps depth else majorParams H nrp depth) r := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  rcases Obs.«KernelCheck::build_major_args_for_member».obs ev with
    ⟨cs₁, hv, ev₁, hc⟩ | ⟨cs₁, hne, ev₁, hc⟩
  · obtain rfl : aux = false := auxVal_eq_zero.mp hv
    simpa using build_major_params_spec hnd ev₁ hH
  · obtain rfl : aux = true := by
      cases aux
      · exact (hne rfl).elim
      · rfl
    simpa using apply_spec_params_lifted_spec hd Ps ev₁
      (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc']) hH hP

/-- **`KernelCheck::build_major_args_for_self(head, nrp, top, lift, is_aux, ps)`**: the head
applied to the recursor's parameters from `bvar top` down (`appBVarsDec`), or at an auxiliary to
the entry's parameters lifted by `lift` (`specParamsLifted`). -/
theorem build_major_args_for_self_spec {nrp top lift : Nat} {aux : Bool} {Ps : List KExpr}
    (hn : nrp < 9223372036854775808) (ht : top < 9223372036854775808) (hnt : nrp ≤ top + 1)
    (hl : lift < 4611686018427387904)
    {xh xps r : SourceValue F} {h h' : Heap F} {cs root : List (Call F)} {H : KExpr}
    (ev : ObsFn W "KernelCheck::build_major_args_for_self"
      [xh, .field (nrp : F), .field (top : F), .field (lift : F), auxVal aux, xps] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hH : TmOExact κ h H xh) (hP : RepList kexprListEnum (TmOExact κ) h Ps xps) :
    Heap.Extends h h' ∧
      TmOExact κ h' (if aux then specParamsLifted H Ps lift else appBVarsDec H nrp top) r := by
  refine ⟨ObsFn.heap_extends ev, ?_⟩
  rcases Obs.«KernelCheck::build_major_args_for_self».obs ev with
    ⟨cs₁, hv, ev₁, hc⟩ | ⟨cs₁, hne, ev₁, hc⟩
  · obtain rfl : aux = true := auxVal_eq_one.mp hv
    simpa using apply_spec_params_lifted_spec hl Ps ev₁
      (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc']) hH hP
  · obtain rfl : aux = false := by
      cases aux
      · rfl
      · exact (hne rfl).elim
    simpa using build_apply_bvars_decreasing_spec hn ht hnt ev₁ hH

/-! ## The motives -/

/-- **`KernelCheck::build_motive_type_flat`** is `motiveType`: the motive's type of the entry at
the address `a`, with the type `T`, `nOwn` parameters and `nIdx` indices, at the levels `us`. -/
theorem build_motive_type_flat_spec {V : ReconView} {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    {a : Bytes.Address} [res : Resolved (κ (ixAddr a))]
    {nOwn nIdx nrp : Nat} {aux : Bool} {Ps : List KExpr} {us : List KLevel} {elim : KLevel}
    {T : KExpr}
    (hnOwn : nOwn < 72057594037927936) (hnIdx : nIdx < 72057594037927936)
    (hnrp : nrp < 4294967296)
    (hj : ∀ i, i < nOwn → ¬ (aux = true ∧ i < Ps.length) → i < nrp)
    {xrc xa xty xus xelim xps xpt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_motive_type_flat"
      [xrc, xa, xty, .field (nOwn : F), .field (nIdx : F), xus, xelim, .field (nrp : F),
        auxVal aux, xps, xpt] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (ra : Bytes.RepAddressRef addrTy h a xa) (hT : TmOExact κ h T xty)
    (hus : RepKLevelList h us xus) (hel : RepKLevel h elim xelim)
    (hP : RepList kexprListEnum (TmOExact κ) h Ps xps) :
    Heap.Extends h h' ∧ ∃ M, TmOExact κ h' M r ∧
      Eventually fun f => motiveType V f (ixAddr a) T nOwn nIdx us elim nrp aux Ps = some M := by
  have hext : Heap.Extends h h' := ObsFn.heap_extends ev
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::build_motive_type_flat».obs ev with
  | .run (v1 := v1) (m2 := m2) (cs42 := cs42) (v31 := v31) (m32 := m32) (v92 := v92) (m93 := m93)
      (m139 := m139) (v169 := v169) (m170 := m170) (v223 := v223) (m224 := m224) (m261 := m261)
      (m284 := m284) (m300 := m300) (m313 := m313) (ev14 := ev14) (ev44 := ev44)
      (ev105 := ev105) (hm149 := hm149) (ev182 := ev182) (ev236 := ev236) (hm271 := hm271)
      (hm294 := hm294) (hm308 := hm308) (hm323 := hm323) (ev356 := ev356) (hc381 := hc) .. =>
    have hPs : Ps.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd (c := ⟨"KernelCheck::peel_motive_params_subst",
        [v1, .field (nOwn : F), .field (nrp : F), auxVal aux, xps, .field 0], m2⟩)
        (p := xps) (by rw [hc]; simp) (by simp) (tmOExactList_mono ev14.heap_extends hP)
    -- the type at the entry's levels, past its parameters
    have hT1 := expr_inst_levels_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hT hus ev14
    have ext₁ : Heap.Extends h m2 := ObsFn.heap_extends ev14
    have ev44' : ObsFn W "KernelCheck::peel_motive_params_subst"
        [v1, .field (nOwn : F), .field (nrp : F), auxVal aux, xps, .field ((0 : Nat) : F)]
        m2 v31 m32 cs42 := by simpa using ev44
    obtain ⟨E', hpeel, hE'⟩ := peel_motive_params_subst_spec (κ := κ) (by omega) (by omega)
      nOwn 0 (by omega) (fun i _ hi hni => hj i (by omega) hni) ev44'
      (sub fun c hc' => by rw [hc]; simp [hc']) hT1 (tmOExactList_mono ext₁ hP)
    have ext₂ : Heap.Extends m2 m32 := ObsFn.heap_extends ev44
    -- its index domains
    obtain ⟨ext₃, Ds, hDs, hev⟩ := collect_index_doms_spec hA hD hI hC hM nIdx (by omega) ev105
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hE'
    have ext₁₃ : Heap.Extends h m93 := ext₁.trans (ext₂.trans ext₃)
    -- the major premise
    subst hm149
    have ext₄ : Heap.Extends m93
        (m93 ++ [.construct "KernelTypes::KExprNode" "Const" [xa, xus]]) := Heap.Extends.snoc _ _
    have hhead : TmOExact κ (m93 ++ [.construct "KernelTypes::KExprNode" "Const" [xa, xus]])
        (.const (κ (ixAddr a)) us) (.ptr (.enum "KernelTypes::KExprNode") m93.length) :=
      ⟨0, .const (by simp) (Bytes.repAddressRef_heapMono₂ addrTy (ext₁₃.trans ext₄) ra)
        (hus.mono (ext₁₃.trans ext₄))⟩
    obtain ⟨ext₅, hargs⟩ := build_major_args_for_member_spec (κ := κ) (root := root)
      (nrp := nrp) (depth := nIdx) (aux := aux) (Ps := Ps) (by omega) (by omega) ev182
      (sub fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hhead
      (tmOExactList_mono (ext₁₃.trans ext₄) hP)
    have hmajor := build_major_indices_spec (κ := κ) (n := nIdx) (by omega) ev236 hargs
    have ext₆ : Heap.Extends m170 m224 := ObsFn.heap_extends ev236
    have ext₁₆ : Heap.Extends h m224 := ext₁₃.trans (ext₄.trans (ext₅.trans ext₆))
    -- the sort, the datum and the binder of the major premise
    have ext₇ : Heap.Extends m224 m261 := by rw [hm271]; exact Heap.Extends.snoc _ _
    have ext₈ : Heap.Extends m261 m300 := by rw [hm308]; exact Heap.Extends.snoc _ _
    have ext₉ : Heap.Extends m300 m284 := by rw [hm294]; exact Heap.Extends.snoc _ _
    have ext₁₀ : Heap.Extends m284 m313 := by rw [hm323]; exact Heap.Extends.snoc _ _
    have ext₇₁₀ := ext₇.trans (ext₈.trans (ext₉.trans ext₁₀))
    have cSrt : m261[m224.length]? = some (.construct kexprEnum "Srt" [xelim]) := by
      rw [hm271]; simp
    have cZero : m300[m261.length]? = some (.construct "KernelTypes::KLevelNode" "Zero" []) := by
      rw [hm308]; simp
    have cSucc : m284[m300.length]? = some (.construct "KernelTypes::KLevelNode" "Succ"
        [.ptr (.enum "KernelTypes::KLevelNode") m261.length]) := by
      rw [hm294]; simp
    have cAll : m313[m284.length]? = some (.construct kexprEnum "Forall"
        [v223, .ptr (.enum "KernelTypes::KExprNode") m224.length,
          .ptr (.enum "KernelTypes::KLevelNode") m300.length]) := by
      rw [hm323]; simp
    have hsort : ∀ k, TmExact κ 0 ghost0 m261 k (.sort elim)
        (.ptr (.enum kexprEnum) m224.length) :=
      fun k => .sort cSrt (hel.mono (ext₁₆.trans ext₇))
    have hnever : RepKLevel m284 (.succ .zero)
        (.ptr (.enum "KernelTypes::KLevelNode") m300.length) :=
      .succ cSucc ((RepKLevel.zero cZero).mono ext₉)
    obtain ⟨k₁, r₁⟩ := hmajor.mono ext₇₁₀
    have hwm : TmOExact κ m313
        (.forallE
          (appBVarsDown (if aux then specParamsLifted (.const (κ (ixAddr a)) us) Ps nIdx
            else majorParams (.const (κ (ixAddr a)) us) nrp nIdx) nIdx)
          (.sort elim) (bmeta (.succ .zero)))
        (.ptr (.enum "KernelTypes::KExprNode") m284.length) :=
      ⟨k₁, .forallE cAll r₁ ((hsort (k₁ + 1)).mono (ext₈.trans (ext₉.trans ext₁₀)))
        (hnever.mono ext₁₀)⟩
    have hres := wrap_foralls_spec (κ := κ) Ds ev356 hwm
      (tmOExactList_mono ((ext₄.trans (ext₅.trans ext₆)).trans ext₇₁₀) hDs) (hnever.mono ext₁₀)
    refine ⟨hext, _, hres, hev.mono fun f hf => ?_⟩
    cases hc' : collectDoms V f nIdx E' with
    | none => rw [hc'] at hf; cases hf
    | some p =>
      obtain ⟨ds, rest⟩ := p
      rw [hc'] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      simp only [motiveType, hpeel, hc', hK]

/-- An entry of a represented family, read off its tuple. -/
theorem FlatEntryRepExact.tuple_inv {h : Heap F} {e : FlatEntry} {xa xaux xps xls : SourceValue F}
    (he : FlatEntryRepExact κ h e (.tuple [xa, xaux, xps, xls])) :
    ∃ a : Bytes.Address, xaux = auxVal e.aux ∧ Bytes.RepAddressRef addrTy h a xa ∧
      ixAddr a = e.addr ∧ RepList kexprListEnum (TmOExact κ) h e.params xps ∧
      RepKLevelList h e.levels xls := by
  obtain ⟨xa', xps', xls', a, htup, ra, ha, hps, hls⟩ := he
  injection htup with hl
  injection hl with h1 hl
  injection hl with h2 hl
  injection hl with h3 hl
  injection hl with h4
  subst h1 h2 h3 h4
  exact ⟨a, rfl, ra, ha, hps, hls⟩

/-- **`KernelCheck::build_all_motives_walk(rc, flat, elim, nrp, j, ptypes)`** is `allMotives`:
every entry's motive type, the first lifted by `j`. -/
theorem build_all_motives_walk_spec {V : ReconView} {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    {elim : KLevel} {nrp : Nat} (hnrp : nrp < 4294967296) :
    ∀ (es : List FlatEntry) (j : Nat), j + es.length < 4611686018427387904 →
      (∀ e ∈ es, Resolved (κ e.addr)) → AllInd V es → (∀ e ∈ es, ParamsFit V nrp e) →
      ∀ {xrc xflat xelim xpt r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::build_all_motives_walk"
        [xrc, xflat, xelim, .field (nrp : F), .field (j : F), xpt] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat → RepKLevel h elim xelim →
      Heap.Extends h h' ∧ ∃ Ms, RepList kexprListEnum (TmOExact κ) h' Ms r ∧
        Eventually fun f => allMotives V f elim nrp es j = some Ms := by
  intro es
  induction es with
  | nil =>
    intro j hjl hres hind hfit xrc xflat xelim xpt r h h' cs ev hbnd hroot hes hel
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      subst hr hh
      exact ⟨hext, [], Lib.rep_store_nil h, Eventually.always fun _ => rfl⟩
    | .Cons_Induct (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hzs
  | cons e es ih =>
    intro j hjl hres hind hfit xrc xflat xelim xpt r h h' cs ev hbnd hroot hes hel
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    simp only [List.length_cons] at hjl
    match Obs.«KernelCheck::build_all_motives_walk».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons_Induct (x_rest := xrest) (m83 := m1) (v168 := vmt) (m169 := m2) (cs281 := csl)
        (v270 := vl) (m271 := m3) (v316 := vrest) (m325 := m4) (v340 := vj) (ld12 := ld)
        (ev98 := evg) (ld92 := ldci) (ev181 := evm) (ev283 := evl) (he311 := hr) (hm310 := hh)
        (op383 := op) (ev335 := evr) (hc392 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨a, rfl, ra, ha, hps, hls⟩ := FlatEntryRepExact.tuple_inv hz
      obtain ⟨d, ba, hd, -, hnp, hni, -, -, -, hty, rfl, rfl, -⟩ :=
        (hI ra evg (hroot _ (by rw [hc]; simp))
          (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).1 _ _ _ _ _ _ _ _ rfl
      rw [ha] at hd
      have ext₁ : Heap.Extends h m1 := ObsFn.heap_extends evg
      have : Resolved (κ (ixAddr a)) := by rw [ha]; exact hres _ (by simp)
      obtain ⟨ext₂, M, hM', hmt⟩ := build_motive_type_flat_spec hA hD hI hC hM hK
        hnp hni hnrp (hfit _ (by simp) d hd) evm (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (Bytes.repAddressRef_heapMono₂ addrTy ext₁ ra) hty (hls.mono ext₁) (hel.mono ext₁)
        (tmOExactList_mono ext₁ hps)
      rw [ha] at hmt
      have evl' : ObsFn W "KernelSubst::expr_lift"
          [vmt, .field (j : F), .field ((0 : Nat) : F)] m2 vl m3 csl := by simpa using evl
      have hlift := expr_lift_tmOExact (shift := j) (cut := 0) (by omega) (by decide)
        (sub fun c hc' => by rw [hc]; simp [hc']) hM' evl'
      have ext₃ : Heap.Extends m2 m3 := ObsFn.heap_extends evl
      have ext₁₃ := ext₁.trans (ext₂.trans ext₃)
      obtain rfl := binop_add_one_nat op
      obtain ⟨ext₄, Ms, hMs, hrest⟩ := ih (j + 1) (by omega)
        (fun x hx => hres x (List.mem_cons_of_mem _ hx)) hind.tail
        (fun x hx => hfit x (List.mem_cons_of_mem _ hx)) evr
        (sub fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc']))
        (flatList_mono ext₁₃ hzs') (hel.mono ext₁₃)
      subst hr hh
      refine ⟨hext, _, Lib.rep_store_cons tmOExact_heapMono₂ (hlift.mono ext₄) hMs,
        (hmt.and hrest).mono fun f ⟨h1, h2⟩ => ?_⟩
      simp only [allMotives, hd, h1, h2, Option.map_some]
    | .Cons_other (ld12 := ld) (ev98 := evg) (ld92 := ldci) (hne393 := hne) (hc451 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨a, rfl, ra, ha, hps, hls⟩ := FlatEntryRepExact.tuple_inv hz
      have hnone := (hI ra evg (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci).2 hne
      rw [ha] at hnone
      obtain ⟨d, hd⟩ := hind e (by simp)
      rw [hd] at hnone
      cases hnone

/-- **`KernelCheck::build_all_motives(rc, flat, elim, nrp)`** is `allMotives` from `0`: every
entry's motive type, the `j`-th lifted by `j`. -/
theorem build_all_motives_spec {V : ReconView} {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    {elim : KLevel} {nrp : Nat} (hnrp : nrp < 4294967296) {es : List FlatEntry}
    (hlen : es.length < 4611686018427387904)
    (hres : ∀ e ∈ es, Resolved (κ e.addr)) (hind : AllInd V es)
    (hfit : ∀ e ∈ es, ParamsFit V nrp e)
    {xrc xflat xelim r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_all_motives" [xrc, xflat, xelim, .field (nrp : F)] h r h'
      cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat) (hel : RepKLevel h elim xelim) :
    Heap.Extends h h' ∧ ∃ Ms, RepList kexprListEnum (TmOExact κ) h' Ms r ∧
      Eventually fun f => allMotives V f elim nrp es 0 = some Ms := by
  obtain ⟨cs₁, vpt, m₁, cs₂, evc, evw, hc⟩ := Obs.«KernelCheck::build_all_motives».obs ev
  have ext₁ : Heap.Extends h m₁ := ObsFn.heap_extends evc
  have evw' : ObsFn W "KernelCheck::build_all_motives_walk"
      [xrc, xflat, xelim, .field (nrp : F), .field ((0 : Nat) : F), vpt] m₁ r h' cs₁ := by
    simpa using evw
  obtain ⟨-, Ms, hMs, hev⟩ := build_all_motives_walk_spec hA hD hI hC hM hK hnrp es 0
    (by omega) hres hind hfit evw'
    (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
    (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (flatList_mono ext₁ hes) (hel.mono ext₁)
  exact ⟨ObsFn.heap_extends ev, Ms, hMs, hev⟩

/-! ## The entries' parameter counts -/

/-- **`KernelCheck::build_flat_own_params(flat)`** is `flatOwnParams`: each entry's parameter
count. -/
theorem build_flat_own_params_spec {V : ReconView} {root : List (Call F)}
    (hI : IndAnswers root κ V) :
    ∀ (es : List FlatEntry), AllInd V es →
      ∀ {xflat r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelCheck::build_flat_own_params" [xflat] h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      Heap.Extends h h' ∧ ∃ ns, flatOwnParams V es = some ns ∧
        RepList fieldListEnum RepNatField h' ns r := by
  intro es
  induction es with
  | nil =>
    intro hind xflat r h h' cs ev hbnd hroot hes
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::build_flat_own_params».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      subst hr hh
      exact ⟨hext, [], rfl, Lib.rep_store_nil h⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      cases hzs
  | cons e es ih =>
    intro hind xflat r h h' cs ev hbnd hroot hes
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    match Obs.«KernelCheck::build_flat_own_params».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases IxVM.Refinement.Core.RepList.nil_of_load hes ld
    | .Cons (m83 := m1) (v181 := vnp) (m182 := m2) (v199 := vrest) (m208 := m3) (ld12 := ld)
        (ev98 := evg) (ld92 := ldci) (sg189 := sg) (he194 := hr) (hm193 := hh) (ev218 := evr)
        (hc227 := hc) .. =>
      obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hes ld
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain ⟨a, -, ra, ha, -, -⟩ := FlatEntryRepExact.tuple_inv hz
      have ext₁ : Heap.Extends h m1 := ObsFn.heap_extends evg
      have hans := hI ra evg (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ldci
      have hseg : ∃ d, V.ind e.addr = some (some d) ∧ vnp = .field (d.np : F) ∧ m2 = m1 := by
        cases sg with
        | Induct w1 w2 xn w3 w4 w5 w6 w7 hv hr' hh' _ =>
          obtain ⟨d, ba, hd, -, -, -, -, -, -, -, hxn, -⟩ :=
            hans.1 _ _ _ _ _ _ _ _ hv
          rw [ha] at hd
          exact ⟨d, hd, by rw [hr', hxn], hh'⟩
        | other hne _ _ _ =>
          have hnone := hans.2 hne
          rw [ha] at hnone
          obtain ⟨d, hd⟩ := hind e (by simp)
          rw [hd] at hnone
          cases hnone
      obtain ⟨d, hd, rfl, rfl⟩ := hseg
      obtain ⟨ext₂, ns, hns, hrep⟩ := ih hind.tail evr
        (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc'])
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (flatList_mono ext₁ hzs')
      subst hr hh
      refine ⟨hext, d.np :: ns, by simp only [flatOwnParams, hd, hns], ?_⟩
      exact Lib.rep_store_cons repNatField_heapMono₂ rfl hrep

/-! ## The recursor's level parameters, lengths and telescopes -/

/-- **`KernelCheck::build_param_lvls_range(start, count, i)`**: the level parameters
`start + i`, …, `start + count - 1`. -/
theorem build_param_lvls_range_go :
    ∀ (rem start i : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      start + i + rem ≤ 4294967296 →
      ObsFn W "KernelCheck::build_param_lvls_range"
        [.field (start : F), .field ((i + rem : Nat) : F), .field (i : F)] h r h' cs →
      RepKLevelList h' ((List.range rem).map fun k => Ix.Kernel.Level.param (start + (i + k))) r
  | 0, start, i, r, h, h', cs, _, ev => by
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (he28 := hr) (hm27 := hh) .. =>
      subst hr hh
      have hnil : RepKLevelList
          (h ++ [.construct KernelLevels.klevelListEnum "Nil" []]) []
          (.ptr (.enum KernelLevels.klevelListEnum) h.length) := .nil (by simp)
      rwa [← klevelListEnum_eq] at hnil
    | .other (op17 := op17) (hne33 := hne33) .. =>
      exact absurd rfl (binop_sub_ne_nat op17 hne33)
  | rem + 1, start, i, r, h, h', cs, hlt, ev => by
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (op17 := op17) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op17
      omega
    | .other (v46 := v46) (m48 := m48) (v60 := v60) (m78 := m78) (v91 := v91)
        (he41 := hr) (hm40 := hh) (hm56 := hm56) (op74 := op74) (op119 := op119)
        (ev88 := ev88) .. =>
      subst hr hh
      obtain rfl := binop_add_nat op74
      obtain rfl := binop_add_one_nat op119
      rw [show i + (rem + 1) = (i + 1) + rem by omega] at ev88
      have htl := build_param_lvls_range_go rem start (i + 1) (by omega) ev88
      have hhd_m48 : RepKLevel m48 (.param (start + i))
          (.ptr (.enum "KernelTypes::KLevelNode") h.length) := by
        rw [hm56]
        exact .param (by omega) (by simp)
      have hhd_m78 := repKLevel_heapMono₂ ev88.heap_extends hhd_m48
      have ext_end : Heap.Extends m78
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]]) := Heap.Extends.snoc _ _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap_eq :
          List.map ((fun k => Ix.Kernel.Level.param (start + (i + k))) ∘ Nat.succ)
              (List.range rem) =
            List.map (fun k => Ix.Kernel.Level.param (start + (i + 1 + k))) (List.range rem) := by
        apply List.map_congr_left; intro k _
        simp only [Function.comp_apply]
        apply congrArg Ix.Kernel.Level.param
        show (start + (i + k.succ) : Nat) = start + (i + 1 + k)
        omega
      rw [Nat.add_zero, hmap_eq]
      have hcons : RepKLevelList
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]])
          (.param (start + i) ::
            (List.range rem).map fun k => Ix.Kernel.Level.param (start + (i + 1 + k)))
          (.ptr (.enum KernelLevels.klevelListEnum) m78.length) :=
        .cons (by rw [← klevelListEnum_eq]; simp)
          (repKLevel_heapMono₂ ext_end hhd_m78)
          (htl.mono ext_end)
      rwa [← klevelListEnum_eq] at hcons

/-- **`KernelCheck::build_param_lvls_range(start, count, 0)`**: the level parameters `start`, …,
`start + count - 1` (each below `2^32`). -/
theorem build_param_lvls_range_spec {start count : Nat} {r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hlt : start + count ≤ 4294967296)
    (ev : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (start : F), .field (count : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range count).map fun k => Ix.Kernel.Level.param (start + k)) r := by
  have ev' : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (start : F), .field ((0 + count : Nat) : F), .field ((0 : Nat) : F)] h r h' cs := by
    simpa using ev
  simpa using build_param_lvls_range_go count start 0 (by omega) ev'

/-- The length of a represented family. -/
theorem flat_length {R : Heap F → FlatEntry → SourceValue F → Prop} {xs : List FlatEntry}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [l] h r h' cs)
    (hl : RepList flatListEnum R h xs l) : r = .field (xs.length : F) ∧ h' = h :=
  Lib.Lists.length_spec
    (t := .tuple [.ptr (.array .field 32), .field,
      .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]),
      .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])])]) (R := R)
    (by rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]; exact hl)

/-- `collectDoms` gives at most the domains asked for. -/
theorem collectDoms_length_le {V : ReconView} {f : Nat} :
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
          have := collectDoms_length_le n bb q hc
          simp only [List.length_cons]
          omega

/-! ## The recursor type -/

/-- **`KernelCheck::build_rec_type_from`** at the family's first type (`prim`, the entry `e0`) is
`recTypeAt`: the recursor type at entry `k` of the family `es`, at the elimination offset `off`,
over `nP` parameters, from the reading of `build_all_minors` (`allMinors`). The index count the
circuit is handed is entry `k`'s (`hself`), and the family's parameter counts are `fop`. -/
theorem build_rec_type_from_spec {V : ReconView} {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    {es : List FlatEntry} {fop : List Nat} {off nP nI k : Nat} {e0 : FlatEntry} {prim : IndData}
    (hnP : nP < 4294967296) (hnI : nI < 4294967296) (hoff : off + prim.nl ≤ 4294967296)
    (hk : k < es.length)
    (hres : ∀ e ∈ es, Resolved (κ e.addr)) (hind : AllInd V es)
    (hfit : ∀ e ∈ es, ParamsFit V nP e)
    (he0 : es[0]? = some e0) (hprim : V.ind e0.addr = some (some prim))
    (hself : ∀ ek d, es[k]? = some ek → V.ind ek.addr = some (some d) → d.ni = nI)
    (hfop : flatOwnParams V es = some fop)
    (build_all_minors : ∀ {xrc xflat xfop xelim r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors"
        [xrc, xflat, xfop, .field (nP : F), .field (es.length : F), .field (nP : F), xelim]
        h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList fieldListEnum RepNatField h fop xfop → RepKLevel h (elimLevel off) xelim →
      ∃ Ms, RepList kexprListEnum (TmOExact κ) h' Ms r ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    {xrc xpty xity xinl xelim xflat xfop r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_rec_type_from"
      [xrc, xpty, .field (prim.nl : F), xity, xinl, .field (nP : F), .field (nI : F), xelim,
        .field (off : F), xflat, xfop, .field (k : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hPT : TmOExact κ h prim.ty xpty)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (hfopr : RepList fieldListEnum RepNatField h fop xfop)
    (hel : RepKLevel h (elimLevel off) xelim) :
    Heap.Extends h h' ∧ ∃ R, TmOExact κ h' R r ∧
      Eventually fun f => recTypeAt V f es off nP k = some R := by
  have b : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelCheck::build_rec_type_from».obs ev with
  | .run (v1 := v1) (m2 := m2) (v32 := v32) (m33 := m33) (v85 := v85) (m96 := m96)
      (m131 := m131) (x_param_doms := xpd) (x_after_params := xap) (m70 := m70) (v159 := v159)
      (m160 := m160) (v205 := v205) (m206 := m206) (v275 := v275) (m276 := m276) (m298 := m298)
      (x_self_addr := xsa) (x_self_is_aux := xsaux) (x_self_spec_params := xsp)
      (x_self_occ_us := xsus) (m351 := m351) (p358 := p358) (x_self_ind_ty := xsty)
      (x_self_own_params := xsnp) (v424 := v424) (m425 := m425) (cs465 := cs465) (v454 := v454)
      (m455 := m455) (v532 := v532) (m555 := m555) (v515 := v515) (m516 := m516) (v589 := v589)
      (cs585 := cs585) (v574 := v574) (m575 := m575) (m621 := m621) (v651 := v651)
      (x659 := x659) (x667 := x667) (v687 := v687) (m688 := m688) (v703 := v703) (v704 := v704)
      (x742 := x742) (v775 := v775) (m776 := m776) (v812 := v812) (v829 := v829) (x837 := x837)
      (y838 := y838) (m865 := m865) (v887 := v887) (m888 := m888) (m925 := m925) (m949 := m949)
      (m969 := m969) (v1007 := v1007) (m1008 := m1008) (v1045 := v1045) (m1046 := m1046)
      (v1083 := v1083) (m1084 := m1084)
      (ev14 := ev14) (ev45 := ev45) (ev106 := ev106) (hm139 := hm139) (ev83 := ev83)
      (ev172 := ev172) (ev218 := ev218) (ev288 := ev288) (ev310 := ev310) (ev366 := ev366)
      (ld360 := ld360) (ev437 := ev437) (ev467 := ev467) (ev565 := ev565) (ev528 := ev528)
      (op611 := op611) (ev587 := ev587) (hm631 := hm631) (op682 := op682) (op674 := op674)
      (op666 := op666) (op734 := op734) (op757 := op757) (op749 := op749) (ev700 := ev700)
      (ev788 := ev788) (op827 := op827) (op852 := op852) (op861 := op861) (op844 := op844)
      (hm875 := hm875) (ev900 := ev900) (hm935 := hm935) (hm957 := hm957) (hm979 := hm979)
      (ev1020 := ev1020) (ev1058 := ev1058) (ev1096 := ev1096) (ev1126 := ev1126)
      (hc1151 := hc) .. =>
    -- the motive count
    have heslt : es.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd (c := ⟨Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>», [xflat], h⟩) (p := xflat)
        (by rw [hc]; simp) (by simp) hes
    obtain ⟨rfl, hm2⟩ := flat_length ev14 hes
    have hm2' := hm2.symm
    subst hm2'
    -- the parameters: the first type's telescope at the recursor's levels
    have x1 : Heap.Extends h m33 := ObsFn.heap_extends ev45
    have hpus := build_param_lvls_range_spec hoff ev45
    have x2 : Heap.Extends m33 m96 := ObsFn.heap_extends ev106
    have hPT1 := expr_inst_levels_tmOExact (b fun c hc' => by rw [hc]; simp [hc'])
      (hPT.mono x1) hpus ev106
    have x3 : Heap.Extends m96 m131 := by rw [hm139]; exact Heap.Extends.snoc _ _
    obtain ⟨-, xl, xa, Pd, A, he, hPd, -, hevP⟩ := collect_n_doms_whnf_spec hA hD hI hC hM nP
      (by omega) ev83 (b fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (hPT1.mono x3)
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨he1, he2⟩ := he
    subst he1 he2
    have x4 : Heap.Extends m131 m70 := ObsFn.heap_extends ev83
    have c70 : Heap.Extends h m70 := x1.trans (x2.trans (x3.trans x4))
    -- the motives and the minor premises
    obtain ⟨-, Mo, hMo, hevMo⟩ := build_all_motives_spec hA hD hI hC hM hK hnP (by omega) hres
      hind hfit ev172 (b fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (flatList_mono c70 hes) (hel.mono c70)
    have x5 : Heap.Extends m70 m160 := ObsFn.heap_extends ev172
    have c160 : Heap.Extends h m160 := c70.trans x5
    obtain ⟨Mi, hMi, hevMi⟩ := build_all_minors ev218 (b fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (flatList_mono c160 hes) (fieldList_mono c160 hfopr)
      (hel.mono c160)
    have x6 : Heap.Extends m160 m206 := ObsFn.heap_extends ev218
    have c206 : Heap.Extends h m206 := c160.trans x6
    have hMilt : Mi.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [v205], m206⟩) (p := v205)
        (by rw [hc]; simp) (by simp) hMi
    obtain ⟨rfl, hm276⟩ := kexpr_length ev288 hMi
    have hm276' := hm276.symm
    subst hm276'
    -- entry `k`
    obtain ⟨hm298, ek, hek, hekr⟩ := flat_member_at_spec es k hk (by omega) ev310
      (flatList_mono c206 hes)
    have hm298' := hm298.symm
    subst hm298'
    obtain ⟨a, rfl, ra, ha, hps, hls⟩ := FlatEntryRepExact.tuple_inv hekr
    have hekm : ek ∈ es := List.mem_of_getElem? hek
    obtain ⟨d, ba, hd, -, hnp, hni, -, -, -, hty, rfl, -⟩ :=
      (hI ra ev366 (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld360).1 _ _ _ _ _ _ _ _ rfl
    rw [ha] at hd
    obtain rfl := hself ek d hek hd
    have x7 : Heap.Extends m206 m351 := ObsFn.heap_extends ev366
    have hT1 := expr_inst_levels_tmOExact (b fun c hc' => by rw [hc]; simp [hc']) hty
      (hls.mono x7) ev437
    have x8 : Heap.Extends m351 m425 := ObsFn.heap_extends ev437
    have hPslt : ek.params.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbnd (c := ⟨"KernelCheck::peel_motive_params_subst",
        [v424, .field (d.np : F), .field (nP : F), auxVal ek.aux, xsp, .field 0], m425⟩)
        (p := xsp) (by rw [hc]; simp) (by simp) (tmOExactList_mono (x7.trans x8) hps)
    have ev467' : ObsFn W "KernelCheck::peel_motive_params_subst"
        [v424, .field (d.np : F), .field (nP : F), auxVal ek.aux, xsp, .field ((0 : Nat) : F)]
        m425 v454 m455 cs465 := by rw [Nat.cast_zero]; exact ev467
    obtain ⟨SA, hpeel, hSA⟩ := peel_motive_params_subst_spec (κ := κ) (by omega) (by omega)
      d.np 0 (by omega) (fun i _ hi hni => hfit ek hekm d hd i (by omega) hni) ev467'
      (b fun c hc' => by rw [hc]; simp [hc']) hT1 (tmOExactList_mono (x7.trans x8) hps)
    have x9 : Heap.Extends m425 m455 := ObsFn.heap_extends ev467
    -- its indices, under the motives and the minor premises
    have x10 : Heap.Extends m455 m555 := ObsFn.heap_extends ev565
    obtain ⟨-, Ix, hIx, hevIx⟩ := collect_index_doms_spec hA hD hI hC hM d.ni (by omega) ev528
      (b fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) (hSA.mono x10)
    have x11 : Heap.Extends m555 m516 := ObsFn.heap_extends ev528
    have hIxlen : Ix.length ≤ d.ni := by
      obtain ⟨a0, ha0⟩ := hevIx
      have h0 : (collectDoms V a0 d.ni SA).map Prod.fst = some Ix := ha0 a0 le_rfl
      cases hc0 : collectDoms V a0 d.ni SA with
      | none => rw [hc0] at h0; cases h0
      | some p =>
        rw [hc0] at h0
        simp only [Option.map_some, Option.some.injEq] at h0
        rw [← h0]
        exact collectDoms_length_le _ _ _ hc0
    obtain rfl := binop_add_nat op611
    have ev587' : ObsFn W "KernelCheck::list_lift_indices"
        [v515, .field ((es.length + Mi.length : Nat) : F), .field ((0 : Nat) : F)]
        m516 v574 m575 cs585 := by rw [Nat.cast_zero]; exact ev587
    have hLi : RepList kexprListEnum (TmOExact κ) m575
        (liftIndices Ix (es.length + Mi.length)) v574 :=
      list_lift_indices_spec (κ := κ) (shift := es.length + Mi.length) (by omega) Ix 0
        (by omega) ev587' (b fun c hc' => by rw [hc]; simp [hc']) hIx
    have x12 : Heap.Extends m516 m575 := ObsFn.heap_extends ev587
    -- the major premise
    have x13 : Heap.Extends m575 m621 := by rw [hm631]; exact Heap.Extends.snoc _ _
    have d621 : Heap.Extends m206 m621 :=
      x7.trans (x8.trans (x9.trans (x10.trans (x11.trans (x12.trans x13)))))
    have cConst : m621[m575.length]? = some (.construct kexprEnum "Const" [xsa, xsus]) := by
      rw [hm631]; simp
    have : Resolved (κ (ixAddr a)) := by rw [ha]; exact hres _ hekm
    have hhead : TmOExact κ m621 (.const (κ ek.addr) ek.levels)
        (.ptr (.enum "KernelTypes::KExprNode") m575.length) := by
      rw [← ha]
      exact ⟨0, .const cConst (Bytes.repAddressRef_heapMono₂ addrTy d621 ra)
        (hls.mono d621)⟩
    obtain rfl := binop_add_nat op682
    obtain rfl := binop_add_nat op674
    obtain rfl := binop_add_nat op666
    obtain rfl := binop_sub_one_nat (by omega) op734
    obtain rfl := binop_add_nat op757
    obtain rfl := binop_add_nat op749
    obtain ⟨-, hargs⟩ := build_major_args_for_self_spec (κ := κ) (root := root) (nrp := nP)
      (top := nP + es.length + Mi.length + d.ni - 1) (lift := es.length + Mi.length + d.ni)
      (aux := ek.aux)
      (Ps := ek.params) (by omega) (by omega) (by omega) (by omega) ev700
      (b fun c hc' => by rw [hc]; simp [hc']) (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hhead
      (tmOExactList_mono d621 hps)
    have x14 : Heap.Extends m621 m688 := ObsFn.heap_extends ev700
    have hmajor := build_major_indices_spec (κ := κ) (n := d.ni) (by omega) ev788 hargs
    have x15 : Heap.Extends m688 m776 := ObsFn.heap_extends ev788
    -- the result: the motive applied to the indices and the major premise
    obtain rfl := binop_add_one_nat op827
    obtain rfl := binop_sub_one_nat (by omega) op852
    obtain rfl := binop_add_nat op861
    obtain rfl := binop_sub_nat (by omega) op844
    have hpre : nP + es.length + Mi.length + d.ni + 1 - 1 - (nP + k) =
        nP + es.length + Mi.length + d.ni - (nP + k) := by omega
    rw [hpre] at hm875
    have x16 : Heap.Extends m776 m865 := by rw [hm875]; exact Heap.Extends.snoc _ _
    have hmv : TmOExact κ m865 (.bvar (nP + es.length + Mi.length + d.ni - (nP + k)))
        (.ptr (.enum kexprEnum) m776.length) := by
      rw [hm875]
      exact tmOExact_bvar_cell (by omega)
    have hci := apply_indices_in_conclusion_spec (κ := κ) (n := d.ni) (by omega) ev900 hmv
    have x17 : Heap.Extends m865 m888 := ObsFn.heap_extends ev900
    have x18 : Heap.Extends m888 m949 := by rw [hm957]; exact Heap.Extends.snoc _ _
    have x19 : Heap.Extends m949 m925 := by rw [hm935]; exact Heap.Extends.snoc _ _
    have hconcl : TmOExact κ m925
        (.app (conclIndices (.bvar (nP + es.length + Mi.length + d.ni - (nP + k))) d.ni)
          (.bvar 0))
        (.ptr (.enum kexprEnum) m949.length) := by
      have h0 := tmOExact_app_bvar (κ := κ) (b := 0) (by omega) hci
      rw [hm935, hm957]
      simpa using h0
    have x20 : Heap.Extends m925 m969 := by rw [hm979]; exact Heap.Extends.snoc _ _
    have d969 : Heap.Extends m621 m969 :=
      x14.trans (x15.trans (x16.trans (x17.trans (x18.trans (x19.trans x20)))))
    have d206 : Heap.Extends m206 m969 := d621.trans d969
    have c969 : Heap.Extends h m969 := c206.trans d206
    have cAll : m969[m925.length]? = some (.construct kexprEnum "Forall"
        [v775, .ptr (.enum "KernelTypes::KExprNode") m949.length, xelim]) := by
      rw [hm979]; simp
    obtain ⟨k₁, r₁⟩ := hmajor.mono (x16.trans (x17.trans (x18.trans (x19.trans x20))))
    obtain ⟨k₂, r₂⟩ := hconcl.mono x20
    have hwm : TmOExact κ m969
        (.forallE
          (appBVarsDown (if ek.aux then specParamsLifted (.const (κ ek.addr) ek.levels) ek.params
              (es.length + Mi.length + d.ni)
            else appBVarsDec (.const (κ ek.addr) ek.levels) nP
              (nP + es.length + Mi.length + d.ni - 1)) d.ni)
          (.app (conclIndices (.bvar (nP + es.length + Mi.length + d.ni - (nP + k))) d.ni)
            (.bvar 0))
          (bmeta (elimLevel off)))
        (.ptr (.enum "KernelTypes::KExprNode") m925.length) :=
      ⟨max k₁ k₂, .forallE cAll (tmExact_depth_le r₁ _ (Nat.le_max_left _ _))
        (tmExact_depth_le r₂ _ (by omega)) (hel.mono c969)⟩
    -- the binders: indices, minor premises, motives, parameters
    have h1 := wrap_foralls_spec (κ := κ) _ ev1020 hwm
      (tmOExactList_mono (x13.trans d969) hLi) (hel.mono c969)
    have x21 : Heap.Extends m969 m1008 := ObsFn.heap_extends ev1020
    have h2 := wrap_foralls_spec (κ := κ) Mi ev1058 h1
      (tmOExactList_mono (d206.trans x21) hMi)
      (hel.mono (c969.trans x21))
    have x22 : Heap.Extends m1008 m1046 := ObsFn.heap_extends ev1058
    have h3 := wrap_foralls_spec (κ := κ) Mo ev1096 h2
      (tmOExactList_mono (x6.trans (d206.trans (x21.trans x22))) hMo)
      (hel.mono (c969.trans (x21.trans x22)))
    have x23 : Heap.Extends m1046 m1084 := ObsFn.heap_extends ev1096
    have h4 := wrap_foralls_spec (κ := κ) Pd ev1126 h3
      (tmOExactList_mono (x5.trans (x6.trans (d206.trans (x21.trans (x22.trans x23))))) hPd)
      (hel.mono (c969.trans (x21.trans (x22.trans x23))))
    refine ⟨ObsFn.heap_extends ev, _, h4,
      (((hevP.and hevMo).and hevMi).and hevIx).mono fun f ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ => ?_⟩
    cases hcI : collectDoms V f d.ni SA with
    | none => rw [hcI] at e4; cases e4
    | some p =>
      obtain ⟨ds, rest⟩ := p
      rw [hcI] at e4
      simp only [Option.map_some, Option.some.injEq] at e4
      subst e4
      simp only [recTypeAt, he0, hek, hprim, hd, e1, e2, e3, hfop, hpeel, hcI, hK]

/-- **`KernelCheck::build_rec_type`** is `recTypeAt`: the recursor type at entry `k` of the family
`es`, at the elimination offset `off`, over `nP` parameters, from the reading of
`build_all_minors` (`allMinors`). The inductive type and level count the circuit is handed are
read only where the family's first entry is no inductive type, which `AllInd` excludes. -/
theorem build_rec_type_spec {V : ReconView} {root : List (Call F)}
    (hA : AddrOf κ V) (hD : DefnAnswers root κ V) (hI : IndAnswers root κ V)
    (hC : CtorOfAnswers root V) (hM : ModeledAnswers root V) (hK : ∀ a, V.key a = κ a)
    {es : List FlatEntry} {fop : List Nat} {off nP nI k : Nat}
    (hnP : nP < 4294967296) (hnI : nI < 4294967296) (hoff : off ≤ 1) (hk : k < es.length)
    (hres : ∀ e ∈ es, Resolved (κ e.addr)) (hind : AllInd V es)
    (hfit : ∀ e ∈ es, ParamsFit V nP e)
    (hself : ∀ ek d, es[k]? = some ek → V.ind ek.addr = some (some d) → d.ni = nI)
    (hfop : flatOwnParams V es = some fop)
    (build_all_minors : ∀ {xrc xflat xfop xelim r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      ObsFn W "KernelCheck::build_all_minors"
        [xrc, xflat, xfop, .field (nP : F), .field (es.length : F), .field (nP : F), xelim]
        h r h' cs →
      IxVM.Consistency.Bounded cs → (∀ c ∈ cs, c ∈ root) →
      RepList flatListEnum (FlatEntryRepExact κ) h es xflat →
      RepList fieldListEnum RepNatField h fop xfop → RepKLevel h (elimLevel off) xelim →
      ∃ Ms, RepList kexprListEnum (TmOExact κ) h' Ms r ∧
        Eventually fun f =>
          allMinors V f es fop nP es.length nP (elimLevel off) es 0 0 = some Ms)
    {xrc xity xinl xelim xflat xfop r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_rec_type"
      [xrc, xity, xinl, .field (nP : F), .field (nI : F), xelim, .field (off : F), xflat, xfop,
        .field (k : F)] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hroot : ∀ c ∈ cs, c ∈ root)
    (hes : RepList flatListEnum (FlatEntryRepExact κ) h es xflat)
    (hfopr : RepList fieldListEnum RepNatField h fop xfop)
    (hel : RepKLevel h (elimLevel off) xelim) :
    Heap.Extends h h' ∧ ∃ R, TmOExact κ h' R r ∧
      Eventually fun f => recTypeAt V f es off nP k = some R := by
  have b : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  have hext : Heap.Extends h h' := ObsFn.heap_extends ev
  match Obs.«KernelCheck::build_rec_type».obs ev with
  | .Induct (m2 := m2) (cs13 := cs13) (x_prim_addr := xpa) (x__pia := xpia) (x__pisp := xpisp)
      (x__piou := xpiou) (m58 := m58) (ev15 := ev15) (ev74 := ev74) (ld68 := ld68)
      (ev140 := ev140) (hc237 := hc) .. =>
    have ev15' : ObsFn W "KernelCheck::flat_member_at" [xflat, .field ((0 : Nat) : F)] h
        (.tuple [xpa, xpia, xpisp, xpiou]) m2 cs13 := by rw [Nat.cast_zero]; exact ev15
    obtain ⟨hm2, e0, he0, he0r⟩ := flat_member_at_spec es 0 (by omega) (by decide) ev15' hes
    have hm2' := hm2.symm
    subst hm2'
    obtain ⟨a, -, ra, ha, -, -⟩ := FlatEntryRepExact.tuple_inv he0r
    obtain ⟨d, ba, hd, hnl, -, -, -, -, rfl, hty, -⟩ :=
      (hI ra ev74 (hroot _ (by rw [hc]; simp))
        (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld68).1 _ _ _ _ _ _ _ _ rfl
    rw [ha] at hd
    have ext₁ : Heap.Extends h m58 := ObsFn.heap_extends ev74
    obtain ⟨-, R, hR, hev⟩ := build_rec_type_from_spec hA hD hI hC hM hK hnP hnI (by omega) hk hres
      hind hfit he0 hd hself hfop @build_all_minors ev140 (b fun c hc' => by rw [hc]; simp [hc'])
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) hty (flatList_mono ext₁ hes)
      (fieldList_mono ext₁ hfopr) (hel.mono ext₁)
    exact ⟨hext, R, hR, hev⟩
  | .other (m2 := m2) (cs13 := cs13) (x_prim_addr := xpa) (x__pia := xpia) (x__pisp := xpisp)
      (x__piou := xpiou) (ev15 := ev15) (ev74 := ev74) (ld68 := ld68)
      (hne238 := hne) (hc344 := hc) .. =>
    have ev15' : ObsFn W "KernelCheck::flat_member_at" [xflat, .field ((0 : Nat) : F)] h
        (.tuple [xpa, xpia, xpisp, xpiou]) m2 cs13 := by rw [Nat.cast_zero]; exact ev15
    obtain ⟨hm2, e0, he0, he0r⟩ := flat_member_at_spec es 0 (by omega) (by decide) ev15' hes
    have hm2' := hm2.symm
    subst hm2'
    obtain ⟨a, -, ra, ha, -, -⟩ := FlatEntryRepExact.tuple_inv he0r
    have hnone := (hI ra ev74 (hroot _ (by rw [hc]; simp))
      (fun c hc' => hroot c (by rw [hc]; simp [hc'])) ld68).2 hne
    rw [ha] at hnone
    obtain ⟨d, hd⟩ := hind e0 (List.mem_of_getElem? he0)
    rw [hd] at hnone
    cases hnone

end

end IxVM.Refinement.Binding.FamilyRecon
