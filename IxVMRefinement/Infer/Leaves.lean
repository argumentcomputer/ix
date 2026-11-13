import IxVMRefinement.Infer.Basic
import IxVMRefinement.Nat.PrimStr
import IxVMRefinement.Nat.PrimNat

/-! # Step lemmas of the inference leaves and wrappers

The functions of `KernelInfer` and `KernelInferOnly` that read a context entry, a loaded
constant's head fields, a binder datum or a literal, and those that wrap one inference with a
head normalization, a conversion or a context cut:

* `types_lookup`, `io_types_lookup`: the type of an opened variable (`lookup_lift`);
* `const_num_lvls`, `const_type_of` and their infer-only twins: a loaded constant's level count
  and positional type (`CIRep.nl_of_eq`, `CIRep.ty_of_eq`);
* `forall_datum_ok`, `lam_datum_ok`: a binder's datum is the zero-ness the rule names
  (`pw_eq`'s answer `1`);
* `inst_subs`: the delayed substitution of a spine (`instantiateList`);
* `k_infer_lit`: a literal's type, the bound `Nat` or `String` role's constant (keyed by the role,
  `keyOf_of_addressOf`), with the literal support from the environment facts;
* `k_ensure_sort`, `ensure_sort_only`, `k_check`, `io_app_cod`, `k_infer_let_start`, `k_infer`,
  `k_infer_only`: one inference followed by `whnf`, `k_is_def_eq`, an instantiation or a context
  cut. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel.Rules (Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## Context lookups -/

/-- `KernelInfer::types_lookup`: the type of the opened variable `BVar i` stands for. -/
theorem types_lookup_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::types_lookup" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.types_lookup c args h r h' calls := by
  intro types i hargs good
  subst hargs
  obtain ⟨v1, m2, cs12, cs34, v38, ev14, op60, ev36, hc68⟩ := Obs.«KernelInfer::types_lookup».obs ev
  exact lookup_lift c ih good ev14 op60 ev36 hc68

/-- `KernelInferOnly::io_types_lookup`: as `types_lookup`. -/
theorem io_types_lookup_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_types_lookup" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_types_lookup c args h r h' calls := by
  intro types i hargs good
  subst hargs
  obtain ⟨v1, m2, cs12, cs34, v38, ev14, op60, ev36, hc68⟩ :=
    Obs.«KernelInferOnly::io_types_lookup».obs ev
  exact lookup_lift c ih good ev14 op60 ev36 hc68

/-! ## A loaded constant's level count and type -/

/-- `KernelInfer::const_num_lvls`: the first field, whatever the kind. -/
theorem const_num_lvls_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::const_num_lvls" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.const_num_lvls c args h r h' calls := by
  intro v ci hargs good hci
  subst hargs
  rcases Obs.«KernelInfer::const_num_lvls».obs ev with
    ⟨x_n, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals exact ⟨he.trans (hci.nl_of_eq hv), hh⟩

/-- `KernelInferOnly::io_const_num_lvls`: as `const_num_lvls`. -/
theorem io_const_num_lvls_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_const_num_lvls" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_const_num_lvls c args h r h' calls := by
  intro v ci hargs good hci
  subst hargs
  rcases Obs.«KernelInferOnly::io_const_num_lvls».obs ev with
    ⟨x_n, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals exact ⟨he.trans (hci.nl_of_eq hv), hh⟩

/-- `KernelInfer::const_type_of`: the second field, whatever the kind. -/
theorem const_type_of_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::const_type_of" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.const_type_of c args h r h' calls := by
  intro v ci hargs good hci
  subst hargs
  rcases Obs.«KernelInfer::const_type_of».obs ev with
    ⟨_, x_ty, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals (rw [he, hh]; exact ⟨hci.ty_of_eq hv, rfl⟩)

/-- `KernelInferOnly::io_const_type_of`: as `const_type_of`. -/
theorem io_const_type_of_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_const_type_of" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_const_type_of c args h r h' calls := by
  intro v ci hargs good hci
  subst hargs
  rcases Obs.«KernelInferOnly::io_const_type_of».obs ev with
    ⟨_, x_ty, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals (rw [he, hh]; exact ⟨hci.ty_of_eq hv, rfl⟩)

/-! ## Binder data -/

/-- `KernelInferOnly::forall_datum_ok`: `pw_eq(v, bl) = 1`, so the ∀'s datum is the zero-ness of
the body's sort. -/
theorem forall_datum_ok_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::forall_datum_ok" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.forall_datum_ok c args h r h' calls := by
  intro v bl hargs good u ℓ hu hℓ
  subst hargs
  obtain ⟨v12, m15, cs23, ev25, heq48, -, -, hc53⟩ := Obs.«KernelInferOnly::forall_datum_ok».obs ev
  subst hc53 heq48
  obtain ⟨la, hla, hle⟩ := hu
  obtain ⟨hr, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev25 v bl rfl
    (good.sub fun x hx => by simp [hx]) la ℓ hla hℓ
  exact (zeronessOf_congr hle).trans (zeroness_eq_of_one hr)

/-- `KernelInferOnly::lam_datum_ok`: at a `λ` body the two data agree (`pw_eq(bl, inner) = 1`);
otherwise the datum is the zero-ness of the io-grade sort of the body's type
(`ensure_sort_only`, then `pw_eq`). -/
theorem lam_datum_ok_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::lam_datum_ok" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.lam_datum_ok c args h r h' calls := by
  intro rc body bt bl types hargs good hrc d Γ htypes Bo Bt ℓ hBo hBt hℓ
  subst hargs
  rcases Obs.«KernelInferOnly::lam_datum_ok».obs ev with
    ⟨w20, w21, x_inner, v48, m51, cs59, ld12, ev61, heq84, -, -, hc89⟩ |
    ⟨v1, v105, m108, cs116, v119, m122, cs130, ld12, hne90, ev132, ev118, heq170, -, -, hc175⟩
  · subst hc89 heq84
    obtain ⟨T', B', ℓ', rfl, -, -, hℓ'⟩ := hBo.lam_of_load ld12
    obtain ⟨hr, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev61 bl x_inner rfl
      (good.sub fun x hx => by simp [hx]) ℓ ℓ' hℓ hℓ'
    exact .inl ⟨T', B', ℓ', rfl, zeroness_eq_of_one hr⟩
  · subst hc175 heq170
    obtain ⟨T, u, hinf, hred, la, hla, hle⟩ := ih.get (.infer .ensure_sort_only) (by lt_calls) ev132
      rc bt types rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes Bt hBt
    have e1 := ObsFn.heap_extends ev132
    obtain ⟨hr, -⟩ := ih.get (.levels .pw_eq) (by lt_calls) ev118 v119 bl rfl
      (good.sub fun x hx => by simp [hx]) la ℓ hla (hℓ.mono e1)
    exact .inr ⟨T, u, hinf, hred, (zeronessOf_congr hle).trans (zeroness_eq_of_one hr)⟩

/-! ## The delayed substitution of a spine -/

/-- `KernelInfer::inst_subs`: nothing to substitute, or `expr_inst_many` at `0`. -/
theorem inst_subs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::inst_subs" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.inst_subs c args h r h' calls := by
  intro e subs hargs good d Γ Ss B hSs hB
  subst hargs
  rcases Obs.«KernelInfer::inst_subs».obs ev with
    ⟨ld12, he21, he22, -⟩ | ⟨w31, w32, cs46, ld12, ev48, hc72⟩
  · obtain rfl := RepList.nil_of_load hSs ld12
    rw [he21, he22, Ix.Kernel.Expr.instantiateList_nil]
    exact hB
  · subst hc72
    have hB' : c.tmk d Γ (ZMod.val (0 : F) + Ss.length) h B e := by
      rw [ZMod.val_zero, Nat.zero_add]; exact hB
    have := ih.get (.subst .expr_inst_many) (by lt_calls) ev48 e subs 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B Ss hB' hSs
    rw [ZMod.val_zero] at this
    exact this

/-! ## Literals -/

/-- `KernelInfer::k_infer_lit`: the constant of the bound `Nat` role (`role_addr`) or `String`
role (`role_used_implicitly`) at no levels; `Infer.natLit`/`Infer.strLit` with the literal
support of the roles in force. -/
theorem k_infer_lit_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_lit" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_lit c args h r h' calls := by
  intro rc lit hargs good hrc l hl d Γ
  subst hargs
  rcases Obs.«KernelInfer::k_infer_lit».obs ev with
    ⟨w17, v31, m34, cs42, v46, m55, cs63, m67, hv15, he27, hm26, ev65, ev44, hm75, hc79⟩ |
    ⟨w87, v101, m104, cs112, v116, m125, cs133, m137, hne80, hv85, he97, hm96, ev135, ev114, hm145,
      hc149⟩
  · subst hc79
    obtain ⟨hv46, hm55⟩ := ih.get (.roles .role_nat) (by lt_calls) ev65 rfl
    rw [hv46, hm55] at ev44
    obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_addr) (by lt_calls) ev44 rc .nat rfl
      (good.sub fun x hx => by simp [hx]) hrc
    rcases hl with ⟨lp, n, hlit, -, rfl⟩ | ⟨bp, bytes, s, hlit, -, -, rfl⟩
    · rw [he27]
      exact ⟨_, PrimStrAux.tmc_role_const_nil hc ha hb hm75 hm26 d Γ,
        .natLit (PrimNat.natLit_of_natBlock hc hf (by decide) (by decide) (by decide))⟩
    · rw [hv15] at hlit
      injection hlit with _ h2
      exact absurd h2 (by decide)
  · subst hc149
    obtain ⟨hv116, hm125⟩ := ih.get (.roles .role_string) (by lt_calls) ev135 rfl
    rw [hv116, hm125] at ev114
    obtain ⟨a, ha, hb, hf⟩ := ih.get (.roles .role_used_implicitly) (by lt_calls) ev114 rc .string
      rfl (good.sub fun x hx => by simp [hx]) hrc
    rcases hl with ⟨lp, n, hlit, -, rfl⟩ | ⟨bp, bytes, s, hlit, -, -, rfl⟩
    · rw [hv85] at hlit
      injection hlit with _ h2
      exact absurd h2 (by decide)
    · rw [he97]
      exact ⟨_, PrimStrAux.tmc_role_const_nil hc ha hb hm145 hm96 d Γ, .strLit (hc.env.strLit hf)⟩

/-! ## One inference, then a normalization, a conversion or a cut -/

/-- `KernelInfer::k_ensure_sort`: `k_infer`, then `whnf` to a sort. -/
theorem k_ensure_sort_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_ensure_sort" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_ensure_sort c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨v1, m2, cs12, v39, m40, cs50, x_l, ev14, ev52, ld88, he102, he103, hc104⟩ :=
    Obs.«KernelInfer::k_ensure_sort».obs ev
  subst hc104
  obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer) (by lt_calls) ev14 rc e types rfl
    (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
  have e1 := ObsFn.heap_extends ev14
  obtain ⟨T', hT', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) T hT
  obtain ⟨u, rfl, hu⟩ := hT'.sort_of_load ld88
  rw [he102, he103]
  exact ⟨T, u, hinf, hred, hu⟩

/-- `KernelInferOnly::ensure_sort_only`: `k_infer_only`, then (unless it is already a sort)
`whnf` to a sort. -/
theorem ensure_sort_only_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::ensure_sort_only" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.ensure_sort_only c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelInferOnly::ensure_sort_only».obs ev with
    ⟨v1, m2, cs12, x_l, ev14, ld50, he64, he65, hc66⟩ |
    ⟨v1, m2, cs12, v39, v71, m72, cs82, x_l, ev14, ld50, hne67, ev84, ld120, he134, he135, hc136⟩
  · subst hc66
    obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc e types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
    obtain ⟨u, rfl, hu⟩ := hT.sort_of_load ld50
    rw [he64, he65]
    exact ⟨_, u, hinf, .refl, hu⟩
  · subst hc136
    obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc e types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨T', hT', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev84 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) T hT
    obtain ⟨u, rfl, hu⟩ := hT'.sort_of_load ld120
    rw [he134, he135]
    exact ⟨T, u, hinf, hred, hu⟩

/-- `KernelInfer::k_check`: `k_infer`, then `k_is_def_eq` against the expected type, asserted
`1`. -/
theorem k_check_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_check" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_check c args h r h' calls := by
  intro rc e x types hargs good hrc d Γ htypes E X hE hX
  subst hargs
  obtain ⟨v1, m2, cs12, v39, m40, cs50, ev14, ev52, heq111, -, -, hc116⟩ :=
    Obs.«KernelInfer::k_check».obs ev
  subst hc116 heq111
  obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer) (by lt_calls) ev14 rc e types rfl
    (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE
  have e1 := ObsFn.heap_extends ev14
  exact ⟨T, hinf, ih.get (.defEq .k_is_def_eq) (by lt_calls) ev52 rc v1 x types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) T X hT
    (Tm.mono e1 hX) field_one_ne_zero⟩

/-- `KernelInferOnly::io_app_cod`: the codomain instantiated by the argument (`expr_inst1` at
`0`); at a datum the never-zero test does not accept, the argument's io-grade type is
`k_is_def_eq` to the domain. -/
theorem io_app_cod_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::io_app_cod" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.io_app_cod c args h r h' calls := by
  intro rc dom cod bl a types hargs good hrc d Γ htypes D C ℓ A hD hC hℓ hA
  subst hargs
  have hC' : c.tmk d Γ (ZMod.val (0 : F) + 1) h C cod := by rw [ZMod.val_zero]; exact hC
  rcases Obs.«KernelInferOnly::io_app_cod».obs ev with
    ⟨m2, cs13, cs31, ev15, ev33, hc57⟩ |
    ⟨v1, m2, cs13, v73, m76, cs84, v88, m99, cs107, cs158, ev15, hne58, ev109, ev86, heq154, ev160,
      hc184⟩
  · subst hc57
    obtain ⟨hr, hm2⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev15 bl rfl ℓ hℓ
    rw [hm2] at ev33
    have hnz : ℓ.isNeverZero = true := by
      by_contra hn
      rw [ite_eq_right hn] at hr
      exact field_one_ne_zero hr
    have hi := ih.get (.subst .expr_inst1) (by lt_calls) ev33 cod a 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ C A hC' hA
    rw [ZMod.val_zero] at hi
    refine ⟨hi, .inl ?_⟩
    show ℓ.zeronessOf.isNever = true
    rw [← Ix.Kernel.Level.isNeverZero_eq_isNever]
    exact hnz
  · subst hc184 heq154
    obtain ⟨-, hm2⟩ := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev15 bl rfl ℓ hℓ
    rw [hm2] at ev109
    obtain ⟨TA, hTA, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev109 rc a types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A hA
    have e1 := ObsFn.heap_extends ev109
    have hdeq := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev86 rc v88 dom types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) TA D
      hTA (Tm.mono e1 hD) field_one_ne_zero
    have e2 := e1.trans (ObsFn.heap_extends ev86)
    have hi := ih.get (.subst .expr_inst1) (by lt_calls) ev160 cod a 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ C A (Tm.mono e2 hC') (Tm.mono e2 hA)
    rw [ZMod.val_zero] at hi
    exact ⟨hi, .inr ⟨TA, hinf, hdeq⟩⟩

/-- `KernelInfer::k_infer_let_start`: the type's sort and the value's type are checked
(`k_ensure_sort`, `k_check`, which no rule reads); the result is the type of the body instantiated
by the value, the image of the `let`. -/
theorem k_infer_let_start_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer_let_start" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_let_start c args h r h' calls := by
  intro rc ty val body types hargs good hrc d Γ htypes Ty V B hTy hV hB
  subst hargs
  obtain ⟨v1, m2, cs12, v39, m40, cs50, cs88, v92, m102, cs110, ev14, ev52, ev112, ev90, hc143⟩ :=
    Obs.«KernelInfer::k_infer_let_start».obs ev
  subst hc143
  have e1 := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev52)
  have hB' : c.tmk d Γ (ZMod.val (0 : F) + 1) m40 B body := by
    rw [ZMod.val_zero]; exact Tm.mono e1 hB
  have hi := ih.get (.subst .expr_inst1) (by lt_calls) ev112 body val 0 rfl
    (good.sub fun x hx => by simp [hx]) d Γ B V hB' (Tm.mono e1 hV)
  rw [ZMod.val_zero] at hi
  have e2 := e1.trans (ObsFn.heap_extends ev112)
  obtain ⟨T, hT, hinf⟩ := ih.get (.infer .k_infer) (by lt_calls) ev90 rc v92 types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ (types_mono e2 htypes)
    (B.instantiate1 V 0) hi
  refine ⟨T, hT, ?_⟩
  rw [instShift_eq_instantiate1 hV.looseBVarsBounded]
  exact hinf

/-- `KernelInfer::k_infer`: a term with no loose bound variable (`expr_lbr = 0`) is inferred under
the empty context list, which is a segment at the same depth; any other through
`k_infer_rebase`. -/
theorem k_infer_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::k_infer" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelInfer::k_infer».obs ev with
    ⟨m2, cs12, cs40, m61, ev14, hm69, ev42, hc73⟩ | ⟨v1, m2, cs12, cs81, ev14, hne74, ev83, hc116⟩
  · subst hc73
    obtain ⟨hm2, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev14 e rfl
      (good.sub fun x hx => by simp [hx])
    subst hm69
    rw [hm2] at ev42
    have ext := Heap.Extends.snoc h (.construct kexprListEnum "Nil" [])
    have hnil : c.types Γ (h ++ [.construct kexprListEnum "Nil" []]) d
        (.ptr (.enum kexprListEnum) h.length) :=
      ⟨.nil List.getElem?_concat_length, htypes.2⟩
    exact ih.get (.infer .k_infer_core) (by lt_calls) ev42 rc e _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ hnil E (Tm.mono ext hE)
  · subst hc116
    obtain ⟨hm2, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev14 e rfl
      (good.sub fun x hx => by simp [hx])
    rw [hm2] at ev83
    exact ih.get (.infer .k_infer_rebase) (by lt_calls) ev83 rc e types v1 rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes E hE

/-- `KernelInferOnly::k_infer_only`: the core under the context cut to the term's loose bound
variables (`ctx_trim`, a segment at the same depth). -/
theorem k_infer_only_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInferOnly::k_infer_only" args h r h' calls) (ih : IH c calls) :
    Specs.Infer.k_infer_only c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨cs4, v9, m25, cs33, v37, m46, cs54, ev56, ev35, ev6, hc65⟩ :=
    Obs.«KernelInferOnly::k_infer_only».obs ev
  subst hc65
  obtain ⟨hm46, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev56 e rfl
    (good.sub fun x hx => by simp [hx])
  rw [hm46] at ev35
  have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev35 types v37 rfl
    (good.sub fun x hx => by simp [hx]) Γ d htypes
  have e1 := ObsFn.heap_extends ev35
  exact ih.get (.infer .k_infer_only_core) (by lt_calls) ev6 rc e v9 rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ htr E (Tm.mono e1 hE)

end IxVM.Refinement.Core
