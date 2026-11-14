import IxVMRefinement.Core.Steps.Whnf

/-! # Step lemmas of `KernelWhnf`: the normalizers without δ, the structural normalizer, and the
projection heads

`whnf_nd`, `whnf_nd_core` and `whnf_nd_with_spine` have the shape of `whnf`, `whnf_core` and
`whnf_with_spine` (the head normalizer without δ at definition heads); `whnf_struct_core` and
`whnf_struct_core_spine` the same shape again (β, ζ, projections and ι only). A projection head
normalizes its scrutinee (`Red.projArg`), takes `red_proj`'s step (`Red.proj`) and goes on with
the field applied to the spine, or leaves the projection of the normalized scrutinee applied to
the spine (`whnf_proj_head`, `whnf_nd_proj_head`), or the original projection
(`whnf_struct_core_proj`). Each lemma reads its callees' specs from the induction hypothesis. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option linter.unusedVariables false

/-! ## The normalizer without δ -/

/-- `KernelWhnf::whnf_nd_core` is `whnf_nd_with_spine` at the empty spine. -/
theorem whnf_nd_core_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_nd_core" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_nd_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨cs4, m26, hm34, ev6, hc45⟩ := Obs.«KernelWhnf::whnf_nd_core».obs ev
  subst hc45 hm34
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_nd_with_spine) (by lt_calls) ev6 rc e _ types
    rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) E
    [] (Tm.mono ext hE) (TmL.store_nil h)
  exact ⟨E', hE', hred⟩

/-- `KernelWhnf::whnf_nd`: a value form is its own normal form; any other term is
head-normalized under the context cut to its loose bound variables (`ctx_trim`). -/
theorem whnf_nd_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_nd" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_nd c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf_nd».obs ev with
    ⟨w20, ld12, he27, he28, hc29⟩ | ⟨w37, ld12, he44, he45, hc46⟩ |
    ⟨w54, w55, w56, ld12, he73, he74, hc75⟩ | ⟨w83, w84, w85, ld12, he102, he103, hc104⟩ |
    ⟨w112, ld12, he119, he120, hc121⟩ |
    ⟨v1, cs129, v134, m150, cs158, v162, m171, cs179, ld12, hne30, hne47, hne76, hne105, hne122,
      ev181, ev160, ev131, hc190⟩
  · subst he27 he28; exact ⟨E, hE, .refl⟩
  · subst he44 he45; exact ⟨E, hE, .refl⟩
  · subst he73 he74; exact ⟨E, hE, .refl⟩
  · subst he102 he103; exact ⟨E, hE, .refl⟩
  · subst he119 he120; exact ⟨E, hE, .refl⟩
  · subst hc190
    have g1 : Good c cs179 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs158 := good.sub fun x hx => by simp [hx]
    have g3 : Good c cs129 := good.sub fun x hx => by simp [hx]
    obtain ⟨hm171, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev181 e rfl g1
    subst m171
    have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev160 types v162 rfl g2 Γ d htypes
    have ext := ObsFn.heap_extends ev160
    exact ih.get (.whnf .whnf_nd_core) (by lt_calls) ev131 rc e v134 rfl g3 (RCRep.mono ext hrc)
      d Γ htr E (Tm.mono ext hE)

/-- `KernelWhnf::whnf_nd_with_spine`: as `whnf_with_spine`, with `whnf_nd_const_head` and
`whnf_nd_proj_head` at constant and projection heads. -/
theorem whnf_nd_with_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_nd_with_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_nd_with_spine c args h r h' calls := by
  intro rc hd sp types hargs good hrc d Γ htypes H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_nd_with_spine».obs ev with
    ⟨x_f, x_a, m31, cs42, x_ih, x_is, cs72, v77, m94, cs102, ld12, ev44, ev104, ev74, hc128⟩ |
    ⟨x_ty, x_body, w137, m154, cs165, x_reduct, x_rest, cs226, ld12, ev167, ev228, hc261⟩ |
    ⟨x_ty, x_body, w137, v153, m154, cs165, cs268, ld12, ev167, ev270, hc287⟩ |
    ⟨x_addr, x_lvls, cs308, ld12, ev310, hc359⟩ |
    ⟨w367, x_val, x_body, v383, m384, cs394, cs423, ld12, ev396, ev425, hc458⟩ |
    ⟨x_sa, x_fidx, x_inner, cs484, ld12, ev486, hc535⟩ |
    ⟨v1, cs543, ld12, hne130, hne288, hne360, hne459, hne536, ev545, hc562⟩
  · -- an application: collect its spine and go on with the appended spine
    subst hc128
    have e0 := ObsFn.heap_extends ev44
    have e1 := ObsFn.heap_extends ev104
    obtain ⟨ih', is', H', As', he, hH', hAs', rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev44 hd rfl
        (good.sub fun x hx => by simp [hx]) d Γ 0 H hH
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    have hcat := Lib.Lists.concat_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
      (R := TmE c.κ d Γ) tmE_heapMono₂ (xs := As') (ys := As)
      (by rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev104)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs')
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e0 hAs)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hcat
    have ext := e0.trans e1
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_nd_with_spine) (by lt_calls) ev74 rc _ v77 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      H' (As' ++ As) (Tm.mono e1 hH') hcat
    refine ⟨E', hE', ?_⟩
    rw [show Specs.Whnf.mkAppN (Ix.Kernel.Expr.mkAppN H' As') As = Specs.Whnf.mkAppN H' (As' ++ As)
      from mkAppN_mkAppN H' As' As]
    exact hred
  · -- a `λ` head that takes a β step
    subst hc261
    obtain ⟨E, Bs, hE, hBs, hred⟩ := ih.get (.whnf .red_beta) (by lt_calls) ev167 rc hd sp types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes H As hH hAs x_reduct x_rest rfl
    have ext := ObsFn.heap_extends ev167
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_nd_with_spine) (by lt_calls) ev228 rc x_reduct
      x_rest types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) E Bs hE hBs
    exact ⟨E', hE', .trans hred hred'⟩
  · -- a `λ` head that takes no step: stuck
    subst hc287
    have ext := ObsFn.heap_extends ev167
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev270 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As (Tm.mono ext hH) (tml_mono ext hAs)
    exact ⟨_, happ, .refl⟩
  · -- a constant head
    subst hc359
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld12
    exact ih.get (.whnf .whnf_nd_const_head) (by lt_calls) ev310 rc x_addr x_lvls hd sp types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hH hAs
  · -- a `let` head: its instantiation is its image
    subst hc458
    obtain ⟨T, V, B, rfl, hT, hV, hB⟩ := hH.letE_of_load ld12
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev396 x_body x_val 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B V (by simpa using hB) hV
    simp only [ZMod.val_zero] at hinst
    rw [← instShift_eq_instantiate1 (Tm.looseBVarsBounded hV)] at hinst
    have ext := ObsFn.heap_extends ev396
    exact ih.get (.whnf .whnf_nd_with_spine) (by lt_calls) ev425 rc v383 sp types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      (instShift V 0 B) As hinst (tml_mono ext hAs)
  · -- a projection head
    subst hc535
    obtain ⟨s, i, S, rfl, rfl, hs, hS⟩ := hH.proj_of_load ld12
    exact ih.get (.whnf .whnf_nd_proj_head) (by lt_calls) ev486 rc x_sa (.field i) x_inner sp types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes s i S As hs rfl hS hAs
  · -- any other head: stuck
    subst hc562
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev545 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As hH hAs
    exact ⟨_, happ, .refl⟩

/-! ## The structural normalizer -/

/-- `KernelWhnf::whnf_struct_core`: a value form is its own normal form; any other term goes to
`whnf_struct_core_spine` at the empty spine, under the context cut to its loose bound
variables. -/
theorem whnf_struct_core_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_struct_core" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_struct_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf_struct_core».obs ev with
    ⟨w20, ld12, he27, he28, hc29⟩ | ⟨w37, ld12, he44, he45, hc46⟩ |
    ⟨w54, w55, w56, ld12, he73, he74, hc75⟩ | ⟨w83, w84, w85, ld12, he102, he103, hc104⟩ |
    ⟨w112, ld12, he119, he120, hc121⟩ |
    ⟨v1, cs129, v135, m151, m164, cs172, v176, m185, cs193, ld12, hne30, hne47, hne76, hne105,
      hne122, hm159, ev195, ev174, ev131, hc204⟩
  · subst he27 he28; exact ⟨E, hE, .refl⟩
  · subst he44 he45; exact ⟨E, hE, .refl⟩
  · subst he73 he74; exact ⟨E, hE, .refl⟩
  · subst he102 he103; exact ⟨E, hE, .refl⟩
  · subst he119 he120; exact ⟨E, hE, .refl⟩
  · subst hc204 hm159
    have g1 : Good c cs193 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs172 := good.sub fun x hx => by simp [hx]
    have g3 : Good c cs129 := good.sub fun x hx => by simp [hx]
    have e0 : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
    obtain ⟨hm185, -⟩ := ih.get (.subst .expr_lbr) (by lt_calls) ev195 e rfl g1
    subst m185
    have htr := ih.get (.subst .ctx_trim) (by lt_calls) ev174 types v176 rfl g2 Γ d
      (types_mono e0 htypes)
    have e1 := ObsFn.heap_extends ev174
    have ext := e0.trans e1
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_struct_core_spine) (by lt_calls) ev131 rc e _
      v135 rfl g3 (RCRep.mono ext hrc) d Γ htr E [] (Tm.mono ext hE)
      (tml_mono e1 (TmL.store_nil h))
    exact ⟨E', hE', hred⟩

/-- `KernelWhnf::whnf_struct_core_spine`: an application's spine is collected and appended; a
`λ` head takes a β step (`red_beta`); a `let` head is replaced by its instantiation, which is
its image; a projection head goes to `whnf_struct_core_proj`, a constant head to
`whnf_struct_core_const`; any other head is stuck. -/
theorem whnf_struct_core_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_struct_core_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_struct_core_spine c args h r h' calls := by
  intro rc hd sp types hargs good hrc d Γ htypes H As hH hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_struct_core_spine».obs ev with
    ⟨w20, w21, m33, cs44, x_h, x_s, cs74, v79, m96, cs104, ld12, ev46, ev106, ev76, hc130⟩ |
    ⟨w139, w140, w141, m158, cs169, x_reduct, x_rest, cs230, ld12, ev171, ev232, hc265⟩ |
    ⟨w139, w140, w141, v157, m158, cs169, cs272, ld12, ev171, ev274, hc291⟩ |
    ⟨w299, x_val, x_body, cs318, v322, m333, cs341, ld12, ev343, ev320, hc381⟩ |
    ⟨x_sa, x_fidx, x_inner, cs407, ld12, ev409, hc466⟩ |
    ⟨x_addr, x_lvls, cs487, ld12, ev489, hc538⟩ |
    ⟨v1, cs546, ld12, hne132, hne292, hne382, hne467, hne539, ev548, hc565⟩
  · -- an application: collect its spine and go on with the appended spine
    subst hc130
    have e0 := ObsFn.heap_extends ev46
    have e1 := ObsFn.heap_extends ev106
    obtain ⟨ih', is', H', As', he, hH', hAs', rfl⟩ :=
      ih.get (.subst .collect_spine) (by lt_calls) ev46 hd rfl
        (good.sub fun x hx => by simp [hx]) d Γ 0 H hH
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    have hcat := Lib.Lists.concat_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
      (R := TmE c.κ d Γ) tmE_heapMono₂ (xs := As') (ys := As)
      (by rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev106)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hAs')
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e0 hAs)
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hcat
    have ext := e0.trans e1
    obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_struct_core_spine) (by lt_calls) ev76 rc _ v79
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) H' (As' ++ As) (Tm.mono e1 hH') hcat
    refine ⟨E', hE', ?_⟩
    rw [show Specs.Whnf.mkAppN (Ix.Kernel.Expr.mkAppN H' As') As = Specs.Whnf.mkAppN H' (As' ++ As)
      from mkAppN_mkAppN H' As' As]
    exact hred
  · -- a `λ` head that takes a β step
    subst hc265
    obtain ⟨E, Bs, hE, hBs, hred⟩ := ih.get (.whnf .red_beta) (by lt_calls) ev171 rc hd sp types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes H As hH hAs x_reduct x_rest rfl
    have ext := ObsFn.heap_extends ev171
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_struct_core_spine) (by lt_calls) ev232 rc
      x_reduct x_rest types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) E Bs hE hBs
    exact ⟨E', hE', .trans hred hred'⟩
  · -- a `λ` head that takes no step: stuck
    subst hc291
    have ext := ObsFn.heap_extends ev171
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev274 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As (Tm.mono ext hH) (tml_mono ext hAs)
    exact ⟨_, happ, .refl⟩
  · -- a `let` head: its instantiation is its image
    subst hc381
    obtain ⟨T, V, B, rfl, hT, hV, hB⟩ := hH.letE_of_load ld12
    have hinst := ih.get (.subst .expr_inst1) (by lt_calls) ev343 x_body x_val 0 rfl
      (good.sub fun x hx => by simp [hx]) d Γ B V (by simpa using hB) hV
    simp only [ZMod.val_zero] at hinst
    rw [← instShift_eq_instantiate1 (Tm.looseBVarsBounded hV)] at hinst
    have ext := ObsFn.heap_extends ev343
    exact ih.get (.whnf .whnf_struct_core_spine) (by lt_calls) ev320 rc v322 sp types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes)
      (instShift V 0 B) As hinst (tml_mono ext hAs)
  · -- a projection head
    subst hc466
    obtain ⟨s, i, S, rfl, rfl, hs, hS⟩ := hH.proj_of_load ld12
    exact ih.get (.whnf .whnf_struct_core_proj) (by lt_calls) ev409 rc x_sa (.field i) x_inner sp
      types hd rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes s i S As hs rfl hS hH hAs
  · -- a constant head
    subst hc538
    obtain ⟨a, us, rfl, ha, hus⟩ := hH.const_of_load ld12
    exact ih.get (.whnf .whnf_struct_core_const) (by lt_calls) ev489 rc x_addr x_lvls hd sp types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes a us As ha hus hH hAs
  · -- any other head: stuck
    subst hc565
    have happ := ih.get (.whnf .apply_spine) (by lt_calls) ev548 hd sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 H As hH hAs
    exact ⟨_, happ, .refl⟩

/-! ## Projection heads -/

/-- `KernelWhnf::whnf_struct_core_proj`: the scrutinee is normalized by `whnf_struct_core`
(`Red.projArg`); where `red_proj` takes its step (`Red.proj`) the field goes on with the spine;
otherwise the original projection, applied to the spine, is stuck. -/
theorem whnf_struct_core_proj_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_struct_core_proj" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_struct_core_proj c args h r h' calls := by
  intro rc sa fidx inner sp types orig hargs good hrc d Γ htypes s i S As hs hfidx hS horig hAs
  subst hargs hfidx
  rcases Obs.«KernelWhnf::whnf_struct_core_proj».obs ev with
    ⟨v1, m2, cs12, m40, cs51, x_field, cs115, ev14, ev53, ev117, hc150⟩ |
    ⟨v1, m2, cs12, v39, m40, cs51, cs157, ev14, ev53, ev159, hc176⟩
  · subst hc150
    obtain ⟨S', hS', hred⟩ := ih.get (.whnf .whnf_struct_core) (by lt_calls) ev14 rc inner types
      rfl (good.sub fun x hx => by simp [hx]) hrc d Γ htypes S hS
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨E, hE, hredp⟩ := ih.get (.whnf .red_proj) (by lt_calls) ev53 rc sa (.field i) v1 types
      rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) s i
      S' (Bytes.repAddressRef_heapMono₂ addrTy e0 hs) rfl hS' x_field rfl
    have ext := e0.trans (ObsFn.heap_extends ev53)
    obtain ⟨E', hE', hred'⟩ := ih.get (.whnf .whnf_struct_core_spine) (by lt_calls) ev117 rc
      x_field sp types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ
      (types_mono ext htypes) E As hE (tml_mono ext hAs)
    exact ⟨E', hE', .trans (red_mkAppN As (.trans (.projArg hred) hredp)) hred'⟩
  · subst hc176
    have ext := (ObsFn.heap_extends ev14).trans (ObsFn.heap_extends ev53)
    exact ⟨_, ih.get (.whnf .apply_spine) (by lt_calls) ev159 orig sp rfl
      (good.sub fun x hx => by simp [hx]) d Γ 0 _ As (Tm.mono ext horig) (tml_mono ext hAs),
      .refl⟩

/-- **A projection head, normalized by `norm`** (`whnf` or `whnf_nd`), its scrutinee then
expanded where it is a string literal (`str_lit_to_ctor_app_or_self`), then `red_proj`'s step and
`cont` (`whnf_with_spine` or `whnf_nd_with_spine`) on the field; otherwise the projection of the
normalized scrutinee, applied to the spine, is stuck. -/
theorem proj_head_step (c : Ctx) (norm cont : Specs.Whnf.Fn)
    (hnorm : norm.spec = Specs.Whnf.NormSpec) (hcont : cont.spec = Specs.Whnf.SpineSpec)
    {calls : List (Call F)} (ih : IH c calls) (good : Good c calls)
    {rc sa inner sp types : SourceValue F} {i : F} {h h' : Heap F} {r : SourceValue F}
    (path :
      (∃ (v1 : SourceValue F) (m2 : Heap F) (cs12 : List (Call F)) (v39 : SourceValue F)
          (m40 : Heap F) (cs50 : List (Call F)) (m78 : Heap F) (cs89 : List (Call F))
          (x_field : SourceValue F) (cs153 : List (Call F)),
        ObsFn W (Fn.whnf norm).name [rc, inner, types] h v1 m2 cs12 ∧
        ObsFn W "KernelNatPrim::str_lit_to_ctor_app_or_self" [rc, v1, types] m2 v39 m40 cs50 ∧
        ObsFn W "KernelWhnf::red_proj" [rc, sa, .field i, v39, types] m40
          (.tuple [(.field 1), x_field]) m78 cs89 ∧
        ObsFn W (Fn.whnf cont).name [rc, x_field, sp, types] m78 r h' cs153 ∧
        cs12.length < calls.length ∧ cs50.length < calls.length ∧ cs89.length < calls.length ∧
        cs153.length < calls.length ∧ (∀ x ∈ cs12, x ∈ calls) ∧ (∀ x ∈ cs50, x ∈ calls) ∧
        (∀ x ∈ cs89, x ∈ calls) ∧ (∀ x ∈ cs153, x ∈ calls)) ∨
      (∃ (v1 : SourceValue F) (m2 : Heap F) (cs12 : List (Call F)) (v39 : SourceValue F)
          (m40 : Heap F) (cs50 : List (Call F)) (v77 : SourceValue F) (m78 : Heap F)
          (cs89 : List (Call F)) (cs234 : List (Call F)),
        ObsFn W (Fn.whnf norm).name [rc, inner, types] h v1 m2 cs12 ∧
        ObsFn W "KernelNatPrim::str_lit_to_ctor_app_or_self" [rc, v1, types] m2 v39 m40 cs50 ∧
        ObsFn W "KernelWhnf::red_proj" [rc, sa, .field i, v39, types] m40 v77 m78 cs89 ∧
        ObsFn W "KernelWhnf::apply_spine"
          [(.ptr (.enum "KernelTypes::KExprNode") (m78).length), sp]
          (m78 ++ [(.construct "KernelTypes::KExprNode" "Proj" [sa, .field i, v1])]) r h' cs234 ∧
        cs12.length < calls.length ∧ cs50.length < calls.length ∧ cs234.length < calls.length ∧
        (∀ x ∈ cs12, x ∈ calls) ∧ (∀ x ∈ cs50, x ∈ calls) ∧ (∀ x ∈ cs234, x ∈ calls)))
    (hrc : c.rc h rc) {d : Nat} {Γ : Nat → KExpr} (htypes : c.types Γ h d types)
    {s : Bytes.Address} {S : KExpr} {As : List KExpr} (hs : RepAddr h s sa)
    (hS : c.tm d Γ h S inner) (hAs : c.tml d Γ h As sp) :
    ∃ E', c.tm d Γ h' E' r ∧
      Red c.env d (Specs.Whnf.mkAppN (.proj (c.κ (ixAddr s)) (ZMod.val i) S) As) E' := by
  rcases path with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_field, cs153, ev14, ev52, ev91, ev155, l1, l2, l3,
      l4, s1, s2, s3, s4⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, cs234, ev14, ev52, ev91, ev236, l1, l2, l3, s1,
      s2, s3⟩
  · have hn : Specs.Whnf.NormSpec c [rc, inner, types] h v1 m2 cs12 := by
      have := ih.get (.whnf norm) l1 ev14
      rwa [show (Fn.whnf norm).spec = Specs.Whnf.NormSpec from hnorm] at this
    obtain ⟨S1, hS1, hred1⟩ := hn rc inner types rfl (good.sub s1) hrc d Γ htypes S hS
    have e0 := ObsFn.heap_extends ev14
    obtain ⟨S2, hS2, hred2⟩ := ih.get (.nat .str_lit_to_ctor_app_or_self) l2 ev52 rc v1 types rfl
      (good.sub s2) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) S1 hS1
    have ext := e0.trans (ObsFn.heap_extends ev52)
    obtain ⟨E, hE, hredp⟩ := ih.get (.whnf .red_proj) l3 ev91 rc sa (.field i) v39 types rfl
      (good.sub s3) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) s i S2
      (Bytes.repAddressRef_heapMono₂ addrTy ext hs) rfl hS2 x_field rfl
    have ext' := ext.trans (ObsFn.heap_extends ev91)
    have hk : Specs.Whnf.SpineSpec c [rc, x_field, sp, types] m78 r h' cs153 := by
      have := ih.get (.whnf cont) l4 ev155
      rwa [show (Fn.whnf cont).spec = Specs.Whnf.SpineSpec from hcont] at this
    obtain ⟨E', hE', hred'⟩ := hk rc x_field sp types rfl (good.sub s4) (RCRep.mono ext' hrc) d Γ
      (types_mono ext' htypes) E As hE (tml_mono ext' hAs)
    exact ⟨E', hE', .trans (red_mkAppN As (.trans (.projArg (.trans hred1 hred2)) hredp)) hred'⟩
  · have hn : Specs.Whnf.NormSpec c [rc, inner, types] h v1 m2 cs12 := by
      have := ih.get (.whnf norm) l1 ev14
      rwa [show (Fn.whnf norm).spec = Specs.Whnf.NormSpec from hnorm] at this
    obtain ⟨S1, hS1, hred1⟩ := hn rc inner types rfl (good.sub s1) hrc d Γ htypes S hS
    have ext := (ObsFn.heap_extends ev14).trans
      ((ObsFn.heap_extends ev52).trans (ObsFn.heap_extends ev91))
    have e1 := (ObsFn.heap_extends ev52).trans (ObsFn.heap_extends ev91)
    have esn := Heap.Extends.snoc m78 (.construct kexprEnum "Proj" [sa, .field i, v1])
    have hcell : Tm c.κ d Γ (m78 ++ [.construct kexprEnum "Proj" [sa, .field i, v1]]) 0
        (.proj (c.κ (ixAddr s)) (ZMod.val i) S1) (.ptr (.enum kexprEnum) m78.length) :=
      .proj List.getElem?_concat_length (Bytes.repAddressRef_heapMono₂ addrTy (ext.trans esn) hs)
        (Tm.mono (e1.trans esn) hS1)
    exact ⟨_, ih.get (.whnf .apply_spine) l3 ev236 _ sp rfl (good.sub s3) d Γ 0 _ As hcell
      (tml_mono (ext.trans esn) hAs), red_mkAppN As (.projArg hred1)⟩

/-- `KernelWhnf::whnf_proj_head`: the scrutinee is normalized (`whnf`, `Red.projArg`) and
expanded where it is a string literal (`Red.strLit`); where `red_proj` takes its step
(`Red.proj`) the field goes on with the spine (`whnf_with_spine`); otherwise the projection of
the normalized scrutinee, applied to the spine, is stuck. -/
theorem whnf_proj_head_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_proj_head" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_proj_head c args h r h' calls := by
  intro rc sa fidx inner sp types hargs good hrc d Γ htypes s i S As hs hfidx hS hAs
  subst hargs hfidx
  refine proj_head_step c .whnf .whnf_with_spine rfl rfl ih good ?_ hrc htypes hs hS hAs
  rcases Obs.«KernelWhnf::whnf_proj_head».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_field, cs153, ev14, ev52, ev91, ev155, hc188⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, m193, cs234, ev14, ev52, ev91, hm203, ev236,
      hc253⟩
  · subst hc188
    exact .inl ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_field, cs153, ev14, ev52, ev91, ev155,
      by lt_calls, by lt_calls, by lt_calls, by lt_calls, fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  · subst hc253 hm203
    exact .inr ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, cs234, ev14, ev52, ev91, ev236,
      by lt_calls, by lt_calls, by lt_calls, fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx]⟩

/-- `KernelWhnf::whnf_nd_proj_head`: as `whnf_proj_head`, with `whnf_nd` and
`whnf_nd_with_spine`. -/
theorem whnf_nd_proj_head_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_nd_proj_head" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_nd_proj_head c args h r h' calls := by
  intro rc sa fidx inner sp types hargs good hrc d Γ htypes s i S As hs hfidx hS hAs
  subst hargs hfidx
  refine proj_head_step c .whnf_nd .whnf_nd_with_spine rfl rfl ih good ?_ hrc htypes hs hS hAs
  rcases Obs.«KernelWhnf::whnf_nd_proj_head».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_field, cs153, ev14, ev52, ev91, ev155, hc188⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, m193, cs234, ev14, ev52, ev91, hm203, ev236,
      hc253⟩
  · subst hc188
    exact .inl ⟨v1, m2, cs12, v39, m40, cs50, m78, cs89, x_field, cs153, ev14, ev52, ev91, ev155,
      by lt_calls, by lt_calls, by lt_calls, by lt_calls, fun x hx => by simp [hx],
      fun x hx => by simp [hx], fun x hx => by simp [hx], fun x hx => by simp [hx]⟩
  · subst hc253 hm203
    exact .inr ⟨v1, m2, cs12, v39, m40, cs50, v77, m78, cs89, cs234, ev14, ev52, ev91, ev236,
      by lt_calls, by lt_calls, by lt_calls, fun x hx => by simp [hx], fun x hx => by simp [hx],
      fun x hx => by simp [hx]⟩

end IxVM.Refinement.Core
