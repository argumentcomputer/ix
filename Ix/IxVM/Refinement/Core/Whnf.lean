import Ix.IxVM.Refinement.Core.Specs

/-! # The step lemmas of the whnf slice, and the induction

Spike S3. One lemma per function: from the induction hypothesis at strictly
fewer calls (`IH`) and an observed derivation of the function, its spec. Each
proof inverts the body (`ObsFn.function_inv`, then the `ObsExpr.*_inv`
lemmas: the part a generator can emit) and applies the callees' specs (the
part that is reasoning). `core_sound` is the induction: every observed
derivation of a function of the slice satisfies its spec. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List
open Ix.Kernel.Rules (Red)

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Lengths of concatenated call lists. -/
macro "lenlt" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_cons, List.length_nil]; omega))

/-- Membership in concatenated call lists. -/
macro "memsub" : tactic => `(tactic| (intro x hx; simp [hx]))

/-! ## `apply_spine` -/

theorem applySpine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::apply_spine" args h r h' calls) (ih : IH c calls) :
    ApplySpineSpec c args h r h' := by
  intro hd sp hargs d Γ H As hH hAs
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.apply_spine.lookup
    (by simp [IxVM.KernelWhnf.apply_spine, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.apply_spine] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `Nil => head`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨_, _⟩ <;> simp at hlen
    simp [matchListWith, pure, Except.pure] at hml
    subst hml
    simp only [kexprList_ctor] at hv
    subst hv
    have := RepList.nil_of_load hAs ld
    subst this
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact hH
  · -- `Cons(a, rest) => apply_spine(&App(head, a), rest)`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexprList_ctor] at hv
    subst hv
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld
    obtain ⟨vs, m, ca, cb, cargs, callee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at callee
    obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
    obtain ⟨sv, sm, d1', rfl, rfl⟩ := d1.store_inv
    obtain ⟨cvs, cargs', rfl⟩ := d1'.construct_inv
    obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs'.cons_inv
    obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
    simp at lu1
    subst lu1
    obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, cargs2, rfl⟩ := cargs1.cons_inv
    obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
    simp at lu2
    subst lu2
    obtain ⟨rfl, rfl, rfl⟩ := cargs2.nil_inv
    obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
    obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
    simp at l2
    subst l2
    obtain ⟨rfl, rfl, rfl⟩ := args2.nil_inv
    simp only [instanceName_plain_some, Value.type] at callee
    have spec := (ih _ _ _ _ _ _ (by lenlt) callee).applySpine rfl
    exact spec _ _ rfl d Γ (.app H A) As' (RepE.store_app hH hA)
      (RepSpine.mono (Heap.Extends.snoc _ _) hAs')

/-! ## `collect_spine` -/

theorem collect_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelTypes::collect_spine" args h r h' calls) (ih : IH c calls) :
    CollectSpec c args h r h' := by
  intro e hargs d Γ E hE
  subst hargs
  have body := ev.function_inv IxVM.KernelTypes.collect_spine.lookup
    (by simp [IxVM.KernelTypes.collect_spine, ControlLower.hasControl])
  simp only [IxVM.KernelTypes.collect_spine] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `App(f, a) => let (head, args) = collect_spine(f); (head, snoc(args, a))`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨te, rte, tte⟩ := hE
    obtain ⟨f, a, rfl, rf, ra⟩ := RepK.app_of_load rte ld
    obtain ⟨Ef, Ea, rfl, tf, ta⟩ := Tr.app_inv tte
    obtain ⟨lv, lm, lbs, lc1, lc2, dl, mt, dbody, rfl⟩ := darm.letValue_inv
    obtain ⟨vs, m, ca, cb, cargs, callee, rfl⟩ := dl.call_inv
    rw [instanceName_plain_some] at callee
    obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
    obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
    simp at l1
    subst l1
    obtain ⟨rfl, rfl, rfl⟩ := args1.nil_inv
    have extm := callee.heap_extends
    obtain ⟨hdp, sp, Hh, As, rfl, hHh, hAs, rfl⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) callee).collect rfl _ rfl d Γ Ef ⟨f, rf, tf⟩
    obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv mt
    rcases ys with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hl
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml
    subst ml
    obtain ⟨tvs, targs, rfl⟩ := dbody.tuple_inv
    obtain ⟨w1, ws1, k1, ka1, kb1, rfl, dw1, targs1, rfl⟩ := targs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, k2, ka2, kb2, rfl, dw2, targs2, rfl⟩ := targs1.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := targs2.nil_inv
    obtain ⟨svs, sk, ska, skb, sargs, scallee, rfl⟩ := dw2.call_inv
    rw [snoc_inst] at scallee
    obtain ⟨s1, ss1, sm1, sa1, sb1, rfl, ds1, sargs1, rfl⟩ := sargs.cons_inv
    obtain ⟨ls1, rfl, rfl⟩ := ds1.var_inv
    simp at ls1
    subst ls1
    obtain ⟨s2, ss2, sm2, sa2, sb2, rfl, ds2, sargs2, rfl⟩ := sargs1.cons_inv
    obtain ⟨ls2, rfl, rfl⟩ := ds2.var_inv
    simp at ls2
    subst ls2
    obtain ⟨rfl, rfl, rfl⟩ := sargs2.nil_inv
    have hEa := RepEk.mono extm (show RepE c.κ d Γ _ Ea y2 from ⟨a, ra, ta⟩)
    have hsn := hA.snoc _ _ _ _ _ _ scallee d Γ As Ea hAs hEa
    exact ⟨hdp, _, Hh, As ++ [Ea], rfl, RepEk.mono scallee.heap_extends hHh, hsn,
      (K.mkAppN_snoc Hh Ea As).symm⟩
  · -- `_ => (e, &Nil)`
    have := wild_bs hm
    subst this
    obtain ⟨tvs, targs, rfl⟩ := darm.tuple_inv
    obtain ⟨w1, ws1, k1, ka1, kb1, rfl, dw1, targs1, rfl⟩ := targs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, k2, ka2, kb2, rfl, dw2, targs2, rfl⟩ := targs1.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := targs2.nil_inv
    obtain ⟨sv, sm, d2', rfl, rfl⟩ := dw2.store_inv
    obtain ⟨cvs, cargs', rfl⟩ := d2'.construct_inv
    obtain ⟨rfl, rfl, rfl⟩ := cargs'.nil_inv
    simp only [kexprList_inst, Value.type]
    exact ⟨_, _, E, [], rfl, RepEk.mono (Heap.Extends.snoc _ _) hE, RepSpine.store_nil _, rfl⟩

/-! ## `expr_inst_levels` at an empty level list -/

theorem instLevels_step {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::expr_inst_levels" args h r h' calls) :
    InstLevelsSpec args h r h' := by
  intro e ps hargs hps
  subst hargs
  have body := ev.function_inv IxVM.KernelLevels.expr_inst_levels.lookup
    (by simp [IxVM.KernelLevels.expr_inst_levels, ControlLower.hasControl])
  simp only [IxVM.KernelLevels.expr_inst_levels] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  have hv0 : v0 = .construct klevelListEnum "Nil" [] := by
    cases hps with
    | nil cell =>
      rw [loadValue_enum_cell cell] at ld
      injection ld with hv
      exact hv.symm
  subst hv0
  rcases selectArm_construct_inv (by trivial) sel with ⟨vs, hv, hlen, hml, rfl⟩ | ⟨hmiss, _⟩
  · rcases vs with _ | ⟨_, _⟩ <;> simp at hlen
    simp [matchListWith, pure, Except.pure] at hml
    subst hml
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨rfl, rfl⟩
  · have := hmiss (α := Bool) (fun _ => true) false
    simp [klevelList_ctor] at this

/-! ## `whnf_core` and `whnf` -/

theorem whnfCore_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_core" args h r h' calls) (ih : IH c calls) :
    WhnfSpec c args h r h' calls := by
  intro rc e types hargs good d Γ E hE
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.whnf_core.lookup
    (by simp [IxVM.KernelWhnf.whnf_core, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.whnf_core] at body
  obtain ⟨vs, m, ca, cb, cargs, callee, rfl⟩ := body.call_inv
  rw [instanceName_plain_some] at callee
  obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
  obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
  simp at l1
  subst l1
  obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
  obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
  simp at l2
  subst l2
  obtain ⟨v3, vs3, m3, ca3, cb3, rfl, d3, args3, rfl⟩ := args2.cons_inv
  obtain ⟨sv, sm, d3', rfl, rfl⟩ := d3.store_inv
  obtain ⟨cvs, ccargs, rfl⟩ := d3'.construct_inv
  obtain ⟨rfl, rfl, rfl⟩ := ccargs.nil_inv
  obtain ⟨v4, vs4, m4, ca4, cb4, rfl, d4, args4, rfl⟩ := args3.cons_inv
  obtain ⟨l4, rfl, rfl⟩ := d4.var_inv
  simp at l4
  subst l4
  obtain ⟨rfl, rfl, rfl⟩ := args4.nil_inv
  simp only [kexprList_inst, Value.type] at callee
  have spec := (ih _ _ _ _ _ _ (by lenlt) callee).withSpine rfl
  exact spec _ _ _ _ rfl (good.sub (by memsub) (by lenlt)) d Γ E []
    (RepEk.mono (Heap.Extends.snoc _ _) hE) (RepSpine.store_nil _)

theorem whnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" args h r h' calls) (ih : IH c calls) :
    WhnfSpec c args h r h' calls := by
  intro rc e types hargs good d Γ E hE
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.whnf.lookup
    (by simp [IxVM.KernelWhnf.whnf, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.whnf] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 1) hm
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨E, hE, .refl⟩
  · obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 1) hm
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨E, hE, .refl⟩
  · obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 2) hm
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨E, hE, .refl⟩
  · obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 2) hm
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨E, hE, .refl⟩
  · obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 1) hm
    obtain ⟨l1, rfl, rfl⟩ := darm.var_inv
    simp at l1
    subst l1
    exact ⟨E, hE, .refl⟩
  · have := wild_bs hm
    subst this
    obtain ⟨vs, m, ca, cb, cargs, callee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at callee
    obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
    obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
    simp at l1
    subst l1
    obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
    obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
    simp at l2
    subst l2
    obtain ⟨v3, vs3, m3, ca3, cb3, rfl, d3, args3, rfl⟩ := args2.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := args3.nil_inv
    have spec := (ih _ _ _ _ _ _ (by lenlt) callee).whnfCore rfl
    exact spec _ _ _ rfl (good.sub (by memsub) (by lenlt)) d Γ E
      (RepEk.mono d3.heap_extends hE)

/-! ## `whnf_with_spine` -/

theorem withSpine_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_with_spine" args h r h' calls) (ih : IH c calls) :
    WithSpineSpec c args h r h' calls := by
  intro rc hd sp types hargs good d Γ H As hH hAs
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.whnf_with_spine.lookup
    (by simp [IxVM.KernelWhnf.whnf_with_spine, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.whnf_with_spine] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `App(f, a) => match collect_spine(head) { (ih, is) => whnf_with_spine(rc, ih, concat(is, spine), types) }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    obtain ⟨iv, im, ibs, iarm, ic1, ic2, iscr, isel, iarmd, rfl⟩ := darm.matchValue_inv
    obtain ⟨cvs, cm, cca, ccb, ccargs, ccallee, rfl⟩ := iscr.call_inv
    rw [instanceName_plain_some] at ccallee
    obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := ccargs.cons_inv
    obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
    simp at lu1
    subst lu1
    obtain ⟨rfl, rfl, rfl⟩ := cargs1.nil_inv
    have extc := ccallee.heap_extends
    obtain ⟨hdp, sp0, Hh, Is, rfl, hHh, hIs, rfl⟩ :=
      (ih _ _ _ _ _ _ (by lenlt) ccallee).collect rfl _ rfl d Γ H hH
    obtain ⟨ipat, ihmem, ihm⟩ := selectArm_mem isel
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at ihmem
    obtain ⟨rfl, rfl⟩ := ihmem
    obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv ihm
    rcases ys with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hl
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml
    subst ml
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := iarmd.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
    obtain ⟨kvs, km, kca, kcb, kargs, kcallee, rfl⟩ := dw3.call_inv
    rw [concat_inst] at kcallee
    obtain ⟨k1, ks1, km1, kk1, kl1, rfl, dk1, kargs1, rfl⟩ := kargs.cons_inv
    obtain ⟨lk1, rfl, rfl⟩ := dk1.var_inv
    simp at lk1
    subst lk1
    obtain ⟨k2, ks2, km2, kk2, kl2, rfl, dk2, kargs2, rfl⟩ := kargs1.cons_inv
    obtain ⟨lk2, rfl, rfl⟩ := dk2.var_inv
    simp at lk2
    subst lk2
    obtain ⟨rfl, rfl, rfl⟩ := kargs2.nil_inv
    have hcat := hA.concat _ _ _ _ _ _ kcallee d Γ Is As hIs (RepSpine.mono extc hAs)
    have extk := kcallee.heap_extends
    obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
    obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
    simp at lw4
    subst lw4
    obtain ⟨rfl, rfl, rfl⟩ := wargs4.nil_inv
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) wcallee).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ Hh (Is ++ As) (RepEk.mono extk hHh) hcat
    refine ⟨E', hE', ?_⟩
    rw [← K.mkAppN_append]
    exact hred
  · -- `Lam(ty, body) => whnf_apply_beta(rc, spine, head, types)`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
    obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
    simp at lw3
    subst lw3
    obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
    obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
    simp at lw4
    subst lw4
    obtain ⟨rfl, rfl, rfl⟩ := wargs4.nil_inv
    exact (ih _ _ _ _ _ _ (by lenlt) wcallee).applyBeta rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ H As hH hAs
  · -- `Const(addr, lvls) => whnf_const_head(rc, addr, lvls, head, spine, types)`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨a, ls, rfl, ha, hls⟩ := RepK.const_of_load rt ld
    obtain ⟨rfl, rfl⟩ := Tr.const_inv tt
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
    obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
    simp at lw3
    subst lw3
    obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
    obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
    simp at lw4
    subst lw4
    obtain ⟨w5, ws5, wm5, wa5, wb5, rfl, dw5, wargs5, rfl⟩ := wargs4.cons_inv
    obtain ⟨lw5, rfl, rfl⟩ := dw5.var_inv
    simp at lw5
    subst lw5
    obtain ⟨w6, ws6, wm6, wa6, wb6, rfl, dw6, wargs6, rfl⟩ := wargs5.cons_inv
    obtain ⟨lw6, rfl, rfl⟩ := dw6.var_inv
    simp at lw6
    subst lw6
    obtain ⟨rfl, rfl, rfl⟩ := wargs6.nil_inv
    exact (ih _ _ _ _ _ _ (by lenlt) wcallee).constHead rfl _ _ _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ a As ha hls ⟨_, rt, .const⟩ hAs
  · -- `Let` has no image
    obtain ⟨vs, hv, _, _⟩ := matchPattern_construct_inv hm
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨_, _, _, rfl⟩ := RepK.let_of_load rt ld
    exact (Tr.let_inv tt).elim
  · -- `Proj` has no image
    obtain ⟨vs, hv, _, _⟩ := matchPattern_construct_inv hm
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨t, rt, tt⟩ := hH
    obtain ⟨_, _, _, rfl⟩ := RepK.proj_of_load rt ld
    exact (Tr.proj_inv tt).elim
  · -- `_ => apply_spine(head, spine)`
    have := wild_bs hm
    subst this
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨rfl, rfl, rfl⟩ := wargs2.nil_inv
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) wcallee).applySpine rfl _ _ rfl d Γ H As hH hAs, .refl⟩

/-! ## `peel_beta` -/

theorem peel_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta" args h r h' calls) (ih : IH c calls) :
    PeelSpec c args h r h' calls := by
  intro lam sp acc hargs d Γ k L As Cs hL hAs hCs
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.peel_beta.lookup
    (by simp [IxVM.KernelWhnf.peel_beta, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.peel_beta] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `Lam(_, body) => match *spine { … }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
      Except.pure] at hml
    subst hml
    simp only [kexpr_ctor] at hv
    subst hv
    have hL0 := hL
    obtain ⟨t, rt, tt⟩ := hL
    obtain ⟨ty, b, rfl, rty, rb⟩ := RepK.lam_of_load rt ld
    obtain ⟨T, B, rfl, tty, tb⟩ := Tr.lam_inv tt
    obtain ⟨iv, im, ibs, iarm, ic1, ic2, iscr, isel, iarmd, rfl⟩ := darm.matchValue_inv
    obtain ⟨ip, idp, ild⟩ := iscr.load_inv
    obtain ⟨il, rfl, rfl⟩ := idp.var_inv
    simp at il
    subst il
    obtain ⟨ipat, ihmem, ihm⟩ := selectArm_mem isel
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at ihmem
    rcases ihmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `Cons(a, rest) => peel_beta(body, rest, &Cons(a, acc))`
      obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv ihm
      rcases vs with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
      simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
      subst hml
      simp only [kexprList_ctor] at hv
      subst hv
      obtain ⟨A, As', rfl, hA1, hAs'⟩ := RepList.cons_of_load hAs ild
      obtain ⟨cvs, cm, cca, ccb, cargs, callee, rfl⟩ := iarmd.call_inv
      rw [instanceName_plain_some] at callee
      obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
      obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
      simp at l1
      subst l1
      obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
      obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
      simp at l2
      subst l2
      obtain ⟨v3, vs3, m3, ca3, cb3, rfl, d3, args3, rfl⟩ := args2.cons_inv
      obtain ⟨sv, sm, d3', rfl, rfl⟩ := d3.store_inv
      obtain ⟨svs, sargs, rfl⟩ := d3'.construct_inv
      obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, sargs1, rfl⟩ := sargs.cons_inv
      obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
      simp at lu1
      subst lu1
      obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, sargs2, rfl⟩ := sargs1.cons_inv
      obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
      simp at lu2
      subst lu2
      obtain ⟨rfl, rfl, rfl⟩ := sargs2.nil_inv
      obtain ⟨rfl, rfl, rfl⟩ := args3.nil_inv
      simp only [kexprList_inst, Value.type] at callee
      obtain ⟨deep, cons, rest, Ts, D, rfl, rfl, hlenA, hlenC, hD, hcons, hrest⟩ :=
        (ih _ _ _ _ _ _ (by lenlt) callee).peel rfl _ _ _ rfl d Γ (k + 1) B As' (A :: Cs)
          (RepEk.mono (Heap.Extends.snoc _ _) ⟨b, rb, tb⟩)
          (RepSpine.mono (Heap.Extends.snoc _ _) hAs')
          (.cons (by simp) (RepEk.mono (Heap.Extends.snoc _ _) hA1)
            (RepSpine.mono (Heap.Extends.snoc _ _) hCs))
      refine ⟨deep, cons, rest, T :: Ts, D, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons, List.length_append, List.length_nil]; omega
      · have hk : k + (T :: Ts).length = k + 1 + Ts.length := by simp; omega
        rw [hk]; exact hD
      · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
      · simpa [List.drop_succ_cons] using hrest
    · -- `Nil => (lam, acc, spine)`
      obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv ihm
      rcases vs with _ | ⟨_, _⟩ <;> simp at hlen
      simp [matchListWith, pure, Except.pure] at hml
      subst hml
      obtain ⟨tvs, targs, rfl⟩ := iarmd.tuple_inv
      obtain ⟨w1, ws1, k1, ka1, kb1, rfl, dw1, targs1, rfl⟩ := targs.cons_inv
      obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
      simp at lw1
      subst lw1
      obtain ⟨w2, ws2, k2, ka2, kb2, rfl, dw2, targs2, rfl⟩ := targs1.cons_inv
      obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
      simp at lw2
      subst lw2
      obtain ⟨w3, ws3, k3, ka3, kb3, rfl, dw3, targs3, rfl⟩ := targs2.cons_inv
      obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
      simp at lw3
      subst lw3
      obtain ⟨rfl, rfl, rfl⟩ := targs3.nil_inv
      exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL0, by simpa using hCs,
        by simpa using hAs⟩
  · -- `_ => (lam, acc, spine)`
    have := wild_bs hm
    subst this
    obtain ⟨tvs, targs, rfl⟩ := darm.tuple_inv
    obtain ⟨w1, ws1, k1, ka1, kb1, rfl, dw1, targs1, rfl⟩ := targs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, k2, ka2, kb2, rfl, dw2, targs2, rfl⟩ := targs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, k3, ka3, kb3, rfl, dw3, targs3, rfl⟩ := targs2.cons_inv
    obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
    simp at lw3
    subst lw3
    obtain ⟨rfl, rfl, rfl⟩ := targs3.nil_inv
    exact ⟨_, _, _, [], _, rfl, rfl, by simp, by simp, by simpa using hL, by simpa using hCs,
      by simpa using hAs⟩

/-! ## `whnf_apply_beta` -/

theorem field_lit_eq {n m : Nat} {x : F} (hn : n < 4294967296) (hm : m < 4294967296)
    (h1 : ((n : F)) = x) (h2 : x = (m : F)) : n = m :=
  natCast_lt_inj hn hm (h1.trans h2)

theorem applyBeta_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_apply_beta" args h r h' calls) (ih : IH c calls) :
    ApplyBetaSpec c args h r h' calls := by
  intro rc sp lam types hargs good d Γ L As hL hAs
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.whnf_apply_beta.lookup
    (by simp [IxVM.KernelWhnf.whnf_apply_beta, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.whnf_apply_beta] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  -- the scrutinee: `peel_beta(lam, spine, &Nil)`
  obtain ⟨pvs, pm, pca, pcb, pargs, pcallee, rfl⟩ := dscr.call_inv
  rw [instanceName_plain_some] at pcallee
  obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := pargs.cons_inv
  obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
  simp at l1
  subst l1
  obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
  obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
  simp at l2
  subst l2
  obtain ⟨v3, vs3, m3, ca3, cb3, rfl, d3, args3, rfl⟩ := args2.cons_inv
  obtain ⟨sv, sm, d3', rfl, rfl⟩ := d3.store_inv
  obtain ⟨cvs, ccargs, rfl⟩ := d3'.construct_inv
  obtain ⟨rfl, rfl, rfl⟩ := ccargs.nil_inv
  obtain ⟨rfl, rfl, rfl⟩ := args3.nil_inv
  simp only [kexprList_inst, Value.type] at pcallee
  have hpeel := (ih _ _ _ _ _ _ (by lenlt) pcallee).peel rfl _ _ _ rfl d Γ 0 L As []
    (RepEk.mono (Heap.Extends.snoc _ _) hL) (RepSpine.mono (Heap.Extends.snoc _ _) hAs)
    (RepSpine.store_nil _)
  obtain ⟨deep, cons, rest, Ts, D, rfl, rfl, hlenA, hlenC, hD, hcons, hrest⟩ := hpeel
  have extp := pcallee.heap_extends
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv hm
  rcases ys with _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hl
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml
  subst ml
  -- `match Lists::length(consumed) { 0 => …, 1 => …, _ => … }`
  obtain ⟨lv, lm, lbs, larm, lc1, lc2, lscr, lsel, larmd, rfl⟩ := darm.matchValue_inv
  obtain ⟨gvs, gm, gca, gcb, gargs, gcallee, rfl⟩ := lscr.call_inv
  rw [length_inst] at gcallee
  obtain ⟨g1, gs1, gm1, ga1, gb1, rfl, dg1, gargs1, rfl⟩ := gargs.cons_inv
  obtain ⟨lg1, rfl, rfl⟩ := dg1.var_inv
  simp at lg1
  subst lg1
  obtain ⟨rfl, rfl, rfl⟩ := gargs1.nil_inv
  have hlv := hA.length _ _ _ _ _ gcallee d Γ _ hcons
  have hclen : ((As.take Ts.length).reverse ++ []).length = Ts.length := by
    simp; omega
  rw [hclen] at hlv
  subst hlv
  have extg := gcallee.heap_extends
  obtain ⟨lpat, lmem, lm'⟩ := selectArm_mem lsel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at lmem
  rcases lmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `0 => apply_spine(lam, spine)`
    obtain ⟨_, rfl⟩ := literal_bs lm'
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := larmd.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨rfl, rfl, rfl⟩ := wargs2.nil_inv
    have ext := (Heap.Extends.snoc _ _).trans (extp.trans extg)
    exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) wcallee).applySpine rfl _ _ rfl d Γ _ As
      (RepEk.mono ext hL) (RepSpine.mono ext hAs), .refl⟩
  · -- `1 => whnf_with_spine(rc, expr_inst1(deep, lookup(consumed, 0), 0), rest, types)`
    obtain ⟨hlit, rfl⟩ := literal_bs lm'
    have hlt := good.2.2.2
    have hn1 : Ts.length < 4294967296 := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      omega
    have hn : Ts.length = 1 := by
      injection hlit with hlit
      exact field_lit_eq (m := 1) hn1 (by omega) hlit (by decide)
    obtain ⟨T1, rfl⟩ : ∃ T1, Ts = [T1] := by
      rcases Ts with _ | ⟨T1, _ | ⟨_, _⟩⟩
      · simp at hn
      · exact ⟨T1, rfl⟩
      · simp at hn
    obtain ⟨A1, As'', rfl⟩ : ∃ A1 As'', As = A1 :: As'' := by
      rcases As with _ | ⟨A1, As''⟩
      · simp at hlenA
      · exact ⟨A1, As'', rfl⟩
    obtain ⟨bv, bm, bbs, bc1, bc2, dbv, mbv, dbody, rfl⟩ := larmd.letValue_inv
    obtain ⟨ivs, imm, ica, icb, iargs, icallee, rfl⟩ := dbv.call_inv
    rw [instanceName_plain_some] at icallee
    obtain ⟨i1, is1, im1, ia1, ib1, rfl, di1, iargs1, rfl⟩ := iargs.cons_inv
    obtain ⟨li1, rfl, rfl⟩ := di1.var_inv
    simp at li1
    subst li1
    obtain ⟨i2, is2, im2, ia2, ib2, rfl, di2, iargs2, rfl⟩ := iargs1.cons_inv
    obtain ⟨kvs, km, kca, kcb, kargs, kcallee, rfl⟩ := di2.call_inv
    rw [lookup_inst] at kcallee
    obtain ⟨k1, ks1, km1, kk1, kl1, rfl, dk1, kargs1, rfl⟩ := kargs.cons_inv
    obtain ⟨lk1, rfl, rfl⟩ := dk1.var_inv
    simp at lk1
    subst lk1
    obtain ⟨k2, ks2, km2, kk2, kl2, rfl, dk2, kargs2, rfl⟩ := kargs1.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := dk2.literal_inv
    obtain ⟨rfl, rfl, rfl⟩ := kargs2.nil_inv
    have hcons1 := hcons
    simp at hcons1
    have hA1 := hA.lookup0 _ _ _ _ _ kcallee d Γ A1 [] (RepSpine.mono extg hcons1)
    obtain ⟨i3, is3, im3, ia3, ib3, rfl, di3, iargs3, rfl⟩ := iargs2.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := di3.literal_inv
    obtain ⟨rfl, rfl, rfl⟩ := iargs3.nil_inv
    have extk := kcallee.heap_extends
    have hD1 := hD
    simp at hD1
    have hbody := hA.inst1 _ _ _ _ _ _ icallee d Γ D A1 (RepEk.mono (extg.trans extk) hD1) hA1
    rw [matchPattern_bind] at mbv
    simp only [Except.ok.injEq, Option.some.injEq] at mbv
    subst mbv
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := dbody.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
    obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
    simp at lw3
    subst lw3
    obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
    obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
    simp at lw4
    subst lw4
    obtain ⟨rfl, rfl, rfl⟩ := wargs4.nil_inv
    have hrest1 := hrest
    simp at hrest1
    have exti := icallee.heap_extends
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) wcallee).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ _ As'' hbody
      (RepSpine.mono (extg.trans (extk.trans exti)) hrest1)
    refine ⟨E', hE', ?_⟩
    show Red c.env d (K.mkAppN (.app (.lam T1 D nb) A1) As'') E'
    exact .trans (K.red_mkAppN As'' (.betaGate nb_isNever)) hred
  · -- `_ => whnf_with_spine(rc, expr_inst_many(deep, consumed, 0), rest, types)`
    have := wild_bs lm'
    subst this
    obtain ⟨bv, bm, bbs, bc1, bc2, dbv, mbv, dbody, rfl⟩ := larmd.letValue_inv
    obtain ⟨ivs, imm, ica, icb, iargs, icallee, rfl⟩ := dbv.call_inv
    rw [instanceName_plain_some] at icallee
    obtain ⟨i1, is1, im1, ia1, ib1, rfl, di1, iargs1, rfl⟩ := iargs.cons_inv
    obtain ⟨li1, rfl, rfl⟩ := di1.var_inv
    simp at li1
    subst li1
    obtain ⟨i2, is2, im2, ia2, ib2, rfl, di2, iargs2, rfl⟩ := iargs1.cons_inv
    obtain ⟨li2, rfl, rfl⟩ := di2.var_inv
    simp at li2
    subst li2
    obtain ⟨i3, is3, im3, ia3, ib3, rfl, di3, iargs3, rfl⟩ := iargs2.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := di3.literal_inv
    obtain ⟨rfl, rfl, rfl⟩ := iargs3.nil_inv
    have hDn := hD
    rw [show 0 + Ts.length = ((As.take Ts.length).reverse ++ []).length by rw [hclen]; simp]
      at hDn
    have hbody := hA.instMany _ _ _ _ _ _ icallee d Γ D _ (RepEk.mono extg hDn)
      (RepSpine.mono extg hcons)
    rw [matchPattern_bind] at mbv
    simp only [Except.ok.injEq, Option.some.injEq] at mbv
    subst mbv
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := dbody.call_inv
    rw [instanceName_plain_some] at wcallee
    obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
    obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
    simp at lw1
    subst lw1
    obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
    obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
    simp at lw2
    subst lw2
    obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
    obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
    simp at lw3
    subst lw3
    obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
    obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
    simp at lw4
    subst lw4
    obtain ⟨rfl, rfl, rfl⟩ := wargs4.nil_inv
    have exti := icallee.heap_extends
    obtain ⟨E', hE', hred⟩ := (ih _ _ _ _ _ _ (by lenlt) wcallee).withSpine rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) d Γ _ _ hbody
      (RepSpine.mono (extg.trans exti) hrest)
    refine ⟨E', hE', ?_⟩
    have hchain := K.red_beta_chain (env := c.env) (d := d) (As.take Ts.length) Ts D
      (As.drop Ts.length) (by simp; omega)
    rw [List.take_append_drop] at hchain
    simp only [List.append_nil] at hred
    exact .trans hchain hred

/-! ## `whnf_const_head` -/

theorem constHead_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_const_head" args h r h' calls) (ih : IH c calls) :
    ConstHeadSpec c args h r h' calls := by
  intro rc addr lvls hd sp types hargs good d Γ a As ha hls hhd hAs
  subst hargs
  have body := ev.function_inv IxVM.KernelWhnf.whnf_const_head.lookup
    (by simp [IxVM.KernelWhnf.whnf_const_head, ControlLower.hasControl])
  simp only [IxVM.KernelWhnf.whnf_const_head] at body
  obtain ⟨pv, pm, pbs, pc1, pc2, dp, mp, drest, rfl⟩ := body.letValue_inv
  obtain ⟨vs, m, ca, cb, cargs, pcallee, rfl⟩ := dp.call_inv
  rw [instanceName_plain_some] at pcallee
  obtain ⟨v1, vs1, m1, ca1, cb1, rfl, d1, args1, rfl⟩ := cargs.cons_inv
  obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
  simp at l1
  subst l1
  obtain ⟨v2, vs2, m2, ca2, cb2, rfl, d2, args2, rfl⟩ := args1.cons_inv
  obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
  simp at l2
  subst l2
  obtain ⟨v3, vs3, m3, ca3, cb3, rfl, d3, args3, rfl⟩ := args2.cons_inv
  obtain ⟨l3, rfl, rfl⟩ := d3.var_inv
  simp at l3
  subst l3
  obtain ⟨v4, vs4, m4, ca4, cb4, rfl, d4, args4, rfl⟩ := args3.cons_inv
  obtain ⟨l4, rfl, rfl⟩ := d4.var_inv
  simp at l4
  subst l4
  obtain ⟨v5, vs5, m5, ca5, cb5, rfl, d5, args5, rfl⟩ := args4.cons_inv
  obtain ⟨l5, rfl, rfl⟩ := d5.var_inv
  simp at l5
  subst l5
  obtain ⟨rfl, rfl, rfl⟩ := args5.nil_inv
  rw [matchPattern_bind] at mp
  simp only [Except.ok.injEq, Option.some.injEq] at mp
  subst mp
  have hprim := hA.tryPrim _ _ _ _ _ _ _ _ _ pcallee (good.sub (by memsub) (by lenlt)).2.2.1
  have extp := pcallee.heap_extends
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := drest.matchValue_inv
  obtain ⟨l0, rfl, rfl⟩ := dscr.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `(1, reduced) => whnf(rc, reduced, types)`
    -- not taken in the fragment: no native fires
    obtain ⟨y, rfl, rfl⟩ := litTuple_bs hm
    obtain ⟨x, hx⟩ := hprim
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hx
    exact absurd hx.1 (by decide)
  · -- `(2, stuck) => stuck`: not taken in the fragment
    obtain ⟨y, rfl, rfl⟩ := litTuple_bs hm
    obtain ⟨x, hx⟩ := hprim
    simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hx
    exact absurd hx.1 (by decide)
  · -- `_ => let ci = *get_ci(addr); match ci { … }`
    have := wild_bs hm
    subst this
    obtain ⟨cv, cm, cbs, cc1, cc2, dci, mci, dci2, rfl⟩ := darm.letValue_inv
    obtain ⟨cip, dcall, ldci⟩ := dci.load_inv
    obtain ⟨gvs, gm, gca, gcb, gargs, gcallee, rfl⟩ := dcall.call_inv
    have hstored := good.2.1 ⟨instanceName [] "Ingress::get_ci" (some []), gvs, gm⟩
      (by simp) (by simp)
    rw [instanceName_plain_some] at gcallee
    obtain ⟨g1, gs1, gm1, ga1, gb1, rfl, dg1, gargs1, rfl⟩ := gargs.cons_inv
    obtain ⟨lg1, rfl, rfl⟩ := dg1.var_inv
    simp at lg1
    subst lg1
    obtain ⟨rfl, rfl, rfl⟩ := gargs1.nil_inv
    rw [matchPattern_bind] at mci
    simp only [Except.ok.injEq, Option.some.injEq] at mci
    subst mci
    -- the record load, with the escape
    have ha1 := Bytes.repAddressRef_heapMono₂ addrTy extp ha
    obtain ⟨⟨lc, hst⟩, hfrag⟩ := hstored _ a rfl ha1
    have hci := hA.getCI _ _ _ _ _ gcallee a ha1 hfrag
      (load_escape hst (good.sub (by memsub) (by lenlt)).1)
    have extg := gcallee.heap_extends
    obtain ⟨u0, um0, ubs, uarm, uc1, uc2, uscr, usel, uarmd, rfl⟩ := dci2.matchValue_inv
    obtain ⟨lu0, rfl, rfl⟩ := uscr.var_inv
    simp at lu0
    subst lu0
    obtain ⟨upat, umem, um⟩ := selectArm_mem usel
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at umem
    rcases umem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `Defn(_, _, value, _, _) => …`
      obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv um
      rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp at hlen
      simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
        Except.pure] at hml
      subst hml
      simp only [kci_ctor] at hv
      subst hv
      obtain ⟨cvv, V, hn, hfind, hlp, hV⟩ := hci.defn _ _ _ _ _ ldci
      have hδ : Red c.env d (K.mkAppN (.const (c.κ a) []) As) (K.mkAppN V As) :=
        .delta (K.unfold_const_head As hfind hlp)
      obtain ⟨dv, dm, dbs, dc1, dc2, ddv, mdv, ddrest, rfl⟩ := uarmd.letValue_inv
      obtain ⟨jvs, jm, jca, jcb, jargs, jcallee, rfl⟩ := ddv.call_inv
      rw [instanceName_plain_some] at jcallee
      obtain ⟨j1, js1, jm1, ja1, jb1, rfl, dj1, jargs1, rfl⟩ := jargs.cons_inv
      obtain ⟨lj1, rfl, rfl⟩ := dj1.var_inv
      simp at lj1
      subst lj1
      obtain ⟨j2, js2, jm2, ja2, jb2, rfl, dj2, jargs2, rfl⟩ := jargs1.cons_inv
      obtain ⟨lj2, rfl, rfl⟩ := dj2.var_inv
      simp at lj2
      subst lj2
      obtain ⟨rfl, rfl, rfl⟩ := jargs2.nil_inv
      rw [matchPattern_bind] at mdv
      simp only [Except.ok.injEq, Option.some.injEq] at mdv
      subst mdv
      have hpd := hA.tryProjDef _ _ _ _ _ _ jcallee d Γ V (hV d Γ)
      have extj := jcallee.heap_extends
      obtain ⟨x0, xm0, xbs, xarm, xc1, xc2, xscr, xsel, xarmd, rfl⟩ := ddrest.matchValue_inv
      obtain ⟨lx0, rfl, rfl⟩ := xscr.var_inv
      simp at lx0
      subst lx0
      obtain ⟨xpat, xmem, xm⟩ := selectArm_mem xsel
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
        at xmem
      rcases xmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- `(1, reduced) => whnf(rc, reduced, types)`
        -- not taken: the shortcut does not fire on a represented value
        obtain ⟨y, rfl, rfl⟩ := litTuple_bs xm
        obtain ⟨x, hx⟩ := hpd
        simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq] at hx
        exact absurd hx.1 (by decide)
      · -- `_ => whnf_with_spine(rc, expr_inst_levels(value, lvls), spine, types)`
        have := wild_bs xm
        subst this
        obtain ⟨bv, bm, bbs, bc1, bc2, dbv, mbv, dbody, rfl⟩ := xarmd.letValue_inv
        obtain ⟨ivs, imm, ica, icb, iargs, icallee, rfl⟩ := dbv.call_inv
        rw [instanceName_plain_some] at icallee
        obtain ⟨i1, is1, im1, ia1, ib1, rfl, di1, iargs1, rfl⟩ := iargs.cons_inv
        obtain ⟨li1, rfl, rfl⟩ := di1.var_inv
        simp at li1
        subst li1
        obtain ⟨i2, is2, im2, ia2, ib2, rfl, di2, iargs2, rfl⟩ := iargs1.cons_inv
        obtain ⟨li2, rfl, rfl⟩ := di2.var_inv
        simp at li2
        subst li2
        obtain ⟨rfl, rfl, rfl⟩ := iargs2.nil_inv
        have ext3 := extp.trans (extg.trans extj)
        obtain ⟨rfl, rfl⟩ := (ih _ _ _ _ _ _ (by lenlt) icallee).instLevels rfl _ _ rfl
          (repList_heapMono₂ klevelListEnum repIxVMKUniv_heapMono₂ ext3 hls)
        rw [matchPattern_bind] at mbv
        simp only [Except.ok.injEq, Option.some.injEq] at mbv
        subst mbv
        obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := dbody.call_inv
        rw [instanceName_plain_some] at wcallee
        obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
        obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
        simp at lw1
        subst lw1
        obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
        obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
        simp at lw2
        subst lw2
        obtain ⟨w3, ws3, wm3, wa3, wb3, rfl, dw3, wargs3, rfl⟩ := wargs2.cons_inv
        obtain ⟨lw3, rfl, rfl⟩ := dw3.var_inv
        simp at lw3
        subst lw3
        obtain ⟨w4, ws4, wm4, wa4, wb4, rfl, dw4, wargs4, rfl⟩ := wargs3.cons_inv
        obtain ⟨lw4, rfl, rfl⟩ := dw4.var_inv
        simp at lw4
        subst lw4
        obtain ⟨rfl, rfl, rfl⟩ := wargs4.nil_inv
        obtain ⟨E', hE', hred2⟩ := (ih _ _ _ _ _ _ (by lenlt) wcallee).withSpine rfl _ _ _ _ rfl
          (good.sub (by memsub) (by lenlt)) d Γ V As (RepEc.mono extj hV d Γ)
          (RepSpine.mono ext3 hAs)
        exact ⟨E', hE', .trans hδ hred2⟩
    · -- `Thm(_, _, _) => apply_spine(head, spine)`
      obtain ⟨_, _, rfl⟩ := construct_wild_bs (n := 3) um
      obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := uarmd.call_inv
      rw [instanceName_plain_some] at wcallee
      obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
      obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
      simp at lw1
      subst lw1
      obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
      obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
      simp at lw2
      subst lw2
      obtain ⟨rfl, rfl, rfl⟩ := wargs2.nil_inv
      have ext := extp.trans extg
      exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) wcallee).applySpine rfl _ _ rfl d Γ _ As
        (RepEk.mono ext hhd) (RepSpine.mono ext hAs), .refl⟩
    · -- `Quot` is outside the slice
      obtain ⟨vs, hv, _, _⟩ := matchPattern_construct_inv um
      simp only [kci_ctor] at hv
      subst hv
      exact (hci.quot _ ldci).elim
    · -- `Rec` is outside the slice
      obtain ⟨vs, hv, _, _⟩ := matchPattern_construct_inv um
      simp only [kci_ctor] at hv
      subst hv
      exact (hci.recr _ ldci).elim
    · -- `_ => apply_spine(head, spine)`
      have := wild_bs um
      subst this
      obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := uarmd.call_inv
      rw [instanceName_plain_some] at wcallee
      obtain ⟨w1, ws1, wm1, wa1, wb1, rfl, dw1, wargs1, rfl⟩ := wargs.cons_inv
      obtain ⟨lw1, rfl, rfl⟩ := dw1.var_inv
      simp at lw1
      subst lw1
      obtain ⟨w2, ws2, wm2, wa2, wb2, rfl, dw2, wargs2, rfl⟩ := wargs1.cons_inv
      obtain ⟨lw2, rfl, rfl⟩ := dw2.var_inv
      simp at lw2
      subst lw2
      obtain ⟨rfl, rfl, rfl⟩ := wargs2.nil_inv
      have ext := extp.trans extg
      exact ⟨_, (ih _ _ _ _ _ _ (by lenlt) wcallee).applySpine rfl _ _ rfl d Γ _ As
        (RepEk.mono ext hhd) (RepSpine.mono ext hAs), .refl⟩

end IxVM.Refinement.Core
