import Ix.IxVM.Refinement.Core.Whnf

/-! # The step lemmas of the `is_def_eq` fast path

Spike S3. `k_is_def_eq` at closed terms, through `k_is_def_eq_core` and
`k_is_def_eq_ordered` to `try_def_eq_app` (same-head spine congruence) and
`de_args` (pairwise, calling back into `k_is_def_eq`): a nonzero answer is
`DefEq`. The slow tiers and the lowering rebase are not taken in the fragment
(`Good`'s list of functions the fragment does not call). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.IxVMRep Aiur.Library.List
open Ix.Kernel.Rules (Red DefEq DefEqList)

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Helpers -/

theorem RepK.bvar_of_load {h : Heap F} {t : IxVMKExpr F} {p x : SourceValue F}
    (rep : RepK h t p) (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i, t = .bvar i ∧ x = .field i := by
  cases rep with
  | bvar cell =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs; injection hargs with hx _
    exact ⟨_, rfl, hx.symm⟩
  | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _
  | letE cell _ _ _ | litNat cell _ | litStr cell _ | proj cell _ _ =>
    rw [loadValue_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

theorem Tr.bvar_det {κ : Bytes.Address → Ix.Kernel.Key .anon} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {i : F} {E₁ E₂ : KExpr}
    (h₁ : Tr κ d Γ k (.bvar i) E₁) (h₂ : Tr κ d Γ k (.bvar i) E₂) : E₁ = E₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | omega

theorem evalBinOp_sub_inv {x y r : SourceValue F} (h : evalBinOp .sub x y = .ok r) :
    ∃ a b, x = .field a ∧ y = .field b ∧ r = .field (a - b) := by
  cases x <;> cases y <;> simp [evalBinOp] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- A call to a function the fragment does not call. -/
theorem outside_absurd {c : Ctx} {calls : List (Call F)} (good : Good c calls) {n : String}
    {args : List (SourceValue F)} {heap : Heap F}
    (hmem : (⟨instanceName [] n (some []), args, heap⟩ : Call F) ∈ calls)
    (hn : n ∈ nativeNames) : False :=
  good.2.2.1 _ hmem (by simpa using hn)

/-! ## `de_args` -/

theorem deArgs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_args" args h r h' calls) (ih : IH c calls) :
    DeArgsSpec c args h r calls := by
  intro rc aa bb types hargs good hr d Γ As Bs hAs hBs
  subst hargs
  have body := ev.function_inv IxVM.KernelDefEq.de_args.lookup
    (by simp [IxVM.KernelDefEq.de_args, ControlLower.hasControl])
  simp only [IxVM.KernelDefEq.de_args] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨p0, dp, ld⟩ := dscr.load_inv
  obtain ⟨l0, rfl, rfl⟩ := dp.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `Nil => match *bb { Nil => 1, _ => 0 }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨_, _⟩ <;> simp at hlen
    simp [matchListWith, pure, Except.pure] at hml
    subst hml
    simp only [kexprList_ctor] at hv
    subst hv
    have := RepList.nil_of_load hAs ld
    subst this
    obtain ⟨iv, im, ibs, iarm, ic1, ic2, iscr, isel, iarmd, rfl⟩ := darm.matchValue_inv
    obtain ⟨ip, idp, ild⟩ := iscr.load_inv
    obtain ⟨il, rfl, rfl⟩ := idp.var_inv
    simp at il
    subst il
    obtain ⟨ipat, ihmem, ihm⟩ := selectArm_mem isel
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at ihmem
    rcases ihmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv ihm
      simp only [kexprList_ctor] at hv
      subst hv
      rcases vs with _ | ⟨_, _⟩ <;> simp at hlen
      have := RepList.nil_of_load hBs ild
      subst this
      exact .nil
    · obtain ⟨rfl, -, -⟩ := iarmd.literal_inv
      exact (hr rfl).elim
  · -- `Cons(a, ar) => match *bb { Nil => 0, Cons(b, br) => … }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexprList_ctor] at hv
    subst hv
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld
    obtain ⟨iv, im, ibs, iarm, ic1, ic2, iscr, isel, iarmd, rfl⟩ := darm.matchValue_inv
    obtain ⟨ip, idp, ild⟩ := iscr.load_inv
    obtain ⟨il, rfl, rfl⟩ := idp.var_inv
    simp at il
    subst il
    obtain ⟨ipat, ihmem, ihm⟩ := selectArm_mem isel
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at ihmem
    rcases ihmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨rfl, -, -⟩ := iarmd.literal_inv
      exact (hr rfl).elim
    · obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv ihm
      rcases vs with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
      simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
      subst hml
      simp only [kexprList_ctor] at hv
      subst hv
      obtain ⟨B, Bs', rfl, hB, hBs'⟩ := RepList.cons_of_load hBs ild
      -- `match k_is_def_eq(rc, a, b, types) { 0 => 0, _ => de_args(rc, ar, br, types) }`
      obtain ⟨kv, km, kbs, karm, kc1, kc2, kscr, ksel, karmd, rfl⟩ := iarmd.matchValue_inv
      obtain ⟨cvs, cm, cca, ccb, cargs, ccallee, rfl⟩ := kscr.call_inv
      rw [instanceName_plain_some] at ccallee
      obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs.cons_inv
      obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
      simp at lu1
      subst lu1
      obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, cargs2, rfl⟩ := cargs1.cons_inv
      obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
      simp at lu2
      subst lu2
      obtain ⟨u3, us3, n3, ka3, kb3, rfl, du3, cargs3, rfl⟩ := cargs2.cons_inv
      obtain ⟨lu3, rfl, rfl⟩ := du3.var_inv
      simp at lu3
      subst lu3
      obtain ⟨u4, us4, n4, ka4, kb4, rfl, du4, cargs4, rfl⟩ := cargs3.cons_inv
      obtain ⟨lu4, rfl, rfl⟩ := du4.var_inv
      simp at lu4
      subst lu4
      obtain ⟨rfl, rfl, rfl⟩ := cargs4.nil_inv
      rcases selectArm_literal_inv ksel with ⟨_, rfl, rfl⟩ | ⟨hne, ksel'⟩
      · obtain ⟨rfl, -, -⟩ := karmd.literal_inv
        exact (hr rfl).elim
      · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv ksel'
        have hAB := (ih _ _ _ _ _ _ (by lenlt) ccallee).defEq rfl _ _ _ _ rfl
          (good.sub (by memsub) (by lenlt)) hne d Γ A B hA hB
        have extk := ccallee.heap_extends
        obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := karmd.call_inv
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
        have hrest := (ih _ _ _ _ _ _ (by lenlt) wcallee).deArgs rfl _ _ _ _ rfl
          (good.sub (by memsub) (by lenlt)) hr d Γ As' Bs'
          (RepSpine.mono extk hAs') (RepSpine.mono extk hBs')
        exact .cons hAB hrest

/-! ## `try_def_eq_app` -/

theorem tryApp_step (c : Ctx) (hA : Assumed c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::try_def_eq_app" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA' hB'
  subst hargs
  have body := ev.function_inv IxVM.KernelDefEq.try_def_eq_app.lookup
    (by simp [IxVM.KernelDefEq.try_def_eq_app, ControlLower.hasControl])
  simp only [IxVM.KernelDefEq.try_def_eq_app] at body
  -- `match collect_spine(a) { (ah, aa) => … }`
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨cvs, cm, cca, ccb, cargs, ccallee, rfl⟩ := dscr.call_inv
  rw [instanceName_plain_some] at ccallee
  obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs.cons_inv
  obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
  simp at lu1
  subst lu1
  obtain ⟨rfl, rfl, rfl⟩ := cargs1.nil_inv
  have exta := ccallee.heap_extends
  obtain ⟨ahp, aap, AH, As, rfl, hAH, hAs, rfl⟩ :=
    (ih _ _ _ _ _ _ (by lenlt) ccallee).collect rfl _ rfl d Γ A hA'
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv hm
  rcases ys with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hl
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml
  subst ml
  -- `match collect_spine(b) { (bh, bb) => … }`
  obtain ⟨v1, m1, bs1, arm1, c₃, c₄, dscr1, sel1, darm1, rfl⟩ := darm.matchValue_inv
  obtain ⟨dvs, dm, dca, dcb, dargs, dcallee, rfl⟩ := dscr1.call_inv
  rw [instanceName_plain_some] at dcallee
  obtain ⟨t1, ts1, tn1, ta1, tb1, rfl, dt1, dargs1, rfl⟩ := dargs.cons_inv
  obtain ⟨lt1, rfl, rfl⟩ := dt1.var_inv
  simp at lt1
  subst lt1
  obtain ⟨rfl, rfl, rfl⟩ := dargs1.nil_inv
  have extb := dcallee.heap_extends
  obtain ⟨bhp, bbp, BH, Bs, rfl, hBH, hBs, rfl⟩ :=
    (ih _ _ _ _ _ _ (by lenlt) dcallee).collect rfl _ rfl d Γ B (RepEk.mono exta hB')
  obtain ⟨pat1, hmem1, hm1⟩ := selectArm_mem sel1
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem1
  obtain ⟨rfl, rfl⟩ := hmem1
  obtain ⟨ys, hp, hl, ml⟩ := matchPattern_tuple_inv hm1
  rcases ys with _ | ⟨z1, _ | ⟨z2, _ | ⟨_, _⟩⟩⟩ <;> simp at hl
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at ml
  subst ml
  have hAH' := RepEk.mono extb hAH
  have hAs' := RepSpine.mono extb hAs
  -- `match *ah { BVar(i) => …, Const(a_addr, al) => …, _ => 0 }`
  obtain ⟨v2, m2, bs2, arm2, c₅, c₆, dscr2, sel2, darm2, rfl⟩ := darm1.matchValue_inv
  obtain ⟨p2, dp2, ld2⟩ := dscr2.load_inv
  obtain ⟨l2, rfl, rfl⟩ := dp2.var_inv
  simp at l2
  subst l2
  obtain ⟨pat2, hmem2, hm2⟩ := selectArm_mem sel2
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem2
  rcases hmem2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `BVar(i) => match *bh { BVar(j) => match i - j { 0 => de_args(…), _ => 0 }, _ => 0 }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm2
    rcases vs with _ | ⟨y1, _ | ⟨_, _⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨ta, rta, tta⟩ := hAH'
    obtain ⟨i, rfl, rfl⟩ := RepK.bvar_of_load rta ld2
    obtain ⟨v3, m3, bs3, arm3, c₇, c₈, dscr3, sel3, darm3, rfl⟩ := darm2.matchValue_inv
    obtain ⟨p3, dp3, ld3⟩ := dscr3.load_inv
    obtain ⟨l3, rfl, rfl⟩ := dp3.var_inv
    simp at l3
    subst l3
    obtain ⟨pat3, hmem3, hm3⟩ := selectArm_mem sel3
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at hmem3
    rcases hmem3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm3
      rcases vs with _ | ⟨y2, _ | ⟨_, _⟩⟩ <;> simp at hlen
      simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
      subst hml
      simp only [kexpr_ctor] at hv
      subst hv
      obtain ⟨tb, rtb, ttb⟩ := hBH
      obtain ⟨j, rfl, rfl⟩ := RepK.bvar_of_load rtb ld3
      obtain ⟨v4, m4, bs4, arm4, c₉, c₁₀, dscr4, sel4, darm4, rfl⟩ := darm3.matchValue_inv
      obtain ⟨x, y, mm, cx, cy, dx, dy, hop, rfl⟩ := dscr4.binary_inv
      obtain ⟨lx, rfl, rfl⟩ := dx.var_inv
      simp at lx
      subst lx
      obtain ⟨ly, rfl, rfl⟩ := dy.var_inv
      simp at ly
      subst ly
      obtain ⟨_, _, hx1, hy1, rfl⟩ := evalBinOp_sub_inv hop
      injection hx1 with hx1
      injection hy1 with hy1
      subst hx1 hy1
      obtain ⟨pat4, hmem4, hm4⟩ := selectArm_mem sel4
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
        at hmem4
      rcases hmem4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hz, rfl⟩ := literal_bs hm4
        injection hz with hz
        have hij : i = j := sub_eq_zero.mp (hz.trans (by decide))
        subst hij
        have hHB : AH = BH := Tr.bvar_det tta ttb
        subst hHB
        obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm4.call_inv
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
        have hargs := (ih _ _ _ _ _ _ (by lenlt) wcallee).deArgs rfl _ _ _ _ rfl
          (good.sub (by memsub) (by lenlt)) hr d Γ As Bs hAs' hBs
        exact DefEq.mkAppN .refl hargs
      · have := wild_bs hm4
        subst this
        obtain ⟨rfl, -, -⟩ := darm4.literal_inv
        exact (hr rfl).elim
    · have := wild_bs hm3
      subst this
      obtain ⟨rfl, -, -⟩ := darm3.literal_inv
      exact (hr rfl).elim
  · -- `Const(a_addr, al) => match *bh { Const(b_addr, bl) => … , _ => 0 }`
    obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm2
    rcases vs with _ | ⟨y1, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
    simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
    subst hml
    simp only [kexpr_ctor] at hv
    subst hv
    obtain ⟨ta, rta, tta⟩ := hAH'
    obtain ⟨aa, als, rfl, haa, hals⟩ := RepK.const_of_load rta ld2
    obtain ⟨rfl, rfl⟩ := Tr.const_inv tta
    obtain ⟨v3, m3, bs3, arm3, c₇, c₈, dscr3, sel3, darm3, rfl⟩ := darm2.matchValue_inv
    obtain ⟨p3, dp3, ld3⟩ := dscr3.load_inv
    obtain ⟨l3, rfl, rfl⟩ := dp3.var_inv
    simp at l3
    subst l3
    obtain ⟨pat3, hmem3, hm3⟩ := selectArm_mem sel3
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
      at hmem3
    rcases hmem3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨vs, hv, hlen, hml⟩ := matchPattern_construct_inv hm3
      rcases vs with _ | ⟨y3, _ | ⟨y4, _ | ⟨_, _⟩⟩⟩ <;> simp at hlen
      simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure] at hml
      subst hml
      simp only [kexpr_ctor] at hv
      subst hv
      obtain ⟨tb, rtb, ttb⟩ := hBH
      obtain ⟨bb', bls, rfl, hbb, hbls⟩ := RepK.const_of_load rtb ld3
      obtain ⟨rfl, rfl⟩ := Tr.const_inv ttb
      -- `match (1 - address_eq(a_addr, b_addr)) { 0 => …, _ => 0 }`
      obtain ⟨v4, m4, bs4, arm4, c₉, c₁₀, dscr4, sel4, darm4, rfl⟩ := darm3.matchValue_inv
      obtain ⟨x, y, mm, cx, cy, dx, dy, hop, rfl⟩ := dscr4.binary_inv
      obtain ⟨rfl, rfl, rfl⟩ := dx.literal_inv
      obtain ⟨evs, em, eca, ecb, eargs, ecallee, rfl⟩ := dy.call_inv
      rw [instanceName_plain_some] at ecallee
      obtain ⟨e1, es1, em1, ea1, eb1, rfl, de1, eargs1, rfl⟩ := eargs.cons_inv
      obtain ⟨le1, rfl, rfl⟩ := de1.var_inv
      simp at le1
      subst le1
      obtain ⟨e2, es2, em2, ea2, eb2, rfl, de2, eargs2, rfl⟩ := eargs1.cons_inv
      obtain ⟨le2, rfl, rfl⟩ := de2.var_inv
      simp at le2
      subst le2
      obtain ⟨rfl, rfl, rfl⟩ := eargs2.nil_inv
      obtain ⟨_, ev', hx1, hy1, rfl⟩ := evalBinOp_sub_inv hop
      subst hy1
      obtain ⟨pat4, hmem4, hm4⟩ := selectArm_mem sel4
      simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
        at hmem4
      rcases hmem4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨hz, rfl⟩ := literal_bs hm4
        injection hz with hz
        injection hx1 with hx1
        have he : ev' = 1 := by
          have := sub_eq_zero.mp (hz.trans (by decide))
          rw [← this, ← hx1]
          try decide
        subst he
        have hab := hA.addressEq _ _ _ _ _ _ ecallee aa bb' haa hbb rfl
        subst hab
        have exte := ecallee.heap_extends
        -- `match level_list_eq(al, bl) { 0 => 0, _ => … }`
        obtain ⟨v5, m5, bs5, arm5, c₁₁, c₁₂, dscr5, sel5, darm5, rfl⟩ := darm4.matchValue_inv
        obtain ⟨lvs, lm, lca, lcb, largs, lcallee, rfl⟩ := dscr5.call_inv
        have extl := lcallee.heap_extends
        obtain ⟨pat5, hmem5, hm5⟩ := selectArm_mem sel5
        simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
          at hmem5
        rcases hmem5 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨_, rfl⟩ := literal_bs hm5
          obtain ⟨rfl, -, -⟩ := darm5.literal_inv
          exact (hr rfl).elim
        · have := wild_bs hm5
          subst this
          -- `match length(aa) - length(bb) { 0 => de_args(…), _ => 0 }`
          obtain ⟨v6, m6, bs6, arm6, c₁₃, c₁₄, dscr6, sel6, darm6, rfl⟩ :=
            darm5.matchValue_inv
          have ext6 := dscr6.heap_extends
          obtain ⟨pat6, hmem6, hm6⟩ := selectArm_mem sel6
          simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil,
            or_false] at hmem6
          rcases hmem6 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨_, rfl⟩ := literal_bs hm6
            obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm6.call_inv
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
            have ext := exte.trans (largs.heap_extends.trans (extl.trans ext6))
            have hargs := (ih _ _ _ _ _ _ (by lenlt) wcallee).deArgs rfl _ _ _ _ rfl
              (good.sub (by memsub) (by lenlt)) hr d Γ As Bs
              (RepSpine.mono ext hAs') (RepSpine.mono ext hBs)
            exact DefEq.mkAppN .refl hargs
          · have := wild_bs hm6
            subst this
            obtain ⟨rfl, -, -⟩ := darm6.literal_inv
            exact (hr rfl).elim
      · have := wild_bs hm4
        subst this
        obtain ⟨rfl, -, -⟩ := darm4.literal_inv
        exact (hr rfl).elim
    · have := wild_bs hm3
      subst this
      obtain ⟨rfl, -, -⟩ := darm3.literal_inv
      exact (hr rfl).elim
  · have := wild_bs hm2
    subst this
    obtain ⟨rfl, -, -⟩ := darm2.literal_inv
    exact (hr rfl).elim

/-! ## `k_is_def_eq`, `k_is_def_eq_core`, `k_is_def_eq_ordered` -/

theorem defEqOrdered_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_ordered" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  have body := ev.function_inv IxVM.KernelDefEq.k_is_def_eq_ordered.lookup
    (by simp [IxVM.KernelDefEq.k_is_def_eq_ordered, ControlLower.hasControl])
  simp only [IxVM.KernelDefEq.k_is_def_eq_ordered] at body
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := body.matchValue_inv
  obtain ⟨cvs, cm, cca, ccb, cargs, ccallee, rfl⟩ := dscr.call_inv
  rw [instanceName_plain_some] at ccallee
  obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs.cons_inv
  obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
  simp at lu1
  subst lu1
  obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, cargs2, rfl⟩ := cargs1.cons_inv
  obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
  simp at lu2
  subst lu2
  obtain ⟨u3, us3, n3, ka3, kb3, rfl, du3, cargs3, rfl⟩ := cargs2.cons_inv
  obtain ⟨lu3, rfl, rfl⟩ := du3.var_inv
  simp at lu3
  subst lu3
  obtain ⟨u4, us4, n4, ka4, kb4, rfl, du4, cargs4, rfl⟩ := cargs3.cons_inv
  obtain ⟨lu4, rfl, rfl⟩ := du4.var_inv
  simp at lu4
  subst lu4
  obtain ⟨rfl, rfl, rfl⟩ := cargs4.nil_inv
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `1 => 1`
    obtain ⟨hv, rfl⟩ := literal_bs hm
    subst hv
    exact (ih _ _ _ _ _ _ (by lenlt) ccallee).tryApp rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) (fun h => by injection h with h; exact absurd h (by decide))
      d Γ A B hA hB
  · -- `_ => k_is_def_eq_slow(…)`: not taken in the fragment
    have := wild_bs hm
    subst this
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm.call_inv
    exact (outside_absurd (n := "KernelDefEq::k_is_def_eq_slow") (args := wvs) (heap := wm) good
      (by simp) (by simp [nativeNames])).elim

theorem defEqCore_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_core" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  have body := ev.function_inv IxVM.KernelDefEq.k_is_def_eq_core.lookup
    (by simp [IxVM.KernelDefEq.k_is_def_eq_core, ControlLower.hasControl])
  simp only [IxVM.KernelDefEq.k_is_def_eq_core] at body
  obtain ⟨cvs, cm, cca, ccb, cargs, ccallee, rfl⟩ := body.call_inv
  rw [instanceName_plain_some] at ccallee
  obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs.cons_inv
  obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
  simp at lu1
  subst lu1
  obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, cargs2, rfl⟩ := cargs1.cons_inv
  obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
  simp at lu2
  subst lu2
  obtain ⟨u3, us3, n3, ka3, kb3, rfl, du3, cargs3, rfl⟩ := cargs2.cons_inv
  obtain ⟨lu3, rfl, rfl⟩ := du3.var_inv
  simp at lu3
  subst lu3
  obtain ⟨u4, us4, n4, ka4, kb4, rfl, du4, cargs4, rfl⟩ := cargs3.cons_inv
  obtain ⟨lu4, rfl, rfl⟩ := du4.var_inv
  simp at lu4
  subst lu4
  obtain ⟨rfl, rfl, rfl⟩ := cargs4.nil_inv
  exact (ih _ _ _ _ _ _ (by lenlt) ccallee).defEqOrdered rfl _ _ _ _ rfl
    (good.sub (by memsub) (by lenlt)) hr d Γ A B hA hB

theorem defEq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  have body := ev.function_inv IxVM.KernelDefEq.k_is_def_eq.lookup
    (by simp [IxVM.KernelDefEq.k_is_def_eq, ControlLower.hasControl])
  simp only [IxVM.KernelDefEq.k_is_def_eq] at body
  obtain ⟨bv, bm, bbs, bc1, bc2, dbv, mbv, drest, rfl⟩ := body.letValue_inv
  have extb := dbv.heap_extends
  rw [matchPattern_bind] at mbv
  simp only [Except.ok.injEq, Option.some.injEq] at mbv
  subst mbv
  obtain ⟨v0, m0, bs, arm, c₁, c₂, dscr, sel, darm, rfl⟩ := drest.matchValue_inv
  obtain ⟨l0, rfl, rfl⟩ := dscr.var_inv
  simp at l0
  subst l0
  obtain ⟨pat, hmem, hm⟩ := selectArm_mem sel
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `0 => k_is_def_eq_core(rc, a, b, &Nil)`
    obtain ⟨_, rfl⟩ := literal_bs hm
    obtain ⟨cvs, cm, cca, ccb, cargs, ccallee, rfl⟩ := darm.call_inv
    rw [instanceName_plain_some] at ccallee
    obtain ⟨u1, us1, n1, ka1, kb1, rfl, du1, cargs1, rfl⟩ := cargs.cons_inv
    obtain ⟨lu1, rfl, rfl⟩ := du1.var_inv
    simp at lu1
    subst lu1
    obtain ⟨u2, us2, n2, ka2, kb2, rfl, du2, cargs2, rfl⟩ := cargs1.cons_inv
    obtain ⟨lu2, rfl, rfl⟩ := du2.var_inv
    simp at lu2
    subst lu2
    obtain ⟨u3, us3, n3, ka3, kb3, rfl, du3, cargs3, rfl⟩ := cargs2.cons_inv
    obtain ⟨lu3, rfl, rfl⟩ := du3.var_inv
    simp at lu3
    subst lu3
    obtain ⟨u4, us4, n4, ka4, kb4, rfl, du4, cargs4, rfl⟩ := cargs3.cons_inv
    obtain ⟨sv, sm, d4', rfl, rfl⟩ := du4.store_inv
    obtain ⟨svs, sargs, rfl⟩ := d4'.construct_inv
    obtain ⟨rfl, rfl, rfl⟩ := sargs.nil_inv
    obtain ⟨rfl, rfl, rfl⟩ := cargs4.nil_inv
    simp only [kexprList_inst, Value.type] at ccallee
    exact (ih _ _ _ _ _ _ (by lenlt) ccallee).defEqCore rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) hr d Γ A B
      (RepEk.mono (extb.trans (Heap.Extends.snoc _ _)) hA)
      (RepEk.mono (extb.trans (Heap.Extends.snoc _ _)) hB)
  · -- `_ => k_def_eq_rebase(…)`: not taken in the fragment
    have := wild_bs hm
    subst this
    obtain ⟨wvs, wm, wca, wcb, wargs, wcallee, rfl⟩ := darm.call_inv
    exact (outside_absurd (n := "KernelDefEq::k_def_eq_rebase") (args := wvs) (heap := wm) good
      (by simp) (by simp [nativeNames])).elim

end IxVM.Refinement.Core
