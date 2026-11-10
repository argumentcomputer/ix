import Ix.IxVM.Refinement.Core.Whnf
import Ix.IxVM.Refinement.Obs.KernelDefEq

/-! # The step lemmas of the `is_def_eq` fast path

Spike S3. `k_is_def_eq` at closed terms, through `k_is_def_eq_core` and
`k_is_def_eq_ordered` to `try_def_eq_app` (same-head spine congruence) and
`de_args` (pairwise, calling back into `k_is_def_eq`): a nonzero answer is
`DefEq`. The slow tiers and the lowering rebase are not taken in the fragment
(`Good`'s list of functions the fragment does not call). Each proof takes the
derivation's path from the generated path lemma (`Ix.IxVM.Refinement.Obs`). -/

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
    (hmem : (⟨n, args, heap⟩ : Call F) ∈ calls) (hn : n ∈ nativeNames) : False :=
  good.2.2.1 _ hmem hn

/-- The heads and spines of both sides, from the two `collect_spine` calls that
open `try_def_eq_app`. -/
theorem collect_both (c : Ctx) {calls : List (Call F)} (ih : IH c calls)
    {a b ah aa bh bb : SourceValue F} {h m2 m41 : Heap F} {cs13 cs52 : List (Call F)}
    (ev15 : ObsFn W "KernelTypes::collect_spine" [a] h (.tuple [ah, aa]) m2 cs13)
    (h15 : cs13.length < calls.length)
    (ev54 : ObsFn W "KernelTypes::collect_spine" [b] m2 (.tuple [bh, bb]) m41 cs52)
    (h54 : cs52.length < calls.length)
    {d : Nat} {Γ : Nat → KExpr} {A B : KExpr}
    (hA : RepE c.κ d Γ h A a) (hB : RepE c.κ d Γ h B b) :
    ∃ AH As BH Bs, A = K.mkAppN AH As ∧ B = K.mkAppN BH Bs ∧
      RepE c.κ d Γ m41 AH ah ∧ RepSpine c.κ d Γ m41 As aa ∧
      RepE c.κ d Γ m41 BH bh ∧ RepSpine c.κ d Γ m41 Bs bb := by
  obtain ⟨ahp, aap, AH, As, hpa, hAH, hAs, rfl⟩ :=
    (ih _ _ _ _ _ _ h15 ev15).collect rfl _ rfl d Γ A hA
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpa
  obtain ⟨rfl, rfl⟩ := hpa
  obtain ⟨bhp, bbp, BH, Bs, hpb, hBH, hBs, rfl⟩ :=
    (ih _ _ _ _ _ _ h54 ev54).collect rfl _ rfl d Γ B (RepEk.mono ev15.heap_extends hB)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hpb
  obtain ⟨rfl, rfl⟩ := hpb
  exact ⟨AH, As, BH, Bs, rfl, rfl, RepEk.mono ev54.heap_extends hAH,
    RepSpine.mono ev54.heap_extends hAs, hBH, hBs⟩

/-! ## `de_args` -/

theorem deArgs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_args" args h r h' calls) (ih : IH c calls) :
    DeArgsSpec c args h r calls := by
  intro rc aa bb types hargs good hr d Γ As Bs hAs hBs
  subst hargs
  rcases Obs.«KernelDefEq::de_args».obs ev with
    ⟨ld, ld', rfl, rfl, -⟩ | ⟨_, -, -, -, rfl, -, -⟩ | ⟨_, _, -, -, rfl, -, -⟩ |
    ⟨_, _, _, _, _, _, -, -, -, rfl, -, -⟩ |
    ⟨a, ar, b, br, v, m, cs, cs', ld, ld', ev1, hne, ev2, rfl⟩
  · -- `Nil`, `Nil => 1`
    obtain rfl := RepList.nil_of_load hAs ld
    obtain rfl := RepList.nil_of_load hBs ld'
    exact .nil
  -- `Nil`, `_ => 0`; `Cons`, `Nil => 0`; `Cons`, `Cons`, `0 => 0`
  all_goals first | exact (hr rfl).elim | skip
  -- `Cons(a, ar)`, `Cons(b, br)`, `_ => de_args(rc, ar, br, types)`
  obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld
  obtain ⟨B, Bs', rfl, hB, hBs'⟩ := RepList.cons_of_load hBs ld'
  have hAB := (ih _ _ _ _ _ _ (by lenlt) ev1).defEq rfl _ _ _ _ rfl
    (good.sub (by memsub) (by lenlt)) hne d Γ A B hA hB
  have extk := ev1.heap_extends
  have hrest := (ih _ _ _ _ _ _ (by lenlt) ev2).deArgs rfl _ _ _ _ rfl
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
  cases Obs.«KernelDefEq::try_def_eq_app».obs ev with
  | BVar_BVar_n0 m2 cs13 ah aa m41 cs52 bh bb i j cs153 ev15 ev54 ld90 ld114 op ev155 hc =>
    -- `BVar(i)`, `BVar(j)`, `i - j = 0 => de_args(rc, aa, bb, types)`
    subst hc
    obtain ⟨AH, As, BH, Bs, rfl, rfl, hAH, hAs, hBH, hBs⟩ :=
      collect_both c ih ev15 (by lenlt) ev54 (by lenlt) hA' hB'
    obtain ⟨ta, rta, tta⟩ := hAH
    obtain ⟨i', rfl, rfl⟩ := RepK.bvar_of_load rta ld90
    obtain ⟨tb, rtb, ttb⟩ := hBH
    obtain ⟨j', rfl, rfl⟩ := RepK.bvar_of_load rtb ld114
    obtain ⟨_, _, hx1, hy1, hz⟩ := evalBinOp_sub_inv op
    injection hx1 with hx1
    injection hy1 with hy1
    subst hx1 hy1
    injection hz with hz
    have hij : i' = j' := sub_eq_zero.mp (hz.symm.trans (by decide))
    subst hij
    have hHB : AH = BH := Tr.bvar_det tta ttb
    subst hHB
    have hargs := (ih _ _ _ _ _ _ (by lenlt) ev155).deArgs rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) hr d Γ As Bs hAs hBs
    exact DefEq.mkAppN .refl hargs
  | Const_Const_n0_other_n0 m2 cs13 ah aa m41 cs52 bh bb aaddr al baddr bl m250 y259 cs269 v292
      m293 cs304 m335 x343 y344 m345 cs354 cs368 cs386 ev15 ev54 ld90 ld231 ev271 op265 ev306 hne
      ev356 ev370 op350 ev388 hc =>
    -- `Const`, `Const`, equal addresses, `level_list_eq ≠ 0`, equal lengths `=> de_args(…)`
    subst hc
    obtain ⟨AH, As, BH, Bs, rfl, rfl, hAH, hAs, hBH, hBs⟩ :=
      collect_both c ih ev15 (by lenlt) ev54 (by lenlt) hA' hB'
    obtain ⟨ta, rta, tta⟩ := hAH
    obtain ⟨aa', als, rfl, haa, hals⟩ := RepK.const_of_load rta ld90
    obtain ⟨rfl, rfl⟩ := Tr.const_inv tta
    obtain ⟨tb, rtb, ttb⟩ := hBH
    obtain ⟨bb', bls, rfl, hbb, hbls⟩ := RepK.const_of_load rtb ld231
    obtain ⟨rfl, rfl⟩ := Tr.const_inv ttb
    obtain ⟨_, e', hx1, hy1, hz⟩ := evalBinOp_sub_inv op265
    subst hy1
    injection hx1 with hx1
    injection hz with hz
    have he : e' = 1 := by
      have := sub_eq_zero.mp (hz.symm.trans (by decide))
      rw [← this, ← hx1]
      try decide
    subst he
    have hab := hA.addressEq _ _ _ _ _ _ ev271 aa' bb' haa hbb rfl
    subst hab
    have ext := ev271.heap_extends.trans
      (ev306.heap_extends.trans (ev356.heap_extends.trans ev370.heap_extends))
    have hargs := (ih _ _ _ _ _ _ (by lenlt) ev388).deArgs rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) hr d Γ As Bs
      (RepSpine.mono ext hAs) (RepSpine.mono ext hBs)
    exact DefEq.mkAppN .refl hargs
  | _ =>
    -- every other path answers `0`
    exact (hr ‹r = .field 0›).elim

/-! ## `k_is_def_eq`, `k_is_def_eq_core`, `k_is_def_eq_ordered` -/

theorem defEqOrdered_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_ordered" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq_ordered».obs ev with
    ⟨m2, cs, ev1, rfl, rfl, rfl⟩ | ⟨v, m2, cs, cs', ev1, -, ev2, rfl⟩
  · -- `1 => 1`
    exact (ih _ _ _ _ _ _ (by lenlt) ev1).tryApp rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) (fun h => by injection h with h; exact absurd h (by decide))
      d Γ A B hA hB
  · -- `_ => k_is_def_eq_slow(…)`: not taken in the fragment
    exact (outside_absurd (n := "KernelDefEq::k_is_def_eq_slow") (args := [rc, a, b, types])
      (heap := m2) good (by simp) (by simp [nativeNames])).elim

theorem defEqCore_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq_core" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  obtain ⟨cs, ev1, rfl⟩ := Obs.«KernelDefEq::k_is_def_eq_core».obs ev
  exact (ih _ _ _ _ _ _ (by lenlt) ev1).defEqOrdered rfl _ _ _ _ rfl
    (good.sub (by memsub) (by lenlt)) hr d Γ A B hA hB

theorem defEq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" args h r h' calls) (ih : IH c calls) :
    DefEqSpec c args h r calls := by
  intro rc a b types hargs good hr d Γ A B hA hB
  subst hargs
  rcases Obs.«KernelDefEq::k_is_def_eq».obs ev with
    ⟨m2, cs12, v15, v16, m18, cs26, m38, cs46, cs74, m103, ev28, ev48, ev14, rfl, ev76, rfl⟩ |
    ⟨v1, m2, cs12, v15, v16, m18, cs26, m38, cs46, cs123, ev28, ev48, ev14, -, ev125, rfl⟩
  · -- `0 => k_is_def_eq_core(rc, a, b, &Nil)`
    have extb := ev28.heap_extends.trans (ev48.heap_extends.trans ev14.heap_extends)
    exact (ih _ _ _ _ _ _ (by lenlt) ev76).defEqCore rfl _ _ _ _ rfl
      (good.sub (by memsub) (by lenlt)) hr d Γ A B
      (RepEk.mono (extb.trans (Heap.Extends.snoc _ _)) hA)
      (RepEk.mono (extb.trans (Heap.Extends.snoc _ _)) hB)
  · -- `_ => k_def_eq_rebase(…)`: not taken in the fragment
    exact (outside_absurd (n := "KernelDefEq::k_def_eq_rebase") (args := [rc, a, b, types, v1])
      (heap := m2) good (by simp) (by simp [nativeNames])).elim

end IxVM.Refinement.Core
