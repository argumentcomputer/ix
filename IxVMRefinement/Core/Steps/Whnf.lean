import IxVMRefinement.Core.Registry
import IxVMRefinement.Core.Open
import IxVMRefinement.Obs.KernelWhnf

/-! # Step lemmas of `KernelWhnf`, on the registry

Each lemma takes the derivation's path from the generated path lemma, reads its callees' specs
from the induction hypothesis (`IH.get`), and concludes the function's registered spec. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)

/-! ## Helpers -/

/-- A callee's derivation has fewer calls than its caller's. -/
macro "lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

theorem types_mono {c : Ctx} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {d : Nat} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : c.types Γ h₁ d p) : c.types Γ h₂ d p :=
  ⟨r.1.mono ext, r.2⟩

theorem tml_mono {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F} {Es : List KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (r : c.tml d Γ h₁ Es p) : c.tml d Γ h₂ Es p :=
  TmL.mono ext r

/-- A level the never-zero test accepts has the datum `never`. -/
theorem bmeta_of_isNeverZero {ℓ : KLevel} (h : ℓ.isNeverZero = true) :
    bmeta ℓ = Specs.Whnf.nbMeta := by
  have e := Ix.Kernel.Verify.PropWhen.isNeverZero_eq_isNever ℓ
  rw [h] at e
  have := Ix.Kernel.PropWhen.isNever_iff.mp e.symm
  simp [bmeta, Specs.Whnf.nbMeta, this]

theorem field_one_ne_zero : (SourceValue.field (1 : F) : SourceValue F) ≠ .field 0 := by
  intro h
  injection h with h
  exact one_ne_zero h

/-! ## `peel_beta` -/

/-- `KernelWhnf::peel_beta` consumes the arguments of the `λ`s whose level the never-zero test
accepts. -/
theorem peel_beta_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::peel_beta" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.peel_beta c args h r h' calls := by
  intro lam sp acc hargs good d Γ k L As Cs hL hAs hCs
  subst hargs
  rcases Obs.«KernelWhnf::peel_beta».obs ev with
    ⟨w20, x_body, x_bl, x_a, x_rest, m66, cs77, cs95, m116, ld12, ld47, ev79, hm124, ev97,
      hc144⟩ |
    ⟨w20, x_body, x_bl, x_a, x_rest, v65, m66, cs77, ld12, ld47, ev79, hne145, he154, he176,
      hc177⟩ |
    ⟨w20, x_body, x_bl, ld12, ld47, he190, he212, hc213⟩ |
    ⟨v1, ld12, hne215, he224, he246, hc247⟩
  · -- a `λ` with an argument, the level never zero: consume it
    obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hL.lam_of_load ld12
    obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld47
    subst hc144
    have hlv := ih.get (.levelOps .level_is_not_zero) (by lt_calls) ev79 x_bl rfl ℓ hℓ
    obtain ⟨hr1, hm66⟩ := hlv
    subst m66
    have hnz : ℓ.isNeverZero = true := by
      by_contra hn
      have h10 : (SourceValue.field (1 : F)) = .field 0 := by rw [hr1, ite_eq_right hn]
      exact field_one_ne_zero h10
    subst hm124
    have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [x_a, acc]]) :=
      Heap.Extends.snoc _ _
    have hacc : c.tml d Γ (h ++ [.construct kexprListEnum "Cons" [x_a, acc]]) (A :: Cs)
        (.ptr (.enum kexprListEnum) h.length) := TmL.store_cons hA hCs
    obtain ⟨deep, cons, rest, Ts, D, hr, hBD, hlen, hD, hcons, hrest⟩ :=
      ih.get (.whnf .peel_beta) (by lt_calls) ev97 x_body x_rest _ rfl
        (good.sub fun x hx => by simp [hx]) d Γ (k + 1) B As' (A :: Cs)
        (Tm.mono ext hB) (tml_mono ext hAs') hacc
    refine ⟨deep, cons, rest, T :: Ts, D, hr, ?_, by simp; omega, ?_, ?_, ?_⟩
    · rw [bmeta_of_isNeverZero hnz, hBD]; rfl
    · have e : k + (T :: Ts).length = k + 1 + Ts.length := by
        simp only [List.length_cons]; omega
      rw [e]; exact hD
    · simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hcons
    · simpa using hrest
  · -- the level may be zero: stop
    obtain ⟨T, B, ℓ, rfl, -, -, hℓ⟩ := hL.lam_of_load ld12
    subst hc177
    obtain ⟨-, hm66⟩ := ih.get (.levelOps .level_is_not_zero)
      (by lt_calls) ev79 x_bl rfl ℓ hℓ
    subst m66
    subst he154 he176
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, hL, by simpa using hCs, by simpa using hAs⟩
  · -- no argument left: stop
    subst he190 he212
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, hL, by simpa using hCs, by simpa using hAs⟩
  · -- not a `λ`: stop
    subst he224 he246
    exact ⟨lam, acc, sp, [], _, rfl, rfl, by simp, hL, by simpa using hCs, by simpa using hAs⟩

/-! ## The normalizers -/

/-- `KernelWhnf::whnf_core` is `whnf_with_spine` at the empty spine. -/
theorem whnf_core_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_core" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨cs4, m26, hm34, ev6, hc45⟩ := Obs.«KernelWhnf::whnf_core».obs ev
  subst hc45 hm34
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  obtain ⟨E', hE', hred⟩ := ih.get (.whnf .whnf_with_spine) (by lt_calls) ev6 rc e _ types rfl
    (good.sub fun x hx => by simp [hx]) (RCRep.mono ext hrc) d Γ (types_mono ext htypes) E []
    (Tm.mono ext hE) (TmL.store_nil h)
  exact ⟨E', hE', hred⟩

/-- `KernelWhnf::whnf`: a value form is its own normal form; any other term is head-normalized
under the context cut to its loose bound variables (`ctx_trim`), which keeps the depth and the
ghost context. -/
theorem whnf_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  rcases Obs.«KernelWhnf::whnf».obs ev with
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
    exact ih.get (.whnf .whnf_core) (by lt_calls) ev131 rc e v134 rfl g3 (RCRep.mono ext hrc) d Γ
      htr E (Tm.mono ext hE)

/-- `KernelWhnf::whnf_spine` head-normalizes each argument. -/
theorem whnf_spine_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf_spine" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_spine c args h r h' calls := by
  intro rc sp types hargs good hrc d Γ htypes As hAs
  subst hargs
  rcases Obs.«KernelWhnf::whnf_spine».obs ev with
    ⟨ld12, he24, hm23, hc28⟩ |
    ⟨x_a, x_rest, v46, m47, cs57, v93, m102, cs110, ld12, ev59, he88, hm87, ev112, hc137⟩
  · obtain rfl := RepList.nil_of_load hAs ld12
    subst he24 hm23
    exact ⟨[], TmL.store_nil h, .nil⟩
  · obtain ⟨A, As', rfl, hA, hAs'⟩ := RepList.cons_of_load hAs ld12
    subst hc137 he88 hm87
    have g1 : Good c cs57 := good.sub fun x hx => by simp [hx]
    have g2 : Good c cs110 := good.sub fun x hx => by simp [hx]
    obtain ⟨A', hA', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev59 rc x_a types rfl g1 hrc d Γ
      htypes A hA
    have ext1 := ObsFn.heap_extends ev59
    obtain ⟨Bs, hBs, hreds⟩ := ih.get (.whnf .whnf_spine) (by lt_calls) ev112 rc x_rest types rfl g2
      (RCRep.mono ext1 hrc) d Γ (types_mono ext1 htypes) As' (tml_mono ext1 hAs')
    have ext2 := ObsFn.heap_extends ev112
    exact ⟨A' :: Bs, TmL.store_cons (Tm.mono ext2 hA') hBs, .cons hred hreds⟩

end IxVM.Refinement.Core
