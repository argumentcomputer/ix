/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Judgment
import Ix.Kernel.Model.LetRules
import Ix.Kernel.Model.Substitution
import Ix.Kernel.Model.Inductive.Telescope

/-! # Claims produced by the checker

The checker's functions return their results together with semantic claims,
erased at run time. Besides the ported `TypingClaim` and `ConversionClaim`:

* `FormedClaim`: the term is well denoted in every model, under every valid
  context valuation (hereditary validity of its annotations);
* `ConvClaim`: conditional conversion, equal interpretations wherever both
  sides are well denoted; the head-reduction based conversion check produces
  this form, and typing transports it (`TypingClaim.convF`);
* `ProofValueClaim`: a well-denoted term denotes the canonical proof point;
  a proposition-valued constant telescope and its applications can establish
  this without re-inferring their arguments;
* `ReductionClaim`: head reduction preserves interpretation and
  well-denotedness. Beta needs the argument's typing at the lambda's own
  domain (`ReductionClaim.beta`), which the checker re-establishes at each
  redex, except at a uniformly non-Prop binder (`ReductionClaim.betaNever`),
  where the redex's own well-denotedness suffices; delta and zeta need
  nothing.

Every rule below is proved from the ported model; none is assumed. -/

namespace Ix.Kernel

open Model Model.SetTheory Model.SetModel

universe u v

variable {β : Type u} {entries : Environment β} {Γ : Context β}

/-- `e` is well denoted in every model of `entries` under every valid valuation of `Γ`. -/
def FormedClaim (entries : Environment β) (Γ : Context β) (e : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env e

/-- Conditional conversion: `a` and `b` denote the same set wherever both are well denoted. -/
def ConvClaim (entries : Environment β) (Γ : Context β) (a b : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env a → WellDenoted constants levels env b →
        interp constants levels env a = interp constants levels env b

/-- A conditional proof value, without a claim about the term's inferred
type or the well-denotedness of unchecked arguments. -/
def ProofValueClaim (entries : Environment β) (Γ : Context β) (e : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env e → interp constants levels env e = pt

/-- Head reduction: `e'` denotes what `e` denotes and stays well denoted. -/
def ReductionClaim (entries : Environment β) (Γ : Context β) (e e' : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env e →
        interp constants levels env e = interp constants levels env e' ∧
          WellDenoted constants levels env e'

namespace Model.TypingClaim

/-- A `let` is typed by its substituted body: the value is typed at the
annotation, and the body with the value substituted is typed at `B`. This is
how the official kernel infers a `let`; the let variable is transparent. -/
theorem letSubst {t v b B : AExpr β} {l : VLevel}
    (ht : TypingClaim.{u,v} entries Γ t (.sort l)) (hv : TypingClaim.{u,v} entries Γ v t)
    (hb : TypingClaim.{u,v} entries Γ (b.inst v) B) :
    TypingClaim.{u,v} entries Γ (.letE t v b) B := by
  intro V _ constants hM levels env hΓ
  obtain ⟨htw, -, -⟩ := ht V constants hM levels env hΓ
  obtain ⟨hvw, -, -⟩ := hv V constants hM levels env hΓ
  obtain ⟨hbw, hBw, hbm⟩ := hb V constants hM levels env hΓ
  have hbw' := (wellDenoted_inst_iff b v constants levels env 0 (by simpa using hvw)).1 hbw
  refine ⟨⟨htw, hvw, by simpa [Valuation.skip_zero, Valuation.insert_zero] using hbw'⟩, hBw, ?_⟩
  simpa only [interp, interp_inst, Valuation.skip_zero, Valuation.insert_zero] using hbm

theorem formed {e A : AExpr β} (h : TypingClaim.{u,v} entries Γ e A) :
    FormedClaim.{u,v} entries Γ e :=
  fun V _ constants hM levels env hΓ => by
    obtain ⟨hA, -⟩ := h V constants hM levels env hΓ
    exact hA

theorem formedType {e A : AExpr β} (h : TypingClaim.{u,v} entries Γ e A) :
    FormedClaim.{u,v} entries Γ A :=
  fun V _ constants hM levels env hΓ => (h V constants hM levels env hΓ).2.1

/-- Transport along a conditional conversion to a formed target type. -/
theorem convF {e A B : AExpr β} (he : TypingClaim.{u,v} entries Γ e A)
    (hB : FormedClaim.{u,v} entries Γ B) (hc : ConvClaim.{u,v} entries Γ A B) :
    TypingClaim.{u,v} entries Γ e B := by
  intro V _ constants hM levels env hΓ
  obtain ⟨hew, hAw, hem⟩ := he V constants hM levels env hΓ
  have hBw := hB V constants hM levels env hΓ
  exact ⟨hew, hBw, hc V constants hM levels env hΓ hAw hBw ▸ hem⟩

theorem sortEquiv {e : AExpr β} {l l' : VLevel} (h : TypingClaim.{u,v} entries Γ e (.sort l))
    (hl : ∀ values, l.eval values = l'.eval values) : TypingClaim.{u,v} entries Γ e (.sort l') :=
  TypingClaim.conv h (TypingClaim.sort l') (ConversionClaim.sort hl)

end Model.TypingClaim

namespace FormedClaim

theorem sort (l : VLevel) : FormedClaim.{u,v} entries Γ (.sort l) :=
  fun _ _ _ _ _ _ _ => trivial

theorem appFn {f a : AExpr β} (h : FormedClaim.{u,v} entries Γ (.app f a)) :
    FormedClaim.{u,v} entries Γ f :=
  fun V _ constants hM levels env hΓ => (h V constants hM levels env hΓ).1

theorem domain {p : Certified.PropWhen} {A B : AExpr β}
    (h : FormedClaim.{u,v} entries Γ (.forallE p A B)) : FormedClaim.{u,v} entries Γ A :=
  fun V _ constants hM levels env hΓ => by
    obtain ⟨hA, -⟩ := h V constants hM levels env hΓ
    exact hA

theorem lamDomain {p : Certified.PropWhen} {A b : AExpr β}
    (h : FormedClaim.{u,v} entries Γ (.lam p A b)) : FormedClaim.{u,v} entries Γ A :=
  fun V _ constants hM levels env hΓ => by
    obtain ⟨hA, -⟩ := h V constants hM levels env hΓ
    exact hA

end FormedClaim

namespace Model.TypingClaim

/-- An already-formed application of a non-Prop function supplies its own
argument membership. Positive-regime products determine their domain, so no
second inference of the argument is needed to recover the ordinary claim. -/
theorem appFormedNever {f a D B : AExpr β}
    (hf : TypingClaim.{u,v} entries Γ f (.forallE .never D B))
    (hfa : FormedClaim.{u,v} entries Γ (.app f a)) :
    TypingClaim.{u,v} entries Γ (.app f a) (B.inst a) := by
  apply TypingClaim.app hf
  intro V _ constants hM levels env hΓ
  obtain ⟨_, hPi, hfm⟩ := hf V constants hM levels env hΓ
  obtain ⟨_, haw, k, A, C, hfk, ham, _⟩ := hfa V constants hM levels env hΓ
  change interp constants levels env f ∈ˢ
    piR 1 (interp constants levels env D)
      (fun x => interp constants levels (Valuation.cons x env) B) at hfm
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have hpt := eq_pt_of_mem_piR_zero hfk
    exact not_pt_mem_piR_pos (by decide : 1 ≠ 0) (hpt ▸ hfm)
  have hdom := piR_dom_unique (by decide : 1 ≠ 0) hk hfm hfk
  exact ⟨haw, hPi.1, hdom ▸ ham⟩

end Model.TypingClaim

namespace ProofValueClaim

/-- The outermost proposition-valued product already makes the constant a
proof, before any argument is applied. The universe arity is checked against
the entry because well-denotedness of a constant alone does not check it. -/
theorem const {r : ConstRef β} {entry : ConstantEntry β} {ls : List VLevel} {D B : AExpr β}
    {p : Certified.PropWhen}
    (hr : entries r = some entry) (hn : ls.length = entry.universes)
    (ht : entry.type = .forallE p D B) (hp : Certified.instCondition ls p = .always) :
    ProofValueClaim.{u,v} entries Γ (.const r ls) := by
  intro V _ constants hM levels env _ _
  have member := hM.member r entry hr (ls.map (VLevel.eval levels)) (by simpa using hn) env
  rw [ht] at member
  have hp0 : regime p (ls.map (VLevel.eval levels)) = 0 := by
    rw [← regime_instCondition, hp, regime_always]
  change constants r (ls.map (VLevel.eval levels)) = pt
  apply eq_pt_of_mem_piR_zero
  simpa only [interp, hp0] using member

/-- Proof-valued lambdas interpret as the proof point. This does not certify
their binder annotations: ordinary type checking still validates those. -/
theorem lam {D b : AExpr β} : ProofValueClaim.{u,v} entries Γ (.lam .always D b) := by
  intro V _ constants _ levels env _ _
  simp only [interp, regime_always, lamR_zero]

/-- Applying a proof value keeps the proof point. No argument inference is
needed: conversion remains conditional on the supplied term's validity. -/
theorem app {f a : AExpr β} (hf : ProofValueClaim.{u,v} entries Γ f) :
    ProofValueClaim.{u,v} entries Γ (.app f a) := by
  intro V _ constants hM levels env hΓ hw
  simp only [interp, hf V constants hM levels env hΓ hw.1, app_pt]

/-- Ordinary inference can supply the same proof-point witness when syntax
alone does not identify a proof, for example at a local variable. -/
theorem ofTyping {e A : AExpr β} (hA : TypingClaim.{u,v} entries Γ A (.sort .zero))
    (he : TypingClaim.{u,v} entries Γ e A) : ProofValueClaim.{u,v} entries Γ e := by
  intro V _ constants hM levels env hΓ _
  have hAm := (hA V constants hM levels env hΓ).2.2
  have hA0 : interp constants levels env A ∈ˢ (univZero : V) := by
    simpa only [interp, VLevel.eval, univ_zero] using hAm
  exact eq_pt_of_mem_univZero hA0 (he V constants hM levels env hΓ).2.2

end ProofValueClaim

namespace ConvClaim

theorem refl (a : AExpr β) : ConvClaim.{u,v} entries Γ a a :=
  fun _ _ _ _ _ _ _ _ _ => rfl

theorem symm {a b : AExpr β} (h : ConvClaim.{u,v} entries Γ a b) : ConvClaim.{u,v} entries Γ b a :=
  fun V _ constants hM levels env hΓ hb ha => (h V constants hM levels env hΓ ha hb).symm

theorem trans {a b c : AExpr β} (hb : FormedClaim.{u,v} entries Γ b)
    (h₁ : ConvClaim.{u,v} entries Γ a b) (h₂ : ConvClaim.{u,v} entries Γ b c) :
    ConvClaim.{u,v} entries Γ a c :=
  fun V _ constants hM levels env hΓ ha hc =>
    (h₁ V constants hM levels env hΓ ha (hb V constants hM levels env hΓ)).trans
      (h₂ V constants hM levels env hΓ (hb V constants hM levels env hΓ) hc)

theorem ofConversion {a b : AExpr β} (h : ConversionClaim.{u,v} entries Γ a b) :
    ConvClaim.{u,v} entries Γ a b :=
  fun V _ constants hM levels env hΓ _ _ => h V constants hM levels env hΓ

theorem ofReduction {a b : AExpr β} (h : ReductionClaim.{u,v} entries Γ a b) :
    ConvClaim.{u,v} entries Γ a b :=
  fun V _ constants hM levels env hΓ ha _ => (h V constants hM levels env hΓ ha).1

/-- Compare after reducing both sides. -/
theorem ofReductions {a a' b b' : AExpr β} (ha : ReductionClaim.{u,v} entries Γ a a')
    (hb : ReductionClaim.{u,v} entries Γ b b') (h : ConvClaim.{u,v} entries Γ a' b') :
    ConvClaim.{u,v} entries Γ a b := by
  intro V _ constants hM levels env hΓ haw hbw
  obtain ⟨ea, haw'⟩ := ha V constants hM levels env hΓ haw
  obtain ⟨eb, hbw'⟩ := hb V constants hM levels env hΓ hbw
  exact ea.trans ((h V constants hM levels env hΓ haw' hbw').trans eb.symm)

theorem sort {l l' : VLevel} (h : ∀ values, l.eval values = l'.eval values) :
    ConvClaim.{u,v} entries Γ (.sort l) (.sort l') :=
  ofConversion (ConversionClaim.sort h)

theorem const {r : ConstRef β} {ls ls' : List VLevel}
    (h : ∀ values, ls.map (VLevel.eval values) = ls'.map (VLevel.eval values)) :
    ConvClaim.{u,v} entries Γ (.const r ls) (.const r ls') := by
  intro V _ constants hM levels env hΓ _ _
  simp only [interp, h levels]

theorem app {f f' a a' : AExpr β} (hf : ConvClaim.{u,v} entries Γ f f')
    (ha : ConvClaim.{u,v} entries Γ a a') :
    ConvClaim.{u,v} entries Γ (.app f a) (.app f' a') := by
  intro V _ constants hM levels env hΓ h₁ h₂
  obtain ⟨hfw, haw, -⟩ := h₁
  obtain ⟨hf'w, ha'w, -⟩ := h₂
  simp only [interp, hf V constants hM levels env hΓ hfw hf'w, ha V constants hM levels env hΓ haw ha'w]

theorem proj {r : ConstRef β} {i : Nat} {a b : AExpr β} (h : ConvClaim.{u,v} entries Γ a b) :
    ConvClaim.{u,v} entries Γ (.proj r i a) (.proj r i b) := by
  intro V _ constants hM levels env hΓ ha hb
  simp only [interp, h V constants hM levels env hΓ ha hb]

theorem lam {p : Certified.PropWhen} {D D' b b' : AExpr β} (hD : ConvClaim.{u,v} entries Γ D D')
    (hb : ConvClaim.{u,v} entries (Γ.push D) b b') :
    ConvClaim.{u,v} entries Γ (.lam p D b) (.lam p D' b') := by
  intro V _ constants hM levels env hΓ h₁ h₂
  obtain ⟨hDw, hbw, -⟩ := h₁
  obtain ⟨hD'w, hb'w, -⟩ := h₂
  have hDD := hD V constants hM levels env hΓ hDw hD'w
  simp only [interp]
  rw [← hDD]
  apply lamR_congr
  intro x hx
  exact hb V constants hM levels (Valuation.cons x env) (hΓ.push hDw hx) (hbw x hx)
    (hb'w x (by rw [← hDD]; exact hx))

theorem forallE {p : Certified.PropWhen} {D D' B B' : AExpr β} (hD : ConvClaim.{u,v} entries Γ D D')
    (hB : ConvClaim.{u,v} entries (Γ.push D) B B') :
    ConvClaim.{u,v} entries Γ (.forallE p D B) (.forallE p D' B') := by
  intro V _ constants hM levels env hΓ h₁ h₂
  obtain ⟨hDw, hBw, -⟩ := h₁
  obtain ⟨hD'w, hB'w, -⟩ := h₂
  have hDD := hD V constants hM levels env hΓ hDw hD'w
  simp only [interp]
  rw [← hDD]
  apply piR_congr
  intro x hx
  exact hB V constants hM levels (Valuation.cons x env) (hΓ.push hDw hx) (hBw x hx)
    (hB'w x (by rw [← hDD]; exact hx))

theorem proofIrrel {A a b : AExpr β} (hA : TypingClaim.{u,v} entries Γ A (.sort .zero))
    (ha : TypingClaim.{u,v} entries Γ a A) (hb : TypingClaim.{u,v} entries Γ b A) :
    ConvClaim.{u,v} entries Γ a b :=
  ofConversion (ConversionClaim.proofIrrel hA ha hb)

theorem ofProofValues {a b : AExpr β} (ha : ProofValueClaim.{u,v} entries Γ a)
    (hb : ProofValueClaim.{u,v} entries Γ b) : ConvClaim.{u,v} entries Γ a b := by
  intro V _ constants hM levels env hΓ haw hbw
  exact (ha V constants hM levels env hΓ haw).trans (hb V constants hM levels env hΓ hbw).symm

/-- Proofs of proposition-valued types have the same interpretation even
when establishing conversion of their types would require further search.
Both types must independently be proved to inhabit `Prop`. -/
theorem proofIrrelHet {A B a b : AExpr β}
    (hA : TypingClaim.{u,v} entries Γ A (.sort .zero))
    (hB : TypingClaim.{u,v} entries Γ B (.sort .zero))
    (ha : TypingClaim.{u,v} entries Γ a A) (hb : TypingClaim.{u,v} entries Γ b B) :
    ConvClaim.{u,v} entries Γ a b := by
  intro V _ constants hM levels env hΓ _ _
  have hAm := (hA V constants hM levels env hΓ).2.2
  have hBm := (hB V constants hM levels env hΓ).2.2
  have ham := (ha V constants hM levels env hΓ).2.2
  have hbm := (hb V constants hM levels env hΓ).2.2
  have hA0 : interp constants levels env A ∈ˢ (univZero : V) := by
    simpa only [interp, VLevel.eval, univ_zero] using hAm
  have hB0 : interp constants levels env B ∈ˢ (univZero : V) := by
    simpa only [interp, VLevel.eval, univ_zero] using hBm
  exact (eq_pt_of_mem_univZero hA0 ham).trans (eq_pt_of_mem_univZero hB0 hbm).symm

end ConvClaim

namespace ReductionClaim

theorem refl (e : AExpr β) : ReductionClaim.{u,v} entries Γ e e :=
  fun _ _ _ _ _ _ _ he => ⟨rfl, he⟩

theorem trans {a b c : AExpr β} (h₁ : ReductionClaim.{u,v} entries Γ a b)
    (h₂ : ReductionClaim.{u,v} entries Γ b c) : ReductionClaim.{u,v} entries Γ a c := by
  intro V _ constants hM levels env hΓ ha
  obtain ⟨e₁, hb⟩ := h₁ V constants hM levels env hΓ ha
  obtain ⟨e₂, hc⟩ := h₂ V constants hM levels env hΓ hb
  exact ⟨e₁.trans e₂, hc⟩

theorem formed {e e' : AExpr β} (h : ReductionClaim.{u,v} entries Γ e e')
    (he : FormedClaim.{u,v} entries Γ e) : FormedClaim.{u,v} entries Γ e' :=
  fun V _ constants hM levels env hΓ => (h V constants hM levels env hΓ (he V constants hM levels env hΓ)).2

/-- Reduce the head of an application. -/
theorem appHead {f f' a : AExpr β} (h : ReductionClaim.{u,v} entries Γ f f') :
    ReductionClaim.{u,v} entries Γ (.app f a) (.app f' a) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨hfw, haw, v, A, B, hfm, ham, hB⟩ := hw
  obtain ⟨eq, hf'w⟩ := h V constants hM levels env hΓ hfw
  exact ⟨by simp only [interp, eq], hf'w, haw, v, A, B, eq ▸ hfm, ham, hB⟩

/-- Typed beta: the argument must be typed at the lambda's own domain. -/
theorem beta {p : Certified.PropWhen} {D b a A' : AExpr β} (ha : TypingClaim.{u,v} entries Γ a A')
    (hc : ConvClaim.{u,v} entries Γ A' D) :
    ReductionClaim.{u,v} entries Γ (.app (.lam p D b) a) (b.inst a) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨hlw, haw, -⟩ := hw
  obtain ⟨-, hA'w, ham⟩ := ha V constants hM levels env hΓ
  have hDw : WellDenoted constants levels env D := And.left hlw
  have ham' : interp constants levels env a ∈ˢ interp constants levels env D :=
    hc V constants hM levels env hΓ hA'w hDw ▸ ham
  obtain ⟨hw', eq⟩ := wellDenoted_beta hlw haw ham'
  exact ⟨eq, hw'⟩

/-- Beta at a uniformly non-Prop binder needs no premise about the argument:
where the redex is well denoted, the function's domain is the lambda's own
domain (`piR_dom_unique` for a nonzero regime), so the argument is a member of
it. The argument follows con-leche's graph-regime domain uniqueness proof
(`ConLeche/Model/Rules/RedSoundKit.lean`, `betaDomPos`, revision
`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`, Apache-2.0), first checked as
`plans/review/BetaNever.lean`. -/
theorem betaNever {D b a : AExpr β} :
    ReductionClaim.{u,v} entries Γ (.app (.lam .never D b) a) (b.inst a) := by
  intro V _ constants _ levels env _ hw
  obtain ⟨hlw, haw, k, A, B, hf, ham, _⟩ := hw
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have hpt := eq_pt_of_mem_piR_zero hf
    change lamR 1 (interp constants levels env D)
      (fun x => interp constants levels (Valuation.cons x env) b) = pt at hpt
    exact lamR_ne_pt (by decide : 1 ≠ 0) hpt
  have hlam := hlw
  obtain ⟨_, _, _, C, _, hC⟩ := hlam
  have hown : interp constants levels env (.lam .never D b) ∈ˢ
      piR 1 (interp constants levels env D) C := by
    change lamR 1 _ _ ∈ˢ piR 1 _ C
    exact lamR_mem fun x hx => (hC x hx).1
  have hdom := piR_dom_unique (by decide : 1 ≠ 0) hk hown hf
  have haD : interp constants levels env a ∈ˢ interp constants levels env D := by
    rw [hdom]
    exact ham
  obtain ⟨formed, equation⟩ := wellDenoted_beta hlw haw haD
  exact ⟨equation, formed⟩

theorem delta {r : ConstRef β} {entry : ConstantEntry β} {body : AExpr β} {ls : List VLevel}
    (h : entries r = some entry) (hb : entry.body = some body) (hn : ls.length = entry.universes) :
    ReductionClaim.{u,v} entries Γ (.const r ls) (body.instL ls) := by
  intro V _ constants hM levels env hΓ _
  refine ⟨ConversionClaim.delta h hb hn V constants hM levels env hΓ, ?_⟩
  rw [wellDenoted_instL]
  exact hM.bodyValid r entry h body hb _ (by simpa using hn) env

theorem zeta {t v b : AExpr β} : ReductionClaim.{u,v} entries Γ (.letE t v b) (b.inst v) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨-, hvw, hbw⟩ := hw
  refine ⟨ConversionClaim.zeta t v b V constants hM levels env hΓ, ?_⟩
  apply wellDenoted_inst
  · simpa using hvw
  · simpa using hbw

end ReductionClaim

end Ix.Kernel

namespace Ix.Kernel.ConvClaim

open Model Model.SetTheory Model.SetModel

universe u v

variable {β : Type u} {entries : Model.Environment β} {Γ : Model.Context β}

/-- Eta: a lambda whose body is the function applied to the bound variable is
the function. The function is typed at a Pi whose domain converts to the
lambda's domain; the body comparison is under the lambda's domain. -/
theorem eta {p : Certified.PropWhen} {D D'' B'' e g : AExpr β}
    (hg : TypingClaim.{u,v} entries Γ g (.forallE p D'' B''))
    (hD : ConvClaim.{u,v} entries Γ D'' D)
    (he : ConvClaim.{u,v} entries (Γ.push D) e (.app (g.liftN 1) (.bvar 0))) :
    ConvClaim.{u,v} entries Γ (.lam p D e) g := by
  intro V _ constants hM levels env hΓ h₁ h₂
  obtain ⟨hDw, hew, -⟩ := h₁
  obtain ⟨hgw, hPw, hgm⟩ := hg V constants hM levels env hΓ
  obtain ⟨hD''w, -, vB, hz, hB''m⟩ := hPw
  have hDD := hD V constants hM levels env hΓ hD''w hDw
  simp only [interp] at hgm ⊢
  rw [hDD] at hgm hB''m
  rw [← lamR_eta hgm]
  apply lamR_congr
  intro x hx
  have hbody : WellDenoted constants levels (Valuation.cons x env) (.app (g.liftN 1) (.bvar 0)) := by
    refine ⟨(wellDenoted_liftN g constants levels _ 1 0).mpr ?_, trivial, vB,
      interp constants levels env D, fun y => interp constants levels (Valuation.cons y env) B'', ?_, hx, hB''m⟩
    · simpa only [Valuation.skip_one_cons] using hgw
    · rw [interp_liftN, Valuation.skip_one_cons, ← piR_zero_agree hz (fun _ _ => rfl)]
      exact hgm
  have := he V constants hM levels (Valuation.cons x env) (hΓ.push hDw hx) (hew x hx) hbody
  simpa only [interp, interp_liftN, Valuation.skip_one_cons, Valuation.cons_zero] using this

end Ix.Kernel.ConvClaim

namespace Ix.Kernel

open Model

universe u v

variable {β : Type u} [DecidableEq β] {entries : Environment β} {Γ : Context β}

omit [DecidableEq β] in
/-- Congruence of a conversion under an argument spine. -/
theorem Model.ConversionClaim.appN {f f' : AExpr β} (h : ConversionClaim.{u,v} entries Γ f f') :
    ∀ args : List (AExpr β), ConversionClaim.{u,v} entries Γ (AExpr.appN f args) (AExpr.appN f' args)
  | [] => h
  | a :: args => ConversionClaim.appN (ConversionClaim.app h (ConversionClaim.refl a)) args

omit [DecidableEq β] in
/-- Reduce the head of an application spine: `ReductionClaim.appHead` folded
over the arguments, first argument innermost. -/
theorem ReductionClaim.appHeadN {f f' : AExpr β} (h : ReductionClaim.{u,v} entries Γ f f') :
    ∀ args : List (AExpr β), ReductionClaim.{u,v} entries Γ (AExpr.appN f args) (AExpr.appN f' args)
  | [] => h
  | a :: args => ReductionClaim.appHeadN (ReductionClaim.appHead (a := a) h) args

omit [DecidableEq β] in
/-- Pairwise conversion of two argument lists of the same length. -/
def ConvClaim.Args (entries : Environment β) (Γ : Context β) :
    List (AExpr β) → List (AExpr β) → Prop
  | [], [] => True
  | x :: xs, y :: ys => ConvClaim.{u,v} entries Γ x y ∧ ConvClaim.Args entries Γ xs ys
  | _, _ => False

omit [DecidableEq β] in
/-- Application congruence along two spines: `ConvClaim.app` folded over
pairwise converting argument lists. -/
theorem ConvClaim.appN {f g : AExpr β} (h : ConvClaim.{u,v} entries Γ f g) :
    ∀ {xs ys : List (AExpr β)}, ConvClaim.Args.{u,v} entries Γ xs ys →
      ConvClaim.{u,v} entries Γ (AExpr.appN f xs) (AExpr.appN g ys)
  | [], [], _ => h
  | _ :: _, _ :: _, ⟨hxy, hs⟩ => ConvClaim.appN (ConvClaim.app h hxy) hs
  | [], _ :: _, hs | _ :: _, [], hs => hs.elim

omit [DecidableEq β] in
/-- Iota: the target converts to the typed instance of a rule's left side,
which equals the typed instance of its right side. -/
theorem ReductionClaim.iota {e l r : AExpr β} (hc : ConvClaim.{u,v} entries Γ e l)
    (hl : FormedClaim.{u,v} entries Γ l) (he : ConversionClaim.{u,v} entries Γ l r)
    (hr : FormedClaim.{u,v} entries Γ r) : ReductionClaim.{u,v} entries Γ e r := by
  intro V _ constants hM levels env hΓ hwe
  exact ⟨(hc V constants hM levels env hΓ hwe (hl V constants hM levels env hΓ)).trans
    (he V constants hM levels env hΓ), hr V constants hM levels env hΓ⟩

end Ix.Kernel

namespace Ix.Kernel

open Model

universe u v

variable {β : Type u} [DecidableEq β] {entries : Environment β} {Γ : Context β}

omit [DecidableEq β] in
theorem FormedClaim.natLit (f : ConstRef β) (n : Nat) :
    FormedClaim.{u,v} entries Γ (.natLit f n) := fun _ _ _ _ _ _ _ => trivial

omit [DecidableEq β] in
theorem FormedClaim.const (r : ConstRef β) (ls : List VLevel) :
    FormedClaim.{u,v} entries Γ (.const r ls) := fun _ _ _ _ _ _ _ => trivial

omit [DecidableEq β] in
/-- Literals of one value denote the same numeral whatever family they name. -/
theorem ConvClaim.natLit (f g : ConstRef β) (n : Nat) :
    ConvClaim.{u,v} entries Γ (.natLit f n) (.natLit g n) := fun _ _ _ _ _ _ _ _ _ => rfl

omit [DecidableEq β] in
theorem ConvClaim.natZero {f r zero succ : ConstRef β} {entry : ConstantEntry β}
    (h : entries r = some entry) (hf : .natural zero succ ∈ entry.facts) (hn : entry.universes = 0) :
    ConvClaim.{u,v} entries Γ (.natLit f 0) (.const zero []) :=
  ConvClaim.ofConversion (ConversionClaim.natZero h hf hn)

omit [DecidableEq β] in
theorem ConvClaim.natSucc {f r zero succ : ConstRef β} {entry : ConstantEntry β}
    (h : entries r = some entry) (hf : .natural zero succ ∈ entry.facts) (hn : entry.universes = 0) (n : Nat) :
    ConvClaim.{u,v} entries Γ (.natLit f (n + 1)) (.app (.const succ []) (.natLit f n)) :=
  ConvClaim.ofConversion (ConversionClaim.natSucc h hf hn n)

omit [DecidableEq β] in
/-- An application of the successor to a literal is well denoted. -/
theorem FormedClaim.natSucc {f r zero succ : ConstRef β} {entry : ConstantEntry β}
    (h : entries r = some entry) (hf : .natural zero succ ∈ entry.facts) (hn : entry.universes = 0) (n : Nat) :
    FormedClaim.{u,v} entries Γ (.app (.const succ []) (.natLit f n)) := by
  intro V _ constants hM levels env _
  have hh := hM.factMeaning r entry h (.natural zero succ) hf [] (by simpa using hn.symm) env
  refine ⟨trivial, trivial, ?_⟩
  simpa only [interp, List.map_nil] using hh.2.succApp n

omit [DecidableEq β] in
/-- A binary operation's constant applied to arguments that reduce to literals
reduces to the literal of its value. -/
theorem ReductionClaim.natOp {r f g : ConstRef β} {entry : ConstantEntry β} {op : NatOp}
    (h : entries r = some entry) (hf : .natOp op ∈ entry.facts) (hn : entry.universes = 0)
    (hbin : op ≠ .pred) {a b : AExpr β} {x y : Nat}
    (ha : ReductionClaim.{u,v} entries Γ a (.natLit f x))
    (hb : ReductionClaim.{u,v} entries Γ b (.natLit g y)) :
    ReductionClaim.{u,v} entries Γ (.app (.app (.const r []) a) b) (.natLit f (op.eval x y)) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨⟨-, hwa, -⟩, hwb, -⟩ := hw
  have hm := hM.factMeaning r entry h (.natOp op) hf [] (by simpa using hn.symm) env
  have hx := (ha V constants hM levels env hΓ hwa).1
  have hy := (hb V constants hM levels env hΓ hwb).1
  refine ⟨?_, trivial⟩
  simp only [interp, List.map_nil] at hx hy ⊢
  rw [hx, hy]
  cases op with
  | pred => exact absurd rfl hbin
  | _ => exact hm.2 x y

omit [DecidableEq β] in
/-- A test's constant applied to arguments that reduce to literals reduces to
the outcome constant of its value. -/
theorem ReductionClaim.natTest {r f g yes no : ConstRef β} {entry : ConstantEntry β}
    {test : NatTest} (h : entries r = some entry) (hf : .natTest test yes no ∈ entry.facts)
    (hn : entry.universes = 0) {a b : AExpr β} {x y : Nat}
    (ha : ReductionClaim.{u,v} entries Γ a (.natLit f x))
    (hb : ReductionClaim.{u,v} entries Γ b (.natLit g y)) :
    ReductionClaim.{u,v} entries Γ (.app (.app (.const r []) a) b)
      (.const (if test.eval x y then yes else no) []) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨⟨-, hwa, -⟩, hwb, -⟩ := hw
  have hm := hM.factMeaning r entry h (.natTest test yes no) hf [] (by simpa using hn.symm) env
  have hx := (ha V constants hM levels env hΓ hwa).1
  have hy := (hb V constants hM levels env hΓ hwb).1
  refine ⟨?_, trivial⟩
  simp only [interp, List.map_nil] at hx hy ⊢
  rw [hx, hy, hm.2 x y]
  split <;> rfl

omit [DecidableEq β] in
/-- The predecessor's constant applied to an argument that reduces to a
literal reduces to the literal of its value. -/
theorem ReductionClaim.natPred {r f : ConstRef β} {entry : ConstantEntry β}
    (h : entries r = some entry) (hf : .natOp .pred ∈ entry.facts) (hn : entry.universes = 0)
    {a : AExpr β} {x : Nat} (ha : ReductionClaim.{u,v} entries Γ a (.natLit f x)) :
    ReductionClaim.{u,v} entries Γ (.app (.const r []) a) (.natLit f (NatOp.pred.eval x 0)) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨-, hwa, -⟩ := hw
  have hm := hM.factMeaning r entry h (.natOp .pred) hf [] (by simpa using hn.symm) env
  have hx := (ha V constants hM levels env hΓ hwa).1
  refine ⟨?_, trivial⟩
  simp only [interp, List.map_nil] at hx ⊢
  rw [hx]
  exact hm.2 x 0

end Ix.Kernel

/-! ## Infer-only claims for rule steps (review M3)

A rule step (ι, projection, structure η, quotient) fires on a target whose
well-denotedness is the premise of the claim it produces (`ReductionClaim`,
`ConvClaim`). Its arguments are read off that target's spine, so where the
function they are applied to has a uniformly non-Prop binder, domain
determination (`piR_dom_unique`) recovers each argument's membership from the
target's own application nodes and no inference is needed. At any other
binder the argument is inferred and its type converted to the domain: this is
the possibly-Prop residue, which cannot be removed (con-leche task #73).

The rule's endpoints are applied to those same arguments, so their
applications are not themselves known to be well denoted; every claim below is
therefore relative to a witness `w`, the target, whose well-denotedness is the
premise. With `w = e`, `IOClaim w e A` is typing conditional on the term's
own well-denotedness. The spine form follows con-leche's gated iota
certificates (`iotaCertsG`, `certsG_fit`, tasks #49 and #71). -/

namespace Ix.Kernel

open Model Model.SetTheory Model.SetModel

universe u v

variable {β : Type u} {entries : Environment β} {Γ : Context β}

theorem Model.wellDenoted_appN_head {V : Type v} [SetTheory V] {constants : Assignment β V}
    {levels : List Nat} {env : Nat → V} :
    ∀ {f : AExpr β} {args : List (AExpr β)},
      WellDenoted constants levels env (f.appN args) → WellDenoted constants levels env f
  | _, [], h => h
  | f, a :: args, h => (wellDenoted_appN_head (f := .app f a) (args := args) h).1

theorem Model.interp_appN_congr {V : Type v} [SetTheory V] {constants : Assignment β V}
    {levels : List Nat} {env : Nat → V} :
    ∀ {f f' : AExpr β} (args : List (AExpr β)),
      interp constants levels env f = interp constants levels env f' →
        interp constants levels env (f.appN args) = interp constants levels env (f'.appN args)
  | _, _, [], h => h
  | f, f', a :: args, h =>
    interp_appN_congr (f := .app f a) (f' := .app f' a) args (by simp only [interp, h])

/-- Wherever `w` is well denoted, so is `e`. -/
def SupportClaim (entries : Environment β) (Γ : Context β) (w e : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env w → WellDenoted constants levels env e

/-- Infer-only typing: wherever the witness `w` is well denoted, `e` and `A`
are well denoted and `e` denotes a member of `A`. -/
def IOClaim (entries : Environment β) (Γ : Context β) (w e A : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env w →
        WellDenoted constants levels env e ∧ WellDenoted constants levels env A ∧
          interp constants levels env e ∈ˢ interp constants levels env A

/-- Reduction under a witness: wherever `w` is well denoted, `e` denotes what
`e'` denotes and `e'` is well denoted. -/
def IOReductionClaim (entries : Environment β) (Γ : Context β) (w e e' : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env w →
        interp constants levels env e = interp constants levels env e' ∧
          WellDenoted constants levels env e'

namespace SupportClaim

theorem refl (w : AExpr β) : SupportClaim.{u,v} entries Γ w w := fun _ _ _ _ _ _ _ h => h

theorem ofFormed {w e : AExpr β} (h : FormedClaim.{u,v} entries Γ e) :
    SupportClaim.{u,v} entries Γ w e :=
  fun V _ constants hM levels env hΓ _ => h V constants hM levels env hΓ

theorem ofReduction {w e e' : AExpr β} (hs : SupportClaim.{u,v} entries Γ w e)
    (h : ReductionClaim.{u,v} entries Γ e e') : SupportClaim.{u,v} entries Γ w e' :=
  fun V _ constants hM levels env hΓ hw =>
    (h V constants hM levels env hΓ (hs V constants hM levels env hΓ hw)).2

theorem appFn {w f a : AExpr β} (h : SupportClaim.{u,v} entries Γ w (.app f a)) :
    SupportClaim.{u,v} entries Γ w f :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).1

theorem appArg {w f a : AExpr β} (h : SupportClaim.{u,v} entries Γ w (.app f a)) :
    SupportClaim.{u,v} entries Γ w a :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).2.1

theorem appNHead {w f : AExpr β} {args : List (AExpr β)}
    (h : SupportClaim.{u,v} entries Γ w (f.appN args)) : SupportClaim.{u,v} entries Γ w f :=
  fun V _ constants hM levels env hΓ hw => wellDenoted_appN_head (h V constants hM levels env hΓ hw)

theorem appNPrefix {w f : AExpr β} {xs ys : List (AExpr β)}
    (h : SupportClaim.{u,v} entries Γ w (f.appN (xs ++ ys))) :
    SupportClaim.{u,v} entries Γ w (f.appN xs) := by
  rw [AExpr.appN_append] at h
  exact h.appNHead

theorem proj {w x : AExpr β} {r : ConstRef β} {i : Nat}
    (h : SupportClaim.{u,v} entries Γ w (.proj r i x)) : SupportClaim.{u,v} entries Γ w x :=
  fun V _ constants hM levels env hΓ hw => h V constants hM levels env hΓ hw

theorem lamDomain {w D b : AExpr β} {p : Certified.PropWhen}
    (h : SupportClaim.{u,v} entries Γ w (.lam p D b)) : SupportClaim.{u,v} entries Γ w D :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).1

end SupportClaim

namespace IOClaim

theorem ofTyping {w e A : AExpr β} (h : TypingClaim.{u,v} entries Γ e A) :
    IOClaim.{u,v} entries Γ w e A :=
  fun V _ constants hM levels env hΓ _ => h V constants hM levels env hΓ

theorem support {w e A : AExpr β} (h : IOClaim.{u,v} entries Γ w e A) :
    SupportClaim.{u,v} entries Γ w e :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).1

/-- A witness that is well denoted everywhere makes infer-only typing ordinary typing. -/
theorem typing {w e A : AExpr β} (h : IOClaim.{u,v} entries Γ w e A)
    (hw : FormedClaim.{u,v} entries Γ w) : TypingClaim.{u,v} entries Γ e A :=
  fun V _ constants hM levels env hΓ => h V constants hM levels env hΓ (hw V constants hM levels env hΓ)

theorem domain {w f D B : AExpr β} {p : Certified.PropWhen}
    (h : IOClaim.{u,v} entries Γ w f (.forallE p D B)) : SupportClaim.{u,v} entries Γ w D :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).2.1.1

/-- Application, as `TypingClaim.app`, under the witness. -/
theorem app {w f a D B : AExpr β} {p : Certified.PropWhen}
    (hf : IOClaim.{u,v} entries Γ w f (.forallE p D B)) (ha : IOClaim.{u,v} entries Γ w a D) :
    IOClaim.{u,v} entries Γ w (.app f a) (B.inst a) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨hfw, hpw, hfm⟩ := hf V constants hM levels env hΓ hw
  obtain ⟨haw, _, ham⟩ := ha V constants hM levels env hΓ hw
  obtain ⟨_, hBw, bv, hz, hBm⟩ := hpw
  have hfm' : interp constants levels env f ∈ˢ
      piR bv (interp constants levels env D)
        (fun x => interp constants levels (Valuation.cons x env) B) := by
    simpa only [interp, piR_zero_agree hz (fun _ _ => rfl)] using hfm
  refine ⟨⟨hfw, haw, bv, interp constants levels env D,
    (fun x => interp constants levels (Valuation.cons x env) B), hfm', ham, hBm⟩, ?_, ?_⟩
  · apply wellDenoted_inst
    · simpa using haw
    · simpa using hBw _ ham
  · simp only [interp_inst, Valuation.skip_zero, Valuation.insert_zero]
    apply app_mem_piR hfm' ham
    intro hzero x hx
    simpa only [hzero, univ_zero] using hBm x hx

/-- Domain determination at a uniformly non-Prop binder: where the application
node is well denoted, its argument lies in the function's own domain, because
the function is a graph over that domain (`piR_dom_unique`); a zero-regime
slot would make the function the proof point, which no positive-regime
product contains. This is `TypingClaim.appFormedNever` under a witness. -/
theorem argNever {w f a D B : AExpr β}
    (hf : IOClaim.{u,v} entries Γ w f (.forallE .never D B))
    (hs : SupportClaim.{u,v} entries Γ w (.app f a)) : IOClaim.{u,v} entries Γ w a D := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨_, hPi, hfm⟩ := hf V constants hM levels env hΓ hw
  obtain ⟨_, haw, k, A, C, hfk, ham, _⟩ := hs V constants hM levels env hΓ hw
  change interp constants levels env f ∈ˢ
    piR 1 (interp constants levels env D)
      (fun x => interp constants levels (Valuation.cons x env) B) at hfm
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have hpt := eq_pt_of_mem_piR_zero hfk
    exact not_pt_mem_piR_pos (by decide : 1 ≠ 0) (hpt ▸ hfm)
  have hdom := piR_dom_unique (by decide : 1 ≠ 0) hk hfm hfk
  exact ⟨haw, hPi.1, hdom ▸ ham⟩

/-- An application at a uniformly non-Prop binder, typed without inferring
its argument. -/
theorem appNever {w f a D B : AExpr β}
    (hf : IOClaim.{u,v} entries Γ w f (.forallE .never D B))
    (hs : SupportClaim.{u,v} entries Γ w (.app f a)) :
    IOClaim.{u,v} entries Γ w (.app f a) (B.inst a) :=
  hf.app (hf.argNever hs)

/-- The residue: an inferred argument whose type converts to a domain that is
well denoted wherever the witness is. -/
theorem checked {w a A' D : AExpr β} (ha : TypingClaim.{u,v} entries Γ a A')
    (hc : ConvClaim.{u,v} entries Γ A' D) (hD : SupportClaim.{u,v} entries Γ w D) :
    IOClaim.{u,v} entries Γ w a D := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨haw, hA'w, ham⟩ := ha V constants hM levels env hΓ
  have hDw := hD V constants hM levels env hΓ hw
  exact ⟨haw, hDw, hc V constants hM levels env hΓ hA'w hDw ▸ ham⟩

/-- An application at any other binder: the argument is inferred and its type
converted to the domain. -/
theorem appChecked {w f a A' D B : AExpr β} {p : Certified.PropWhen}
    (hf : IOClaim.{u,v} entries Γ w f (.forallE p D B)) (ha : TypingClaim.{u,v} entries Γ a A')
    (hc : ConvClaim.{u,v} entries Γ A' D) : IOClaim.{u,v} entries Γ w (.app f a) (B.inst a) :=
  hf.app (checked ha hc hf.domain)

end IOClaim

namespace IOReductionClaim

theorem refl {w e : AExpr β} (h : SupportClaim.{u,v} entries Γ w e) :
    IOReductionClaim.{u,v} entries Γ w e e :=
  fun V _ constants hM levels env hΓ hw => ⟨rfl, h V constants hM levels env hΓ hw⟩

theorem support {w e e' : AExpr β} (h : IOReductionClaim.{u,v} entries Γ w e e') :
    SupportClaim.{u,v} entries Γ w e' :=
  fun V _ constants hM levels env hΓ hw => (h V constants hM levels env hΓ hw).2

/-- Beta at an argument that fits the lambda's own domain under the witness. -/
theorem beta {w D b a : AExpr β} {p : Certified.PropWhen}
    (hl : SupportClaim.{u,v} entries Γ w (.lam p D b)) (ha : IOClaim.{u,v} entries Γ w a D) :
    IOReductionClaim.{u,v} entries Γ w (.app (.lam p D b) a) (b.inst a) := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨haw, -, ham⟩ := ha V constants hM levels env hΓ hw
  obtain ⟨hw', eq⟩ := wellDenoted_beta (hl V constants hM levels env hΓ hw) haw ham
  exact ⟨eq, hw'⟩

/-- Reduce the head of an application spine, then the spine it leaves. -/
theorem appN {w f f' r : AExpr β} (args : List (AExpr β))
    (h₁ : IOReductionClaim.{u,v} entries Γ w f f')
    (h₂ : IOReductionClaim.{u,v} entries Γ w (f'.appN args) r) :
    IOReductionClaim.{u,v} entries Γ w (f.appN args) r := by
  intro V _ constants hM levels env hΓ hw
  obtain ⟨e₁, -⟩ := h₁ V constants hM levels env hΓ hw
  obtain ⟨e₂, hr⟩ := h₂ V constants hM levels env hΓ hw
  exact ⟨(interp_appN_congr args e₁).trans e₂, hr⟩

theorem append {w f f' r : AExpr β} {xs ys : List (AExpr β)}
    (h₁ : IOReductionClaim.{u,v} entries Γ w (f.appN xs) f')
    (h₂ : IOReductionClaim.{u,v} entries Γ w (f'.appN ys) r) :
    IOReductionClaim.{u,v} entries Γ w (f.appN (xs ++ ys)) r := by
  rw [AExpr.appN_append]
  exact appN ys h₁ h₂

end IOReductionClaim

/-- Iota under the target's own well-denotedness: the target converts to the
left instance, the rule's equation relates the unreduced applications of its
endpoints, and both endpoint applications reduce, wherever the target is well
denoted, to their instances. Same conclusion as `ReductionClaim.iota`, whose
formedness premises are unconditional. -/
theorem ReductionClaim.iotaIO {e l L R r : AExpr β} (hc : ConvClaim.{u,v} entries Γ e l)
    (hl : IOReductionClaim.{u,v} entries Γ e L l) (heq : ConversionClaim.{u,v} entries Γ L R)
    (hr : IOReductionClaim.{u,v} entries Γ e R r) : ReductionClaim.{u,v} entries Γ e r := by
  intro V _ constants hM levels env hΓ hwe
  obtain ⟨eL, hlw⟩ := hl V constants hM levels env hΓ hwe
  obtain ⟨eR, hrw⟩ := hr V constants hM levels env hΓ hwe
  exact ⟨(hc V constants hM levels env hΓ hwe hlw).trans
    (eL.symm.trans ((heq V constants hM levels env hΓ).trans eR)), hrw⟩

/-- A conversion through a rule whose right instance is the other side, under
the well-denotedness of the side whose spine supplied the arguments. -/
theorem ConvClaim.ofRuleIO {a b l L R : AExpr β} (hc : ConvClaim.{u,v} entries Γ a l)
    (hl : IOReductionClaim.{u,v} entries Γ a L l) (heq : ConversionClaim.{u,v} entries Γ L R)
    (hr : IOReductionClaim.{u,v} entries Γ a R b) : ConvClaim.{u,v} entries Γ a b := by
  intro V _ constants hM levels env hΓ hwa _
  obtain ⟨eL, hlw⟩ := hl V constants hM levels env hΓ hwa
  obtain ⟨eR, -⟩ := hr V constants hM levels env hΓ hwa
  exact (hc V constants hM levels env hΓ hwa hlw).trans
    (eL.symm.trans ((heq V constants hM levels env hΓ).trans eR))

end Ix.Kernel
