/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Judgment
import Ix.Kernel.Model.LetRules
import Ix.Kernel.Model.Inductive.Telescope

/-! # Claims produced by the checker

The checker's functions return their results together with semantic claims,
erased at run time. Besides the ported `TypingClaim` and `ConversionClaim`:

* `FormedClaim`: the term is well denoted in every model, under every valid
  context valuation (hereditary validity of its annotations);
* `ConvClaim`: conditional conversion, equal interpretations wherever both
  sides are well denoted; the head-reduction based conversion check produces
  this form, and typing transports it (`TypingClaim.convF`);
* `ReductionClaim`: head reduction preserves interpretation and
  well-denotedness. Beta needs the argument's typing at the lambda's own
  domain (`ReductionClaim.beta`), which the checker re-establishes at each
  redex; delta and zeta need nothing.

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

/-- Head reduction: `e'` denotes what `e` denotes and stays well denoted. -/
def ReductionClaim (entries : Environment β) (Γ : Context β) (e e' : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V), Realizes constants entries →
    ∀ (levels : List Nat) (env : Nat → V), Γ.Valid constants levels env →
      WellDenoted constants levels env e →
        interp constants levels env e = interp constants levels env e' ∧
          WellDenoted constants levels env e'

namespace Model.TypingClaim

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

end Ix.Kernel
