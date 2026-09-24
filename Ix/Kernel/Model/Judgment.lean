/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Judgment.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: `natLit` carries the reference of its natural-number family, on raw and
annotated syntax alike, with its cases.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Environment

/-!
# Semantic contracts and their rule producers

These specifications quantify over every compatible dependency assignment,
universe valuation, and satisfying context. The executable validator uses the
proved rules below to construct these propositions; they are never unchecked
witness fields supplied by its caller.
-/

namespace Ix.Kernel.Model

open SetTheory SetModel Certified

universe u v
variable {β : Type u}

/-- Membership together with the hereditary invariants for term and type. -/
def TypingClaim (entries : Environment β) (Γ : Context β) (e A : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    Realizes constants entries → ∀ levels env, Γ.Valid constants levels env →
      WellDenoted constants levels env e ∧ WellDenoted constants levels env A ∧
        interp constants levels env e ∈ˢ interp constants levels env A

/-- Equality is a congruence on the total interpretation. Conversion does not
manufacture typing or hereditary validity of either endpoint. -/
def ConversionClaim (entries : Environment β) (Γ : Context β) (a b : AExpr β) : Prop :=
  ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
    Realizes constants entries → ∀ levels env, Γ.Valid constants levels env →
      interp constants levels env a = interp constants levels env b

variable {entries : Environment β} {Γ : Context β}

namespace TypingClaim

theorem sort (l : VLevel) : TypingClaim.{u,v} entries Γ (.sort l) (.sort (.succ l)) := by
  intro V _ constants _ levels env _
  exact ⟨trivial, trivial, univ_mem_univ _⟩

theorem bvar {i : Nat} {A : AExpr β} (h : Γ[i]? = some A) :
    TypingClaim.{u,v} entries Γ (.bvar i) A := by
  intro V _ constants _ levels env hΓ
  exact ⟨trivial, hΓ i A h⟩

theorem const {r : ConstRef β} {entry : ConstantEntry β} {ls : List VLevel}
    (h : entries r = some entry) (hn : ls.length = entry.universes) :
    TypingClaim.{u,v} entries Γ (.const r ls) (entry.type.instL ls) := by
  intro V _ constants hM levels env _
  have hlen : (ls.map (VLevel.eval levels)).length = entry.universes := by simpa using hn
  refine ⟨trivial, (wellDenoted_instL ..).mpr (hM.typeValid r entry h _ hlen env), ?_⟩
  simpa only [interp, interp_instL] using hM.member r entry h _ hlen env

theorem forallE {A B : AExpr β} {a b : VLevel} {p : PropWhen}
    (hA : TypingClaim.{u,v} entries Γ A (.sort a))
    (hB : TypingClaim.{u,v} entries (Γ.push A) B (.sort b))
    (hp : p = zeroCondition b) :
    TypingClaim.{u,v} entries Γ (.forallE p A B) (.sort (.imax a b)) := by
  intro V _ constants hM levels env hΓ
  obtain ⟨hAw, _, hAm⟩ := hA V constants hM levels env hΓ
  have hBx x hx := hB V constants hM levels (Valuation.cons x env) (hΓ.push hAw hx)
  have hz : regime p levels = 0 ↔ b.eval levels = 0 := by
    rw [hp]; exact regime_zeroCondition ..
  refine ⟨⟨hAw, fun x hx => (hBx x hx).1,
    b.eval levels, hz, fun x hx => (hBx x hx).2.2⟩, trivial, ?_⟩
  exact annotated_pi_mem_univ hp hAm (fun x hx => (hBx x hx).2.2)

theorem lam {A B body : AExpr β} {a b : VLevel} {p : PropWhen}
    (hA : TypingClaim.{u,v} entries Γ A (.sort a))
    (hB : TypingClaim.{u,v} entries (Γ.push A) B (.sort b))
    (hbody : TypingClaim.{u,v} entries (Γ.push A) body B)
    (hp : p = zeroCondition b) :
    TypingClaim.{u,v} entries Γ (.lam p A body) (.forallE p A B) := by
  intro V _ constants hM levels env hΓ
  obtain ⟨hAw, _, _⟩ := hA V constants hM levels env hΓ
  have hBx x hx := hB V constants hM levels (Valuation.cons x env) (hΓ.push hAw hx)
  have hbodyx x hx := hbody V constants hM levels (Valuation.cons x env) (hΓ.push hAw hx)
  have hz : regime p levels = 0 ↔ b.eval levels = 0 := by
    rw [hp]; exact regime_zeroCondition ..
  refine ⟨⟨hAw, fun x hx => (hbodyx x hx).1, b.eval levels,
    (fun x => interp constants levels (Valuation.cons x env) B), hz,
    fun x hx => ⟨(hbodyx x hx).2.2, (hBx x hx).2.2⟩⟩, ?_, ?_⟩
  · exact (forallE hA hB hp V constants hM levels env hΓ).1
  · exact lamR_mem (fun x hx => (hbodyx x hx).2.2)

theorem app {f a A B : AExpr β} {p : PropWhen}
    (hf : TypingClaim.{u,v} entries Γ f (.forallE p A B))
    (ha : TypingClaim.{u,v} entries Γ a A) :
    TypingClaim.{u,v} entries Γ (.app f a) (B.inst a) := by
  intro V _ constants hM levels env hΓ
  obtain ⟨hfw, hpw, hfm⟩ := hf V constants hM levels env hΓ
  obtain ⟨haw, _, ham⟩ := ha V constants hM levels env hΓ
  obtain ⟨_, hBw, bv, hz, hBm⟩ := hpw
  have hfm' : interp constants levels env f ∈ˢ
      piR bv (interp constants levels env A)
        (fun x => interp constants levels (Valuation.cons x env) B) := by
    simpa only [interp, piR_zero_agree hz (fun _ _ => rfl)] using hfm
  refine ⟨⟨hfw, haw, bv, interp constants levels env A,
    (fun x => interp constants levels (Valuation.cons x env) B), hfm', ham, hBm⟩,
    ?_, ?_⟩
  · apply wellDenoted_inst
    · simpa using haw
    · simpa using hBw _ ham
  · simp only [interp_inst, Valuation.skip_zero, Valuation.insert_zero]
    apply app_mem_piR hfm' ham
    intro hzero x hx
    simpa only [hzero, univ_zero] using hBm x hx

theorem conv {e A B : AExpr β} {l : VLevel}
    (he : TypingClaim.{u,v} entries Γ e A)
    (hB : TypingClaim.{u,v} entries Γ B (.sort l))
    (hEq : ConversionClaim.{u,v} entries Γ A B) :
    TypingClaim.{u,v} entries Γ e B := by
  intro V _ constants hM levels env hΓ
  obtain ⟨hew, _, hem⟩ := he V constants hM levels env hΓ
  exact ⟨hew, (hB V constants hM levels env hΓ).1,
    hEq V constants hM levels env hΓ ▸ hem⟩

/-- Closed typed facts come only from an admitted semantic producer. -/
theorem fact {r : ConstRef β} {entry : ConstantEntry β} {e A : AExpr β} {ls : List VLevel}
    (hr : entries r = some entry) (hf : .typed e A ∈ entry.facts) (hn : ls.length = entry.universes) :
    TypingClaim.{u,v} entries Γ (e.instL ls) (A.instL ls) := by
  intro V _ constants hM levels env _
  have hh := hM.factMeaning r entry hr (.typed e A) hf (ls.map (VLevel.eval levels))
    (by simpa using hn) env
  simpa only [ConstantFact.Meaning, wellDenoted_instL, interp_instL] using hh

theorem natLit {r zero succ : ConstRef β} {entry : ConstantEntry β}
    (hr : entries r = some entry) (hf : .natural zero succ ∈ entry.facts)
    (hn : entry.universes = 0) (value : Nat) :
    TypingClaim.{u,v} entries Γ (.natLit r value) (.const r []) := by
  intro V _ constants hM _ env _
  have hh := hM.factMeaning r entry hr (.natural zero succ) hf [] (by simpa using hn.symm) env
  exact ⟨trivial, trivial, hh.2.member value⟩

/-- A typed lambda application gives a typed result of beta reduction,
including the hereditary validity of that result. -/
theorem betaResult {p : PropWhen} {D body arg B : AExpr β}
    (hl : TypingClaim.{u,v} entries Γ (.lam p D body) (.forallE p D B))
    (ha : TypingClaim.{u,v} entries Γ arg D) :
    TypingClaim.{u,v} entries Γ (body.inst arg) (B.inst arg) := by
  intro V _ constants hM levels env hΓ
  have hl' := hl V constants hM levels env hΓ
  have ha' := ha V constants hM levels env hΓ
  have happ := app hl ha V constants hM levels env hΓ
  have hbeta := wellDenoted_beta hl'.1 ha'.1 ha'.2.2
  exact ⟨hbeta.1, happ.2.1, hbeta.2 ▸ happ.2.2⟩

end TypingClaim

namespace ConversionClaim

theorem natZero {f r zero succ : ConstRef β} {entry : ConstantEntry β}
    (hr : entries r = some entry) (hf : .natural zero succ ∈ entry.facts) (hn : entry.universes = 0) :
    ConversionClaim.{u,v} entries Γ (.natLit f 0) (.const zero []) := by
  intro V _ constants hM _ env _
  have hh := hM.factMeaning r entry hr (.natural zero succ) hf [] (by simpa using hn.symm) env
  exact hh.2.zeroValue.symm

theorem natSucc {f r zero succ : ConstRef β} {entry : ConstantEntry β}
    (hr : entries r = some entry) (hf : .natural zero succ ∈ entry.facts) (hn : entry.universes = 0) (value : Nat) :
    ConversionClaim.{u,v} entries Γ (.natLit f (value + 1)) (.app (.const succ []) (.natLit f value)) := by
  intro V _ constants hM _ env _
  have hh := hM.factMeaning r entry hr (.natural zero succ) hf [] (by simpa using hn.symm) env
  exact (hh.2.succValue value).symm

theorem refl (e : AExpr β) : ConversionClaim.{u,v} entries Γ e e := by
  intro V _ constants hM levels env hΓ
  rfl

theorem symm {a b : AExpr β} (h : ConversionClaim.{u,v} entries Γ a b) :
    ConversionClaim.{u,v} entries Γ b a := by
  intro V _ constants hM levels env hΓ
  exact (h V constants hM levels env hΓ).symm

theorem trans {a b c : AExpr β} (h : ConversionClaim.{u,v} entries Γ a b)
    (h' : ConversionClaim.{u,v} entries Γ b c) :
    ConversionClaim.{u,v} entries Γ a c := by
  intro V _ constants hM levels env hΓ
  exact (h V constants hM levels env hΓ).trans (h' V constants hM levels env hΓ)

theorem app {f f' a a' : AExpr β} (hf : ConversionClaim.{u,v} entries Γ f f')
    (ha : ConversionClaim.{u,v} entries Γ a a') :
    ConversionClaim.{u,v} entries Γ (.app f a) (.app f' a') := by
  intro V _ constants hM levels env hΓ
  simp only [interp, hf V constants hM levels env hΓ, ha V constants hM levels env hΓ]

theorem proj {r : ConstRef β} {i : Nat} {a b : AExpr β}
    (h : ConversionClaim.{u,v} entries Γ a b) :
    ConversionClaim.{u,v} entries Γ (.proj r i a) (.proj r i b) := by
  intro V _ constants hM levels env hΓ
  exact congrArg (projectValue i) (h V constants hM levels env hΓ)

theorem lam {A A' b b' : AExpr β} {p : PropWhen} {l : VLevel}
    (hA : TypingClaim.{u,v} entries Γ A (.sort l))
    (hdom : ConversionClaim.{u,v} entries Γ A A')
    (hbody : ConversionClaim.{u,v} entries (Γ.push A) b b') :
    ConversionClaim.{u,v} entries Γ (.lam p A b) (.lam p A' b') := by
  intro V _ constants hM levels env hΓ
  have hAw := (hA V constants hM levels env hΓ).1
  simp only [interp]
  rw [← hdom V constants hM levels env hΓ]
  apply lamR_congr
  intro x hx
  exact hbody V constants hM levels _ (hΓ.push hAw hx)

theorem forallE {A A' B B' : AExpr β} {p : PropWhen} {l : VLevel}
    (hA : TypingClaim.{u,v} entries Γ A (.sort l))
    (hdom : ConversionClaim.{u,v} entries Γ A A')
    (hbody : ConversionClaim.{u,v} entries (Γ.push A) B B') :
    ConversionClaim.{u,v} entries Γ (.forallE p A B) (.forallE p A' B') := by
  intro V _ constants hM levels env hΓ
  have hAw := (hA V constants hM levels env hΓ).1
  simp only [interp]
  rw [← hdom V constants hM levels env hΓ]
  apply piR_congr
  intro x hx
  exact hbody V constants hM levels _ (hΓ.push hAw hx)

theorem beta {p : PropWhen} {A b a T : AExpr β}
    (hl : TypingClaim.{u,v} entries Γ (.lam p A b) T)
    (ha : TypingClaim.{u,v} entries Γ a A) :
    ConversionClaim.{u,v} entries Γ (.app (.lam p A b) a) (b.inst a) := by
  intro V _ constants hM levels env hΓ
  have hl' := (hl V constants hM levels env hΓ).1
  obtain ⟨haw, _, ham⟩ := ha V constants hM levels env hΓ
  exact (wellDenoted_beta hl' haw ham).2

theorem eta {p : PropWhen} {A B f : AExpr β}
    (hf : TypingClaim.{u,v} entries Γ f (.forallE p A B)) :
    ConversionClaim.{u,v} entries Γ (.lam p A (.app (f.liftN 1) (.bvar 0))) f := by
  intro V _ constants hM levels env hΓ
  have hfm := (hf V constants hM levels env hΓ).2.2
  simp only [interp, interp_liftN, Valuation.skip_one_cons, Valuation.cons_zero]
  exact lamR_eta hfm

theorem proofIrrel {A a b : AExpr β}
    (hA : TypingClaim.{u,v} entries Γ A (.sort .zero))
    (ha : TypingClaim.{u,v} entries Γ a A)
    (hb : TypingClaim.{u,v} entries Γ b A) :
    ConversionClaim.{u,v} entries Γ a b := by
  intro V _ constants hM levels env hΓ
  have hAm := (hA V constants hM levels env hΓ).2.2
  have ham := (ha V constants hM levels env hΓ).2.2
  have hbm := (hb V constants hM levels env hΓ).2.2
  exact subsingleton_of_mem_univZero
    (by simpa only [interp, VLevel.eval, univ_zero] using hAm) ham hbm

theorem delta {r : ConstRef β} {entry : ConstantEntry β} {body : AExpr β}
    {ls : List VLevel} (h : entries r = some entry) (hb : entry.body = some body)
    (hn : ls.length = entry.universes) :
    ConversionClaim.{u,v} entries Γ (.const r ls) (body.instL ls) := by
  intro V _ constants hM levels env _
  have hlen : (ls.map (VLevel.eval levels)).length = entry.universes := by simpa using hn
  simpa only [interp, interp_instL] using hM.bodyValue r entry h body hb _ hlen env

theorem sort {l l' : VLevel} (h : ∀ values, l.eval values = l'.eval values) :
    ConversionClaim.{u,v} entries Γ (.sort l) (.sort l') := by
  intro V _ constants hM levels env hΓ
  simp only [interp, h]

/-- Only an equation of the selected admitted entry may be instantiated.
Typing of its applications remains a separate checker obligation. -/
theorem equation {r : ConstRef β} {entry : ConstantEntry β}
    {law : ConstantEquation β} {ls : List VLevel}
    (h : entries r = some entry) (he : law ∈ entry.equations)
    (hn : ls.length = entry.universes) :
    ConversionClaim.{u,v} entries Γ (law.lhs.instL ls) (law.rhs.instL ls) := by
  intro V _ constants hM levels env _
  have hlen : (ls.map (VLevel.eval levels)).length = entry.universes := by simpa using hn
  simpa only [interp_instL] using hM.equationValue r entry h law he _ hlen env

end ConversionClaim

end Ix.Kernel.Model
