/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Quotient/Reading.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the single `Reading` of all five values is replaced by one reading per
pinned value (`FormerReading`, `CtorReading`, `LiftReading`), which the
published `quotient` facts supply, so that each primitive is installed on its
own; the values live in `Ix.Kernel.Model.Quotient`.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Quotient.Syntax
import Ix.Kernel.Model.QuotientValues
import Ix.Kernel.Model.Judgment

namespace Ix.Kernel.Certified.Quotient

open Model Model.SetTheory Model.SetModel Model.Quotient

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

/-- The former is pinned to its value. -/
def FormerReading (constants : Assignment β V) (type : ConstRef β) : Prop :=
  ∀ u, constants type [u] = formerValue u

/-- The constructor is pinned to its value. -/
def CtorReading (constants : Assignment β V) (ctor : ConstRef β) : Prop :=
  ∀ u, constants ctor [u] = constructorValue u

/-- The lift is pinned to its value over the equality family. -/
def LiftReading (constants : Assignment β V) (eq lift : ConstRef β) : Prop :=
  ∀ u v, constants lift [u, v] = liftValue constants eq u v

noncomputable def formerAt (constants : Assignment β V) (refs : Refs β) (u : Nat) (A R : V) : V :=
  app (app (constants refs.type [u]) A) R

noncomputable def constructorAt (constants : Assignment β V) (refs : Refs β) (u : Nat) (A R a : V) : V :=
  app (app (app (constants refs.ctor [u]) A) R) a

variable {constants : Assignment β V} {refs : Refs β}

theorem formerAt_eq (h : FormerReading constants refs.type) {u : Nat} {A R : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) : formerAt constants refs u A R = quotSet u A R := by
  rw [formerAt, h]
  exact formerValue_apply hA hR

theorem constructorAt_eq (h : CtorReading constants refs.ctor) {u : Nat} {A R a : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) (ha : a ∈ˢ A) :
    constructorAt constants refs u A R a = quotClass u A R a := by
  rw [constructorAt, h]
  exact constructorValue_apply hA hR ha

theorem typeType_interp (constants : Assignment β V) (u : Nat) (env : Nat → V) :
    interp constants [u] env (typeType : AExpr β) = formerSet u := by
  simp [typeType, relationType, formerSet, relationSet, interp, VLevel.eval, Valuation.cons, univ_zero]

theorem ctorType_interp (h : FormerReading constants refs.type) (u : Nat) (env : Nat → V) :
    interp constants [u] env (ctorType refs) = constructorSet u := by
  simp [ctorType, applied, AExpr.appN, relationType, interp, VLevel.eval, Valuation.cons, regime, PropWhen.param, PropWhen.holds, univ_zero]
  change piR (bit u) (univ u) (fun A => piR (bit u) (relationSet A) (fun R =>
    piR (bit u) A (fun _ => formerAt constants refs u A R))) = constructorSet u
  apply piR_congr
  intro A hA
  apply piR_congr
  intro R hR
  simp only [formerAt_eq h hA hR]

theorem liftType_interp (h : FormerReading constants refs.type) (u v : Nat) (env : Nat → V) :
    interp constants [u, v] env (liftType refs) = liftSet constants refs.eq u v := by
  simp [liftType, liftPrefix, AExpr.forallN, invariantType, Basis.Equality.applied,
    relationType, applied, AExpr.appN, interp, VLevel.eval,
    Valuation.cons, regime, PropWhen.param, PropWhen.holds, univ_zero]
  change piR (bit v) (univ u) (fun A => piR (bit v) (relationSet A) (fun R =>
    piR (bit v) (univ v) (fun B => piR (bit v) (piR (bit v) A (fun _ => B)) (fun f =>
      piR (bit v) (invariantSet constants refs.eq v A R B f) (fun _ =>
        piR (bit v) (formerAt constants refs u A R) (fun _ => B)))))) = liftSet constants refs.eq u v
  apply piR_congr
  intro A hA
  apply piR_congr
  intro R hR
  simp only [formerAt_eq h hA hR]

theorem indType_interp (hf : FormerReading constants refs.type) (hc : CtorReading constants refs.ctor)
    (u : Nat) (env : Nat → V) :
    interp constants [u] env (indType refs) = indSet u := by
  simp [indType, indPrefix, AExpr.forallN, relationType, applied, constructed, AExpr.appN,
    interp, VLevel.eval, Valuation.cons,
    regime, PropWhen.holds, univ_zero]
  change piR 0 (univ u) (fun A => piR 0 (relationSet A) (fun R =>
    piR 0 (piR 1 (formerAt constants refs u A R) (fun _ => univZero)) (fun motive =>
      piR 0 (piR 0 A (fun a => app motive (constructorAt constants refs u A R a))) (fun _ =>
        piR 0 (formerAt constants refs u A R) (fun q => app motive q))))) = indSet u
  apply piR_congr
  intro A hA
  apply piR_congr
  intro R hR
  simp only [formerAt_eq hf hA hR]
  apply piR_congr
  intro motive _
  have he : piR 0 A (fun a => app motive (constructorAt constants refs u A R a)) =
      piR 0 A (fun a => app motive (quotClass u A R a)) := by
    apply piR_congr
    intro a ha
    rw [constructorAt_eq hc hA hR ha]
  rw [he]

theorem soundType_interp (hf : FormerReading constants refs.type) (hc : CtorReading constants refs.ctor)
    (u : Nat) (env : Nat → V) :
    interp constants [u] env (soundType refs) = soundSet constants refs.eq u := by
  simp [soundType, relationType, applied, constructed, Basis.Equality.applied, AExpr.appN,
    interp, VLevel.eval, Valuation.cons,
    regime, PropWhen.holds, univ_zero]
  change piR 0 (univ u) (fun A => piR 0 (relationSet A) (fun R =>
    piR 0 A (fun a => piR 0 A (fun b => piR 0 (app (app R a) b) (fun _ =>
      eqValue constants refs.eq u (formerAt constants refs u A R)
        (constructorAt constants refs u A R a) (constructorAt constants refs u A R b)))))) =
    soundSet constants refs.eq u
  apply piR_congr
  intro A hA
  apply piR_congr
  intro R hR
  apply piR_congr
  intro a ha
  apply piR_congr
  intro b hb
  simp only [formerAt_eq hf hA hR, constructorAt_eq hc hA hR ha, constructorAt_eq hc hA hR hb]

theorem type_mem (u : Nat) (env : Nat → V) :
    (formerValue u : V) ∈ˢ interp constants [u] env (typeType : AExpr β) := by
  rw [typeType_interp]
  exact formerValue_mem u

theorem ctor_mem (hf : FormerReading constants refs.type) (u : Nat) (env : Nat → V) :
    (constructorValue u : V) ∈ˢ interp constants [u] env (ctorType refs) := by
  rw [ctorType_interp hf]
  exact constructorValue_mem u

theorem lift_mem (hf : FormerReading constants refs.type) (u v : Nat) (env : Nat → V) :
    liftValue constants refs.eq u v ∈ˢ interp constants [u, v] env (liftType refs) := by
  rw [liftType_interp hf]
  exact liftValue_mem constants refs.eq u v

theorem ind_mem (hf : FormerReading constants refs.type) (hc : CtorReading constants refs.ctor)
    (u : Nat) (env : Nat → V) : (pt : V) ∈ˢ interp constants [u] env (indType refs) := by
  rw [indType_interp hf hc]
  exact indValue_mem u

/-- The meaning of equality follows from the admitted `Eq` interface. -/
theorem Equality.value_eq_eqValue (constants : Assignment β V) (family : ConstRef β) (u : Nat) (A a b : V) :
    Basis.Equality.value constants family u A a b = eqValue constants family u A a b := rfl

theorem soundValue_mem {entries : Environment β} {refl recursor : ConstRef β}
    (hE : Basis.Equality.Interface entries refs.eq refl recursor) (hM : Realizes constants entries) (u : Nat) :
    (pt : V) ∈ˢ soundSet constants refs.eq u := by
  apply pt_mem_piR_zero_of
  intro A hA
  apply pt_mem_piR_zero_of
  intro R _
  apply pt_mem_piR_zero_of
  intro a ha
  apply pt_mem_piR_zero_of
  intro b hb
  apply pt_mem_piR_zero_of
  intro h hh
  rw [← Equality.value_eq_eqValue,
    Basis.Equality.value_eq_eqv hE hM (quotSet_mem_univ hA) (quotClass_mem ha) (quotClass_mem hb),
    quotSound ha hb hh]
  exact pt_mem_eqv_self _

theorem sound_mem {entries : Environment β} {refl recursor : ConstRef β}
    (hf : FormerReading constants refs.type) (hc : CtorReading constants refs.ctor)
    (hE : Basis.Equality.Interface entries refs.eq refl recursor) (hM : Realizes constants entries)
    (u : Nat) (env : Nat → V) : (pt : V) ∈ˢ interp constants [u] env (soundType refs) := by
  rw [soundType_interp hf hc]
  exact soundValue_mem hE hM u

theorem invariant_of_mem {entries : Environment β} {refl recursor : ConstRef β}
    (hE : Basis.Equality.Interface entries refs.eq refl recursor)
    (hM : Realizes constants entries) {v : Nat} {A R B f h : V}
    (hB : B ∈ˢ univ v) (hf : f ∈ˢ piR (bit v) A (fun _ => B))
    (hh : h ∈ˢ invariantSet constants refs.eq v A R B f) :
    ∀ a b, a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) → app f a = app f b := by
  intro a b ha hb ⟨w, hw⟩
  obtain ⟨ha', hha⟩ := Basis.Equality.exists_of_mem_piR_zero hh ha
  obtain ⟨hb', hhb⟩ := Basis.Equality.exists_of_mem_piR_zero hha hb
  obtain ⟨q, hq⟩ := Basis.Equality.exists_of_mem_piR_zero hhb hw
  exact Basis.Equality.eq_of_mem hE hM hB (app_mem_bit hB hf ha) (app_mem_bit hB hf hb) hq

/-- The whole quotient-lift application computes for any typed invariant
function. Both the Prop and graph regimes are included. -/
theorem liftValue_apply {entries : Environment β} {refl recursor : ConstRef β}
    (hE : Basis.Equality.Interface entries refs.eq refl recursor)
    (hM : Realizes constants entries) {u v : Nat} {A R B f h a : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) (hB : B ∈ˢ univ v)
    (hf : f ∈ˢ piR (bit v) A (fun _ => B))
    (hh : h ∈ˢ invariantSet constants refs.eq v A R B f) (ha : a ∈ˢ A) :
    app (app (app (app (app (app (liftValue constants refs.eq u v) A) R) B) f) h)
      (quotClass u A R a) = app f a := by
  by_cases hv : v = 0
  · subst v
    have he : f = pt := eq_pt_of_mem_piR_zero hf
    simp [liftValue, bit, lamR_zero, he, app_pt]
  · simp only [liftValue, bit, if_neg hv]
    rw [app_lamR_pos (by decide : 1 ≠ 0) hA,
      app_lamR_pos (by decide : 1 ≠ 0) hR,
      app_lamR_pos (by decide : 1 ≠ 0) hB,
      app_lamR_pos (by decide : 1 ≠ 0) (by simpa only [bit, if_neg hv] using hf),
      app_lamR_pos (by decide : 1 ≠ 0) hh,
      app_lamR_pos (by decide : 1 ≠ 0) (quotClass_mem ha)]
    have hs := qrep_spec (u := u) (R := R) (quotClass_mem ha)
    exact app_eq_of_quotClass_eq hA hs.1 ha (invariant_of_mem hE hM hB hf hh) hs.2.symm

/-- Equality of the complete lambda endpoints published as the primitive
computation law, for every environment and both universe regimes. -/
theorem liftRule_eq {entries : Environment β} {refl recursor : ConstRef β}
    (_hf : FormerReading constants refs.type) (hc : CtorReading constants refs.ctor)
    (hl : LiftReading constants refs.eq refs.lift)
    (hE : Basis.Equality.Interface entries refs.eq refl recursor) (hM : Realizes constants entries)
    (u v : Nat) (env : Nat → V) :
    interp constants [u, v] env (liftRuleLhs refs) = interp constants [u, v] env (liftRuleRhs refs) := by
  simp [liftRuleLhs, liftRuleRhs, liftRuleBinders, liftPrefix, List.cons_append, List.nil_append,
    AExpr.lamN, relationType, invariantType, Basis.Equality.applied, AExpr.appN, constructed,
    interp, VLevel.eval, Valuation.cons, regime, PropWhen.param, PropWhen.holds, univ_zero]
  apply lamR_congr
  intro A hA
  apply lamR_congr
  intro R hR
  apply lamR_congr
  intro B hB
  apply lamR_congr
  intro f hf'
  apply lamR_congr
  intro proof hp
  apply lamR_congr
  intro a ha
  change app (app (app (app (app (app (constants refs.lift [u, v]) A) R) B) f) proof)
    (constructorAt constants refs u A R a) = app f a
  rw [hl, constructorAt_eq hc hA hR ha]
  exact liftValue_apply hE hM hA hR hB hf' hp ha

theorem indRule_eq (constants : Assignment β V) (refs : Refs β) (levels : List Nat) (env : Nat → V) :
    interp constants levels env (indRuleLhs refs) = interp constants levels env (indRuleRhs refs) := by
  simp only [indRuleLhs, indRuleRhs, indRuleBinders, indPrefix, List.cons_append, List.nil_append,
    AExpr.lamN, interp, regime_always, lamR_zero]


/-! ### Facts in the environment and the rules they yield -/

section
variable [DecidableEq β]

/-- An entry with the given universe count, type, and fact. -/
def HasFact (entries : Environment β) (r : ConstRef β) (n : Nat) (type : AExpr β)
    (fact : ConstantFact β) : Prop :=
  ∃ entry, entries r = some entry ∧ entry.universes = n ∧ entry.type = type ∧ fact ∈ entry.facts

instance (entries : Environment β) (r : ConstRef β) (n : Nat) (type : AExpr β) (fact : ConstantFact β) :
    Decidable (HasFact entries r n type fact) :=
  match h : entries r with
  | none => .isFalse (by rintro ⟨entry, he, _⟩; simp [h] at he)
  | some entry =>
    if hc : entry.universes = n ∧ entry.type = type ∧ fact ∈ entry.facts then
      .isTrue ⟨entry, h, hc.1, hc.2.1, hc.2.2⟩
    else .isFalse (by rintro ⟨other, ho, hu, ht, hf⟩; cases h.symm.trans ho; exact hc ⟨hu, ht, hf⟩)

def HasFormer (entries : Environment β) (refs : Refs β) : Prop :=
  HasFact entries refs.type 1 typeType (.quotient .type)
def HasCtor (entries : Environment β) (refs : Refs β) : Prop :=
  HasFact entries refs.ctor 1 (ctorType refs) (.quotient .ctor)
def HasLift (entries : Environment β) (refs : Refs β) : Prop :=
  HasFact entries refs.lift 2 (liftType refs) (.quotientLift refs.eq)

instance (entries : Environment β) (refs : Refs β) : Decidable (HasFormer entries refs) :=
  inferInstanceAs (Decidable (HasFact entries refs.type 1 typeType (.quotient .type)))
instance (entries : Environment β) (refs : Refs β) : Decidable (HasCtor entries refs) :=
  inferInstanceAs (Decidable (HasFact entries refs.ctor 1 (ctorType refs) (.quotient .ctor)))
instance (entries : Environment β) (refs : Refs β) : Decidable (HasLift entries refs) :=
  inferInstanceAs (Decidable (HasFact entries refs.lift 2 (liftType refs) (.quotientLift refs.eq)))

/-- The equality family sits at member 0 of its block, with the reflexivity
constructor and the eliminator where the ordinary route puts them. -/
def EqInterface (entries : Environment β) (eq : ConstRef β) : Prop :=
  ∃ b, eq = .member b 0 ∧ Basis.Equality.Interface entries eq (.ctor b 0 0) (.member b 1)

instance (entries : Environment β) : (eq : ConstRef β) → Decidable (EqInterface entries eq)
  | .member b 0 =>
    decidable_of_iff (Basis.Equality.Interface entries (.member b 0) (.ctor b 0 0) (.member b 1))
      ⟨fun h => ⟨b, rfl, h⟩, fun ⟨b', hb, h⟩ => by cases hb; exact h⟩
  | .member _ (_ + 1) => .isFalse (by rintro ⟨b, hb, -⟩; cases hb)
  | .ctor .. => .isFalse (by rintro ⟨b, hb, -⟩; cases hb)

omit [DecidableEq β] in
theorem HasFormer.reading {entries : Environment β} {refs : Refs β} (h : HasFormer entries refs)
    (hM : Realizes constants entries) : FormerReading constants refs.type := by
  intro u
  obtain ⟨entry, he, hu, -, hf⟩ := h
  have hm := hM.factMeaning _ entry he _ hf [u] (by simp [hu]) (fun _ => empty)
  simpa [ConstantFact.Meaning] using hm

omit [DecidableEq β] in
theorem HasCtor.reading {entries : Environment β} {refs : Refs β} (h : HasCtor entries refs)
    (hM : Realizes constants entries) : CtorReading constants refs.ctor := by
  intro u
  obtain ⟨entry, he, hu, -, hf⟩ := h
  have hm := hM.factMeaning _ entry he _ hf [u] (by simp [hu]) (fun _ => empty)
  simpa [ConstantFact.Meaning] using hm

omit [DecidableEq β] in
theorem HasLift.reading {entries : Environment β} {refs : Refs β} (h : HasLift entries refs)
    (hM : Realizes constants entries) : LiftReading constants refs.eq refs.lift := by
  intro u v
  obtain ⟨entry, he, hu, -, hf⟩ := h
  have hm := hM.factMeaning _ entry he _ hf [u, v] (by simp [hu]) (fun _ => empty)
  simpa [ConstantFact.Meaning] using hm

omit [DecidableEq β] in
/-- The lift's computation rule, derived from the published facts. -/
theorem liftRule_claim {entries : Environment β} {refs : Refs β} (Γ : Context β)
    (hq : HasFormer entries refs) (hc : HasCtor entries refs) (hl : HasLift entries refs)
    (hE : EqInterface entries refs.eq) {ls : List VLevel} (hn : ls.length = 2) :
    ConversionClaim.{u,v} entries Γ ((liftRuleLhs refs).instL ls) ((liftRuleRhs refs).instL ls) := by
  intro V _ constants hM levels env _
  obtain ⟨b, -, hI⟩ := hE
  rw [interp_instL, interp_instL]
  match hm : ls.map (VLevel.eval levels), (by simpa using hn : (ls.map (VLevel.eval levels)).length = 2) with
  | [u, v], _ => exact liftRule_eq (hq.reading hM) (hc.reading hM) (hl.reading hM) hI hM u v env

omit [DecidableEq β] in
/-- The eliminator's computation rule holds outright: both sides are proofs. -/
theorem indRule_claim {entries : Environment β} (refs : Refs β) (Γ : Context β) (ls : List VLevel) :
    ConversionClaim.{u,v} entries Γ ((indRuleLhs refs).instL ls) ((indRuleRhs refs).instL ls) := by
  intro V _ constants _ levels env _
  rw [interp_instL, interp_instL]
  exact indRule_eq constants refs _ env

end

end Ix.Kernel.Certified.Quotient
