/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Quotient.Value

namespace Ix.Theory.Certified.Quotient

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def Refs.value (refs : Refs β) (constants : Assignment β V)
    (kind : Kind) (levels : List Nat) : V :=
  match kind with
  | .type => formerValue (levels.getD 0 0)
  | .ctor => constructorValue (levels.getD 0 0)
  | .lift => liftValue constants refs.eq (levels.getD 0 0) (levels.getD 1 0)
  | .ind | .sound => pt

/-- This reading is proved for the internally constructed assignment. It is
not a field of an input certificate. -/
structure Reading (constants : Assignment β V) (refs : Refs β) : Prop where
  former : ∀ u, constants refs.type [u] = formerValue u
  ctor : ∀ u, constants refs.ctor [u] = constructorValue u
  lift : ∀ u v, constants refs.lift [u, v] = liftValue constants refs.eq u v
  ind : ∀ u, constants refs.ind [u] = pt
  sound : ∀ u, constants refs.sound [u] = pt

noncomputable def formerAt (constants : Assignment β V) (refs : Refs β) (u : Nat) (A R : V) : V :=
  app (app (constants refs.type [u]) A) R

noncomputable def constructorAt (constants : Assignment β V) (refs : Refs β) (u : Nat) (A R a : V) : V :=
  app (app (app (constants refs.ctor [u]) A) R) a

variable {constants : Assignment β V} {refs : Refs β}

theorem formerAt_eq (h : Reading constants refs) {u : Nat} {A R : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) : formerAt constants refs u A R = quotSet u A R := by
  rw [formerAt, h.former]
  exact formerValue_apply hA hR

theorem constructorAt_eq (h : Reading constants refs) {u : Nat} {A R a : V}
    (hA : A ∈ˢ univ u) (hR : R ∈ˢ relationSet A) (ha : a ∈ˢ A) :
    constructorAt constants refs u A R a = quotClass u A R a := by
  rw [constructorAt, h.ctor]
  exact constructorValue_apply hA hR ha

theorem typeType_interp (constants : Assignment β V) (u : Nat) (env : Nat → V) :
    interp constants [u] env (typeType : AExpr β) = formerSet u := by
  simp [typeType, relationType, formerSet, relationSet, interp, VLevel.eval, Valuation.cons, univ_zero]

theorem ctorType_interp (h : Reading constants refs) (u : Nat) (env : Nat → V) :
    interp constants [u] env (ctorType refs) = constructorSet u := by
  simp [ctorType, applied, AExpr.appN, relationType, interp, VLevel.eval, Valuation.cons, regime, PropWhen.param, PropWhen.holds, univ_zero]
  change piR (bit u) (univ u) (fun A => piR (bit u) (relationSet A) (fun R =>
    piR (bit u) A (fun _ => formerAt constants refs u A R))) = constructorSet u
  apply piR_congr
  intro A hA
  apply piR_congr
  intro R hR
  simp only [formerAt_eq h hA hR]

theorem liftType_interp (h : Reading constants refs) (u v : Nat) (env : Nat → V) :
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

theorem indType_interp (h : Reading constants refs) (u : Nat) (env : Nat → V) :
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
  simp only [formerAt_eq h hA hR]
  apply piR_congr
  intro motive _
  have he : piR 0 A (fun a => app motive (constructorAt constants refs u A R a)) =
      piR 0 A (fun a => app motive (quotClass u A R a)) := by
    apply piR_congr
    intro a ha
    rw [constructorAt_eq h hA hR ha]
  rw [he]

theorem soundType_interp (h : Reading constants refs) (u : Nat) (env : Nat → V) :
    interp constants [u] env (soundType refs) = soundSet constants refs.eq u := by
  simp [soundType, relationType, applied, constructed, Basis.Equality.applied, AExpr.appN,
    interp, VLevel.eval, Valuation.cons,
    regime, PropWhen.holds, univ_zero]
  change piR 0 (univ u) (fun A => piR 0 (relationSet A) (fun R =>
    piR 0 A (fun a => piR 0 A (fun b => piR 0 (app (app R a) b) (fun _ =>
      Basis.Equality.value constants refs.eq u (formerAt constants refs u A R)
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
  simp only [formerAt_eq h hA hR, constructorAt_eq h hA hR ha, constructorAt_eq h hA hR hb]

theorem value_mem {entries : Environment β} (h : Reading constants refs)
    (hE : Basis.Equality.Interface entries refs.eq refs.eqRefl refs.eqRec) (hM : Realizes constants entries)
    (kind : Kind) (levels : List Nat) (hn : levels.length = kind.universes) (env : Nat → V) :
    constants (refs.ref kind) levels ∈ˢ interp constants levels env (refs.entryType kind) := by
  cases kind with
  | type =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [Refs.ref, h.former, Refs.entryType, typeType_interp]
    exact formerValue_mem u
  | ctor =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [Refs.ref, h.ctor, Refs.entryType, ctorType_interp h]
    exact constructorValue_mem u
  | lift =>
    cases levels with
    | nil => cases hn
    | cons u tail =>
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Nat.succ.inj hn)
      rw [Refs.ref, h.lift, Refs.entryType, liftType_interp h]
      exact liftValue_mem constants refs.eq u v
  | ind =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [Refs.ref, h.ind, Refs.entryType, indType_interp h]
    exact indValue_mem u
  | sound =>
    obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [Refs.ref, h.sound, Refs.entryType, soundType_interp h]
    exact soundValue_mem hE hM u

/-- Equality of the complete lambda endpoints published as the primitive
computation law, for every environment and both universe regimes. -/
theorem liftRule_eq {entries : Environment β} (h : Reading constants refs)
    (hE : Basis.Equality.Interface entries refs.eq refs.eqRefl refs.eqRec) (hM : Realizes constants entries)
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
  intro f hf
  apply lamR_congr
  intro proof hp
  apply lamR_congr
  intro a ha
  change app (app (app (app (app (app (constants refs.lift [u, v]) A) R) B) f) proof)
    (constructorAt constants refs u A R a) = app f a
  rw [h.lift, constructorAt_eq h hA hR ha]
  exact liftValue_apply hE hM hA hR hB hf hp ha

theorem indRule_eq (constants : Assignment β V) (refs : Refs β) (levels : List Nat) (env : Nat → V) :
    interp constants levels env (indRuleLhs refs) = interp constants levels env (indRuleRhs refs) := by
  simp only [indRuleLhs, indRuleRhs, indRuleBinders, indPrefix, List.cons_append, List.nil_append,
    AExpr.lamN, interp, regime_always, lamR_zero]

end Ix.Theory.Certified.Quotient
