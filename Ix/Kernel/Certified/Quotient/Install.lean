/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Certified.Checker

import Ix.Kernel.Certified.Quotient.Reading

/-! # Installing the quotient primitives one at a time

The old branch admitted the five quotient declarations together. Here each
is its own block and is installed in order: the former, the constructor, the
lift, the eliminator, and the soundness axiom. What a later one needs of an
earlier one is a published fact: the former and the constructor are pinned to
their set-theoretic values, the lift to its value over the equality family.
The equality family's interface (`Basis.Equality.Interface`) is read off the
environment, since the `Eq` block installs it in a fixed layout. -/

namespace Ix.Kernel.Certified.Quotient

open Model Model.SetTheory Model.Quotient

universe u v

variable {β : Type u} [DecidableEq β]

/-- Install an entry without a body at a fresh reference, given its
well-formedness and its realization in every model of the environment. -/
def installEntry (env : Env β) (r : ConstRef β) (entry : ConstantEntry β)
    (wf : env.toEnvironment.WF → (env.toEnvironment.insert r entry).WF)
    (realize : ∀ (V : Type v) [SetTheory V] (_ : Model.{u,v} V env),
      ∃ constants' : Assignment β V, Realizes constants' (env.toEnvironment.insert r entry)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  ⟨env.push r entry, fun V _ m => by
    obtain ⟨c', hc'⟩ := realize V m
    refine ⟨⟨c', ?_, ?_⟩⟩
    · rw [Env.toEnvironment_push]; exact hc'
    · rw [Env.toEnvironment_push]; exact wf m.wf⟩

/-- The syntactic side of installing a quotient entry: the entry without its
equations first, then with them, so the equations may refer to the entry. -/
theorem wf_insert {entries : Environment β} (hE : entries.WF) {r : ConstRef β} {entry : ConstantEntry β}
    (hbody : entry.body = none)
    (hTs : entry.type.Scope entry.universes 0) (hTr : entry.type.ReferencesIn entries)
    (hQs : ∀ q ∈ entry.equations, q.lhs.Scope entry.universes 0 ∧ q.rhs.Scope entry.universes 0)
    (hQr : ∀ q ∈ entry.equations,
      q.lhs.ReferencesIn (entries.insert r { entry with equations := [] }) ∧
        q.rhs.ReferencesIn (entries.insert r { entry with equations := [] }))
    (hFs : ∀ f ∈ entry.facts, f.Scope entry.universes) (hFr : ∀ f ∈ entry.facts, f.ReferencesIn entries) :
    (entries.insert r entry).WF := by
  have h₁ : (entries.insert r { entry with equations := [] }).WF :=
    hE.insert hTs (fun b hb => by rw [hbody] at hb; cases hb) hTr (fun b hb => by rw [hbody] at hb; cases hb)
      (fun _ h => nomatch h) (fun _ h => nomatch h) hFs hFr
  have h₂ := h₁.insert (r := r) (entry := entry) hTs (fun b hb => by rw [hbody] at hb; cases hb)
    (AExpr.ReferencesIn.insert hTr) (fun b hb => by rw [hbody] at hb; cases hb) hQs hQr hFs
    (fun f hf => ConstantFact.ReferencesIn.insert (hFr f hf))
  simpa only [Environment.insert_replace] using h₂

omit [DecidableEq β] in
theorem constants_ne_of_fresh {entries : Environment β} {r q : ConstRef β} {e : ConstantEntry β}
    (fresh : entries r = none) (hq : entries q = some e) : q ≠ r := by
  intro h; subst h; rw [fresh] at hq; cases hq

/-- The former. -/
def installType (env : Env β) (q : ConstRef β) (fresh : env.toEnvironment q = none)
    (hTs : (typeType : AExpr β).Scope 1 0)
    {l : VLevel} (ht : TypingClaim.{u,v} env.toEnvironment [] typeType (.sort l)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  installEntry env q ⟨1, typeType, none, [], [.quotient .type]⟩
    (fun hE => wf_insert hE rfl hTs (fun _ h => by simp [typeType, relationType, AExpr.references] at h)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => by simp at h; subst h; trivial)
      (fun _ h => by simp at h; subst h; intro _ h; simp [ConstantFact.references] at h))
    (fun V _ m => by
      let c' : Assignment β V := m.constants.insert q (fun levels => formerValue (levels.getD 0 0))
      have hM' : Realizes c' env.toEnvironment := m.realizes.of_agrees m.wf (Assignment.insert_agrees fresh _ _)
      refine ⟨c', hM'.insert ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro levels _ env'
        exact (ht V c' hM' levels env' (Context.valid_nil _ _ _)).1
      · intro levels hn env'
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
        show c' q [u] ∈ˢ _
        simp only [c', Assignment.insert_same, List.getD_cons_zero]
        exact type_mem u env'
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf levels _ _
        simp only [List.mem_singleton] at hf
        subst hf
        simp [ConstantFact.Meaning, c', Assignment.insert_same])

/-- The constructor. -/
def installCtor (env : Env β) (refs : Refs β) (fresh : env.toEnvironment refs.ctor = none)
    (hTs : (ctorType refs).Scope 1 0)
    (hq : HasFormer env.toEnvironment refs) (hTr : (ctorType refs).ReferencesIn env.toEnvironment)
    {l : VLevel} (ht : TypingClaim.{u,v} env.toEnvironment [] (ctorType refs) (.sort l)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  installEntry env refs.ctor ⟨1, ctorType refs, none, [], [.quotient .ctor]⟩
    (fun hE => wf_insert hE rfl hTs hTr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => by simp at h; subst h; trivial)
      (fun _ h => by simp at h; subst h; intro _ h; simp [ConstantFact.references] at h))
    (fun V _ m => by
      let c' : Assignment β V := m.constants.insert refs.ctor (fun levels => constructorValue (levels.getD 0 0))
      have hM' : Realizes c' env.toEnvironment := m.realizes.of_agrees m.wf (Assignment.insert_agrees fresh _ _)
      refine ⟨c', hM'.insert ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro levels _ env'
        exact (ht V c' hM' levels env' (Context.valid_nil _ _ _)).1
      · intro levels hn env'
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
        show c' refs.ctor [u] ∈ˢ _
        simp only [c', Assignment.insert_same, List.getD_cons_zero]
        exact ctor_mem (hq.reading hM') u env'
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf levels _ _
        simp only [List.mem_singleton] at hf
        subst hf
        simp [ConstantFact.Meaning, c', Assignment.insert_same])

/-- The lift; its computation rule is derived at reduction time from the facts. -/
def installLift (env : Env β) (refs : Refs β) (fresh : env.toEnvironment refs.lift = none)
    (hTs : (liftType refs).Scope 2 0)
    (hq : HasFormer env.toEnvironment refs) (hTr : (liftType refs).ReferencesIn env.toEnvironment)
    {l : VLevel} (ht : TypingClaim.{u,v} env.toEnvironment [] (liftType refs) (.sort l)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  installEntry env refs.lift ⟨2, liftType refs, none, [], [.quotientLift refs.eq]⟩
    (fun hE => wf_insert hE rfl hTs hTr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => by simp at h; subst h; trivial)
      (fun _ h => by
        simp at h; subst h
        intro q hq'
        simp only [ConstantFact.references, List.mem_singleton] at hq'
        subst hq'
        exact hTr refs.eq (by simp [liftType, liftPrefix, invariantType, Basis.Equality.applied, AExpr.forallN, AExpr.appN, relationType, applied, AExpr.references])))
    (fun V _ m => by
      let c' : Assignment β V := m.constants.insert refs.lift
        (fun levels => liftValue m.constants refs.eq (levels.getD 0 0) (levels.getD 1 0))
      have hagree := Assignment.insert_agrees (constants := m.constants) fresh
        (fun levels => liftValue m.constants refs.eq (levels.getD 0 0) (levels.getD 1 0))
      have hM' : Realizes c' env.toEnvironment := m.realizes.of_agrees m.wf hagree
      have hceq : ∀ v, c' refs.eq [v] = m.constants refs.eq [v] := by
        intro v
        have hin := hTr refs.eq (by simp [liftType, liftPrefix, invariantType, Basis.Equality.applied, AExpr.forallN, AExpr.appN, relationType, applied, AExpr.references])
        cases he : env.toEnvironment refs.eq with
        | none => simp [he] at hin
        | some entry => exact hagree _ _ he [v]
      have hl : LiftReading c' refs.eq refs.lift := by
        intro u v
        show c' refs.lift [u, v] = _
        simp only [c', Assignment.insert_same, List.getD_cons_zero, List.getD_cons_succ]
        exact (liftValue_congr (hceq v)).symm
      refine ⟨c', hM'.insert ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro levels _ env'
        exact (ht V c' hM' levels env' (Context.valid_nil _ _ _)).1
      · intro levels hn env'
        cases levels with
        | nil => cases hn
        | cons u tail =>
          obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Nat.succ.inj hn)
          rw [hl u v]
          exact lift_mem (hq.reading hM') u v env'
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf levels hn _
        simp only [List.mem_singleton] at hf
        subst hf
        cases levels with
        | nil => cases hn
        | cons u tail =>
          obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp (Nat.succ.inj hn)
          exact hl u v)

/-- The eliminator; its computation rule holds outright. -/
def installInd (env : Env β) (refs : Refs β) (fresh : env.toEnvironment refs.ind = none)
    (hTs : (indType refs).Scope 1 0)
    (hq : HasFormer env.toEnvironment refs) (hc : HasCtor env.toEnvironment refs)
    (hTr : (indType refs).ReferencesIn env.toEnvironment)
    {l : VLevel} (ht : TypingClaim.{u,v} env.toEnvironment [] (indType refs) (.sort l)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  installEntry env refs.ind ⟨1, indType refs, none, [], [.quotient .ind]⟩
    (fun hE => wf_insert hE rfl hTs hTr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => by simp at h; subst h; trivial)
      (fun _ h => by simp at h; subst h; intro _ h; simp [ConstantFact.references] at h))
    (fun V _ m => by
      let c' : Assignment β V := m.constants.insert refs.ind (fun _ => SetTheory.pt)
      have hM' : Realizes c' env.toEnvironment := m.realizes.of_agrees m.wf (Assignment.insert_agrees fresh _ _)
      refine ⟨c', hM'.insert ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro levels _ env'
        exact (ht V c' hM' levels env' (Context.valid_nil _ _ _)).1
      · intro levels hn env'
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
        show c' refs.ind [u] ∈ˢ _
        simp only [c', Assignment.insert_same]
        exact ind_mem (hq.reading hM') (hc.reading hM') u env'
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf _ _ _
        simp only [List.mem_singleton] at hf
        subst hf
        trivial)

/-- The soundness axiom. -/
def installSound (env : Env β) (refs : Refs β) (sound : ConstRef β) (fresh : env.toEnvironment sound = none)
    (hTs : (soundType refs).Scope 1 0)
    (hq : HasFormer env.toEnvironment refs) (hc : HasCtor env.toEnvironment refs)
    (hE : EqInterface env.toEnvironment refs.eq)
    (hTr : (soundType refs).ReferencesIn env.toEnvironment)
    {l : VLevel} (ht : TypingClaim.{u,v} env.toEnvironment [] (soundType refs) (.sort l)) :
    { env' : Env β // StepClaim.{u,v} env env' } :=
  installEntry env sound ⟨1, soundType refs, none, [], []⟩
    (fun hE' => wf_insert hE' rfl hTs hTr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ h => nomatch h))
    (fun V _ m => by
      obtain ⟨b, -, hI⟩ := hE
      let c' : Assignment β V := m.constants.insert sound (fun _ => SetTheory.pt)
      have hM' : Realizes c' env.toEnvironment := m.realizes.of_agrees m.wf (Assignment.insert_agrees fresh _ _)
      refine ⟨c', hM'.insert ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · intro levels _ env'
        exact (ht V c' hM' levels env' (Context.valid_nil _ _ _)).1
      · intro levels hn env'
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hn
        show c' sound [u] ∈ˢ _
        simp only [c', Assignment.insert_same]
        exact sound_mem (hq.reading hM') (hc.reading hM') hI hM' u env'
      · intro body hb; cases hb
      · intro body hb; cases hb
      · intro law hl; cases hl
      · intro fact hf; cases hf)

/-- The references named by a stored quotient type, in order of first occurrence. -/
def occurrences (t : VExpr β) : List (ConstRef β) := t.refs.eraseDups

end Ix.Kernel.Certified.Quotient
