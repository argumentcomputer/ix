/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/LevelCongruence.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Judgment
import Ix.Kernel.Model.Support

/-!
# Replacing universe levels by equivalent levels

Kernel universe substitution uses simplifying constructors. Its result can
therefore differ from structural substitution while denoting the same type.
The relations below retain every term constructor, reference, index, and
binder annotation. Only universe expressions may change, and their values
must agree under every universe valuation.

This congruence preserves hereditary validity as well as interpretation.
Consequently it transports typing without assuming that an arbitrary
semantically equal expression is a valid type.
-/

namespace Ix.Kernel

universe u v
variable {β : Type u}

namespace VExpr

theorem LevelWF.liftN {e : VExpr β} {n : Nat} (scope : e.LevelWF n)
    (count cutoff : Nat) : (e.liftN count cutoff).LevelWF n := by
  induction e generalizing cutoff <;> simp_all [VExpr.liftN, VExpr.LevelWF]

theorem LevelWF.inst {e a : VExpr β} {n : Nat}
    (scope : e.LevelWF n) (argument : a.LevelWF n) (cutoff : Nat := 0) :
    (e.inst a cutoff).LevelWF n := by
  induction e generalizing cutoff with
  | bvar i =>
      by_cases hi : i < cutoff
      · simp [VExpr.inst, instVar, hi, VExpr.LevelWF]
      · by_cases he : i = cutoff
        · simpa [VExpr.inst, instVar, hi, he] using argument.liftN cutoff 0
        · simp [VExpr.inst, instVar, hi, he, VExpr.LevelWF]
  | _ => simp_all [VExpr.inst, VExpr.LevelWF]

/-- Structural equality except for semantically equivalent universe levels. -/
inductive LevelEquivalent : VExpr β → VExpr β → Prop
  | bvar (index) : LevelEquivalent (.bvar index) (.bvar index)
  | sort {left right} (levels : left ≈ right) :
      LevelEquivalent (.sort left) (.sort right)
  | const (ref) {left right}
      (levels : ∀ valuation, left.map (VLevel.eval valuation) =
        right.map (VLevel.eval valuation)) :
      LevelEquivalent (.const ref left) (.const ref right)
  | app {f f' a a'} (fn : LevelEquivalent f f') (arg : LevelEquivalent a a') :
      LevelEquivalent (.app f a) (.app f' a')
  | lam {A A' b b'} (domain : LevelEquivalent A A') (body : LevelEquivalent b b') :
      LevelEquivalent (.lam A b) (.lam A' b')
  | forallE {A A' B B'} (domain : LevelEquivalent A A') (body : LevelEquivalent B B') :
      LevelEquivalent (.forallE A B) (.forallE A' B')
  | proj (ref index) {e e'} (major : LevelEquivalent e e') :
      LevelEquivalent (.proj ref index e) (.proj ref index e')
  | natLit (value) : LevelEquivalent (.natLit value) (.natLit value)

namespace LevelEquivalent

theorem refl (e : VExpr β) : LevelEquivalent e e := by
  induction e with
  | bvar i => exact .bvar i
  | sort l => exact .sort (VLevel.equiv_def.mpr fun _ => rfl)
  | const r ls => exact .const r fun _ => rfl
  | app _ _ hf ha => exact .app hf ha
  | lam _ _ hA hb => exact .lam hA hb
  | forallE _ _ hA hB => exact .forallE hA hB
  | proj r i _ he => exact .proj r i he
  | natLit n => exact .natLit n

theorem liftN {e e' : VExpr β} (h : LevelEquivalent e e') (n k : Nat) :
    LevelEquivalent (e.liftN n k) (e'.liftN n k) := by
  induction h generalizing k with
  | bvar i => exact .bvar _
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ hf ha => exact .app (hf k) (ha k)
  | lam _ _ hA hb => exact .lam (hA k) (hb (k + 1))
  | forallE _ _ hA hB => exact .forallE (hA k) (hB (k + 1))
  | proj r i _ he => exact .proj r i (he k)
  | natLit n => exact .natLit n

theorem inst {e e' a a' : VExpr β} (h : LevelEquivalent e e')
    (ha : LevelEquivalent a a') (k : Nat := 0) :
    LevelEquivalent (e.inst a k) (e'.inst a' k) := by
  induction h generalizing k with
  | bvar i =>
      by_cases hi : i < k
      · simpa [VExpr.inst, instVar, hi] using LevelEquivalent.bvar (β := β) i
      · by_cases hik : i = k
        · simpa [VExpr.inst, instVar, hi, hik] using ha.liftN k 0
        · simpa [VExpr.inst, instVar, hi, hik] using LevelEquivalent.bvar (β := β) (i - 1)
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ hf hb => exact .app (hf k) (hb k)
  | lam _ _ hA hb => exact .lam (hA k) (hb (k + 1))
  | forallE _ _ hA hB => exact .forallE (hA k) (hB (k + 1))
  | proj r i _ he => exact .proj r i (he k)
  | natLit n => exact .natLit n

end LevelEquivalent

theorem instL_liftN (e : VExpr β) (levels : List VLevel) (n k : Nat) :
    (e.liftN n k).instL levels = (e.instL levels).liftN n k := by
  induction e generalizing k <;> simp_all [VExpr.liftN, VExpr.instL]

theorem instL_inst (e a : VExpr β) (levels : List VLevel) (k : Nat := 0) :
    (e.inst a k).instL levels = (e.instL levels).inst (a.instL levels) k := by
  induction e generalizing k with
  | bvar i =>
      by_cases hi : i < k
      · simp [VExpr.inst, VExpr.instL, instVar, hi]
      · by_cases hik : i = k <;>
          simp [VExpr.inst, VExpr.instL, instVar, hi, hik, instL_liftN]
  | _ => simp_all [VExpr.inst, VExpr.instL]

/-- The production empty-argument fast path is justified by universe scope. -/
theorem LevelWF.instL_nil {e : VExpr β} (scope : e.LevelWF 0) :
    e.instL [] = e := by
  induction e with
  | bvar _ | natLit _ => rfl
  | sort l =>
      exact congrArg VExpr.sort (VLevel.inst_id scope)
  | const r ls =>
      simp only [VExpr.instL, VExpr.const.injEq, true_and]
      simpa using List.map_congr_left (f := VLevel.inst []) (g := id)
        (fun l hl => VLevel.inst_id (scope l hl))
  | app _ _ hf ha => simp only [VExpr.instL, hf scope.1, ha scope.2]
  | lam _ _ hA hb => simp only [VExpr.instL, hA scope.1, hb scope.2]
  | forallE _ _ hA hB => simp only [VExpr.instL, hA scope.1, hB scope.2]
  | proj r i _ he => exact congrArg (VExpr.proj r i) (he scope)

end VExpr

namespace Model
namespace AExpr

/-- The binder conditions at their exact expression occurrences. -/
def annotations : AExpr β → AnnotationTree
  | .bvar _ | .sort _ | .const _ _ | .natLit _ => .leaf
  | .app f a => .app f.annotations a.annotations
  | .lam p A b => .lam p.toRaw A.annotations b.annotations
  | .forallE p A B => .forallE p.toRaw A.annotations B.annotations
  | .proj _ _ e => .proj e.annotations

/-- Raw syntax and occurrence annotations uniquely determine a reading. -/
theorem eq_of_erase_annotations {left right : AExpr β}
    (shape : left.erase = right.erase) (conditions : left.annotations = right.annotations) :
    left = right := by
  induction left generalizing right with
  | app f a hf ha =>
      cases right <;> simp [erase] at shape
      next f' a' =>
        simp only [annotations, AnnotationTree.app.injEq] at conditions
        rw [hf shape.1 conditions.1, ha shape.2 conditions.2]
  | lam p A b hA hb =>
      cases right <;> simp [erase] at shape
      next q A' b' =>
        simp only [annotations, AnnotationTree.lam.injEq] at conditions
        have equal := Certified.PropWhen.toRaw_injective conditions.1
        subst q
        rw [hA shape.1 conditions.2.1, hb shape.2 conditions.2.2]
  | forallE p A b hA hb =>
      cases right <;> simp [erase] at shape
      next q A' b' =>
        simp only [annotations, AnnotationTree.forallE.injEq] at conditions
        have equal := Certified.PropWhen.toRaw_injective conditions.1
        subst q
        rw [hA shape.1 conditions.2.1, hb shape.2 conditions.2.2]
  | proj r i e he =>
      cases right <;> simp [erase] at shape
      next r' i' e' =>
        obtain ⟨rfl, rfl, equal⟩ := shape
        exact congrArg (AExpr.proj r i) (he equal (AnnotationTree.proj.inj conditions))
  | _ => cases right <;> simp_all [erase]

theorem Scope.instL {e : AExpr β} {n depth target : Nat} {levels : List VLevel}
    (scope : e.Scope n depth) (arguments : ∀ level ∈ levels, level.WF target) :
    (e.instL levels).Scope target depth := by
  have condition : ∀ p : Certified.PropWhen, p.WF n →
      (Certified.instCondition levels p).WF target := by
    intro p hp
    apply hp.bind
    intro i _
    apply Certified.zeroCondition_wf
    exact VLevel.WF.inst (l := .param i) arguments
  induction e generalizing depth with
  | bvar _ | natLit _ => exact scope
  | sort _ => exact VLevel.WF.inst arguments
  | const r ls =>
      intro level member
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
      exact VLevel.WF.inst arguments
  | app _ _ hf ha => exact ⟨hf scope.1, ha scope.2⟩
  | lam p _ _ hA hb | forallE p _ _ hA hb =>
      exact ⟨condition p scope.1, hA scope.2.1, hb scope.2.2⟩
  | proj _ _ _ he => exact he scope

theorem references_instL (e : AExpr β) (levels : List VLevel) :
    (e.instL levels).references = e.references := by
  induction e <;> simp_all [instL, references]

/-- Universe congruence with the same binder annotations at every occurrence. -/
inductive LevelEquivalent : AExpr β → AExpr β → Prop
  | bvar (index) : LevelEquivalent (.bvar index) (.bvar index)
  | sort {left right} (levels : left ≈ right) :
      LevelEquivalent (.sort left) (.sort right)
  | const (ref) {left right}
      (levels : ∀ valuation, left.map (VLevel.eval valuation) =
        right.map (VLevel.eval valuation)) :
      LevelEquivalent (.const ref left) (.const ref right)
  | app {f f' a a'} (fn : LevelEquivalent f f') (arg : LevelEquivalent a a') :
      LevelEquivalent (.app f a) (.app f' a')
  | lam (condition) {A A' b b'}
      (domain : LevelEquivalent A A') (body : LevelEquivalent b b') :
      LevelEquivalent (.lam condition A b) (.lam condition A' b')
  | forallE (condition) {A A' B B'}
      (domain : LevelEquivalent A A') (body : LevelEquivalent B B') :
      LevelEquivalent (.forallE condition A B) (.forallE condition A' B')
  | proj (ref index) {e e'} (major : LevelEquivalent e e') :
      LevelEquivalent (.proj ref index e) (.proj ref index e')
  | natLit (value) : LevelEquivalent (.natLit value) (.natLit value)

/-- Copy occurrence annotations to a structurally congruent expression. -/
theorem reannotate_levels (e : AExpr β) {source : VExpr β}
    (same : VExpr.LevelEquivalent e.erase source) :
    ∃ result : AExpr β, result.erase = source ∧ LevelEquivalent e result := by
  induction e generalizing source with
  | bvar i => cases same; exact ⟨.bvar i, rfl, .bvar i⟩
  | sort l => cases same with | sort h => exact ⟨.sort _, rfl, .sort h⟩
  | const r ls => cases same with | const _ h => exact ⟨.const r _, rfl, .const r h⟩
  | app f a hf ha =>
      cases same with
      | app sf sa =>
          obtain ⟨f', rfl, ef⟩ := hf sf
          obtain ⟨a', rfl, ea⟩ := ha sa
          exact ⟨.app f' a', rfl, .app ef ea⟩
  | lam p A b hA hb =>
      cases same with
      | lam sA sb =>
          obtain ⟨A', rfl, eA⟩ := hA sA
          obtain ⟨b', rfl, eb⟩ := hb sb
          exact ⟨.lam p A' b', rfl, .lam p eA eb⟩
  | forallE p A B hA hB =>
      cases same with
      | forallE sA sB =>
          obtain ⟨A', rfl, eA⟩ := hA sA
          obtain ⟨B', rfl, eB⟩ := hB sB
          exact ⟨.forallE p A' B', rfl, .forallE p eA eB⟩
  | proj r i e ih =>
      cases same with
      | proj _ _ se =>
          obtain ⟨e', rfl, ee⟩ := ih se
          exact ⟨.proj r i e', rfl, .proj r i ee⟩
  | natLit n => cases same; exact ⟨.natLit n, rfl, .natLit n⟩

namespace LevelEquivalent

theorem annotations {e e' : AExpr β} (same : LevelEquivalent e e') :
    e.annotations = e'.annotations := by
  induction same <;> simp_all [AExpr.annotations]

theorem erase {e e' : AExpr β} (same : LevelEquivalent e e') :
    VExpr.LevelEquivalent e.erase e'.erase := by
  induction same with
  | bvar i => exact .bvar i
  | sort h => exact .sort h
  | const r h => exact .const r h
  | app _ _ hf ha => exact .app hf ha
  | lam _ _ _ hA hb => exact .lam hA hb
  | forallE _ _ _ hA hb => exact .forallE hA hb
  | proj r i _ he => exact .proj r i he
  | natLit n => exact .natLit n

/-- Equivalent levels need not have the same scope: the actual target levels
must separately be well scoped. Indices and binder annotations are preserved. -/
theorem scope {e e' : AExpr β} {n depth : Nat} (same : LevelEquivalent e e')
    (source : e.Scope n depth) (levels : e'.erase.LevelWF n) : e'.Scope n depth := by
  induction same generalizing depth with
  | bvar _ | natLit _ => exact source
  | sort _ | const _ _ => exact levels
  | app _ _ hf ha => exact ⟨hf source.1 levels.1, ha source.2 levels.2⟩
  | lam _ _ _ hA hb | forallE _ _ _ hA hb =>
      exact ⟨source.1, hA source.2.1 levels.1, hb source.2.2 levels.2⟩
  | proj _ _ _ he => exact he source levels

theorem references {e e' : AExpr β} (same : LevelEquivalent e e') :
    e.references = e'.references := by
  induction same <;> simp_all [AExpr.references]

/-- A fixed declared reading agrees when its raw tree is congruent and its
occurrence annotations match. These are syntactic premises, not typing. -/
theorem of_erase_annotations {e e' : AExpr β}
    (shape : VExpr.LevelEquivalent e.erase e'.erase)
    (conditions : e.annotations = e'.annotations) : LevelEquivalent e e' := by
  obtain ⟨output, erased, same⟩ := reannotate_levels e shape
  have equal := eq_of_erase_annotations erased (same.annotations.symm.trans conditions)
  exact equal ▸ same

theorem interp {e e' : AExpr β} (same : LevelEquivalent e e')
    {V : Type v} [SetTheory V] (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    Model.interp constants levels env e = Model.interp constants levels env e' := by
  induction same generalizing env with
  | bvar _ | natLit _ => rfl
  | sort h => exact congrArg SetTheory.univ (VLevel.equiv_def.mp h levels)
  | const r h => exact congrArg (constants r) (h levels)
  | app _ _ hf ha => simp only [Model.interp, hf, ha]
  | lam p _ _ hA hb | forallE p _ _ hA hb =>
      simp only [Model.interp, hA]
      congr 1
      funext x
      exact hb _
  | proj r i _ he => exact congrArg (projectValue i) (he env)

theorem wellDenoted {e e' : AExpr β} (same : LevelEquivalent e e')
    {V : Type v} [SetTheory V] (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    WellDenoted constants levels env e ↔ WellDenoted constants levels env e' := by
  induction same generalizing env with
  | bvar _ | sort _ | const _ _ | natLit _ => rfl
  | app sf sa hf ha =>
      simp only [WellDenoted, hf, ha, sf.interp constants levels, sa.interp constants levels]
  | lam p sA sb hA hb | forallE p sA sb hA hb =>
      simp only [WellDenoted, hA, hb, sA.interp constants levels, sb.interp constants levels]
  | proj r i se he => exact he env

/-- Type transport uses hereditary validity, not just equality of denotations. -/
theorem typing {entries : Environment β} {context : Context β} {e A B : AExpr β}
    (same : LevelEquivalent A B) (typed : TypingClaim.{u,v} entries context e A) :
    TypingClaim.{u,v} entries context e B := by
  intro V _ constants realizes levels env valid
  obtain ⟨termValid, typeValid, member⟩ := typed V constants realizes levels env valid
  exact ⟨termValid, (same.wellDenoted constants levels env).mp typeValid,
    same.interp constants levels env ▸ member⟩

/-- Equivalent universe expressions also preserve typing of the term being
interpreted, including when that term is itself an inferred type. -/
theorem termTyping {entries : Environment β} {context : Context β} {e e' A : AExpr β}
    (same : LevelEquivalent e e') (typed : TypingClaim.{u,v} entries context e A) :
    TypingClaim.{u,v} entries context e' A := by
  intro V _ constants realizes levels env valid
  obtain ⟨termValid, typeValid, member⟩ := typed V constants realizes levels env valid
  exact ⟨(same.wellDenoted constants levels env).mp termValid, typeValid,
    same.interp constants levels env ▸ member⟩

end LevelEquivalent
end AExpr
end Model
end Ix.Kernel
