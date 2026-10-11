import Ix.CompileCert.Canon.ExpandIndex
import Ix.CompileCert.Canon.Rename

namespace Ix.CompileCert.Canon

/-- The Id-loop invariant may use membership in the actual traversed list;
no claim is required for source representatives outside that list. -/
theorem forIn_id_inv_mem {α β : Type} (P : β → Prop)
    (body : α → β → Id (ForInStep β)) (xs : List α) (initial : β)
    (start : P initial)
    (step : ∀ x ∈ xs, ∀ state, P state → P (body x state).value) :
    P (forIn (m := Id) xs initial body) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons x xs ih =>
    rw [List.forIn_cons]
    have next := step x List.mem_cons_self initial start
    have tail : ∀ x ∈ xs, ∀ state, P state → P (body x state).value :=
      fun y member state scopeProof => step y (List.mem_cons_of_mem _ member) state scopeProof
    generalize hbody : body x initial = result at next ⊢
    cases result with
    | done value => exact next
    | yield value => exact ih value next tail

theorem forIn_id_inv_array_mem {α β : Type} (P : β → Prop)
    (body : α → β → Id (ForInStep β)) (xs : Array α) (initial : β)
    (start : P initial)
    (step : ∀ x ∈ xs, ∀ state, P state → P (body x state).value) :
    P (forIn (m := Id) xs initial body) := by
  rw [← Array.forIn_toList]
  exact forIn_id_inv_mem P body xs.toList initial start (by simpa using step)

inductive ForStepRelated {α β : Type} (R : α → β → Prop) :
    ForInStep α → ForInStep β → Prop
  | done {a b} : R a b → ForStepRelated R (.done a) (.done b)
  | yield {a b} : R a b → ForStepRelated R (.yield a) (.yield b)

/-- Paired loop steps preserve related results and identical stopping
decisions. A state relation may existentially carry a growing finite name
correspondence; it need not be one fixed global renaming function. -/
theorem forIn_id_related {α α' β β' : Type}
    {A : α → α' → Prop} {B : β → β' → Prop}
    (left : α → β → Id (ForInStep β))
    (right : α' → β' → Id (ForInStep β'))
    {xs : List α} {ys : List α'} (items : LRel A xs ys)
    (step : ∀ a a', A a a' → ∀ b b', B b b' →
      ForStepRelated B (left a b) (right a' b'))
    {initial : β} {initial' : β'} (start : B initial initial') :
    B (forIn (m := Id) xs initial left) (forIn (m := Id) ys initial' right) := by
  induction items generalizing initial initial' with
  | nil => exact start
  | @cons a a' xs ys item tail ih =>
    rw [List.forIn_cons, List.forIn_cons]
    have next := step a a' item _ _ start
    generalize hl : left a initial = result at next ⊢
    generalize hr : right a' initial' = result' at next ⊢
    cases next with
    | done related => exact related
    | yield related => exact ih related

theorem forIn_id_related_array {α α' β β' : Type}
    {A : α → α' → Prop} {B : β → β' → Prop}
    (left : α → β → Id (ForInStep β))
    (right : α' → β' → Id (ForInStep β'))
    {xs : Array α} {ys : Array α'} (items : LRel A xs.toList ys.toList)
    (step : ∀ a a', A a a' → ∀ b b', B b b' →
      ForStepRelated B (left a b) (right a' b'))
    {initial : β} {initial' : β'} (start : B initial initial') :
    B (forIn (m := Id) xs initial left) (forIn (m := Id) ys initial' right) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_id_related left right items step start

end Ix.CompileCert.Canon
