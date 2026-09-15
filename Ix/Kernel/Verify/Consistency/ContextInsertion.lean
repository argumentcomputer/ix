/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Formation

/-! Insert a local beneath retained dependent binders. The same structural
relation lifts generated typing origins and their beta-conversion evidence. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

inductive ContextInsertion {β : Type u} : Model.Context β → Model.Context β → Nat → Prop
  | root (context : Model.Context β) (domain : AExpr β) :
      ContextInsertion context (context.push domain) 0
  | push {source target cutoff} (prior : ContextInsertion source target cutoff) (domain : AExpr β) :
      ContextInsertion (source.push domain) (target.push (domain.liftN 1 cutoff)) (cutoff + 1)

theorem ContextInsertion.lookup {β : Type u} {source target : Model.Context β} {cutoff index : Nat}
    {type : AExpr β} (insertion : ContextInsertion source target cutoff)
    (found : source[index]? = some type) :
    target[if index < cutoff then index else index + 1]? = some (type.liftN 1 cutoff) := by
  induction insertion generalizing index type with
  | root context domain =>
      simp only [Nat.not_lt_zero, ↓reduceIte, Model.Context.push,
        List.getElem?_cons_succ, List.getElem?_map, found, Option.map_some]
  | @push source target cutoff prior domain ih =>
      cases index with
      | zero =>
          simp only [Model.Context.push, List.getElem?_cons_zero, Option.some.injEq] at found
          subst type
          simp only [Nat.zero_lt_succ, ↓reduceIte, Model.Context.push, List.getElem?_cons_zero]
          exact congrArg some (by
            simpa only [Nat.add_comm 1 cutoff] using
              AExpr.liftN_liftN_comm domain 1 cutoff 1 0 (Nat.zero_le _))
      | succ index =>
          simp only [Model.Context.push, List.getElem?_cons_succ, List.getElem?_map] at found
          obtain ⟨type, atIndex, rfl⟩ := Option.map_eq_some_iff.mp found
          have shifted : (if index + 1 < cutoff + 1 then index + 1 else index + 1 + 1) =
              (if index < cutoff then index else index + 1) + 1 := by
            split <;> split <;> omega
          rw [shifted]
          simp only [Model.Context.push, List.getElem?_cons_succ, List.getElem?_map,
            ih atIndex, Option.map_some]
          exact congrArg some (by
            simpa only [Nat.add_comm 1 cutoff] using
              AExpr.liftN_liftN_comm type 1 cutoff 1 0 (Nat.zero_le _))

theorem ContextInsertion.source_valid {β : Type u} {source target : Model.Context β} {cutoff : Nat}
    (insertion : ContextInsertion source target cutoff)
    {V : Type v} [SetTheory V] {constants : Assignment β V} {levels : List Nat} {env : Nat → V}
    (valid : target.Valid constants levels env) :
    source.Valid constants levels (Valuation.skip 1 cutoff env) := by
  intro index type found
  have selected := valid (if index < cutoff then index else index + 1) (type.liftN 1 cutoff)
    (insertion.lookup found)
  simpa only [wellDenoted_liftN, interp_liftN, Valuation.skip, Nat.add_comm 1 index,
    apply_ite] using selected

theorem ContextInsertion.typing {β : Type u} {entries : Model.Environment β}
    {source target : Model.Context β} {cutoff : Nat} {term type : AExpr β}
    (insertion : ContextInsertion source target cutoff)
    (typed : TypingClaim.{u,v} entries source term type) :
    TypingClaim.{u,v} entries target (term.liftN 1 cutoff) (type.liftN 1 cutoff) := by
  intro V _ constants realizes levels env valid
  simpa only [wellDenoted_liftN, interp_liftN] using
    typed V constants realizes levels _ (insertion.source_valid valid)

theorem ContextInsertion.conversion {β : Type u} {entries : Model.Environment β}
    {source target : Model.Context β} {cutoff : Nat} {left right : AExpr β}
    (insertion : ContextInsertion source target cutoff)
    (converted : ConversionClaim.{u,v} entries source left right) :
    ConversionClaim.{u,v} entries target (left.liftN 1 cutoff) (right.liftN 1 cutoff) := by
  intro V _ constants realizes levels env valid
  simpa only [interp_liftN] using
    converted V constants realizes levels _ (insertion.source_valid valid)

end Ix.Kernel.Consistency
