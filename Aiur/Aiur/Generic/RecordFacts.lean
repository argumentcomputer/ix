import Aiur.Generic.SourceSemantics
import Aiur.Generic.TypeFacts
import Mathlib.Data.List.Forall2

namespace Aiur.Generic

@[simp] theorem RecordHead.positions_subst (h : RecordHead) (types n) :
    (h.subst types).positions n = h.positions n := rfl

@[simp] theorem RecordHead.order_subst (h : RecordHead) (types) (xs : List A) (fallback : A) :
    (h.subst types).order xs fallback = h.order xs fallback := rfl

@[simp] theorem RecordHead.order_length (h : RecordHead) (xs : List A) (fallback : A) :
    (h.order xs fallback).length = (h.positions xs.length).length := by simp [RecordHead.order]

theorem RecordHead.order_map (h : RecordHead) (xs : List A) (fallback : A) (f : A → B) :
    h.order (xs.map f) (f fallback) = (h.order xs fallback).map f := by
  simp only [RecordHead.order, List.length_map, List.map_map]
  apply List.map_congr_left
  intro slot _
  cases slot with
  | none => rfl
  | some i => simp [List.getElem?_map, Option.getD_map]

theorem forall₂_getD {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (fallback : R a b) (i : Nat) :
    R (xs[i]?.getD a) (ys[i]?.getD b) := by
  induction related generalizing i with
  | nil => exact fallback
  | cons h _ ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem RecordHead.order_rel (h : RecordHead) {R : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ R xs ys) (fallback : R a b) :
    List.Forall₂ R (h.order xs a) (h.order ys b) := by
  simp only [RecordHead.order, related.length_eq]
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro slot _
  cases slot with
  | none => exact fallback
  | some i => exact forall₂_getD related fallback i

theorem RecordHead.order_mem (h : RecordHead) {P : A → Prop} (xs : List A) (a : A)
    (items : ∀ x ∈ xs, P x) (fallback : P a) : ∀ x ∈ h.order xs a, P x := by
  intro x hx
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hx
  cases slot with
  | none => exact fallback
  | some i =>
      cases found : xs[i]? with
      | none => simpa [found] using fallback
      | some x => simpa [found] using items x (List.mem_of_getElem? found)

theorem RecordHead.order_attached (h : RecordHead) (xs : List A) (fallback : A) :
    (h.order (xs.attach.map some) none).map
      (fun p => (p.map Subtype.val).getD fallback) = h.order xs fallback := by
  rw [← h.order_map]
  simp

theorem record_bindingNames (head : RecordHead) (ps : List (Pattern F)) :
    (Pattern.record head ps).bindingNames = (head.order ps .wildcard).flatMap Pattern.bindingNames := by
  have h := head.order_map ps (Pattern.wildcard : Pattern F) Pattern.bindingNames
  simp only [Pattern.bindingNames] at h
  simpa only [Pattern.bindingNames, List.flatMap] using congrArg List.flatten h

namespace SourceSemantics

theorem record_matchList_map [DecidableEq F]
    {run : B → SourceValue F → Except EvalError (Option (Environment F Nat))}
    (f : A → B) (xs : List A) (values : List (SourceValue F)) :
    matchListWith run (xs.map f) values = matchListWith (fun x v => run (f x) v) xs values := by
  induction xs generalizing values with
  | nil => cases values <;> rfl
  | cons x xs ih => cases values <;> simp only [List.map_cons, matchListWith, ih]

theorem record_matchList_attach [DecidableEq F] (head : RecordHead)
    (ps : List (Pattern F)) (values : List (SourceValue F)) :
    matchListWith (fun child value => match child with
      | some pat => matchPatternWith constant depth types heap pat.val value
      | none => pure (some [])) (head.order (ps.attach.map some) none) values =
    matchListWith (fun p v => matchPatternWith constant depth types heap p v)
      (head.order ps .wildcard) values := by
  rw [← head.order_attached ps (.wildcard : Pattern F), record_matchList_map]
  congr 1
  funext child value
  cases child <;> simp [matchPatternWith]

/-- Named patterns visit declared fields in layout order, preserving all load errors. -/
theorem match_record [DecidableEq F] (head : RecordHead) (ps : List (Pattern F)) (v : SourceValue F) :
    matchPatternWith constant depth types heap (.record head ps) v =
      match v with
      | .construct n c vs =>
          if n != constructorName types head.type || c != structConstructor then .ok none
          else if (head.order ps .wildcard).length != vs.length then .ok none
          else matchListWith (fun p v => matchPatternWith constant depth types heap p v)
            (head.order ps .wildcard) vs
      | _ => .ok none := by
  cases v <;> simp only [matchPatternWith, RecordHead.order_length,
    List.length_map, List.length_attach, pure, Except.pure, bind, Except.bind]
  split
  · rfl
  · split
    · rfl
    · exact record_matchList_attach head ps _

@[simp] theorem memberValue_subst [DecidableEq F] (types : Types) (field : FieldRef) (v : SourceValue F) :
    memberValue [] (field.subst types) v = memberValue types field v := by
  dsimp only [memberValue, FieldRef.subst]
  have h : constructorName [] ((field.owner.map (Ty.subst types)).getD (.named "$invalid" [])) =
      constructorName types (field.owner.getD (.named "$invalid" [])) := by
    cases field.owner <;> simp [constructorName, Ty.subst_nil, Ty.subst]
  rw [h]

end SourceSemantics
end Aiur.Generic
