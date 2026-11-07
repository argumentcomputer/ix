import Aiur.Generic.PatternSequenceFacts
import Aiur.Generic.PatternChoiceFacts
import Aiur.Generic.OrPatternFacts

namespace Aiur.Generic.PatternLowering
open SourceSemantics

theorem nominal_name (n : String) : constructorName [] (.named n []) = n := by
  simp [constructorName, Ty.subst, Ty.toCore, Instance.symbol]

private theorem tuple_miss [DecidableEq F] (patterns : List (Pattern F)) (names : List String)
    (lengths : patterns.length = names.length) (value : SourceValue F)
    (missed : (Aiur.Pattern.tuple (names.map Aiur.Pattern.bind)).bindings value = none) :
    matchPatternWith constant depth [] heap (.tuple patterns) value = .ok none := by
  cases value <;> simp only [matchPatternWith, pure, Except.pure, bind, Except.bind]
  rename_i values
  simp only [Aiur.Pattern.bindings, bindingsList_binders_eq] at missed
  have different : names.length ≠ values.length := by intro h; simp [h] at missed
  simp [lengths, different]

private theorem construct_miss [DecidableEq F] (patterns : List (Pattern F)) (names : List String)
    (lengths : patterns.length = names.length) (name ctor : String) (value : SourceValue F)
    (missed : (Aiur.Pattern.construct name ctor (names.map Aiur.Pattern.bind)).bindings value = none) :
    matchPatternWith constant depth [] heap (.construct (.named name []) ctor patterns) value = .ok none := by
  cases value <;> simp only [matchPatternWith, nominal_name, pure, Except.pure, bind, Except.bind]
  rename_i other ctor' values
  by_cases namesEq : name = other
  · subst other
    by_cases ctorEq : ctor = ctor'
    · subst ctor'
      simp only [Aiur.Pattern.bindings, true_and, and_self, ↓reduceIte, bindingsList_binders_eq] at missed
      have different : names.length ≠ values.length := by intro h; simp [h] at missed
      simp [lengths, different]
    · simp [ctorEq, Ne.symm ctorEq]
  · simp [namesEq, Ne.symm namesEq]

/-- Soundness of a flattened pattern plan, before its enclosing let or match
continuation runs. The result recovers exactly the native user bindings. -/
theorem PlanTree.attempt_sound [DecidableEq F] (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value))
    {accepted : Bool} {final : Environment F Nat}
    (attempted : Attempt heap (tree.toPlan input).steps locals accepted final) :
    Outcome (matchPatternWith constant depth [] heap tree.erase value)
      (resolveBindings (tree.toPlan input).bindings final) accepted := by
  have sub (child : PlanTree F) (smaller : sizeOf child < sizeOf tree) (name : String)
      (safe : (name :: child.temps).Nodup) (value : SourceValue F) (locals : Environment F Nat)
      (found : locals.find? (·.1 == name) = some (name, value)) {accepted final}
      (attempted : Attempt heap (child.toPlan name).steps locals accepted final) :
      Outcome (matchPatternWith constant depth [] heap child.erase value)
        (resolveBindings (child.toPlan name).bindings final) accepted :=
    PlanTree.attempt_sound child name safe constant depth heap value locals found attempted
  have children (parts : List (String × PlanTree F))
      (smaller : ∀ p ∈ parts, sizeOf p.2 < sizeOf tree)
      (safe : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup)
      (values : List (SourceValue F)) (lengths : parts.length = values.length)
      (locals : Environment F Nat) {accepted final}
      (attempted : Attempt heap (parts.flatMap (fun p => (p.2.toPlan p.1).steps))
        (((parts.map Prod.fst).zip values) ++ locals) accepted final) :
      Outcome (matchListWith (fun p v => matchPatternWith constant depth [] heap p.2.erase v) parts values)
        (resolveBindings (parts.flatMap fun p => (p.2.toPlan p.1).bindings) final) accepted := by
    apply sequence_sound _ parts _ ((grouped_names_perm parts Prod.fst (fun p => p.2.temps)).nodup_iff.mp safe) _ attempted
    · intro part hp locals value accepted final safe found attempted
      exact sub part.2 (smaller part hp) part.1 safe value locals found attempted
    · apply (List.forall₂_map_left_iff
        (R := fun name value => (((parts.map Prod.fst).zip values) ++ locals).find? (·.1 == name) = some (name, value))
        (f := Prod.fst)).mp
      exact lookup_zip _ values locals (List.nodup_append.mp safe).1 (by simpa using lengths)
  cases tree with
  | literal x =>
      simp only [PlanTree.toPlan] at attempted ⊢
      cases attempted with
      | testHit found' matched rest =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          have empty := bindings_names matched
          simp only [patternNames, List.map_eq_nil_iff] at empty
          subst_vars
          cases rest
          exact ⟨[], by simp only [PlanTree.erase, matchPatternWith, matched, pure, Except.pure], rfl⟩
      | testMiss found' missed =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          simp only [Outcome, Bool.false_eq_true, ↓reduceIte, PlanTree.erase, matchPatternWith,
            missed, pure, Except.pure]
  | wildcard =>
      simp only [PlanTree.toPlan] at attempted ⊢
      cases attempted
      exact ⟨[], by simp only [PlanTree.erase, matchPatternWith, pure, Except.pure], rfl⟩
  | bind name =>
      simp only [PlanTree.toPlan] at attempted ⊢
      cases attempted
      refine ⟨[(name, value)], by simp only [PlanTree.erase, matchPatternWith, pure, Except.pure], ?_⟩
      simp [resolveBindings_cons, found]
  | choice stem left right layout =>
      obtain ⟨safeLeft, safeRight, unique⟩ := PlanTree.safe_choice safe
      simp only [PlanTree.toPlan, PlanTree.erase] at attempted ⊢
      cases attempted with
      | choiceLeft selected aligned copied rest =>
          cases rest
          obtain ⟨bs, hm, resolved⟩ := sub left (by simp_wf; omega) input safeLeft value locals found selected
          have aligned := aligned
          simp only [choiceBindings, List.length_map] at aligned
          obtain ⟨ordered, reordered, recovered⟩ := choice_copied resolved unique _ _ aligned copied
          refine ⟨ordered, ?_, recovered⟩
          exact match_or_some_iff.mpr (Or.inl ⟨bs, hm, reordered⟩)
      | choiceRight missed selected aligned copied rest =>
          cases rest
          have failed := sub left (by simp_wf; omega) input safeLeft value locals found missed
          have nextFound := missed.unchanged (by rw [PlanTree.written]; exact (List.nodup_cons.mp safeLeft).1)
          rw [found] at nextFound
          obtain ⟨bs, hm, resolved⟩ := sub right (by simp_wf; omega) input safeRight value _ nextFound selected
          obtain ⟨ordered, reordered, recovered⟩ := choice_copied resolved unique _ _ aligned copied
          refine ⟨ordered, ?_, recovered⟩
          exact match_or_some_iff.mpr (Or.inr ⟨failed, bs, hm, reordered⟩)
      | choiceMiss missed rejected =>
          have failed := sub left (by simp_wf; omega) input safeLeft value locals found missed
          have nextFound := missed.unchanged (by rw [PlanTree.written]; exact (List.nodup_cons.mp safeLeft).1)
          rw [found] at nextFound
          have failedRight := sub right (by simp_wf; omega) input safeRight value _ nextFound rejected
          exact match_or_none_iff.mpr ⟨failed, failedRight⟩
  | load name child =>
      simp only [PlanTree.toPlan] at attempted ⊢
      cases attempted with
      | load found' loaded rest =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          rename_i childValue
          have ih := sub child (by simp_wf <;> omega) name (PlanTree.safe_load safe)
            childValue ((name, childValue) :: locals) (by simp) rest
          convert ih using 1 <;> simp only [PlanTree.erase, matchPatternWith, loaded, bind, Except.bind] <;> rfl
  | tuple parts =>
      have safeParts : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup := by
        simpa only [PlanTree.temps] using (List.nodup_cons.mp safe).2
      have pats : parts.map (fun p => (Aiur.Pattern.bind p.1 : Aiur.Pattern F)) =
          (parts.map Prod.fst).map Aiur.Pattern.bind := by simp only [List.map_map, Function.comp_def]
      simp only [PlanTree.toPlan, List.map_map, List.flatMap_map, Function.comp_def] at attempted ⊢
      rw [pats] at attempted
      cases attempted with
      | testHit found' matched rest =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          cases value <;> simp only [Aiur.Pattern.bindings] at matched
          all_goals first | contradiction | skip
          rename_i values
          simp only [bindingsList_binders_eq] at matched
          split at matched
          · rename_i lengths
            have same := Option.some.inj matched
            subst_vars
            have result := children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
              safeParts values (by simpa using lengths) locals rest
            convert result using 1 <;> simp only [PlanTree.erase, matchPatternWith, Preparation.matchList_attach, List.length_map,
              ← lengths, List.length_map, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              pure, Except.pure, bind, Except.bind, matchList_map] <;> rfl
          · contradiction
      | testMiss found' missed =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          simpa only [Outcome, PlanTree.erase, Bool.false_eq_true, ↓reduceIte] using
            tuple_miss (parts.map fun p => p.2.erase) (parts.map Prod.fst) (by simp) value missed
  | construct name ctor parts =>
      have safeParts : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup := by
        simpa only [PlanTree.temps] using (List.nodup_cons.mp safe).2
      have pats : parts.map (fun p => (Aiur.Pattern.bind p.1 : Aiur.Pattern F)) =
          (parts.map Prod.fst).map Aiur.Pattern.bind := by simp only [List.map_map, Function.comp_def]
      simp only [PlanTree.toPlan, List.map_map, List.flatMap_map, Function.comp_def] at attempted ⊢
      rw [pats] at attempted
      cases attempted with
      | testHit found' matched rest =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          cases value <;> simp only [Aiur.Pattern.bindings] at matched
          all_goals first | contradiction | skip
          rename_i other ctor' values
          split at matched
          · rename_i names
            rcases names with ⟨rfl, rfl⟩
            simp only [bindingsList_binders_eq] at matched
            split at matched
            · rename_i lengths
              have same := Option.some.inj matched
              subst_vars
              have result := children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
                safeParts values (by simpa using lengths) locals rest
              convert result using 1 <;> simp only [PlanTree.erase, matchPatternWith, nominal_name, Preparation.matchList_attach, List.length_map,
                ← lengths, List.length_map, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                pure, Except.pure, bind, Except.bind, matchList_map] <;> rfl
            · contradiction
          · contradiction
      | testMiss found' missed =>
          have same := Option.some.inj (found'.symm.trans found)
          cases Prod.mk.inj same |>.2
          simpa only [Outcome, PlanTree.erase, Bool.false_eq_true, ↓reduceIte] using
            construct_miss (parts.map fun p => p.2.erase) (parts.map Prod.fst) (by simp) name ctor value missed
termination_by sizeOf tree
decreasing_by exact smaller

end Aiur.Generic.PatternLowering
