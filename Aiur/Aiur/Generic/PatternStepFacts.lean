import Aiur.Generic.PatternFacts
import Aiur.Generic.EnvironmentFacts

namespace Aiur.Generic.PatternLowering

variable [DecidableEq F] {heap : Heap F} {front suffix steps : List (Step F)}
  {locals middle final final' : Environment F Nat}

theorem Attempt.append (first : Attempt heap front locals true middle)
    (rest : Attempt heap suffix middle accepted final) :
    Attempt heap (front ++ suffix) locals accepted final := by
  induction front generalizing locals with
  | nil => cases first; exact rest
  | cons step front ih =>
      cases first with
      | testHit found matched tail => exact .testHit found matched (ih tail)
      | load found loaded tail => exact .load found loaded (ih tail)
      | choiceLeft selected aligned copied tail => exact .choiceLeft selected aligned copied (ih tail)
      | choiceRight missed selected aligned copied tail => exact .choiceRight missed selected aligned copied (ih tail)

theorem Attempt.append_failed (first : Attempt heap front locals false final) :
    Attempt heap (front ++ suffix) locals false final := by
  induction front generalizing locals with
  | nil => cases first
  | cons step front ih =>
      cases first with
      | testHit found matched tail => exact .testHit found matched (ih tail)
      | testMiss found missed => exact .testMiss found missed
      | choiceMiss left right => exact .choiceMiss left right
      | load found loaded tail => exact .load found loaded (ih tail)
      | choiceLeft selected aligned copied tail => exact .choiceLeft selected aligned copied (ih tail)
      | choiceRight missed selected aligned copied tail => exact .choiceRight missed selected aligned copied (ih tail)

/-- A rejected front never executes the suffix, even when it contains loads. -/
theorem Attempt.append_iff :
    Attempt heap (front ++ suffix) locals accepted final ↔
      (∃ middle, Attempt heap front locals true middle ∧ Attempt heap suffix middle accepted final) ∨
      (accepted = false ∧ Attempt heap front locals false final) := by
  constructor
  · intro attempted
    induction front generalizing locals with
    | nil => exact Or.inl ⟨locals, .done, attempted⟩
    | cons step front ih =>
        cases step with
        | test pat input =>
            cases attempted with
            | testHit found matched rest =>
                rcases ih rest with ⟨middle, first, last⟩ | ⟨rfl, first⟩
                · exact Or.inl ⟨middle, .testHit found matched first, last⟩
                · exact Or.inr ⟨rfl, .testHit found matched first⟩
            | testMiss found missed => exact Or.inr ⟨rfl, .testMiss found missed⟩
        | load name input =>
            cases attempted with
            | load found loaded rest =>
                rcases ih rest with ⟨middle, first, last⟩ | ⟨rfl, first⟩
                · exact Or.inl ⟨middle, .load found loaded first, last⟩
                · exact Or.inr ⟨rfl, .load found loaded first⟩
        | choice outputs left lbs right rbs order =>
            cases attempted with
            | choiceLeft selected aligned copied rest =>
                rcases ih rest with ⟨middle, first, last⟩ | ⟨rfl, first⟩
                · exact Or.inl ⟨middle, .choiceLeft selected aligned copied first, last⟩
                · exact Or.inr ⟨rfl, .choiceLeft selected aligned copied first⟩
            | choiceRight missed selected aligned copied rest =>
                rcases ih rest with ⟨middle, first, last⟩ | ⟨rfl, first⟩
                · exact Or.inl ⟨middle, .choiceRight missed selected aligned copied first, last⟩
                · exact Or.inr ⟨rfl, .choiceRight missed selected aligned copied first⟩
            | choiceMiss left right => exact Or.inr ⟨rfl, .choiceMiss left right⟩
  · rintro (⟨middle, first, rest⟩ | ⟨rfl, failed⟩)
    · exact first.append rest
    · exact failed.append_failed

theorem Attempt.deterministic (left : Attempt heap steps locals accepted final)
    (right : Attempt heap steps locals accepted' final') : accepted = accepted' ∧ final = final' := by
  induction left generalizing accepted' final' with
  | done => cases right; exact ⟨rfl, rfl⟩
  | testHit found matched rest ih =>
      cases right with
      | testHit found' matched' rest' =>
          have same := Option.some.inj (found.symm.trans found')
          cases Prod.mk.inj same |>.2
          have same := Option.some.inj (matched.symm.trans matched')
          subst_vars
          exact ih rest'
      | testMiss found' missed =>
          have same := Option.some.inj (found.symm.trans found')
          cases Prod.mk.inj same |>.2
          simp [matched] at missed
  | testMiss found missed =>
      cases right with
      | testHit found' matched rest' =>
          have same := Option.some.inj (found.symm.trans found')
          cases Prod.mk.inj same |>.2
          simp [missed] at matched
      | testMiss => exact ⟨rfl, rfl⟩
  | load found loaded rest ih =>
      cases right with
      | load found' loaded' rest' =>
          have same := Option.some.inj (found.symm.trans found')
          cases Prod.mk.inj same |>.2
          have same := Except.ok.inj (loaded.symm.trans loaded')
          subst_vars
          exact ih rest'
  | choiceLeft selected aligned copied rest ihSelected ihRest =>
      cases right with
      | choiceLeft selected' aligned' copied' rest' =>
          obtain ⟨_, rfl⟩ := ihSelected selected'
          cases Option.some.inj (aligned.symm.trans aligned')
          cases Option.some.inj (copied.symm.trans copied')
          exact ihRest rest'
      | choiceRight missed => cases (ihSelected missed).1
      | choiceMiss missed => cases (ihSelected missed).1
  | choiceRight missed selected aligned copied rest ihMissed ihSelected ihRest =>
      cases right with
      | choiceLeft selected' => cases (ihMissed selected').1
      | choiceRight missed' selected' aligned' copied' rest' =>
          obtain ⟨_, rfl⟩ := ihMissed missed'
          obtain ⟨_, rfl⟩ := ihSelected selected'
          cases Option.some.inj (aligned.symm.trans aligned')
          cases Option.some.inj (copied.symm.trans copied')
          exact ihRest rest'
      | choiceMiss missed' rejected' =>
          obtain ⟨_, rfl⟩ := ihMissed missed'
          cases (ihSelected rejected').1
  | choiceMiss missed rejected ihMissed ihRejected =>
      cases right with
      | choiceLeft selected' => cases (ihMissed selected').1
      | choiceRight missed' selected' =>
          obtain ⟨_, rfl⟩ := ihMissed missed'
          cases (ihRejected selected').1
      | choiceMiss missed' rejected' =>
          obtain ⟨_, rfl⟩ := ihMissed missed'
          exact ihRejected rejected'

mutual
  theorem bindings_names {pat : Aiur.Pattern F} {value : SourceValue F}
      (matched : pat.bindings value = some bindings) : bindings.map Prod.fst = patternNames pat := by
    cases pat with
    | wildcard | bind =>
        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
        subst bindings; simp only [patternNames, List.map_cons, List.map_nil]
    | literal x =>
        cases value <;> simp only [Aiur.Pattern.bindings] at matched
        all_goals first | contradiction | skip
        split at matched
        · cases Option.some.inj matched; simp only [patternNames, List.map_nil, List.flatMap_nil]
        · contradiction
    | tuple ps =>
        cases value <;> simp only [Aiur.Pattern.bindings] at matched
        all_goals first | contradiction | skip
        simpa only [patternNames] using bindingsList_names matched
    | construct n c ps =>
        cases value <;> simp only [Aiur.Pattern.bindings] at matched
        all_goals first | contradiction | skip
        split at matched
        · simpa only [patternNames] using bindingsList_names matched
        · contradiction
  termination_by sizeOf pat

  theorem bindingsList_names {ps : List (Aiur.Pattern F)} {values : List (SourceValue F)}
      (matched : Aiur.Pattern.bindingsList ps values = some bindings) :
      bindings.map Prod.fst = ps.flatMap patternNames := by
    cases ps with
    | nil =>
        cases values <;> simp only [Aiur.Pattern.bindingsList] at matched
        all_goals first | contradiction | skip
        cases Option.some.inj matched; simp only [patternNames, List.map_nil, List.flatMap_nil]
    | cons p ps =>
        cases values with
        | nil => simp [Aiur.Pattern.bindingsList] at matched
        | cons v vs =>
            cases head : p.bindings v with
            | none => simp [Aiur.Pattern.bindingsList, head] at matched
            | some first =>
                cases tail : Aiur.Pattern.bindingsList ps vs with
                | none => simp [Aiur.Pattern.bindingsList, head, tail] at matched
                | some rest =>
                    have same : first ++ rest = bindings := by
                      simpa [Aiur.Pattern.bindingsList, head, tail] using matched
                    rw [← same, List.map_append, bindings_names head, bindingsList_names tail]
                    rfl
  termination_by sizeOf ps
end

def stepNames : Step F → List String
  | .test p _ => patternNames p
  | .load n _ => [n]
  | .choice outputs left _ right _ _ =>
      left.flatMap stepNames ++ right.flatMap stepNames ++ outputs.map Prod.snd
termination_by step => sizeOf step

def writtenNames (steps : List (Step F)) : List String := steps.flatMap stepNames


private theorem find_prepend_of_not_mem {added locals : Environment F Nat}
    (fresh : name ∉ added.map Prod.fst) :
    (added ++ locals).find? (·.1 == name) = locals.find? (·.1 == name) := by
  induction added with
  | nil => rfl
  | cons b added ih =>
      have ne : b.1 ≠ name := by intro h; apply fresh; simp [h]
      have rest : name ∉ added.map Prod.fst := fun h => fresh (by simp [h])
      simpa [List.find?, ne] using ih rest

/-- A pattern attempt only shadows its listed temporary names. This holds on
failure as well as success, so an inactive arm cannot alter caller bindings. -/
theorem Attempt.unchanged (attempted : Attempt heap steps locals accepted final)
    (untouched : name ∉ writtenNames steps) :
    final.find? (·.1 == name) = locals.find? (·.1 == name) := by
  induction attempted with
  | done | testMiss => rfl
  | testHit found matched _ ih =>
      rw [ih (by
        intro h
        apply untouched
        simp only [writtenNames, stepNames, List.flatMap_cons, List.mem_append]
        exact Or.inr h)]
      apply find_prepend_of_not_mem
      rw [bindings_names matched]
      intro h; apply untouched; simp [writtenNames, stepNames, h]
  | load found loaded _ ih =>
      simp only [writtenNames, stepNames, List.flatMap_cons, List.singleton_append, List.mem_cons, not_or] at untouched
      rw [ih untouched.2]
      have notSame := beq_eq_false_iff_ne.mpr (Ne.symm untouched.1)
      simp only [List.find?_cons, notSame, Bool.false_eq_true, ↓reduceIte]
  | choiceLeft selected aligned copied rest ihSelected ihRest =>
      have fresh := untouched
      simp only [writtenNames, stepNames, List.flatMap_cons, List.mem_append, not_or, and_assoc] at fresh
      rw [ihRest fresh.2.2.2, find_prepend_of_not_mem, ihSelected fresh.1]
      rw [resolveBindings_names copied]
      rw [reorderBindings_names aligned]
      exact fresh.2.2.1
  | choiceRight missed selected aligned copied rest ihMissed ihSelected ihRest =>
      have fresh := untouched
      simp only [writtenNames, stepNames, List.flatMap_cons, List.mem_append, not_or, and_assoc] at fresh
      rw [ihRest fresh.2.2.2, find_prepend_of_not_mem, ihSelected fresh.2.1, ihMissed fresh.1]
      rw [resolveBindings_names copied]
      rw [reorderBindings_names aligned]
      exact fresh.2.2.1
  | choiceMiss missed rejected ihMissed ihRejected =>
      have fresh := untouched
      simp only [writtenNames, stepNames, List.flatMap_cons, List.mem_append, not_or, and_assoc] at fresh
      rw [ihRejected fresh.2.1, ihMissed fresh.1]

end Aiur.Generic.PatternLowering
