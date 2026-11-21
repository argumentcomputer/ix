import Aiur.Generic.PatternTreeNames

namespace Aiur.Generic.PatternLowering
open SourceSemantics

/-- Failure has no user bindings. On success, the temporary aliases recover
exactly the bindings returned by the native matcher. -/
def Outcome (matched : Except EvalError (Option (Environment F Nat)))
    (produced : Option (Environment F Nat)) (accepted : Bool) : Prop :=
  if accepted then ∃ bindings, matched = .ok (some bindings) ∧ produced = some bindings
  else matched = .ok none

theorem grouped_names_perm (parts : List A) (root : A → String) (temps : A → List String) :
    (parts.map root ++ parts.flatMap temps).Perm (parts.flatMap fun part => root part :: temps part) := by
  induction parts with
  | nil => exact .refl _
  | cons part parts ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append]
      apply List.Perm.cons
      exact (List.perm_append_comm_assoc (parts.map root) (temps part) (parts.flatMap temps)).trans
        (List.Perm.append_left _ ih)

variable [DecidableEq F]

theorem sequence_sound
    (run : (String × PlanTree F) → SourceValue F → Except EvalError (Option (Environment F Nat)))
    (parts : List (String × PlanTree F))
    (each : ∀ part ∈ parts, ∀ (locals : Environment F Nat) value accepted final,
      (part.1 :: part.2.temps).Nodup →
      locals.find? (·.1 == part.1) = some (part.1, value) →
      Attempt heap (part.2.toPlan part.1).steps locals accepted final →
      Outcome (run part value) (resolveBindings (part.2.toPlan part.1).bindings final) accepted)
    (safe : (parts.flatMap fun part => part.1 :: part.2.temps).Nodup)
    (inputs : List.Forall₂ (fun part value => locals.find? (·.1 == part.1) = some (part.1, value)) parts values)
    (attempted : Attempt heap (parts.flatMap fun part => (part.2.toPlan part.1).steps) locals accepted final) :
    Outcome (matchListWith run parts values)
      (resolveBindings (parts.flatMap fun part => (part.2.toPlan part.1).bindings) final) accepted := by
  induction parts generalizing locals values with
  | nil =>
      cases inputs
      cases attempted
      exact ⟨[], rfl, rfl⟩
  | cons part parts ih =>
      cases inputs with
      | cons head inputs =>
          rename_i value values
          obtain ⟨partSafe, restSafe, separated⟩ := List.nodup_append.mp safe
          rcases Attempt.append_iff.mp attempted with ⟨middle, first, rest⟩ | ⟨rfl, failed⟩
          · obtain ⟨bindings, matched, produced⟩ := each part (by simp) locals _ true middle partSafe head first
            have nextInputs : List.Forall₂
                (fun part value => middle.find? (·.1 == part.1) = some (part.1, value)) parts values := by
              have withMem : List.Forall₂ (fun p v => p ∈ parts ∧ locals.find? (·.1 == p.1) = some (p.1, v)) parts values :=
                (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, inputs⟩
              apply withMem.imp
              intro p v h
              rw [first.unchanged]
              · exact h.2
              · rw [PlanTree.written]
                intro member
                exact separated _ (by simp [member]) p.1
                  (List.mem_flatMap.mpr ⟨p, h.1, by simp⟩) rfl
            have tailOutcome := ih (fun p hp => each p (by simp [hp])) restSafe nextInputs rest
            cases accepted with
            | false =>
                simp only [Outcome, Bool.false_eq_true, ↓reduceIte] at tailOutcome ⊢
                simp only [matchListWith, matched, tailOutcome, bind, Except.bind, pure, Except.pure]
            | true =>
                obtain ⟨tailBindings, tailMatched, tailProduced⟩ := tailOutcome
                have firstProduced : resolveBindings (part.2.toPlan part.1).bindings final = some bindings := by
                  rw [resolveBindings_unchanged rest, produced]
                  intro n hn
                  have source := part.2.binding_sources part.1 n hn
                  change n ∉ writtenNames (parts.flatMap fun p => (p.2.toPlan p.1).steps)
                  rw [writtenNames_flatMap]
                  intro member
                  obtain ⟨p, hp, hn'⟩ := List.mem_flatMap.mp member
                  rw [PlanTree.written] at hn'
                  exact separated n (by simpa only [List.mem_cons] using source) n
                    (List.mem_flatMap.mpr ⟨p, hp, by simp [hn']⟩) rfl
                refine ⟨bindings ++ tailBindings, ?_, ?_⟩
                · simp only [matchListWith, matched, tailMatched, bind, Except.bind, pure, Except.pure]
                · simp only [List.flatMap_cons, resolveBindings_append, firstProduced, tailProduced,
                    bind, Option.bind, pure]
          · have miss := each part (by simp) locals _ false final partSafe head failed
            simp only [Outcome, Bool.false_eq_true, ↓reduceIte] at miss ⊢
            simp only [matchListWith, miss, bind, Except.bind, pure, Except.pure]

/-- Successful native matching can execute the whole sequence of plans.
A failed earlier pattern needs no execution of any later pattern. -/
theorem sequence_complete
    (run : (String × PlanTree F) → SourceValue F → Except EvalError (Option (Environment F Nat)))
    (parts : List (String × PlanTree F))
    (each : ∀ part ∈ parts, ∀ (locals : Environment F Nat) value outcome,
      (part.1 :: part.2.temps).Nodup →
      locals.find? (·.1 == part.1) = some (part.1, value) →
      run part value = .ok outcome →
      ∃ final, Attempt heap (part.2.toPlan part.1).steps locals outcome.isSome final)
    (safe : (parts.flatMap fun part => part.1 :: part.2.temps).Nodup)
    (inputs : List.Forall₂ (fun part value => locals.find? (·.1 == part.1) = some (part.1, value)) parts values)
    (matched : matchListWith run parts values = .ok outcome) :
    ∃ final, Attempt heap (parts.flatMap fun part => (part.2.toPlan part.1).steps) locals outcome.isSome final := by
  induction parts generalizing locals values outcome with
  | nil =>
      cases inputs
      have same : outcome = some [] := by simpa [matchListWith, pure, Except.pure] using matched.symm
      subst outcome
      exact ⟨locals, .done⟩
  | cons part parts ih =>
      cases inputs with
      | cons head inputs =>
          rename_i value values
          obtain ⟨partSafe, restSafe, separated⟩ := List.nodup_append.mp safe
          cases firstRun : run part value with
          | error e => simp [matchListWith, firstRun, bind, Except.bind] at matched
          | ok firstResult =>
              obtain ⟨middle, first⟩ := each part (by simp) locals value firstResult partSafe head firstRun
              cases firstResult with
              | none =>
                  have same : outcome = none := by
                    simpa [matchListWith, firstRun, bind, Except.bind, pure, Except.pure] using matched.symm
                  subst outcome
                  exact ⟨middle, first.append_failed⟩
              | some bindings =>
                  have nextInputs : List.Forall₂
                      (fun part value => middle.find? (·.1 == part.1) = some (part.1, value)) parts values := by
                    have withMem : List.Forall₂ (fun p v => p ∈ parts ∧ locals.find? (·.1 == p.1) = some (p.1, v)) parts values :=
                      (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, inputs⟩
                    apply withMem.imp
                    intro p v h
                    rw [first.unchanged]
                    · exact h.2
                    · rw [PlanTree.written]
                      intro member
                      exact separated _ (by simp [member]) p.1
                        (List.mem_flatMap.mpr ⟨p, h.1, by simp⟩) rfl
                  cases tailRun : matchListWith run parts values with
                  | error e => simp [matchListWith, firstRun, tailRun, bind, Except.bind] at matched
                  | ok tailResult =>
                      obtain ⟨final, rest⟩ := ih (fun p hp => each p (by simp [hp])) restSafe nextInputs tailRun
                      have accepted : outcome.isSome = tailResult.isSome := by
                        cases tailResult with
                        | none =>
                            have same : outcome = none := by
                              simpa [matchListWith, firstRun, tailRun, bind, Except.bind, pure, Except.pure] using matched.symm
                            simp only [same]
                        | some bs =>
                            have same : outcome = some (bindings ++ bs) := by
                              simpa [matchListWith, firstRun, tailRun, bind, Except.bind, pure, Except.pure] using matched.symm
                            simp only [same, Option.isSome_some]
                      rw [accepted]
                      exact ⟨final, first.append rest⟩

end Aiur.Generic.PatternLowering
