/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.SourceEval

/-! Tail-match restoration preserves the complete source evaluator result.
This covers the normalization helper used by inlining; expansion and let
hoisting require separate proofs. -/

namespace Aiur.Source.Eval

private theorem evalMatchCases_map (decls : Decls) (fuel : Nat)
    (transform : Term → Term) (arms : List (Pattern × Term))
    (equivalent : ∀ arm ∈ arms, ∀ bindings st,
      interp decls fuel bindings arm.2 st = interp decls fuel bindings (transform arm.2) st)
    (bindings : Bindings) (st : EvalState) (value : Value) :
    evalMatchCases decls fuel bindings st value arms =
      evalMatchCases decls fuel bindings st value (arms.map fun arm => (arm.1, transform arm.2)) := by
  induction arms with
  | nil => rfl
  | cons arm arms ih =>
    rcases arm with ⟨pattern, body⟩
    simp only [List.map_cons, evalMatchCases]
    cases matchPattern st.store pattern value with
    | some bs => exact equivalent (pattern, body) (by simp) (bs ++ bindings) st
    | none => exact ih (fun arm member => equivalent arm (by simp [member]))

/-- All successes, errors and early returns are identical, including their
full memory and I/O states. Fuel is unchanged because it counts calls. -/
theorem interp_restoreTailMatches (decls : Decls) (fuel : Nat) (term : Term)
    (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings term st =
      interp decls fuel bindings term.restoreTailMatches st := by
  induction term using Term.restoreTailMatches.induct generalizing bindings st with
  | case1 x value y same ih =>
    simp only [Term.restoreTailMatches, if_pos same]
    rw [← ih]
    simp only [interp]
    cases interp decls fuel bindings value st with
    | error e => rfl
    | ok result =>
      rcases result with ⟨v, st'⟩
      simp [matchPattern, same]
  | case2 x value y different => simp only [Term.restoreTailMatches, if_neg different]
  | case3 pattern value body notEta ih =>
    rw [Term.restoreTailMatches.eq_def]
    split
    next x value' y impossible =>
      cases impossible
      exact False.elim (notEta x y rfl rfl)
    next =>
      rename_i p v b _ heq
      cases heq
      simp only [interp]
      cases interp decls fuel bindings value st with
      | error e => rfl
      | ok result =>
        rcases result with ⟨v, st'⟩
        dsimp only
        cases matchPattern st'.store pattern v with
        | none => rfl
        | some bs => exact ih (bs ++ bindings) st'
    next s arms impossible => cases impossible
    next => rfl
  | case4 scrut arms ih =>
    simp only [Term.restoreTailMatches, interp]
    cases interp decls fuel bindings scrut st with
    | error e => rfl
    | ok result =>
      rcases result with ⟨v, st'⟩
      simpa only [List.attach_map_val (f := fun (arm : Pattern × Term) =>
        (arm.1, arm.2.restoreTailMatches))] using
        evalMatchCases_map decls fuel Term.restoreTailMatches arms
          (fun arm member => ih ⟨arm, member⟩) bindings st' v
  | case5 term notEta notLet notMatch =>
    rw [Term.restoreTailMatches.eq_def]
    split
    · exact False.elim (notEta _ _ _ rfl)
    · exact False.elim (notLet _ _ _ rfl)
    · exact False.elim (notMatch _ _ rfl)
    · rfl

end Aiur.Source.Eval
