/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.SourceEval

/-! Semantic identities for let frames, continuation sequencing and call
modes. They preserve complete results at unchanged call fuel. These are
components of normalization; fresh naming and complete argument hoisting
require separate proofs. -/

namespace Aiur.Source.Eval

theorem wrapLets_peelLets (term : Term) :
    Term.wrapLets term.peelLets.1 term.peelLets.2 = term := by
  induction term using Term.peelLets.induct with
  | case1 pattern value body frames core peeled ih =>
    simpa only [Term.peelLets, peeled, Term.wrapLets] using congrArg (Term.let pattern value) ih
  | case2 term notLet =>
    rw [Term.peelLets.eq_def]
    split
    · exact False.elim (notLet _ _ _ rfl)
    · rfl

def evalFrames (decls : Decls) (fuel : Nat) :
    List (Pattern × Term) → Bindings → EvalState → Except SourceError (Bindings × EvalState)
  | [], bindings, st => .ok (bindings, st)
  | (pattern, value) :: frames, bindings, st => do
    let (value, st) ← interp decls fuel bindings value st
    let some added := matchPattern st.store pattern value | .error .patternFail
    evalFrames decls fuel frames (added ++ bindings) st

theorem interp_wrapLets (decls : Decls) (fuel : Nat) (frames : List (Pattern × Term))
    (body : Term) (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (Term.wrapLets frames body) st =
      (do let (bindings, st) ← evalFrames decls fuel frames bindings st
          interp decls fuel bindings body st) := by
  induction frames generalizing bindings st with
  | nil => rfl
  | cons frame frames ih =>
    rcases frame with ⟨pattern, value⟩
    simp only [Term.wrapLets, interp, evalFrames]
    cases interp decls fuel bindings value st with
    | error error => rfl
    | ok result =>
      rcases result with ⟨value, st'⟩
      dsimp only [bind, Except.bind]
      cases matchPattern st'.store pattern value with
      | none => rfl
      | some added => exact ih (added ++ bindings) st'

theorem evalFrames_append (decls : Decls) (fuel : Nat)
    (first rest : List (Pattern × Term)) (bindings : Bindings) (st : EvalState) :
    evalFrames decls fuel (first ++ rest) bindings st =
      (do let (bindings, st) ← evalFrames decls fuel first bindings st
          evalFrames decls fuel rest bindings st) := by
  induction first generalizing bindings st with
  | nil => rfl
  | cons frame frames ih =>
    rcases frame with ⟨pattern, value⟩
    simp only [List.cons_append, evalFrames]
    cases interp decls fuel bindings value st with
    | error error => rfl
    | ok result =>
      rcases result with ⟨value, st'⟩
      dsimp only [bind, Except.bind]
      cases matchPattern st'.store pattern value with
      | none => rfl
      | some added => exact ih (added ++ bindings) st'

theorem interp_peelLets (decls : Decls) (fuel : Nat) (term : Term)
    (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings term st =
      (do let (bindings, st) ← evalFrames decls fuel term.peelLets.1 bindings st
          interp decls fuel bindings term.peelLets.2 st) := by
  rw [← interp_wrapLets, wrapLets_peelLets]

theorem interp_ret_wrapLets (decls : Decls) (fuel : Nat)
    (frames : List (Pattern × Term)) (body : Term) (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (.ret (Term.wrapLets frames body)) st =
      interp decls fuel bindings (Term.wrapLets frames (.ret body)) st := by
  rw [interp_wrapLets]
  simp only [interp, interp_wrapLets]
  cases evalFrames decls fuel frames bindings st with
  | error error => rfl
  | ok result => cases result; rfl

theorem interp_ioWrite_sequence (decls : Decls) (fuel : Nat)
    (channel data continuation : Term) (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (.ioWrite channel data continuation) st =
      interp decls fuel bindings (.let .wildcard (.ioWrite channel data .unit) continuation) st := by
  simp only [interp]
  cases interp decls fuel bindings channel st <;> simp only
  next result =>
    rcases result with ⟨channel, st⟩
    cases interp decls fuel bindings data st <;> simp only
    next result =>
      rcases result with ⟨data, st⟩
      cases channel <;> cases data <;> simp only
      split <;> simp only [matchPattern, List.nil_append]

theorem interp_debug_sequence (decls : Decls) (fuel : Nat)
    (label : String) (value : Option Term) (continuation : Term)
    (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (.debug label value continuation) st =
      interp decls fuel bindings (.let .wildcard (.debug label value .unit) continuation) st := by
  cases value with
  | none => simp only [interp, matchPattern, List.nil_append]
  | some value =>
    simp only [interp]
    cases interp decls fuel bindings value st with
    | error error => rfl
    | ok result =>
      rcases result with ⟨value, st'⟩
      simp only [matchPattern, List.nil_append]

theorem interp_assertEq_sequence (decls : Decls) (fuel : Nat)
    (first second : Term) (message : Option String) (continuation : Term)
    (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (.assertEq first second message continuation) st =
      interp decls fuel bindings
        (.let .wildcard (.assertEq first second message .unit) continuation) st := by
  cases message <;> (
    simp only [interp]
    cases interp decls fuel bindings first st <;> simp only
    next result =>
      rcases result with ⟨first, st⟩
      cases interp decls fuel bindings second st <;> simp only
      next result =>
        rcases result with ⟨second, st⟩
        split <;> simp only [matchPattern, List.nil_append])

theorem interp_ioSetInfo_sequence (decls : Decls) (fuel : Nat)
    (channel key index length continuation : Term) (bindings : Bindings) (st : EvalState) :
    interp decls fuel bindings (.ioSetInfo channel key index length continuation) st =
      interp decls fuel bindings
        (.let .wildcard (.ioSetInfo channel key index length .unit) continuation) st := by
  simp only [interp]
  cases interp decls fuel bindings channel st <;> simp only
  next result =>
    rcases result with ⟨channel, st⟩
    cases interp decls fuel bindings key st <;> simp only
    next result =>
      rcases result with ⟨key, st⟩
      cases interp decls fuel bindings index st <;> simp only
      next result =>
        rcases result with ⟨index, st⟩
        cases interp decls fuel bindings length st <;> simp only
        next result =>
          rcases result with ⟨length, st⟩
          cases channel <;> cases key <;> cases index <;> cases length <;> simp only
          split <;> try simp only
          split <;> simp only [matchPattern, List.nil_append]

theorem interp_app_mode (decls : Decls) (fuel : Nat) (bindings : Bindings)
    (global : Global) (args : List Term) (before after : CallMode) (st : EvalState) :
    interp decls fuel bindings (.app global args before) st =
      interp decls fuel bindings (.app global args after) st := by
  simp only [interp]

end Aiur.Source.Eval
