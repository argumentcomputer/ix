/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

/-! # Bounded search outcomes

Only success carries semantic evidence. A candidate that does not apply is
different from an exhausted or unresolved search; none of these establishes
that two terms are unequal. Alternatives preserve a successful later path
and retain the most informative cause when every path fails.
-/

namespace Ix.Kernel

/-- Recover the successful input of a proof-erasing result map. -/
theorem Except.map_eq_ok {ε α γ : Type _} {f : α → γ} {x : Except ε α} {y : γ}
    (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => simp [Except.map] at h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

inductive SearchFailure where
  | exhausted
  | unsupported (reason : String)
  | unresolved (reason : String)
  | malformed (reason : String)
  /-- This particular candidate rule does not apply. -/
  | noMatch
  deriving DecidableEq, Repr

namespace SearchFailure

/-- Failure to type a speculative rule endpoint is not a direct validation
failure of the original input. Preserve ordinary rule inapplicability. -/
def speculative : SearchFailure → SearchFailure
  | .malformed reason => .unresolved reason
  | failure => failure

/-- Exhaustion in any unsuccessful alternative must remain visible. -/
def merge : SearchFailure → SearchFailure → SearchFailure
  | .exhausted, _ | _, .exhausted => .exhausted
  | .unsupported reason, _ | _, .unsupported reason => .unsupported reason
  | .unresolved reason, _ | _, .unresolved reason => .unresolved reason
  | .malformed reason, _ | _, .malformed reason => .malformed reason
  | .noMatch, .noMatch => .noMatch

/-- Failure while trying to establish conversion is not evidence of an
invalid input, even if an optional typing-based strategy could not type it. -/
def conversion : SearchFailure → SearchFailure
  | .malformed _ | .noMatch => .unresolved "conversion search did not establish equality"
  | failure => failure

end SearchFailure

abbrev Search (α : Type u) := Except SearchFailure α

namespace Search

def ofOption (value : Option α) (failure : SearchFailure := .noMatch) : Search α :=
  match value with
  | some a => .ok a
  | none => .error failure

instance : MonadLift Option Search where
  monadLift value := ofOption value

/-- A failed speculative attempt does not consume the fallback's fuel. -/
def orElse (first : Search α) (next : Unit → Search α) : Search α :=
  match first with
  | .ok a => .ok a
  | .error a =>
    match next () with
    | .ok b => .ok b
    | .error b => .error (a.merge b)

/-- Keep normalization's stopping cause only if the subsequent search also
fails. Positive evidence obtained from a partial reduct is still valid. -/
def remember (cause : Option SearchFailure) (result : Search α) : Search α :=
  match result, cause with
  | .error failure, some earlier => .error (earlier.merge failure)
  | result, _ => result

end Search
end Ix.Kernel
