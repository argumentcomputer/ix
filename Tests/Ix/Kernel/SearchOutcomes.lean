/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Search outcome regressions

Keep successful checks, unsuccessful bounded search, and direct input errors
separate. Exhaustion below annotation, conversion, or admission remains a
decline; unsuccessful conversion is not evidence that terms are unequal.
-/

open Ix.Kernel Ix.Kernel.Model

namespace Tests.Ix.Kernel.SearchOutcomes

def prop : VExpr Nat := .sort .zero
def type0 : VExpr Nat := .sort (.succ .zero)
def type1 : VExpr Nat := .sort (.succ (.succ .zero))

/-- `A : Type 1 := Type; x : A := Prop`. Conversion must unfold `A`. -/
def alias : Decl Nat := ⟨0, ⟨[.defn 0 .definition type1 type0 .safe]⟩⟩
def useAlias : Decl Nat :=
  ⟨1, ⟨[.defn 0 .definition (.const (.member 0 0) []) prop .safe]⟩⟩

inductive Outcome where
  | accept
  | reject
  | decline
  deriving BEq, Repr

def outcome {α : Type} : Except Error α → Outcome
  | .ok _ => .accept
  | .error (.rejected _) => .reject
  | .error (.declined _) => .decline

def aliasOutcome (fuel : Nat) : Outcome :=
  outcome (check.{0,1} {fuel} [alias, useAlias])

#guard aliasOutcome 0 == .decline
#guard aliasOutcome 1 == .decline
#guard aliasOutcome 2 == .decline
#guard ([3, 4, 8, 32].map aliasOutcome).all (· == .accept)
#guard ((List.range 33).map aliasOutcome).all (· != .reject)

/-- Level comparison is complete (`levelEquiv_iff`): equal universe expressions
compare equal however they are written. The previous conservative comparison
failed on `max u v` against `max v u`. -/
def maxUV : VLevel := .max (.param 0) (.param 1)
def maxVU : VLevel := .max (.param 1) (.param 0)

example (values : List Nat) : maxUV.eval values = maxVU.eval values := by
  simp [maxUV, maxVU, VLevel.eval, Nat.max_comm]

#guard levelEquiv maxUV maxVU
#guard levelEquiv maxUV maxUV
#guard !levelEquiv maxUV (.param 0)

-- `DecidableEq`'s body lives in `imax u (imax u 1)`, its declared type in `max 1 u`.
#guard levelEquiv (.imax (.param 0) (.imax (.param 0) (.succ .zero))) (.max (.succ .zero) (.param 0))
-- `imax u v ≤ max u v`, as a field bound, and not conversely.
#guard levelEquiv (.max (.imax (.param 0) (.param 1)) (.max (.param 0) (.param 1)))
  (.max (.param 0) (.param 1))
#guard !levelEquiv (.max (.max (.param 0) (.param 1)) (.imax (.param 0) (.param 1)))
  (.imax (.param 0) (.param 1))
-- A zero test sees through `imax` with a zero right side, and nothing else.
#guard levelIsZero (.imax (.param 0) .zero)
#guard !levelIsZero (.imax .zero (.param 0))

-- Direct input defects remain distinguishable from search exhaustion.
#guard outcome (check.{0,1} {} [alias, alias]) == .reject
#guard outcome (check.{0,1} {} [useAlias]) == .reject
#guard outcome (check.{0,1} {}
  [⟨2, ⟨[.defn 0 .definition type0 (.bvar 0) .safe]⟩⟩]) == .reject

-- Reducing without fuel still supplies a sound partial reduct; it does not
-- imply that this application is in weak-head normal form.
def redex : AExpr Nat := .app (.lam .never (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
#guard (whnf.{0,1} 0 (fun _ => none) [] redex).result = redex
#guard (whnf.{0,1} 0 (fun _ => none) [] redex).stopped = some .exhausted
#guard (whnf.{0,1} 32 (fun _ => none) [] redex).result = .sort .zero
#guard (whnf.{0,1} 32 (fun _ => none) [] redex).stopped = none

def failureIs {α : Type u} (result : Search α) (failure : SearchFailure) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => decide (actual = failure)

-- An exhausted optional strategy must leave a later certified success usable.
#guard (Search.orElse (.error .exhausted) (fun _ => .ok (7 : Nat))).toOption == some 7
#guard failureIs (Search.orElse (.error .exhausted) (fun _ => (.error .noMatch : Search Nat)))
  .exhausted
#guard (Search.remember (some .exhausted) (.ok (7 : Nat))).toOption == some 7

/-- Conversion can succeed using a sound partial reduct. -/
def partialConversion : Bool :=
  match check.{0,1} {} [alias] with
  | .ok env =>
    let e : AExpr Nat := .const (.member 0 0) []
    let normalized := whnf.{0,1} 2 env.toEnvironment [] e
    decide (normalized.result = .sort (.succ .zero)) &&
      decide (normalized.stopped = some .exhausted) &&
      (isDefEq.{0,1} 3 env.toEnvironment [] e (.sort (.succ .zero))).isOk
  | .error _ => false
#guard partialConversion

def functionAlias : Decl Nat :=
  ⟨2, ⟨[.defn 0 .definition type1 (.forallE type0 type0) .safe]⟩⟩
def function : Decl Nat :=
  ⟨3, ⟨[.defn 0 .definition (.const (.member 2 0) []) (.lam type0 (.bvar 0)) .safe]⟩⟩

/-- Syntax reading has enough fuel, but Pi search inside inference runs out. -/
def nestedAnnotation : Bool :=
  match check.{0,1} {} [functionAlias, function] with
  | .ok env =>
    let raw := .lam prop (.app (.const (.member 3 0) []) prop)
    failureIs (annotate.{0,1} 3 env.toEnvironment [] raw) .exhausted &&
      (annotate.{0,1} 64 env.toEnvironment [] raw).isOk
  | .error _ => false
#guard nestedAnnotation

def parameterShape : Certified.Ordinary.Shape Nat :=
  ⟨0, [.sort (.succ .zero)], [], .succ .zero, []⟩
def parameterDecl : Decl Nat :=
  ⟨4, ⟨[parameterShape.source 4, parameterShape.recursorSource 4 .large]⟩⟩
#guard failureIs (Certified.Ordinary.readBlock.{0,1} 0 (fun _ => none) 4 parameterDecl.block)
  .exhausted
#guard outcome (check.{0,1} {} [parameterDecl]) == .accept

/-- Applying a checked rule endpoint must preserve its own exhaustion. -/
def exhaustedApplication : Bool :=
  let f : AExpr Nat := .lam .never (.sort (.succ .zero)) (.bvar 0)
  match inferA.{0,1} 64 (fun _ => none) [] f with
  | .ok typed => failureIs
      (applyTyped.{0,1} 0 (fun _ => none) [] f typed.type typed.claim [.sort .zero]) .exhausted
  | .error _ => false
#guard exhaustedApplication

#guard match isDefEq.{0,1} 64 (β := Nat) (fun _ => none) [] (.sort maxUV) (.sort maxVU) with
  | .ok _ => true
  | .error _ => false
#guard failureIs
  (isDefEq.{0,1} 64 (β := Nat) (fun _ => none) [] (.sort maxUV) (.sort (.param 0)))
  (.unresolved "conversion search did not establish equality")

-- This identity is valid by max commutativity, which the complete level
-- comparison establishes.
def maxIdentity : Decl Nat :=
  ⟨5, ⟨[.defn 2 .definition (.forallE (.sort maxUV) (.sort maxUV))
    (.lam (.sort maxVU) (.bvar 0)) .safe]⟩⟩
#guard outcome (check.{0,1} {} [maxIdentity]) == .accept

-- A body at a different universe still fails its conversion: the declaration
-- declines, since conversion search as a whole is not complete.
def maxMismatch : Decl Nat :=
  ⟨5, ⟨[.defn 2 .definition (.forallE (.sort maxUV) (.sort maxUV))
    (.lam (.sort (.param 0)) (.bvar 0)) .safe]⟩⟩
#guard outcome (check.{0,1} {} [maxMismatch]) == .decline

-- Binder regimes are still validated, including on the non-Prop beta path.
#guard failureIs (inferA.{0,1} 64 (β := Nat) (fun _ => none) []
    (.lam .always (.sort (.succ .zero)) (.bvar 0)))
  (.malformed "lambda annotation disagrees with its codomain sort")

end Tests.Ix.Kernel.SearchOutcomes
