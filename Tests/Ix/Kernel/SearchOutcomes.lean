/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Search outcome regressions

Keep successful checks, unsuccessful bounded search, and direct input errors
separate. The low-fuel rejection assertions characterize the P00 baseline;
P01 changes them to declines when nested failures carry their causes.
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
-- Known defect: exhaustion in nested conversion is currently called rejection.
#guard aliasOutcome 1 == .reject
#guard aliasOutcome 2 == .reject
#guard ([3, 4, 8, 32].map aliasOutcome).all (· == .accept)

/-- A conservative level comparison can fail on equal universe expressions. -/
def maxUV : VLevel := .max (.param 0) (.param 1)
def maxVU : VLevel := .max (.param 1) (.param 0)

example (values : List Nat) : maxUV.eval values = maxVU.eval values := by
  simp [maxUV, maxVU, VLevel.eval, Nat.max_comm]

#guard !levelEquiv maxUV maxVU
#guard levelEquiv maxUV maxUV

-- Direct input defects remain distinguishable from search exhaustion.
#guard outcome (check.{0,1} {} [alias, alias]) == .reject
#guard outcome (check.{0,1} {} [useAlias]) == .reject
#guard outcome (check.{0,1} {}
  [⟨2, ⟨[.defn 0 .definition type0 (.bvar 0) .safe]⟩⟩]) == .reject

-- Reducing without fuel still supplies a sound partial reduct; it does not
-- imply that this application is in weak-head normal form.
def redex : AExpr Nat := .app (.lam .never (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
#guard (whnf.{0,1} 0 (fun _ => none) [] redex).result = redex
#guard (whnf.{0,1} 32 (fun _ => none) [] redex).result = .sort .zero

end Tests.Ix.Kernel.SearchOutcomes
