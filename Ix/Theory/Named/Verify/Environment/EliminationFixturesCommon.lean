/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.Elimination
import Ix.Theory.Named.Verify.Environment.InductiveFixtures

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

universe u

/-- A source-universe-bearing small eliminator. Or has no source universes,
so this fixture distinguishes "no fresh level" from "no levels at all". -/
inductive Spec06SmallSource (α : Sort u) : Prop where
  | left : Spec06SmallSource α
  | right : Spec06SmallSource α

def recursorShape06 (info : ConstantInfo) :
    List Name × Nat × Nat × Nat × Nat × Bool × List (Name × Nat) :=
  match info with
  | .recInfo rec =>
      (rec.levelParams, rec.numParams, rec.numIndices, rec.numMotives,
        rec.numMinors, rec.k,
        rec.rules.map fun rule => (rule.ctor, rule.nfields))
  | _ => ([], 0, 0, 0, 0, false, [])

def spec06KernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_spec06 {}

def spec06Context (lparams : List Name) : AddInductive.Context where
  env := spec06KernelEnv
  lparams := lparams
  safety := .safe
  allowPrimitive := false

example : AddInductive.getFreshElimParam [] = `u := by native_decide
example : AddInductive.getFreshElimParam [`u] = `u_1 := by native_decide
example : AddInductive.getFreshElimParam [`u, `u_1] = `u_2 := by native_decide

/-- Decidable structural equality for the exact kernel level lists retained by
the fixtures. `Lean.Level` intentionally has no `DecidableEq` instance. -/
def levelListStructEq06 : List Level → List Level → Bool
  | [], [] => true
  | u :: us, v :: vs =>
      Level.isStructEq u v && levelListStructEq06 us vs
  | _, _ => false

theorem levelListStructEq06_eq {us vs : List Level}
    (h : levelListStructEq06 us vs) : us = vs := by
  induction us generalizing vs with
  | nil => cases vs <;> simp_all [levelListStructEq06]
  | cons u us ih =>
      cases vs with
      | nil => simp [levelListStructEq06] at h
      | cons v vs =>
          simp only [levelListStructEq06, Bool.and_eq_true] at h
          cases Level.isStructEq_eq h.1
          cases ih h.2
          rfl

end Ix.Theory.Named.InductiveReplayFixtures
