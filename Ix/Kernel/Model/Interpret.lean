/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Model/Interpret.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Annotated
import Ix.Kernel.Model.PrimitiveValues
import Ix.Kernel.Model.Value

/-!
# Total interpretation of annotated Ix syntax

Constants are interpreted through an explicit assignment, whose compatibility
with checked declarations is a separate invariant. This definition does not
traverse store references. Projections use the uniform ordinary-node field
decoder, and literals use fixed numeral values. Typing either requires
additional facts whose meanings are constructed during declaration admission.
-/

namespace Ix.Kernel.Model

open SetTheory SetModel

universe u v w

namespace Valuation

def cons (x : V) (env : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => env i

@[simp] theorem cons_zero (x : V) (env : Nat → V) : cons x env 0 = x := rfl
@[simp] theorem cons_succ (x : V) (env : Nat → V) (i : Nat) : cons x env (i + 1) = env i := rfl

def skip (count cutoff : Nat) (env : Nat → V) : Nat → V :=
  fun i => if i < cutoff then env i else env (count + i)

def insert (cutoff : Nat) (x : V) (env : Nat → V) : Nat → V :=
  fun i => if i < cutoff then env i else if i = cutoff then x else env (i - 1)

@[simp] theorem skip_zero (env : Nat → V) : skip 0 0 env = env := by
  funext i; simp [skip]

@[simp] theorem skip_cons (n k : Nat) (x : V) (env : Nat → V) :
    skip n (k + 1) (cons x env) = cons x (skip n k env) := by
  funext i
  cases i <;> simp [skip, cons]

@[simp] theorem insert_cons (k : Nat) (x y : V) (env : Nat → V) :
    insert (k + 1) x (cons y env) = cons y (insert k x env) := by
  funext i
  cases i with
  | zero => simp [insert]
  | succ i =>
    by_cases h : i < k
    · simp [insert, h]
    · by_cases e : i = k
      · simp [insert, e]
      · have hi : i ≠ 0 := by omega
        cases i with
        | zero => exact (hi rfl).elim
        | succ i => simp [insert, h, e]

@[simp] theorem insert_zero (x : V) (env : Nat → V) : insert 0 x env = cons x env := by
  funext i; cases i <;> simp [insert]

@[simp] theorem skip_succ_cons (n : Nat) (x : V) (env : Nat → V) :
    skip (n + 1) 0 (cons x env) = skip n 0 env := by
  funext i
  simp [skip, show n + 1 + i = (n + i) + 1 by omega]

end Valuation

/-- A value for every exact reference and concrete universe argument list. -/
abbrev Assignment (β : Type u) (V : Type v) := ConstRef β → List Nat → V

variable {β : Type u} {V : Type v} [SetTheory V]

noncomputable def interp (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) : AExpr β → V
  | .bvar i => env i
  | .sort l => univ (l.eval levels)
  | .const r ls => constants r (ls.map (VLevel.eval levels))
  | .app f a => app (interp constants levels env f) (interp constants levels env a)
  | .lam p a b => lamR (regime p levels) (interp constants levels env a)
    (fun x => interp constants levels (Valuation.cons x env) b)
  | .forallE p a b => piR (regime p levels) (interp constants levels env a)
    (fun x => interp constants levels (Valuation.cons x env) b)
  | .proj _ i e => projectValue i (interp constants levels env e)
  | .natLit n => Numeral.value n

theorem interp_liftN (e : AExpr β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (n k : Nat) :
    interp constants levels env (e.liftN n k) =
      interp constants levels (Valuation.skip n k env) e := by
  induction e generalizing k env with
  | bvar i => simp [AExpr.liftN, interp, liftVar, Valuation.skip]; split <;> rfl
  | lam p a b ha hb | forallE p a b ha hb =>
    simp only [AExpr.liftN, interp, ha]
    congr 1
    funext x
    rw [hb, Valuation.skip_cons]
  | _ => simp_all [AExpr.liftN, interp]

theorem interp_inst (e a : AExpr β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (k : Nat) :
    interp constants levels env (e.inst a k) =
      interp constants levels
        (Valuation.insert k (interp constants levels (Valuation.skip k 0 env) a) env) e := by
  induction e generalizing k env with
  | bvar i =>
    by_cases h : i < k
    · simp [AExpr.inst, AExpr.instVar, interp, Valuation.insert, h]
    · by_cases h' : i = k <;>
        simp [AExpr.inst, AExpr.instVar, interp, Valuation.insert, h, h', interp_liftN]
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.inst, interp, hA]
    congr 1
    funext x
    rw [hb, Valuation.skip_succ_cons, Valuation.insert_cons]
  | _ => simp_all [AExpr.inst, interp]

theorem interp_instL (e : AExpr β) (constants : Assignment β V) (levels : List Nat)
    (env : Nat → V) (ls : List VLevel) :
    interp constants levels env (e.instL ls) =
      interp constants (ls.map (VLevel.eval levels)) env e := by
  induction e generalizing env with
  | const r us =>
    simp [AExpr.instL, interp, List.map_map, Function.comp_def, VLevel.eval_inst]
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.instL, interp, hA, regime_instCondition]
    congr 1
    funext x
    exact hb _
  | _ => simp_all [AExpr.instL, interp, VLevel.eval_inst]

theorem interp_rename {γ : Type w} (e : AExpr β) (mapping : β → γ)
    (constants : Assignment β V) (constants' : Assignment γ V)
    (h : ∀ r ls, constants' (r.rename mapping) ls = constants r ls)
    (levels : List Nat) (env : Nat → V) :
    interp constants' levels env (e.rename mapping) = interp constants levels env e := by
  induction e generalizing env with
  | lam p A b hA hb | forallE p A b hA hb =>
    simp only [AExpr.rename, interp, hA]
    congr 1
    funext x
    exact hb _
  | _ => simp_all [AExpr.rename, interp]

end Ix.Kernel.Model
