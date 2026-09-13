/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Inductive.Telescope

namespace Ix.Theory.Model

open SetTheory

universe u v
variable {β : Type u} {V : Type v} [SetTheory V]

omit [SetTheory V] in
theorem Valuation.insert_extend_at (env : Nat → V) (xs : List V) (a : V) (k : Nat) :
    Valuation.insert (xs.length + k) a (Telescope.extend env xs) =
      Telescope.extend (Valuation.insert k a env) xs := by
  induction xs generalizing env k with
  | nil => simp only [List.length_nil, Nat.zero_add, Telescope.extend]
  | cons x xs ih =>
    simpa only [List.length_cons, Telescope.extend, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Valuation.insert_cons] using ih (Valuation.cons x env) (k + 1)

omit [SetTheory V] in
theorem Valuation.insert_extend (env : Nat → V) (xs : List V) (a : V) :
    Valuation.insert xs.length a (Telescope.extend env xs) =
      Telescope.extend (Valuation.cons a env) xs := by
  simpa only [Nat.add_zero, Valuation.insert_zero] using Valuation.insert_extend_at env xs a 0

namespace AExpr

/-- Simultaneous substitution of an outermost-first field list. -/
def instRev : AExpr β → List (AExpr β) → AExpr β
  | e, [] => e
  | e, a :: rest => instRev (e.inst a rest.length) rest

theorem erase_instRev (e : AExpr β) (args : List (AExpr β)) :
    (e.instRev args).erase = e.erase.instRev (args.map AExpr.erase) := by
  induction args generalizing e <;> simp_all [instRev, VExpr.instRev]

theorem interp_instRev (e : AExpr β) (args : List (AExpr β)) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V) :
    interp constants levels env (e.instRev args) =
      interp constants levels (Telescope.extend env (args.map (interp constants levels env))) e := by
  induction args generalizing e with
  | nil => rfl
  | cons a rest ih =>
    rw [instRev, ih, interp_inst]
    have hlen : (rest.map (interp constants levels env)).length = rest.length := List.length_map ..
    rw [← hlen, Telescope.skip_extend, Valuation.insert_extend]
    rfl

theorem wellDenoted_instRev (e : AExpr β) (args : List (AExpr β)) (constants : Assignment β V)
    (levels : List Nat) (env : Nat → V)
    (ha : ∀ a ∈ args, WellDenoted constants levels env a)
    (he : WellDenoted constants levels
      (Telescope.extend env (args.map (interp constants levels env))) e) :
    WellDenoted constants levels env (e.instRev args) := by
  induction args generalizing e with
  | nil => exact he
  | cons a rest ih =>
    apply ih (e.inst a rest.length) (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hlen : (rest.map (interp constants levels env)).length = rest.length := List.length_map ..
    apply wellDenoted_inst
    · simpa only [← hlen, Telescope.skip_extend] using ha a List.mem_cons_self
    · simpa only [← hlen, Telescope.skip_extend, Valuation.insert_extend, List.map_cons, Telescope.extend] using he

end AExpr

theorem wellDenoted_congr_env (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) {n k : Nat} (hs : e.Scope n k) (env env' : Nat → V)
    (h : ∀ i, i < k → env i = env' i) :
    WellDenoted constants levels env e ↔ WellDenoted constants levels env' e := by
  induction e generalizing k env env' with
  | app f a hf ha =>
    simp only [WellDenoted, hf hs.1 env env' h, ha hs.2 env env' h,
      interp_congr_env f constants levels hs.1 env env' h,
      interp_congr_env a constants levels hs.2 env env' h]
  | lam p A b hA hb | forallE p A b hA hb =>
    have hcons (x : V) : ∀ i, i < k + 1 → Valuation.cons x env i = Valuation.cons x env' i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact h i (by omega)
    simp only [WellDenoted, hA hs.2.1 env env' h, interp_congr_env A constants levels hs.2.1 env env' h,
      hb hs.2.2 _ _ (hcons _), interp_congr_env b constants levels hs.2.2 _ _ (hcons _)]
  | proj _ _ e ih => exact ih hs env env' h
  | _ => rfl

theorem wellDenoted_closed (e : AExpr β) (constants : Assignment β V)
    (levels : List Nat) {n : Nat} (hs : e.Scope n 0) (env env' : Nat → V) :
    WellDenoted constants levels env e ↔ WellDenoted constants levels env' e :=
  wellDenoted_congr_env e constants levels hs env env' (fun _ h => (Nat.not_lt_zero _ h).elim)

end Ix.Theory.Model
