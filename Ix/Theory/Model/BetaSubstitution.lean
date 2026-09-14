/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Instantiation

/-! Structural laws for substituting an outermost-first argument list.
The natural-number syntax laws are independent of kernel index bounds. -/

namespace Ix.Theory.Model.AExpr

universe u

theorem inst_liftN_top (term argument : AExpr β) (count cutoff : Nat) :
    (term.liftN (count + 1) cutoff).inst argument (count + cutoff) = term.liftN count cutoff := by
  induction term generalizing cutoff with
  | bvar index =>
      by_cases below : index < cutoff
      · simp [liftN, liftVar, inst, instVar, below, show index < count + cutoff by omega]
      · simp [liftN, liftVar, inst, instVar, below,
          show ¬ count + 1 + index < count + cutoff by omega,
          show count + 1 + index ≠ count + cutoff by omega]
  | lam condition domain body ihDomain ihBody | forallE condition domain body ihDomain ihBody =>
      simp only [liftN, inst, ihDomain, show count + cutoff + 1 = count + (cutoff + 1) by omega,
        ihBody]
  | _ => simp_all [liftN, inst]

/-- Simultaneous substitution above a fixed number of retained binders. -/
def instRevAt : AExpr β → List (AExpr β) → Nat → AExpr β
  | term, [], _ => term
  | term, argument :: arguments, cutoff =>
      instRevAt (term.inst argument (cutoff + arguments.length)) arguments cutoff

theorem instRevAt_zero (term : AExpr β) (arguments : List (AExpr β)) :
    term.instRevAt arguments 0 = term.instRev arguments := by
  induction arguments generalizing term with
  | nil => rfl
  | cons argument arguments ih => simpa only [instRevAt, instRev, Nat.zero_add] using ih _

@[simp] theorem erase_instRevAt (term : AExpr β) (arguments : List (AExpr β)) (cutoff : Nat) :
    (term.instRevAt arguments cutoff).erase = term.erase.instRevAt (arguments.map erase) cutoff := by
  induction arguments generalizing term with
  | nil => rfl
  | cons argument arguments ih => simp only [instRevAt, VExpr.instRevAt, List.map_cons,
      List.length_map, erase_inst, ih]

@[simp] theorem instRevAt_sort (level : VLevel) (arguments : List (AExpr β)) (cutoff : Nat) :
    (sort level).instRevAt arguments cutoff = sort level := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih => simpa only [instRevAt, inst] using ih

@[simp] theorem instRevAt_const (ref : ConstRef β) (levels : List VLevel)
    (arguments : List (AExpr β)) (cutoff : Nat) :
    (const ref levels).instRevAt arguments cutoff = const ref levels := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih => simpa only [instRevAt, inst] using ih

@[simp] theorem instRevAt_natLit (value : Nat) (arguments : List (AExpr β)) (cutoff : Nat) :
    (natLit value).instRevAt arguments cutoff = natLit value := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih => simpa only [instRevAt, inst] using ih

theorem instRevAt_liftN (term : AExpr β) (arguments : List (AExpr β)) (cutoff : Nat) :
    (term.liftN (arguments.length + cutoff)).instRevAt arguments cutoff = term.liftN cutoff := by
  induction arguments with
  | nil => simp [instRevAt]
  | cons argument arguments ih =>
      simp only [List.length_cons, instRevAt]
      rw [show arguments.length + 1 + cutoff = (arguments.length + cutoff) + 1 by omega,
        show cutoff + arguments.length = (arguments.length + cutoff) + 0 by omega,
        inst_liftN_top]
      exact ih

theorem instRevAt_bvar_below (arguments : List (AExpr β)) (index cutoff : Nat)
    (below : index < cutoff) :
    (AExpr.bvar index).instRevAt arguments cutoff = .bvar index := by
  induction arguments with
  | nil => rfl
  | cons argument arguments ih =>
      simpa only [instRevAt, inst, instVar, if_pos (show index < cutoff + arguments.length by omega)] using ih

theorem instRevAt_bvar_above (arguments : List (AExpr β)) (index cutoff : Nat)
    (above : cutoff + arguments.length ≤ index) :
    (AExpr.bvar index).instRevAt arguments cutoff = .bvar (index - arguments.length) := by
  induction arguments generalizing index with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [List.length_cons] at above
      simp only [instRevAt, inst, instVar,
        if_neg (show ¬ index < cutoff + arguments.length by omega),
        if_neg (show index ≠ cutoff + arguments.length by omega)]
      rw [ih (index - 1) (by omega)]
      congr 1
      simp only [List.length_cons]
      omega

theorem instRevAt_bvar_selected (arguments : List (AExpr β)) (index cutoff : Nat)
    (inside : index < arguments.length) :
    (AExpr.bvar (cutoff + index)).instRevAt arguments cutoff =
      (arguments[arguments.length - index - 1]'(by omega)).liftN cutoff := by
  induction arguments generalizing index with
  | nil => simp at inside
  | cons argument arguments ih =>
      simp only [List.length_cons] at inside
      by_cases outermost : index = arguments.length
      · subst index
        simp only [instRevAt, inst, instVar, Nat.lt_irrefl, if_false, if_true]
        rw [show cutoff + arguments.length = arguments.length + cutoff by omega, instRevAt_liftN]
        simp
      · have inner : index < arguments.length := by omega
        simp only [instRevAt, inst, instVar,
          if_pos (show cutoff + index < cutoff + arguments.length by omega)]
        rw [ih index inner]
        simp only [List.length_cons,
          show arguments.length + 1 - index - 1 = (arguments.length - index - 1) + 1 by omega,
          List.getElem_cons_succ]

@[simp] theorem instRevAt_app (fn arg : AExpr β) (arguments : List (AExpr β)) (cutoff : Nat) :
    (fn.app arg).instRevAt arguments cutoff =
      (fn.instRevAt arguments cutoff).app (arg.instRevAt arguments cutoff) := by
  induction arguments generalizing fn arg with
  | nil => rfl
  | cons argument arguments ih => simp only [instRevAt, inst, ih]

@[simp] theorem instRevAt_lam (condition : Certified.PropWhen) (domain body : AExpr β)
    (arguments : List (AExpr β)) (cutoff : Nat) :
    (lam condition domain body).instRevAt arguments cutoff =
      lam condition (domain.instRevAt arguments cutoff) (body.instRevAt arguments (cutoff + 1)) := by
  induction arguments generalizing domain body with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [instRevAt, inst, ih,
        show cutoff + arguments.length + 1 = cutoff + 1 + arguments.length by omega]

@[simp] theorem instRevAt_forallE (condition : Certified.PropWhen) (domain body : AExpr β)
    (arguments : List (AExpr β)) (cutoff : Nat) :
    (forallE condition domain body).instRevAt arguments cutoff =
      forallE condition (domain.instRevAt arguments cutoff) (body.instRevAt arguments (cutoff + 1)) := by
  induction arguments generalizing domain body with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [instRevAt, inst, ih,
        show cutoff + arguments.length + 1 = cutoff + 1 + arguments.length by omega]

@[simp] theorem instRevAt_proj (ref : ConstRef β) (field : Nat) (major : AExpr β)
    (arguments : List (AExpr β)) (cutoff : Nat) :
    (proj ref field major).instRevAt arguments cutoff =
      proj ref field (major.instRevAt arguments cutoff) := by
  induction arguments generalizing major with
  | nil => rfl
  | cons argument arguments ih => simp only [instRevAt, inst, ih]

end Ix.Theory.Model.AExpr
