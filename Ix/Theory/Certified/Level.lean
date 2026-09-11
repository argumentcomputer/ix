/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.PropWhen

namespace Ix.Theory.Certified

open VLevel

/-- Compute the exact zero condition of a level. `imax` is zero exactly when
its right operand is zero; its left operand still needs a scoping check. -/
def zeroCondition : VLevel → PropWhen
  | .zero => .always
  | .succ _ => .never
  | .max a b => (zeroCondition a).inter (zeroCondition b)
  | .imax _ b => zeroCondition b
  | .param i => .param i

theorem zeroCondition_correct (l : VLevel) (values : List Nat) :
    (zeroCondition l).holds (values.getD · 0) = (l.eval values == 0) := by
  induction l with
  | zero => rfl
  | succ l ih => simp [zeroCondition, eval]
  | max a b ha hb =>
    rw [zeroCondition, PropWhen.holds_inter, ha, hb]
    apply Bool.eq_iff_iff.mpr
    simp [eval, Nat.max_eq_zero_iff]
  | imax a b ha hb =>
    simp only [zeroCondition, hb]
    apply Bool.eq_iff_iff.mpr
    by_cases h : b.eval values = 0
    · simp [eval, natIMax, h]
    · simp [eval, natIMax, h, Nat.max_eq_zero_iff]
  | param i => simp [zeroCondition, eval]

theorem zeroCondition_wf {n : Nat} {l : VLevel} (h : l.WF n) :
    (zeroCondition l).WF n := by
  induction l with
  | zero => simp [zeroCondition, PropWhen.always, PropWhen.WF]
  | succ l ih => trivial
  | max a b ha hb => exact PropWhen.WF.inter (ha h.1) (hb h.2)
  | imax a b ha hb => exact hb h.2
  | param i => simpa [zeroCondition, PropWhen.param, PropWhen.WF, VLevel.WF] using h

/-- Substitute actual anonymous levels into an annotation. Out-of-bounds
fallback agrees with `VLevel.inst`; successful validation rules it out. -/
def instCondition (levels : List VLevel) (p : PropWhen) : PropWhen :=
  p.bind (fun i => zeroCondition (levels.getD i .zero))

theorem zeroCondition_inst (l : VLevel) (levels : List VLevel) :
    zeroCondition (l.inst levels) = instCondition levels (zeroCondition l) := by
  induction l with
  | zero => rfl
  | succ l ih => rfl
  | max a b ha hb =>
    simpa only [zeroCondition, VLevel.inst, instCondition, PropWhen.bind_inter] using
      congr (congrArg PropWhen.inter ha) hb
  | imax a b ha hb => exact hb
  | param i => simp [VLevel.inst, zeroCondition, instCondition]

theorem instCondition_correct (levels : List VLevel) (p : PropWhen) (values : List Nat) :
    (instCondition levels p).holds (values.getD · 0) =
      p.holds ((levels.map (VLevel.eval values)).getD · 0) := by
  apply PropWhen.holds_bind_of
  intro i
  rw [zeroCondition_correct]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases levels[i]? <;> rfl

theorem instCondition_comp (p : PropWhen) (levels levels' : List VLevel) :
    instCondition levels' (instCondition levels p) =
      instCondition (levels.map (VLevel.inst levels')) p := by
  cases p with
  | never => rfl
  | allZero ps hs =>
    change instCondition levels' (PropWhen.bindList _ ps) = PropWhen.bindList _ ps
    clear hs
    induction ps with
    | nil => rfl
    | cons i ps ih =>
      simp only [PropWhen.bindList, instCondition, PropWhen.bind_inter] at ih ⊢
      rw [ih]
      congr 1
      rw [← instCondition, ← zeroCondition_inst]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases levels[i]? <;> rfl

/-- Validate the exact claimed condition, its canonical encoding, and every
universe index of the source level. This is executable and fails closed. -/
def validateZero? (n : Nat) (l : VLevel) (raw : Option (List Nat)) : Option PropWhen := do
  if !decide (l.WF n) then none else do
    let p ← PropWhen.fromRaw? n raw
    if p = zeroCondition l then some p else none

theorem validateZero?_sound {n : Nat} {l : VLevel} {raw : Option (List Nat)}
    {p : PropWhen} (h : validateZero? n l raw = some p) :
    l.WF n ∧ p.toRaw = raw ∧ p.WF n ∧ p = zeroCondition l := by
  simp only [validateZero?] at h
  split at h
  · contradiction
  next hw =>
    have hw : l.WF n := by simpa using hw
    cases he : PropWhen.fromRaw? n raw with
    | none => simp [he] at h
    | some q =>
      simp only [he] at h
      change (if q = zeroCondition l then some q else none) = some p at h
      split at h
      next hq =>
        cases h
        obtain ⟨hr, hqw⟩ := PropWhen.fromRaw?_sound he
        exact ⟨hw, hr, hqw, hq⟩
      · contradiction

theorem validateZero?_complete {n : Nat} {l : VLevel} (h : l.WF n) :
    validateZero? n l (zeroCondition l).toRaw = some (zeroCondition l) := by
  simp [validateZero?, h, PropWhen.fromRaw?_complete (zeroCondition_wf h)]

end Ix.Theory.Certified
