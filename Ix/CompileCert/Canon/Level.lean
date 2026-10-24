import Ix.CompileCert.Canon.Basic

/-! # Pass 1's level comparison is a total preorder

CS-01, ported from the donor `a9cf3607` (`Canon/Level`), specialized to
today's comparator, which compares levels only after `Ixon.canonUniv`
(the donor's syntactic rule set is gone):

* `compareUniv` (the structural order on `Ixon.Univ`, tag order zero <
  succ < max < imax < var) is a lawful total order
  (`Std.TransCmp compareUniv`, and `compareUniv_eq_iff`);
* `compareLevel` (both sides through `toUniv` with parameters by position
  in each side's own list, then `canonUniv`, then `compareUniv`; a
  metavariable or an unknown parameter an error) is a total preorder on
  the points `(parameter list, level)` (`compareLevel_total`);
* `compareLevels`, a constant's level arguments, lexicographically with the
  shorter list first (`compareLevels_total`). -/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

theorem cmpM_pure (o p : Ordering) :
    SOrder.cmpM (pure ⟨true, o⟩ : Except ε SOrder) (pure ⟨true, p⟩) = pure ⟨true, o.then p⟩ := by
  cases o <;> rfl

/-- A total preorder whose results are strong `pure` values is a lawful `cmp`. -/
theorem transCmp_of_total {α : Type u} (cmp : α → α → Ordering)
    (h : TotalPre (fun a b => (pure ⟨true, cmp a b⟩ : Except ε SOrder))) : Std.TransCmp cmp where
  eq_swap {a b} := by
    have := h.swap (a := b) (b := a) trivial trivial (s := true) (o := cmp b a) rfl
    simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, true_and] at this
    exact this
  isLE_trans {a b c} h1 h2 := by
    obtain ⟨s, o, he, hne⟩ := h.trans (a := a) (b := b) (c := c) trivial trivial trivial
      ⟨true, _, rfl, Ordering.isLE_iff_ne_gt.1 h1⟩ ⟨true, _, rfl, Ordering.isLE_iff_ne_gt.1 h2⟩
    simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact Ordering.isLE_iff_ne_gt.2 hne

/-! ## `compareUniv` -/

def univSize : Ixon.Univ → Nat
  | .zero | .var _ => 1
  | .succ u => univSize u + 1
  | .max a b | .imax a b => univSize a + univSize b + 1

def univTag : Ixon.Univ → Nat
  | .zero => 0
  | .succ _ => 1
  | .max .. => 2
  | .imax .. => 3
  | .var _ => 4

def univL : Ixon.Univ → Ixon.Univ
  | .succ u | .max u _ | .imax u _ => u
  | u => u

def univR : Ixon.Univ → Ixon.Univ
  | .max _ u | .imax _ u => u
  | u => u

def univVar : Ixon.Univ → UInt64
  | .var i => i
  | _ => 0

/-- `compareUniv` as a strong comparison. -/
def univC (a b : Ixon.Univ) : Except Unit SOrder := pure ⟨true, compareUniv a b⟩

theorem univC_total : TotalPre univC := by
  refine PreOn.ofSize univSize fun n ih => ?_
  refine PreOn.ofTag univTag ?_ ?_
  · intro a b _ _ h
    cases a <;> cases b <;> simp_all [univC, univTag, compareUniv, pure, Except.pure] <;> rfl
  · intro T
    have hL : ∀ a, univSize a < n + 1 ∧ univTag a = T → T = 1 ∨ T = 2 ∨ T = 3 →
        univSize (univL a) < n := by
      intro a ⟨hs, ht⟩ hT
      cases a <;> simp_all [univSize, univTag, univL] <;> omega
    have hR : ∀ a, univSize a < n + 1 ∧ univTag a = T → T = 2 ∨ T = 3 →
        univSize (univR a) < n := by
      intro a ⟨hs, ht⟩ hT
      cases a <;> simp_all [univSize, univTag, univR] <;> omega
    match T with
    | 0 =>
      refine (PreOn.const_eq true).congr ?_
      intro a b ⟨_, ha⟩ ⟨_, hb⟩
      cases a <;> cases b <;> simp_all [univC, univTag, compareUniv]
    | 1 =>
      refine (ih.comap univL fun a h => hL a h (by omega)).congr ?_
      intro a b ⟨_, ha⟩ ⟨_, hb⟩
      cases a <;> cases b <;> simp_all [univC, univTag, compareUniv, univL]
    | 2 =>
      refine ((ih.comap univL fun a h => hL a h (by omega)).cmpM
        (ih.comap univR fun a h => hR a h (by omega))).congr ?_
      intro a b ⟨_, ha⟩ ⟨_, hb⟩
      cases a <;> cases b <;> simp_all [univC, univTag, compareUniv, univL, univR, cmpM_pure]
    | 3 =>
      refine ((ih.comap univL fun a h => hL a h (by omega)).cmpM
        (ih.comap univR fun a h => hR a h (by omega))).congr ?_
      intro a b ⟨_, ha⟩ ⟨_, hb⟩
      cases a <;> cases b <;> simp_all [univC, univTag, compareUniv, univL, univR, cmpM_pure]
    | 4 =>
      refine (PreOn.pureCmp (compare : UInt64 → UInt64 → Ordering) univVar).congr ?_
      intro a b ⟨_, ha⟩ ⟨_, hb⟩
      cases a <;> cases b <;> simp_all [univC, univTag, compareUniv, univVar]
    | T + 5 =>
      refine PreOn.empty fun a ⟨_, ha⟩ => ?_
      cases a <;> simp [univTag] at ha

instance transCmp_compareUniv : Std.TransCmp compareUniv :=
  transCmp_of_total compareUniv univC_total

/-- `compareUniv` answers `eq` exactly on equal universes. -/
theorem compareUniv_eq_iff : ∀ {a b : Ixon.Univ}, compareUniv a b = .eq ↔ a = b
  | .zero, .zero | .zero, .succ _ | .zero, .max .. | .zero, .imax .. | .zero, .var _
  | .succ _, .zero | .succ _, .max .. | .succ _, .imax .. | .succ _, .var _
  | .max .., .zero | .max .., .succ _ | .max .., .imax .. | .max .., .var _
  | .imax .., .zero | .imax .., .succ _ | .imax .., .max .. | .imax .., .var _
  | .var _, .zero | .var _, .succ _ | .var _, .max .. | .var _, .imax .. => by simp [compareUniv]
  | .succ x, .succ y => by
    simp only [compareUniv, Ixon.Univ.succ.injEq]; exact compareUniv_eq_iff
  | .max a b, .max c d | .imax a b, .imax c d => by
    simp only [compareUniv, Ordering.then_eq_eq, Ixon.Univ.max.injEq, Ixon.Univ.imax.injEq,
      compareUniv_eq_iff]
  | .var i, .var j => by
    simp only [compareUniv, Ixon.Univ.var.injEq]
    exact ⟨Std.LawfulEqCmp.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self⟩

/-! ## Levels -/

/-- A level with its side's universe-parameter list. -/
abbrev LvlPt := List Ix.Name × Ix.Level

/-- `compareLevel` on points. -/
def lvlC (a b : LvlPt) : Except CmpError SOrder :=
  compareLevel a.1 b.1 a.2 b.2

/-- The level of a point after `toUniv`, or `zero` where it fails. -/
def univOf (a : LvlPt) : Ixon.Univ :=
  match toUniv a.1 a.2 with
  | .ok u => u
  | .error _ => .zero

theorem compareLevel_total : TotalPre lvlC := by
  refine PreOn.ofGood (fun a => ∃ u, toUniv a.1 a.2 = .ok u) ?_ ?_
  · rintro ⟨xl, x⟩ ⟨yl, y⟩ - - hbad r
    simp only [lvlC, compareLevel]
    cases hx : toUniv xl x <;> cases hy : toUniv yl y <;>
      simp_all [bind, Except.bind]
  refine (PreOn.pureCmp compareUniv (fun a => Ixon.canonUniv (univOf a))).congr ?_
  rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨-, ux, hx⟩ ⟨-, uy, hy⟩
  simp only at hx hy
  simp [lvlC, compareLevel, univOf, hx, hy, bind, Except.bind, pure, Except.pure]

theorem compareLevels_eq (xl yl : List Ix.Name) (xs ys : List Ix.Level) :
    compareLevels xl yl xs ys = zipCtx lvlC (xl, xs) (yl, ys) := rfl

theorem compareLevels_total :
    TotalPre (fun a b : List Ix.Name × List Ix.Level => compareLevels a.1 b.1 a.2 b.2) :=
  (compareLevel_total.zipCtx).mono fun _ _ _ _ => trivial

end Ix.CompileCert.Canon
