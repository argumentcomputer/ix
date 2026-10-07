import Ix.CompileCert.Canon.Basic

/-!
# M7 L1: the level comparisons are total preorders

Design document §3.2, leaf "level trees under positional parameters": the level order of
Pass 1 (`Ix/Compile/Canon/Order.lean`) in both rule sets is a total preorder on its
ok-domain:

* `compareUniv` (the structural order on `Ixon.Univ`, tag order zero < succ < max < imax <
  var) is a lawful total order (`Std.TransCmp compareUniv`);
* `compareLevelSyn` (`LevelCompare.syntactic`: the same tag order, parameters by position in
  each side's own list, a metavariable or an unknown parameter an error) is a total
  preorder on the points `(parameter list, level)` (`compareLevelSyn_total`);
* `compareLevel lc` for both `lc` (`afterCanonUniv` compares `canonUniv` forms, which is
  `compareUniv` read through a function) (`compareLevel_total`);
* `compareLevels lc`, the lists of a constant's level arguments, lexicographically with the
  shorter first (`compareLevels_total`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon

/-! ## Induction on a size -/

/-- A comparison is a total preorder once it is one on the points of size `< n + 1`
whenever it is one on the points of size `< n`. -/
theorem PreOn.ofSize {α : Type u} {F : α → α → Except ε SOrder} (size : α → Nat)
    (step : ∀ n, PreOn (fun a => size a < n) F → PreOn (fun a => size a < n + 1) F) :
    TotalPre F := by
  have h : ∀ n, PreOn (fun a => size a < n) F := by
    intro n; induction n with
    | zero => exact ⟨fun ha => absurd ha (by omega), fun ha => absurd ha (by omega)⟩
    | succ n ih => exact step n ih
  constructor
  · intro a b _ _; exact (h (size a + size b + 1)).swap (by omega) (by omega)
  · intro a b c _ _ _
    exact (h (size a + size b + size c + 1)).trans (by omega) (by omega) (by omega)

/-- The empty set of points. -/
theorem PreOn.empty {α : Type u} {S : α → Prop} {F : α → α → Except ε SOrder}
    (h : ∀ a, ¬ S a) : PreOn S F :=
  ⟨fun ha => absurd ha (h _), fun ha => absurd ha (h _)⟩

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

/-! ## Levels -/

/-- A level with its side's universe-parameter list. -/
abbrev LvlPt := List Ix.Name × Ix.Level

def levelSize : Ix.Level → Nat
  | .zero _ | .param .. | .mvar .. => 1
  | .succ l _ => levelSize l + 1
  | .max a b _ | .imax a b _ => levelSize a + levelSize b + 1

def levelTag : Ix.Level → Nat
  | .zero _ => 0
  | .succ .. => 1
  | .max .. => 2
  | .imax .. => 3
  | .param .. => 4
  | .mvar .. => 5

def levelL : Ix.Level → Ix.Level
  | .succ u _ | .max u _ _ | .imax u _ _ => u
  | u => u

def levelR : Ix.Level → Ix.Level
  | .max _ u _ | .imax _ u _ => u
  | u => u

def levelParam : Ix.Level → Ix.Name
  | .param n _ => n
  | _ => rawName

/-- `compareLevelSyn` on points. -/
def lvlSyn (a b : LvlPt) : Except String SOrder := compareLevelSyn a.1 b.1 a.2 b.2

theorem compareLevelSyn_param (xl yl : List Ix.Name) (x y : Ix.Name) (h1 h2 : Address) :
    compareLevelSyn xl yl (.param x h1) (.param y h2) =
      match xl.idxOf? x, yl.idxOf? y with
      | some xi, some yi => pure ⟨true, compare xi yi⟩
      | none, _ => .error s!"unknown universe parameter {namePretty x}"
      | _, none => .error s!"unknown universe parameter {namePretty y}" := by
  rfl

theorem compareLevelSyn_total : TotalPre lvlSyn := by
  refine PreOn.ofSize (fun a => levelSize a.2) fun n ih => ?_
  refine PreOn.ofGood (fun a => levelTag a.2 ≠ 5) ?_ ?_
  · rintro ⟨xl, x⟩ ⟨yl, y⟩ - - h r
    cases x <;> cases y <;> simp only [levelTag] at h <;>
      first | (exfalso; omega) | (intro e; cases e)
  refine PreOn.ofTag (fun a => levelTag a.2) ?_ ?_
  · rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨-, hx⟩ ⟨-, hy⟩ h
    cases x <;> cases y <;> simp only [levelTag] at hx hy h <;> first | omega | rfl
  intro T
  have hL : ∀ a : LvlPt, (levelSize a.2 < n + 1 ∧ levelTag a.2 ≠ 5) ∧ levelTag a.2 = T →
      T = 1 ∨ T = 2 ∨ T = 3 → levelSize (levelL a.2) < n := by
    rintro ⟨l, a⟩ ⟨⟨hs, -⟩, ht⟩ hT
    cases a <;> simp_all [levelSize, levelTag, levelL] <;> omega
  have hR : ∀ a : LvlPt, (levelSize a.2 < n + 1 ∧ levelTag a.2 ≠ 5) ∧ levelTag a.2 = T →
      T = 2 ∨ T = 3 → levelSize (levelR a.2) < n := by
    rintro ⟨l, a⟩ ⟨⟨hs, -⟩, ht⟩ hT
    cases a <;> simp_all [levelSize, levelTag, levelR] <;> omega
  match T with
  | 0 =>
    refine (PreOn.const_eq true).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, ha⟩ ⟨_, hb⟩
    cases x <;> cases y <;> simp only [levelTag] at ha hb <;> first | omega | rfl
  | 1 =>
    refine (ih.comap (fun a => (a.1, levelL a.2)) fun a h => hL a h (by omega)).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, ha⟩ ⟨_, hb⟩
    cases x <;> cases y <;> simp only [levelTag] at ha hb <;> first | omega | rfl
  | 2 =>
    refine ((ih.comap (fun a => (a.1, levelL a.2)) fun a h => hL a h (by omega)).cmpM
      (ih.comap (fun a => (a.1, levelR a.2)) fun a h => hR a h (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, ha⟩ ⟨_, hb⟩
    cases x <;> cases y <;> simp only [levelTag] at ha hb <;> first | omega | rfl
  | 3 =>
    refine ((ih.comap (fun a => (a.1, levelL a.2)) fun a h => hL a h (by omega)).cmpM
      (ih.comap (fun a => (a.1, levelR a.2)) fun a h => hR a h (by omega))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨_, ha⟩ ⟨_, hb⟩
    cases x <;> cases y <;> simp only [levelTag] at ha hb <;> first | omega | rfl
  | 4 =>
    -- parameters by position; an unknown parameter is an error
    refine PreOn.ofGood (fun a => (a.1.idxOf? (levelParam a.2)).isSome) ?_ ?_
    · rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨hsa, ha⟩ ⟨hsb, hb⟩ hbad r
      cases x <;> cases y <;> simp only [levelTag] at ha hb <;> try omega
      rename_i x hx1 y hy1
      simp only [levelParam] at hbad
      simp only [lvlSyn, compareLevelSyn_param]
      cases hx : xl.idxOf? x <;> cases hy : yl.idxOf? y <;> simp_all
    refine (PreOn.pureCmp (compare : Nat → Nat → Ordering)
      (fun a : LvlPt => (a.1.idxOf? (levelParam a.2)).getD 0)).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨⟨hsa, ha⟩, ga⟩ ⟨⟨hsb, hb⟩, gb⟩
    cases x <;> cases y <;> simp only [levelTag] at ha hb <;> try omega
    rename_i x hx1 y hy1
    simp only [levelParam] at ga gb ⊢
    simp only [lvlSyn, compareLevelSyn_param]
    cases hx : xl.idxOf? x <;> cases hy : yl.idxOf? y <;> simp_all
  | T + 5 =>
    refine PreOn.empty fun a ⟨⟨_, h5⟩, ha⟩ => ?_
    obtain ⟨l, a⟩ := a
    cases a <;> simp [levelTag] at ha h5

/-- `compareLevel` on points. -/
def lvlC (lc : LevelCompare) (a b : LvlPt) : Except String SOrder :=
  compareLevel lc a.1 b.1 a.2 b.2

/-- The level of a point after `toUniv`, or `zero` where it fails. -/
def univOf (a : LvlPt) : Ixon.Univ :=
  match toUniv a.1 a.2 with
  | .ok u => u
  | .error _ => .zero

theorem compareLevel_total (lc : LevelCompare) : TotalPre (lvlC lc) := by
  cases lc with
  | syntactic => exact compareLevelSyn_total.congr fun _ _ _ _ => rfl
  | afterCanonUniv =>
    refine PreOn.ofGood (fun a => ∃ u, toUniv a.1 a.2 = .ok u) ?_ ?_
    · rintro ⟨xl, x⟩ ⟨yl, y⟩ - - hbad r
      simp only [lvlC, compareLevel]
      cases hx : toUniv xl x <;> cases hy : toUniv yl y <;>
        simp_all [bind, Except.bind]
    refine (PreOn.pureCmp compareUniv (fun a => Ixon.canonUniv (univOf a))).congr ?_
    rintro ⟨xl, x⟩ ⟨yl, y⟩ ⟨-, ux, hx⟩ ⟨-, uy, hy⟩
    simp only at hx hy
    simp [lvlC, compareLevel, univOf, hx, hy, bind, Except.bind, pure, Except.pure]

theorem compareLevels_eq (lc : LevelCompare) (xl yl : List Ix.Name) (xs ys : List Ix.Level) :
    compareLevels lc xl yl xs ys = zipCtx (lvlC lc) (xl, xs) (yl, ys) := rfl

theorem compareLevels_total (lc : LevelCompare) :
    TotalPre (fun a b : List Ix.Name × List Ix.Level => compareLevels lc a.1 b.1 a.2 b.2) :=
  ((compareLevel_total lc).zipCtx).mono fun _ _ _ _ => trivial

end Ix.CompileCert.Canon
