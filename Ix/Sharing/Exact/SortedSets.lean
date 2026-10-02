/-
  Ascending lists of terms as sets: the least element of a symmetric
  difference (`firstDiff`), the `setPrec` tie order in terms of it, unions of
  sets over disjoint domains, and chains of sets in `setPrec` order (the
  first difference of two sets of a chain is the least first difference of
  the neighbours between them). Used by the rank-based table-count knapsack
  (`Exact.KnapsackFast`).
-/
module

public import Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Common

public section

namespace Ix.Sharing.Exact

/-! ## First differences -/

/-- The least element of the symmetric difference of two ascending lists
(`none` when they are equal): at the first position where they differ, the
smaller element is in one list only. -/
def firstDiff : List Nat → List Nat → Option Nat
  | [], [] => none
  | x :: _, [] => some x
  | [], y :: _ => some y
  | x :: xs, y :: ys => if x = y then firstDiff xs ys else some (min x y)

/-- `m` is the least element of the symmetric difference of `A` and `B`. -/
def IsFD (A B : List Nat) (m : Nat) : Prop :=
  (m ∈ A ↔ m ∉ B) ∧ ∀ y, y < m → (y ∈ A ↔ y ∈ B)

theorem IsFD.symm {A B : List Nat} {m : Nat} (h : IsFD A B m) : IsFD B A m :=
  ⟨by have := h.1; by_cases hA : m ∈ A <;> by_cases hB : m ∈ B <;> simp_all,
   fun y hy => (h.2 y hy).symm⟩

theorem IsFD.unique {A B : List Nat} {m m' : Nat} (h : IsFD A B m) (h' : IsFD A B m') :
    m = m' := by
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · have := h'.2 m hlt
    have := h.1
    exfalso
    by_cases hm : m ∈ A <;> simp_all
  · exact heq
  · have := h.2 m' hgt
    have := h'.1
    exfalso
    by_cases hm : m' ∈ A <;> simp_all

theorem firstDiff_spec : ∀ (A B : List Nat), A.Pairwise (· < ·) → B.Pairwise (· < ·) →
    (firstDiff A B = none ↔ A = B) ∧ ∀ m, firstDiff A B = some m → IsFD A B m
  | [], [], _, _ => ⟨by simp [firstDiff], fun m h => by simp [firstDiff] at h⟩
  | x :: xs, [], hA, _ => by
    refine ⟨by simp [firstDiff], fun m h => ?_⟩
    simp only [firstDiff, Option.some.injEq] at h
    subst h
    refine ⟨by simp, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, iff_false, not_or]
    refine ⟨Nat.ne_of_lt hy, fun hy' => ?_⟩
    have := List.rel_of_pairwise_cons hA hy'
    omega
  | [], y :: ys, _, hB => by
    refine ⟨by simp [firstDiff], fun m h => ?_⟩
    simp only [firstDiff, Option.some.injEq] at h
    subst h
    refine ⟨by simp, fun z hz => ?_⟩
    simp only [List.not_mem_nil, List.mem_cons, false_iff, not_or]
    refine ⟨Nat.ne_of_lt hz, fun hz' => ?_⟩
    have := List.rel_of_pairwise_cons hB hz'
    omega
  | x :: xs, y :: ys, hA, hB => by
    have hxs := hA.of_cons
    have hys := hB.of_cons
    by_cases hxy : x = y
    · subst hxy
      obtain ⟨ih1, ih2⟩ := firstDiff_spec xs ys hxs hys
      simp only [firstDiff, ite_true]
      refine ⟨by rw [ih1]; simp, fun m h => ?_⟩
      obtain ⟨h1, h2⟩ := ih2 m h
      -- `m` is in `xs` or `ys`, so it is above `x`
      have hmx : x < m := by
        by_cases hm : m ∈ xs
        · exact List.rel_of_pairwise_cons hA hm
        · have : m ∈ ys := by
            by_cases hc : m ∈ ys
            · exact hc
            · exact absurd (h1.mpr hc) hm
          exact List.rel_of_pairwise_cons hB this
      refine ⟨?_, fun z hz => ?_⟩
      · simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · omega
          · intro h'
            rcases h' with h' | h'
            · omega
            · exact h1.mp h h'
        · intro h'
          simp only [not_or] at h'
          exact Or.inr (h1.mpr h'.2)
      · simp only [List.mem_cons]
        by_cases hzx : z = x
        · simp [hzx]
        · simp only [hzx, false_or]
          exact h2 z hz
    · simp only [firstDiff, hxy, ite_false]
      refine ⟨by simp [hxy], fun m h => ?_⟩
      simp only [Option.some.injEq] at h
      subst h
      rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
      · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
        refine ⟨?_, fun z hz => ?_⟩
        · simp only [List.mem_cons, true_or, true_iff, not_or]
          refine ⟨hxy, fun h' => ?_⟩
          have := List.rel_of_pairwise_cons hB h'
          omega
        · simp only [List.mem_cons]
          have h1 : z ∉ xs := fun h' => by have := List.rel_of_pairwise_cons hA h'; omega
          have h2 : z ∉ ys := fun h' => by have := List.rel_of_pairwise_cons hB h'; omega
          simp only [h1, h2, or_false]
          omega
      · rw [Nat.min_eq_right (Nat.le_of_lt hgt)]
        refine ⟨?_, fun z hz => ?_⟩
        · simp only [List.mem_cons, true_or, not_true, iff_false, not_or]
          refine ⟨fun h' => hxy h'.symm, fun h' => ?_⟩
          have := List.rel_of_pairwise_cons hA h'
          omega
        · simp only [List.mem_cons]
          have h1 : z ∉ xs := fun h' => by have := List.rel_of_pairwise_cons hA h'; omega
          have h2 : z ∉ ys := fun h' => by have := List.rel_of_pairwise_cons hB h'; omega
          simp only [h1, h2, or_false]
          omega

/-- The first difference is the unique least element of the symmetric
difference. -/
theorem firstDiff_eq_some_iff {A B : List Nat} (hA : A.Pairwise (· < ·))
    (hB : B.Pairwise (· < ·)) {m : Nat} : firstDiff A B = some m ↔ IsFD A B m := by
  obtain ⟨hnone, hsome⟩ := firstDiff_spec A B hA hB
  constructor
  · exact hsome m
  · intro h
    cases hfd : firstDiff A B with
    | none =>
      have hAB := hnone.mp hfd
      subst hAB
      have := h.1
      by_cases hm : m ∈ A <;> simp_all
    | some m' => rw [IsFD.unique (hsome m' hfd) h]

/-- Sorted lists with the same members are equal. -/
theorem eq_of_mem_iff {A B : List Nat} (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· < ·))
    (h : ∀ y, y ∈ A ↔ y ∈ B) : A = B := by
  apply List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h1 h2 => absurd h2 (by omega))
    hA hB
  exact (List.perm_ext_iff_of_nodup (hA.imp Nat.ne_of_lt) (hB.imp Nat.ne_of_lt)).mpr h

/-! ## The tie order -/

theorem compareDesc_eq (x y : Nat) : compareDesc x y = compare y x := by
  unfold compareDesc; rfl

/-- On ascending lists, `setPrec a b` holds exactly when the first difference
is in `b`. -/
theorem setPrec_iff_list : ∀ (A B : List Nat), A.Pairwise (· < ·) → B.Pairwise (· < ·) →
    (List.compareLex compareDesc A B = .lt ↔ ∃ m, firstDiff A B = some m ∧ m ∈ B)
  | [], [], _, _ => by simp [firstDiff, List.compareLex_nil_nil]
  | x :: xs, [], _, _ => by simp [firstDiff, List.compareLex_cons_nil]
  | [], y :: ys, _, _ => by simp [firstDiff, List.compareLex_nil_cons]
  | x :: xs, y :: ys, hA, hB => by
    rw [List.compareLex_cons_cons, compareDesc_eq]
    by_cases hxy : x = y
    · subst hxy
      simp only [Nat.compare_eq_eq.mpr rfl, Ordering.eq_then, firstDiff, ite_true]
      rw [setPrec_iff_list xs ys hA.of_cons hB.of_cons]
      constructor
      · rintro ⟨m, h1, h2⟩; exact ⟨m, h1, List.mem_cons_of_mem _ h2⟩
      · rintro ⟨m, h1, h2⟩
        refine ⟨m, h1, ?_⟩
        rcases List.mem_cons.mp h2 with h | h
        · -- `m = x` is impossible: `m` is in `xs` or `ys`
          exfalso
          obtain ⟨hfd, _⟩ := (firstDiff_spec xs ys hA.of_cons hB.of_cons).2 m h1
          subst h
          by_cases hm : m ∈ xs
          · have := List.rel_of_pairwise_cons hA hm; omega
          · have : m ∈ ys := by
              by_cases hc : m ∈ ys
              · exact hc
              · exact absurd (hfd.mpr hc) hm
            have := List.rel_of_pairwise_cons hB this; omega
        · exact h
    · simp only [firstDiff, hxy, ite_false, Option.some.injEq, exists_eq_left']
      rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
      · rw [Nat.compare_eq_gt.mpr hlt, Nat.min_eq_left (Nat.le_of_lt hlt)]
        simp only [Ordering.gt_then, reduceCtorEq, false_iff, List.mem_cons, not_or]
        refine ⟨hxy, fun h' => ?_⟩
        have := List.rel_of_pairwise_cons hB h'
        omega
      · rw [Nat.compare_eq_lt.mpr hgt, Nat.min_eq_right (Nat.le_of_lt hgt)]
        simp

theorem setPrec_iff {a b : Array Nat} (ha : a.toList.Pairwise (· < ·))
    (hb : b.toList.Pairwise (· < ·)) :
    setPrec a b = true ↔ ∃ m, firstDiff a.toList b.toList = some m ∧ m ∈ b.toList := by
  unfold setPrec
  rw [Array.compareLex_eq_compareLex_toList, ← setPrec_iff_list _ _ ha hb]

  cases List.compareLex compareDesc a.toList b.toList <;> decide

/-! ## Unions over disjoint domains -/

/-- The least of two optional elements, `none` standing for no element. -/
def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

theorem firstDiff_none {A B : List Nat} (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· < ·)) :
    firstDiff A B = none ↔ A = B :=
  (firstDiff_spec A B hA hB).1

/-- The first difference of two unions `S ∪ X`, `S' ∪ Y` whose parts come from
disjoint domains is the smaller of the parts' first differences. -/
theorem firstDiff_union {S S' X Y U V : List Nat}
    (hS : S.Pairwise (· < ·)) (hS' : S'.Pairwise (· < ·)) (hX : X.Pairwise (· < ·))
    (hY : Y.Pairwise (· < ·)) (hUs : U.Pairwise (· < ·)) (hVs : V.Pairwise (· < ·))
    (hU : ∀ z, z ∈ U ↔ z ∈ S ∨ z ∈ X) (hV : ∀ z, z ∈ V ↔ z ∈ S' ∨ z ∈ Y)
    (hdisj : ∀ z, (z ∈ S ∨ z ∈ S') → z ∉ X ∧ z ∉ Y) :
    firstDiff U V = minOpt (firstDiff S S') (firstDiff X Y) := by
  cases h1 : firstDiff S S' with
  | none =>
    have hSS := (firstDiff_none hS hS').mp h1
    subst hSS
    cases h2 : firstDiff X Y with
    | none =>
      have hXY := (firstDiff_none hX hY).mp h2
      subst hXY
      exact (firstDiff_none hUs hVs).mpr (eq_of_mem_iff hUs hVs fun z => by rw [hU, hV])
    | some b =>
      have hb := (firstDiff_eq_some_iff hX hY).mp h2
      simp only [minOpt]
      apply (firstDiff_eq_some_iff hUs hVs).mpr
      have hbS : b ∉ S := by
        intro h
        have := hdisj b (Or.inl h)
        by_cases hbX : b ∈ X
        · exact this.1 hbX
        · exact this.2 (by have := hb.1; by_cases hbY : b ∈ Y <;> simp_all)
      refine ⟨?_, fun z hz => ?_⟩
      · rw [hU, hV]; simp only [hbS, false_or]; exact hb.1
      · rw [hU, hV, hb.2 z hz]
  | some a =>
    have ha := (firstDiff_eq_some_iff hS hS').mp h1
    have haS : a ∈ S ∨ a ∈ S' := by
      have := ha.1; by_cases has : a ∈ S <;> simp_all
    obtain ⟨haX, haY⟩ := hdisj a haS
    cases h2 : firstDiff X Y with
    | none =>
      have hXY := (firstDiff_none hX hY).mp h2
      subst hXY
      simp only [minOpt]
      apply (firstDiff_eq_some_iff hUs hVs).mpr
      refine ⟨?_, fun z hz => ?_⟩
      · rw [hU, hV]; simp only [haX, or_false]; exact ha.1
      · rw [hU, hV, ha.2 z hz]
    | some b =>
      have hb := (firstDiff_eq_some_iff hX hY).mp h2
      have hbXY : b ∈ X ∨ b ∈ Y := by
        have := hb.1; by_cases hbx : b ∈ X <;> simp_all
      have hab : a ≠ b := by
        intro h; subst h
        rcases hbXY with h | h
        · exact haX h
        · exact haY h
      have hbS : b ∉ S ∧ b ∉ S' := by
        constructor
        · intro h
          have := hdisj b (Or.inl h)
          rcases hbXY with h' | h'
          · exact this.1 h'
          · exact this.2 h'
        · intro h
          have := hdisj b (Or.inr h)
          rcases hbXY with h' | h'
          · exact this.1 h'
          · exact this.2 h'
      simp only [minOpt]
      apply (firstDiff_eq_some_iff hUs hVs).mpr
      rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
      · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
        refine ⟨?_, fun z hz => ?_⟩
        · rw [hU, hV]; simp only [haX, haY, or_false]; exact ha.1
        · rw [hU, hV, ha.2 z hz, hb.2 z (by omega)]
      · rw [Nat.min_eq_right (Nat.le_of_lt hgt)]
        refine ⟨?_, fun z hz => ?_⟩
        · rw [hU, hV]; simp only [hbS.1, hbS.2, false_or]; exact hb.1
        · rw [hU, hV, ha.2 z (by omega), hb.2 z hz]

/-! ## Chains in the tie order -/

/-- Three sets in `setPrec` order: the first difference of the outer two is the
smaller of the two neighbouring first differences, and it is in the last. -/
theorem firstDiff_chain3 {A B C : List Nat} (hA : A.Pairwise (· < ·)) (hB : B.Pairwise (· < ·))
    (hC : C.Pairwise (· < ·)) {x y : Nat} (hAB : firstDiff A B = some x) (hxB : x ∈ B)
    (hBC : firstDiff B C = some y) (hyC : y ∈ C) :
    firstDiff A C = some (min x y) ∧ min x y ∈ C := by
  have hx := (firstDiff_eq_some_iff hA hB).mp hAB
  have hy := (firstDiff_eq_some_iff hB hC).mp hBC
  have hxA : x ∉ A := fun h => (hx.1.mp h) hxB
  have hyB : y ∉ B := fun h => (hy.1.mp h) hyC
  have hxy : x ≠ y := fun h => by subst h; exact hyB hxB
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
  · rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
    have hxC : x ∈ C := (hy.2 x hlt).mp hxB
    refine ⟨(firstDiff_eq_some_iff hA hC).mpr ⟨?_, fun z hz => ?_⟩, hxC⟩
    · simp [hxA, hxC]
    · rw [hx.2 z hz, hy.2 z (by omega)]
  · rw [Nat.min_eq_right (Nat.le_of_lt hgt)]
    have hyA : y ∉ A := fun h => hyB ((hx.2 y hgt).mp h)
    refine ⟨(firstDiff_eq_some_iff hA hC).mpr ⟨?_, fun z hz => ?_⟩, hyC⟩
    · simp [hyA, hyC]
    · rw [hx.2 z (by omega), hy.2 z hz]

/-- The least of `d i, …, d (i + k)`. -/
def rmin (d : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => d i
  | k + 1 => min (rmin d i k) (d (i + k + 1))

/-- In a chain of ascending lists in `setPrec` order (each neighbouring first
difference `d r` is in the later set), the first difference of the sets at
`i` and `i + k + 1` is the least neighbouring first difference between them,
and it is in the later set. -/
theorem firstDiff_chain {sets : Nat → List Nat} {d : Nat → Nat} {n : Nat}
    (hsorted : ∀ r, r < n → (sets r).Pairwise (· < ·))
    (hadj : ∀ r, r + 1 < n → firstDiff (sets r) (sets (r + 1)) = some (d r) ∧
      d r ∈ sets (r + 1)) :
    ∀ k i, i + k + 1 < n →
      firstDiff (sets i) (sets (i + k + 1)) = some (rmin d i k) ∧ rmin d i k ∈ sets (i + k + 1) := by
  intro k
  induction k with
  | zero => intro i hi; simpa [rmin] using hadj i (by omega)
  | succ k ih =>
    intro i hi
    obtain ⟨h1, h2⟩ := ih i (by omega)
    obtain ⟨h3, h4⟩ := hadj (i + k + 1) (by omega)
    have := firstDiff_chain3 (hsorted i (by omega)) (hsorted (i + k + 1) (by omega))
      (hsorted (i + k + 1 + 1) (by omega)) h1 h2 h3 h4
    simp only [rmin]
    have e : i + (k + 1) + 1 = i + k + 1 + 1 := by omega
    rw [e]
    exact this

/-! ## Range minima -/

theorem rmin_le (d : Nat → Nat) (i : Nat) :
    ∀ k r, i ≤ r → r ≤ i + k → rmin d i k ≤ d r := by
  intro k
  induction k with
  | zero => intro r h1 h2; have : r = i := by omega
            subst this; simp [rmin]
  | succ k ih =>
    intro r h1 h2
    simp only [rmin]
    by_cases hr : r ≤ i + k
    · exact Nat.le_trans (Nat.min_le_left _ _) (ih r h1 hr)
    · have : r = i + k + 1 := by omega
      subst this; exact Nat.min_le_right _ _

theorem rmin_attained (d : Nat → Nat) (i : Nat) :
    ∀ k, ∃ r, i ≤ r ∧ r ≤ i + k ∧ rmin d i k = d r := by
  intro k
  induction k with
  | zero => exact ⟨i, Nat.le_refl _, by omega, rfl⟩
  | succ k ih =>
    obtain ⟨r, h1, h2, h3⟩ := ih
    simp only [rmin]
    by_cases hle : rmin d i k ≤ d (i + k + 1)
    · exact ⟨r, h1, by omega, by rw [Nat.min_eq_left hle, h3]⟩
    · exact ⟨i + k + 1, by omega, by omega, Nat.min_eq_right (by omega)⟩

/-- Two overlapping windows cover their union. -/
theorem rmin_overlap (d : Nat → Nat) {i a j b : Nat} (hij : i ≤ j) (hj : j ≤ i + a + 1)
    (hend : i + a ≤ j + b) :
    min (rmin d i a) (rmin d j b) = rmin d i (j + b - i) := by
  obtain ⟨r1, h11, h12, h13⟩ := rmin_attained d i a
  obtain ⟨r2, h21, h22, h23⟩ := rmin_attained d j b
  obtain ⟨r, h1, h2, h3⟩ := rmin_attained d i (j + b - i)
  have e1 := rmin_le d i (j + b - i) r1 h11 (by omega)
  have e2 := rmin_le d i (j + b - i) r2 (by omega) (by omega)
  have e3 : min (rmin d i a) (rmin d j b) ≤ d r := by
    by_cases hr : r ≤ i + a
    · exact Nat.le_trans (Nat.min_le_left _ _) (rmin_le d i a r h1 hr)
    · exact Nat.le_trans (Nat.min_le_right _ _) (rmin_le d j b r (by omega) (by omega))
  rw [h13, h23] at *
  rw [h3] at e1 e2 ⊢
  omega

/-- One doubling step of a sparse table: the minima of windows of width `2w`
from those of width `w`. -/
def sparseNext (row : Array Nat) (w : Nat) : Array Nat :=
  (Array.range (row.size - w)).map fun r => min row[r]! row[r + w]!

/-- Sparse-table levels from `row` (windows of width `w`). -/
def sparseLevels : Nat → Array Nat → Nat → Array (Array Nat) → Array (Array Nat)
  | 0, _, _, acc => acc
  | fuel + 1, row, w, acc =>
    if row.size ≤ w then acc
    else
      let next := sparseNext row w
      sparseLevels fuel next (2 * w) (acc.push next)

/-- The sparse table of `adj`: level `l` holds the minimum of every window of
`2^l` consecutive entries. -/
def sparseBuild (adj : Array Nat) : Array (Array Nat) := sparseLevels adj.size adj 1 #[adj]

/-- The minimum of `adj[lo], …, adj[hi - 1]` (`lo < hi`), from the sparse table. -/
def sparseQuery (sp : Array (Array Nat)) (lo hi : Nat) : Nat :=
  let l := Nat.log2 (hi - lo)
  min sp[l]![lo]! sp[l]![hi - (1 <<< l)]!

/-- A row of window minima of width `2^l` over `adj`. -/
def RowOK (adj : Array Nat) (l : Nat) (row : Array Nat) : Prop :=
  row.size + 2 ^ l = adj.size + 1 ∧
    ∀ r, r + 2 ^ l ≤ adj.size → row[r]! = rmin (fun i => adj[i]!) r (2 ^ l - 1)

theorem sparseNext_ok {adj : Array Nat} {l : Nat} {row : Array Nat} (h : RowOK adj l row)
    (hs : 2 ^ l < row.size) : RowOK adj (l + 1) (sparseNext row (2 ^ l)) := by
  obtain ⟨hsz, hrow⟩ := h
  have hp : 0 < 2 ^ l := Nat.two_pow_pos l
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [sparseNext, Array.size_map, Array.size_range, Nat.pow_succ]
    omega
  · have hr' : r < row.size - 2 ^ l := by rw [Nat.pow_succ] at hr; omega
    simp only [sparseNext]
    rw [getElem!_pos _ r (by simpa using hr')]
    simp only [Array.getElem_map, Array.getElem_range]
    rw [hrow r (by rw [Nat.pow_succ] at hr; omega), hrow (r + 2 ^ l) (by rw [Nat.pow_succ] at hr; omega),
      rmin_overlap _ (by omega) (by omega) (by omega)]
    congr 1
    rw [Nat.pow_succ]
    omega

theorem sparseLevels_ok (adj : Array Nat) :
    ∀ (fuel : Nat) (row : Array Nat) (l : Nat) (acc : Array (Array Nat)),
      RowOK adj l row → acc.size = l + 1 → (∀ i, i ≤ l → RowOK adj i acc[i]!) →
      adj.size < 2 ^ l + fuel →
      let sp := sparseLevels fuel row (2 ^ l) acc
      (∀ i, i < sp.size → RowOK adj i sp[i]!) ∧ (adj.size ≠ 0 → Nat.log2 adj.size < sp.size) := by
  intro fuel
  induction fuel with
  | zero =>
    intro row l acc hrow hacc hall hfuel
    simp only [sparseLevels]
    refine ⟨fun i hi => hall i (by omega), fun hn => ?_⟩
    rw [hacc, Nat.lt_succ_iff]
    exact (Nat.log2_lt hn).mpr (by omega) |> Nat.le_of_lt_succ
  | succ fuel ih =>
    intro row l acc hrow hacc hall hfuel
    simp only [sparseLevels]
    split
    · rename_i hle
      refine ⟨fun i hi => hall i (by omega), fun hn => ?_⟩
      rw [hacc, Nat.lt_succ_iff]
      have : adj.size < 2 ^ (l + 1) := by
        have := hrow.1; rw [Nat.pow_succ]; omega
      exact Nat.le_of_lt_succ ((Nat.log2_lt hn).mpr this)
    · rename_i hgt
      have hnext := sparseNext_ok hrow (by omega)
      have e : 2 * 2 ^ l = 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
      rw [e]
      apply ih _ (l + 1) _ hnext (by simp [hacc])
      · intro i hi
        rw [getElem!_def, Array.getElem?_push]
        by_cases hil : i ≤ l
        · have hne : i ≠ acc.size := by omega
          simp only [hne, ite_false]
          rw [← getElem!_def]
          exact hall i hil
        · have : i = acc.size := by omega
          simp only [this, ite_true]
          rw [show acc.size = l + 1 by omega]
          exact hnext
      · have hp := Nat.two_pow_pos l
        rw [Nat.pow_succ]; omega

theorem sparseBuild_ok (adj : Array Nat) :
    (∀ i, i < (sparseBuild adj).size → RowOK adj i (sparseBuild adj)[i]!) ∧
      (adj.size ≠ 0 → Nat.log2 adj.size < (sparseBuild adj).size) := by
  have h0 : RowOK adj 0 adj := ⟨by simp, fun r hr => by simp [rmin]⟩
  have := sparseLevels_ok adj adj.size adj 0 #[adj] h0 (by simp)
    (fun i hi => by have : i = 0 := by omega
                    subst this; simpa using h0)
    (by have := Nat.lt_two_pow_self (n := adj.size); omega)
  simpa [sparseBuild] using this

/-- The sparse-table query is the range minimum. -/
theorem sparseQuery_eq (adj : Array Nat) {lo hi : Nat} (hlo : lo < hi) (hhi : hi ≤ adj.size) :
    sparseQuery (sparseBuild adj) lo hi = rmin (fun i => adj[i]!) lo (hi - lo - 1) := by
  obtain ⟨hrows, hlog⟩ := sparseBuild_ok adj
  have hlen : hi - lo ≠ 0 := by omega
  have hl1 := Nat.log2_self_le hlen
  have hl2 := Nat.lt_log2_self (n := hi - lo)
  have hlvl : Nat.log2 (hi - lo) < (sparseBuild adj).size := by
    have hmono : Nat.log2 (hi - lo) ≤ Nat.log2 adj.size :=
      (Nat.le_log2 (by omega)).mpr (Nat.le_trans hl1 (by omega))
    exact Nat.lt_of_le_of_lt hmono (hlog (by omega))
  have hrow := hrows _ hlvl
  unfold sparseQuery
  simp only [Nat.one_shiftLeft]
  rw [hrow.2 lo (by omega), hrow.2 (hi - 2 ^ Nat.log2 (hi - lo)) (by omega),
    rmin_overlap _ (by omega) (by rw [Nat.pow_succ] at hl2; omega) (by omega)]
  congr 1
  omega

end Ix.Sharing.Exact

end
