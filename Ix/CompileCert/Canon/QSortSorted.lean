module

public import Ix.CompileCert.Canon.QSort
public import Init.Data.Array.QSort.Basic
import all Init.Data.Array.QSort.Basic
import Batteries.Tactic.OpenPrivate

/-!
# `Array.qsort` sorts

`Ix.CompileCert.Canon.QSort` proves that `Array.qsort` permutes its input. This module proves that
it sorts, for a comparison that is irreflexive and transitive (a strict order): no element of the
output is `lt` an element before it (`qsort_pairwise`). Two sorted permutations of one list are
then equal when `lt` orders any two distinct elements (`List.Perm.eq_of_pairwise`).

The proof follows the private `sort` and `qpartition.loop`. A partition rearranges the segment
within itself (`Seg`) and returns the pivot's position (`Parted`): the elements before it are `lt`
the pivot, and the elements after it are not. The median of three leaves an element that is not
`lt` the pivot below the segment's end, so the pivot never lands at the end, and the two
recursive sorts sort the two sides.
-/

open private Array.qsort.sort from Init.Data.Array.QSort.Basic
open private Array.qpartition.loop from Init.Data.Array.QSort.Basic

@[expose] public section

namespace Ix.CompileCert.Canon

variable {α : Type u}

/-- `b` is `a` rearranged within `[lo, hi]`: equal outside, and every element inside is one of
`a`'s inside. -/
def Seg {n : Nat} (a b : Vector α n) (lo hi : Nat) : Prop :=
  (∀ x (hx : x < n), (x < lo ∨ hi < x) → b[x] = a[x]) ∧
    ∀ x (hx : x < n), lo ≤ x → x ≤ hi → ∃ y, ∃ hy : y < n, lo ≤ y ∧ y ≤ hi ∧ b[x] = a[y]

theorem Seg.refl {n : Nat} (a : Vector α n) (lo hi : Nat) : Seg a a lo hi :=
  ⟨fun _ _ _ => rfl, fun x hx h₁ h₂ => ⟨x, hx, h₁, h₂, rfl⟩⟩

theorem Seg.trans {n : Nat} {a b c : Vector α n} {lo hi : Nat} (h₁ : Seg a b lo hi) (h₂ : Seg b c lo hi) :
    Seg a c lo hi := by
  refine ⟨fun x hx hout => (h₂.1 x hx hout).trans (h₁.1 x hx hout), fun x hx l h => ?_⟩
  obtain ⟨y, hy, ly, yh, e⟩ := h₂.2 x hx l h
  obtain ⟨z, hz, lz, zh, e'⟩ := h₁.2 y hy ly yh
  exact ⟨z, hz, lz, zh, e.trans e'⟩

theorem Seg.widen {n : Nat} {a b : Vector α n} {lo hi lo' hi' : Nat} (h : Seg a b lo' hi')
    (l : lo ≤ lo') (r : hi' ≤ hi) : Seg a b lo hi := by
  refine ⟨fun x hx hout => h.1 x hx (by omega), fun x hx l₁ h₁ => ?_⟩
  by_cases hin : lo' ≤ x ∧ x ≤ hi'
  · obtain ⟨y, hy, ly, yh, e⟩ := h.2 x hx hin.1 hin.2
    exact ⟨y, hy, by omega, by omega, e⟩
  · exact ⟨x, hx, l₁, h₁, h.1 x hx (by omega)⟩

theorem Seg.swap {n : Nat} (a : Vector α n) {lo hi i j : Nat} (hi' : i < n) (hj : j < n)
    (li : lo ≤ i) (ih : i ≤ hi) (lj : lo ≤ j) (jh : j ≤ hi) : Seg a (a.swap i j hi' hj) lo hi := by
  refine ⟨fun x hx hout => Vector.getElem_swap_of_ne (by omega) (by omega), fun x hx l h => ?_⟩
  rw [Vector.getElem_swap]
  split
  · exact ⟨j, hj, lj, jh, rfl⟩
  · split
    · exact ⟨i, hi', li, ih, rfl⟩
    · exact ⟨x, hx, l, h, rfl⟩

/-- What a partition of `[lo, hi]` of `as` around `pivot` returns: a position below `hi`, the
segment rearranged, the pivot at the position, the elements before it `lt` the pivot and the
elements after it not. -/
def Parted {n : Nat} (lt : α → α → Bool) (lo hi : Nat) (pivot : α) (as : Vector α n)
    (r : {m // lo ≤ m ∧ m ≤ hi} × Vector α n) : Prop :=
  r.1.1 < hi ∧ Seg as r.2 lo hi ∧ (∀ hm : r.1.1 < n, r.2[r.1.1] = pivot) ∧
    (∀ x (hx : x < n), lo ≤ x → x < r.1.1 → lt r.2[x] pivot = true) ∧
    ∀ x (hx : x < n), r.1.1 < x → x ≤ hi → lt r.2[x] pivot = false

/-- **The partition loop**: from a state whose elements in `[lo, i)` are `lt` the pivot, whose
elements in `[i, k)` are not, with the pivot at `hi` and an element that is not `lt` it in
`[i, hi)`, the loop partitions the segment. -/
private theorem loop_parted (lt : α → α → Bool) {n : Nat} (lo hi : Nat) (hhi : hi < n) (pivot : α)
    (as : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi)
    (hpiv : as[hi] = pivot)
    (below : ∀ x (hx : x < n), lo ≤ x → x < i → lt as[x] pivot = true)
    (above : ∀ x (hx : x < n), i ≤ x → x < k → lt as[x] pivot = false)
    (wit : ∃ p, ∃ hp : p < n, i ≤ p ∧ p < hi ∧ lt as[p] pivot = false) :
    Parted lt lo hi pivot as (Array.qpartition.loop lt lo hi hhi pivot as i k ilo ik w) := by
  rw [Array.qpartition.loop]
  split
  · rename_i hk
    split
    · rename_i hlt
      have hpiv' : (as.swap i k (by omega) (by omega))[hi] = pivot := by
        rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
        exact hpiv
      have below' : ∀ x (hx : x < n), lo ≤ x → x < i + 1 →
          lt (as.swap i k (by omega) (by omega))[x] pivot = true := by
        intro x hx l h
        rw [Vector.getElem_swap]
        split
        · exact hlt
        · split
          · omega
          · exact below x hx l (by omega)
      have above' : ∀ x (hx : x < n), i + 1 ≤ x → x < k + 1 →
          lt (as.swap i k (by omega) (by omega))[x] pivot = false := by
        intro x hx l h
        rw [Vector.getElem_swap]
        split
        · omega
        · split
          · exact above i (by omega) (Nat.le_refl _) (by omega)
          · exact above x hx (by omega) (by omega)
      have wit' : ∃ p, ∃ hp : p < n, i + 1 ≤ p ∧ p < hi ∧
          lt (as.swap i k (by omega) (by omega))[p] pivot = false := by
        obtain ⟨p, hp, ip, ph, hpl⟩ := wit
        by_cases hpi : p = i
        · subst hpi
          have hki : k ≠ p := by
            intro e
            subst e
            rw [hpl] at hlt
            cases hlt
          refine ⟨k, by omega, by omega, hk, ?_⟩
          rw [Vector.getElem_swap_right]
          exact hpl
        · have hpk : p ≠ k := by
            intro e
            subst e
            rw [hpl] at hlt
            cases hlt
          refine ⟨p, hp, by omega, ph, ?_⟩
          rw [Vector.getElem_swap_of_ne hpi hpk]
          exact hpl
      have ih := loop_parted lt lo hi hhi pivot (as.swap i k (by omega) (by omega)) (i + 1) (k + 1)
        (by omega) (by omega) (by omega) hpiv' below' above' wit'
      exact ⟨ih.1, (Seg.swap as _ _ (by omega) (by omega) (by omega) (by omega)).trans ih.2.1, ih.2.2⟩
    · rename_i hlt
      have above' : ∀ x (hx : x < n), i ≤ x → x < k + 1 → lt as[x] pivot = false := by
        intro x hx l h
        by_cases e : x = k
        · subst e
          exact Bool.eq_false_iff.mpr hlt
        · exact above x hx l (by omega)
      exact loop_parted lt lo hi hhi pivot as i (k + 1) ilo (by omega) (by omega) hpiv below above' wit
  · rename_i hk
    obtain ⟨p, hp, ip, ph, -⟩ := wit
    refine ⟨by dsimp only; omega, Seg.swap as (by omega) hhi ilo (by omega) (by omega) (Nat.le_refl _), ?_, ?_, ?_⟩
    · intro _
      dsimp only
      rw [Vector.getElem_swap_left]
      exact hpiv
    · intro x hx l h
      dsimp only at h ⊢
      rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
      exact below x hx l h
    · intro x hx l h
      dsimp only at l ⊢
      rw [Vector.getElem_swap]
      split
      · omega
      · split
        · exact above i (by omega) (Nat.le_refl _) (by omega)
        · exact above x hx (by omega) (by omega)
termination_by hi - k

/-- Swapping two elements the first of which is `lt` the second leaves the first not `lt` the second. -/
private theorem swap_lt_false (lt : α → α → Bool) (asymm : ∀ a b, lt a b = true → lt b a = false) {n : Nat}
    (b : Vector α n) {i j : Nat} (hi : i < n) (hj : j < n) (h : lt b[i] b[j] = true) :
    lt (b.swap i j hi hj)[i] (b.swap i j hi hj)[j] = false := by
  rw [Vector.getElem_swap_left, Vector.getElem_swap_right]
  exact asymm _ _ h

/-- **The partition**, after the median of three. -/
private theorem qpartition_parted (lt : α → α → Bool)
    (asymm : ∀ a b, lt a b = true → lt b a = false) {n : Nat} (as : Vector α n) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (hlt : lo < hi) :
    ∃ pivot, Parted lt lo hi pivot as (Array.qpartition as lt lo hi w hlo hhi) := by
  have key : ∀ b : Vector α n, Seg as b lo hi → lt b[(lo + hi) / 2] b[hi] = false →
      ∃ pivot, Parted lt lo hi pivot as
        (Array.qpartition.loop lt lo hi hhi b[hi] b lo lo (Nat.le_refl _) (Nat.le_refl _) w) := by
    intro b hseg hmed
    have h := loop_parted lt lo hi hhi b[hi] b lo lo (Nat.le_refl _) (Nat.le_refl _) w rfl
      (fun _ _ _ h => absurd h (by omega)) (fun _ _ _ h => absurd h (by omega))
      ⟨(lo + hi) / 2, by omega, by omega, by omega, hmed⟩
    exact ⟨b[hi], h.1, hseg.trans h.2.1, h.2.2⟩
  unfold Array.qpartition
  simp only
  split <;> split <;> split
  all_goals
    refine key _ ?_ ?_
    · first
        | exact Seg.refl _ _ _
        | exact Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega)
        | exact (Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
            (Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega))
        | exact ((Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega)).trans
            (Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega))).trans
            (Seg.swap _ _ _ (by omega) (by omega) (by omega) (by omega))
    · first
        | exact swap_lt_false lt asymm _ _ _ (by assumption)
        | exact Bool.eq_false_iff.mpr (by assumption)

/-- **`sort` sorts its segment**: it rearranges `[lo, hi]` within itself, and no element of the
segment is `lt` one before it. -/
private theorem sort_sorted (lt : α → α → Bool) (irrefl : ∀ a, lt a a = false)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true) {n : Nat} (as : Vector α n)
    (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) :
    Seg as (Array.qsort.sort lt as lo hi w hlo hhi) lo hi ∧
      ∀ x y (hx : x < n) (hy : y < n), lo ≤ x → x < y → y ≤ hi →
        lt (Array.qsort.sort lt as lo hi w hlo hhi)[y] (Array.qsort.sort lt as lo hi w hlo hhi)[x] = false := by
  have asymm : ∀ a b, lt a b = true → lt b a = false := fun a b h => by
    cases e : lt b a
    · rfl
    · have h' := trans a b a h e
      rw [irrefl] at h'
      cases h'
  rw [Array.qsort.sort]
  split
  · rename_i h₁
    split
    rename_i mid hmid as' heq
    obtain ⟨pivot, hpart⟩ := qpartition_parted lt asymm as lo hi w hlo hhi h₁
    rw [heq] at hpart
    obtain ⟨hmh, hseg, hpiv, hbelow, habove⟩ := hpart
    dsimp only at hmh hpiv hbelow habove
    split
    · omega
    · obtain ⟨seg₁, sorted₁⟩ := sort_sorted lt irrefl trans as' lo mid (by omega) hlo (by omega)
      obtain ⟨seg₂, sorted₂⟩ := sort_sorted lt irrefl trans
        (Array.qsort.sort lt as' lo mid (by omega) hlo (by omega)) (mid + 1) hi (by omega) (by omega) hhi
      refine ⟨(hseg.trans (seg₁.widen (Nat.le_refl _) (by omega))).trans
        (seg₂.widen (by omega) (Nat.le_refl _)), fun x y hx hy l xy yh => ?_⟩
      by_cases hym : y ≤ mid
      · rw [seg₂.1 x hx (by omega), seg₂.1 y hy (by omega)]
        exact sorted₁ x y hx hy l xy hym
      · by_cases hxm : mid + 1 ≤ x
        · exact sorted₂ x y hx hy hxm xy yh
        · -- `x` on the pivot's side, `y` after it
          rw [seg₂.1 x hx (by omega)]
          obtain ⟨y', hy', ly', y'h, ey⟩ := seg₂.2 y hy (by omega) yh
          rw [ey, seg₁.1 y' hy' (by omega)]
          obtain ⟨x', hx', lx', x'h, ex⟩ := seg₁.2 x hx l (by omega)
          rw [ex]
          have hy'p := habove y' hy' (by omega) y'h
          cases e : lt as'[y'] as'[x']
          · rfl
          · by_cases hx'm : x' = mid
            · subst hx'm
              rw [hpiv hx'] at e
              rw [hy'p] at e
              cases e
            · have := trans _ _ _ e (hbelow x' hx' lx' (by omega))
              rw [hy'p] at this
              cases this
  · rename_i h₁
    exact ⟨Seg.refl _ _ _, fun x y hx hy l xy yh => absurd (by omega : lo < hi) h₁⟩
termination_by hi - lo

/-- **`Array.qsort` sorts**: for an irreflexive, transitive `lt`, no element of the output is `lt`
an element before it. -/
theorem qsort_pairwise (as : Array α) (lt : α → α → Bool) (irrefl : ∀ a, lt a a = false)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true) :
    (as.qsort lt).toList.Pairwise (fun a b => lt b a = false) := by
  unfold Array.qsort
  split
  · rename_i h
    rw [Array.size_eq_zero_iff.mp h]
    exact List.Pairwise.nil
  · rename_i h
    obtain ⟨-, sorted⟩ := sort_sorted lt irrefl trans as.toVector (min 0 (as.size - 1))
      (max (min 0 (as.size - 1)) (min (as.size - 1) (as.size - 1))) (by omega) (by omega) (by omega)
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Array.length_toList, Vector.size_toArray] at hi hj
    simp only [Array.getElem_toList, Vector.getElem_toArray]
    exact sorted i j hi hj (by omega) hij (by omega)

/-- **Two `qsort`s of permutations of each other are equal** when `lt` is a strict order that
orders any two distinct elements. -/
theorem qsort_eq_of_perm {as bs : Array α} (lt : α → α → Bool) (irrefl : ∀ a, lt a a = false)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (total : ∀ a ∈ as, ∀ b ∈ as, a ≠ b → lt a b = true ∨ lt b a = true) (h : as.Perm bs) :
    as.qsort lt = bs.qsort lt := by
  apply Array.toList_inj.mp
  refine List.Perm.eq_of_pairwise (fun a b ha hb hab hba => ?_) (qsort_pairwise as lt irrefl trans)
    (qsort_pairwise bs lt irrefl trans)
    (((qsort_perm as lt).trans (h.trans (qsort_perm bs lt).symm)).toList)
  have ha' : a ∈ as := (mem_qsort (lt := lt)).mp (Array.mem_toList_iff.mp ha)
  have hb' : b ∈ as := (h.mem_iff.mpr ((mem_qsort (lt := lt)).mp (Array.mem_toList_iff.mp hb)))
  by_cases e : a = b
  · exact e
  · rcases total a ha' b hb' e with t | t
    · rw [t] at hba
      cases hba
    · rw [t] at hab
      cases hab

end Ix.CompileCert.Canon

end
