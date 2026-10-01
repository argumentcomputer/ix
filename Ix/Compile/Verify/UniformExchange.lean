import Ix.Compile.Verify.UniformWritings

/-!
# The monotone exchange

Adding a term `t ∉ S` to the stored set: every writing of the `S`-optimal
encoding is rewritten with `t`'s occurrences replaced by `Share(t)` (head
occurrences: a whole writing of `t`; continuation occurrences: the rest of
a telescope from `t` on), and `t` gets its `S`-optimal inline writing as
its entry. Descendants of `t` are untouched, each ancestor body gets a
`w`-byte leaf where `t`'s part was, and telescopes only shorten.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact

/-! ## Merged part of a telescope -/

/-- The bytes of a telescope from `t` on, without its header: the side
bytes of the first `j` spine nodes and the tail (`w` for a cut). -/
def mergedCuts (p : Prep) (w : Nat) (S : Nat → Bool) (cost : Nat → Nat) (t : Nat) : List Nat :=
  (List.range' 1 (p.spineLen[t]! - 1)).filterMap fun j =>
    if S (spineAt p t j) then some (prefixSides p cost t j + w) else none

/-- `M_S(t)`: the cheapest headerless continuation of a telescope through
`t`. -/
def mergedOf (p : Prep) (w : Nat) (S : Nat → Bool) (cost : Nat → Nat) (t : Nat) : Nat :=
  (mergedCuts p w S cost t).foldl min
    (prefixSides p cost t p.spineLen[t]! + cost p.tail[t]!)

theorem mem_mergedCuts {p : Prep} {w : Nat} {S : Nat → Bool} {f : Nat → Nat} {x c : Nat}
    (h : c ∈ mergedCuts p w S f x) :
    ∃ j, 1 ≤ j ∧ j < p.spineLen[x]! ∧ S (spineAt p x j) = true ∧ c = prefixSides p f x j + w := by
  unfold mergedCuts at h
  obtain ⟨j, hj, hjv⟩ := List.mem_filterMap.mp h
  rw [List.mem_range'_1] at hj
  split at hjv
  · rename_i hS
    simp only [Option.some.injEq] at hjv
    exact ⟨j, hj.1, by omega, hS, hjv.symm⟩
  · cases hjv

theorem merged_mem_mergedCuts (p : Prep) (w : Nat) (S : Nat → Bool) (f : Nat → Nat) {x j : Nat}
    (hj1 : 1 ≤ j) (hj : j < p.spineLen[x]!) (hS : S (spineAt p x j) = true) :
    prefixSides p f x j + w ∈ mergedCuts p w S f x := by
  unfold mergedCuts
  apply List.mem_filterMap.mpr
  refine ⟨j, List.mem_range'_1.mpr ⟨hj1, by omega⟩, ?_⟩
  rw [if_pos hS]

theorem tag4Size_pos (n : Nat) : 1 ≤ tag4Size n := by
  unfold tag4Size; split <;> omega

theorem natByteCount_mono : ∀ {a b : Nat}, a ≤ b → natByteCount a ≤ natByteCount b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
    intro h
    by_cases ha : a = 0
    · subst ha; rw [Ix.Compile.Verify.SharingExact.natByteCount_zero]; omega
    · have hb : b ≠ 0 := by omega
      rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero ha,
        Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero hb]
      have := ih (b / 256) (Nat.div_lt_self (by omega) (by decide))
        (Nat.div_le_div_right (c := 256) h)
      omega

theorem natByteCount_succ_le : ∀ (n : Nat), natByteCount (n + 1) ≤ natByteCount n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero (by decide),
        Ix.Compile.Verify.SharingExact.natByteCount_zero]
      simp
    · rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero (by omega),
        Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero hn]
      have h1 : (n + 1) / 256 ≤ n / 256 + 1 := by omega
      have h2 := natByteCount_mono h1
      have h3 := ih (n / 256) (Nat.div_lt_self (by omega) (by decide))
      omega

theorem tag4Size_mono {a b : Nat} (h : a ≤ b) : tag4Size a ≤ tag4Size b := by
  have := natByteCount_mono h
  unfold tag4Size
  split <;> split <;> omega

theorem tag0Size_succ_le (n : Nat) : tag0Size (n + 1) ≤ tag0Size n + 1 := by
  have := natByteCount_succ_le n
  unfold tag0Size
  split <;> split
  · omega
  · omega
  · rename_i h1 h2
    have : n = 127 := by omega
    subst this
    have h128 : natByteCount 128 = 1 := by
      rw [Ix.Compile.Verify.SharingExact.natByteCount_of_ne_zero (by decide)]
      simp [Ix.Compile.Verify.SharingExact.natByteCount_zero]
    show 1 + natByteCount (127 + 1) ≤ 1 + 1
    rw [show 127 + 1 = 128 from rfl, h128]
    omega
  · omega

/-- An inline telescope writing costs its header plus its merged part:
`1 + M_S(t) ≤ inl_S(t) ≤ tag4Size (spineLen t) + M_S(t)`. -/
theorem inl_merged_bounds (p : Prep) (w : Nat) (S : Nat → Bool) (f : Nat → Nat) {t : Nat}
    (hf : p.family[t]! ≠ .none) :
    1 + mergedOf p w S f t ≤ inlOf p w S f t ∧
      inlOf p w S f t ≤ tag4Size p.spineLen[t]! + mergedOf p w S f t := by
  rw [inl_tele w S f hf]
  constructor
  · rcases List.mem_cons.mp (foldl_min_mem (cutCosts p w S f t) (naturalCost p f t)) with h | h
    · rw [h]
      have := foldl_min_le (mergedCuts p w S f t)
        (prefixSides p f t p.spineLen[t]! + f p.tail[t]!) _ List.mem_cons_self
      have := tag4Size_pos p.spineLen[t]!
      unfold mergedOf naturalCost at *
      omega
    · obtain ⟨j, hj1, hj, hS, hc⟩ := mem_cutCosts h
      rw [hc]
      have := foldl_min_le (mergedCuts p w S f t)
        (prefixSides p f t p.spineLen[t]! + f p.tail[t]!) _
        (List.mem_cons_of_mem _ (merged_mem_mergedCuts p w S f hj1 hj hS))
      have := tag4Size_pos j
      unfold mergedOf cutCost at *
      omega
  · rcases List.mem_cons.mp (foldl_min_mem (mergedCuts p w S f t)
        (prefixSides p f t p.spineLen[t]! + f p.tail[t]!)) with h | h
    · have := foldl_min_le (cutCosts p w S f t) (naturalCost p f t) _ List.mem_cons_self
      unfold mergedOf naturalCost at *
      omega
    · obtain ⟨j, hj1, hj, hS, hc⟩ := mem_mergedCuts h
      have := foldl_min_le (cutCosts p w S f t) (naturalCost p f t) _
        (List.mem_cons_of_mem _ (cut_mem_cutCosts p w S f hj1 hj hS))
      have := tag4Size_mono (show j ≤ p.spineLen[t]! by omega)
      unfold mergedOf cutCost at *
      omega

/-! ## Monotone validity -/

theorem Valid.mono {p : Prep} {S S' : Nat → Bool} (hSS : ∀ y, S y = true → S' y = true) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → Valid p S' x T := by
  intro x T h
  induction h with
  | share hS => exact .share (hSS _ hS)
  | node hf hlen _ ih => exact .node hf hlen ih
  | teleCut hf hj1 hj hlen _ hS ih => exact .teleCut hf hj1 hj hlen ih (hSS _ hS)
  | teleFull hf hlen _ _ ih iht => exact .teleFull hf hlen ih iht

/-! ## Replacing the occurrences of `t` -/

/-- The position of `t` among the spine nodes `1 … j-1` of `x`, if any. -/
def spineHit (p : Prep) (x j t : Nat) : Option Nat :=
  (List.range' 1 (j - 1)).find? fun k => spineAt p x k == t

mutual
/-- Replace the occurrences of `t`: a whole writing of `t` (if `rh`) and the
rest of a telescope from `t` on (if `rc`) become `Share(t)`. -/
def WTree.subst (p : Prep) (t : Nat) (rh rc : Bool) : WTree → WTree
  | .share x => .share x
  | .node x kids =>
    if x = t then (if rh then .share t else .node x kids)
    else .node x (WTree.substs p t rh rc kids)
  | .tele x j sides tail =>
    if x = t then (if rh then .share t else .tele x j sides tail)
    else match spineHit p x j t with
      | some k =>
        if rc then .tele x k ((WTree.substs p t rh rc sides).take k) (.share t)
        else .tele x j (WTree.substs p t rh rc sides) (WTree.subst p t rh rc tail)
      | none => .tele x j (WTree.substs p t rh rc sides) (WTree.subst p t rh rc tail)
def WTree.substs (p : Prep) (t : Nat) (rh rc : Bool) : List WTree → List WTree
  | [] => []
  | k :: ks => WTree.subst p t rh rc k :: WTree.substs p t rh rc ks
end

mutual
/-- Head occurrences of `t`: writings of `t` (a writing of `t` is one). -/
def WTree.occH (t : Nat) : WTree → Nat
  | .share _ => 0
  | .node x kids => if x = t then 1 else WTree.occHs t kids
  | .tele x _ sides tail => if x = t then 1 else WTree.occHs t sides + WTree.occH t tail
def WTree.occHs (t : Nat) : List WTree → Nat
  | [] => 0
  | k :: ks => WTree.occH t k + WTree.occHs t ks
end

mutual
/-- Continuation occurrences of `t`: telescopes running through `t`. -/
def WTree.occC (p : Prep) (t : Nat) : WTree → Nat
  | .share _ => 0
  | .node x kids => if x = t then 0 else WTree.occCs p t kids
  | .tele x j sides tail =>
    if x = t then 0
    else (if (spineHit p x j t).isSome then 1 else 0) + WTree.occCs p t sides + WTree.occC p t tail
def WTree.occCs (p : Prep) (t : Nat) : List WTree → Nat
  | [] => 0
  | k :: ks => WTree.occC p t k + WTree.occCs p t ks
end

theorem substs_eq (p : Prep) (t : Nat) (rh rc : Bool) (l : List WTree) :
    WTree.substs p t rh rc l = l.map (WTree.subst p t rh rc) := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.substs, ih]

theorem occHs_eq (t : Nat) (l : List WTree) : WTree.occHs t l = (l.map (WTree.occH t)).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.occHs, ih]

theorem occCs_eq (p : Prep) (t : Nat) (l : List WTree) :
    WTree.occCs p t l = (l.map (WTree.occC p t)).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.occCs, ih]

theorem spineHit_spec {p : Prep} {x j t k : Nat} (h : spineHit p x j t = some k) :
    1 ≤ k ∧ k < j ∧ spineAt p x k = t := by
  unfold spineHit at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  rw [List.mem_range'_1] at hm
  simp only [beq_iff_eq] at hp
  exact ⟨hm.1, by omega, hp⟩

theorem spineHit_none {p : Prep} {x j t : Nat} (h : ∀ k, 1 ≤ k → k < j → spineAt p x k ≠ t) :
    spineHit p x j t = none := by
  unfold spineHit
  rw [List.find?_eq_none]
  intro k hk
  rw [List.mem_range'_1] at hk
  simpa using h k hk.1 (by omega)

theorem sum_map_eq_zero {α : Type} {f : α → Nat} {l : List α} (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, h x List.mem_cons_self,
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem map_eq_self {α : Type} {f : α → α} {l : List α} (h : ∀ a ∈ l, f a = a) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, h x List.mem_cons_self,
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem forall_mem_of_getElem {α : Type} {P : α → Prop} {l : List α}
    (h : ∀ (i : Nat) (hi : i < l.length), P l[i]) : ∀ a ∈ l, P a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  exact h i hi

theorem PrepWF.spineAt_le {p : Prep} (hp : PrepWF p) {x k : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hk : k < p.spineLen[x]!) : spineAt p x k ≤ x :=
  ((hp.spine x hx hf).2.1 k hk).1

/-- Writings of terms below `t` contain no occurrence of `t`. -/
theorem PrepWF.below_t {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {t : Nat} (rh rc : Bool) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < t → x < p.dag.size →
      T.occH t = 0 ∧ T.occC p t = 0 ∧ T.subst p t rh rc = T := by
  intro x T h
  induction h with
  | share _ => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | @node x kids hf hlen _ ih =>
    intro hxt hx
    have hne : x ≠ t := by omega
    have hk := forall_mem_of_getElem (l := kids) (P := fun (a : WTree) => a.occH t = 0 ∧ a.occC p t = 0 ∧
        a.subst p t rh rc = a) fun i hi => by
      have hc := hp.dag.childAt_lt hx (k := i) (by omega)
      exact ih i hi (by omega) (by omega)
    simp only [WTree.occH, WTree.occC, WTree.subst, hne, if_false, occHs_eq, occCs_eq,
      substs_eq]
    exact ⟨sum_map_eq_zero fun a ha => (hk a ha).1, sum_map_eq_zero fun a ha => (hk a ha).2.1,
      by rw [map_eq_self fun a ha => (hk a ha).2.2]⟩
  | @teleCut x j sides hf hj1 hj hlen _ hS ih =>
    intro hxt hx
    have hne : x ≠ t := by omega
    have hk := forall_mem_of_getElem (l := sides) (P := fun (a : WTree) => a.occH t = 0 ∧ a.occC p t = 0 ∧
        a.subst p t rh rc = a) fun i hi => by
      have hc := hp.sideAt_lt hx hf (k := i) (by omega)
      exact ih i hi (by omega) (by omega)
    have hhit : spineHit p x j t = none := spineHit_none fun k h1 h2 => by
      have := hp.spineAt_le hx hf (k := k) (by omega); omega
    simp only [WTree.occH, WTree.occC, WTree.subst, hne, if_false, occHs_eq, occCs_eq,
      substs_eq, hhit, Option.isSome_none, Bool.false_eq_true]
    exact ⟨by rw [sum_map_eq_zero fun a ha => (hk a ha).1],
      by rw [sum_map_eq_zero fun a ha => (hk a ha).2.1],
      by rw [map_eq_self fun a ha => (hk a ha).2.2]⟩
  | @teleFull x sides tail hf hlen _ _ ih iht =>
    intro hxt hx
    have hne : x ≠ t := by omega
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    have hk := forall_mem_of_getElem (l := sides) (P := fun (a : WTree) => a.occH t = 0 ∧ a.occC p t = 0 ∧
        a.subst p t rh rc = a) fun i hi => by
      have hc := hp.sideAt_lt hx hf (k := i) (by omega)
      exact ih i hi (by omega) (by omega)
    have hhit : spineHit p x p.spineLen[x]! t = none := spineHit_none fun k h1 h2 => by
      have := hp.spineAt_le hx hf (k := k) (by omega); omega
    obtain ⟨ht1, ht2, ht3⟩ := iht (by omega) (by omega)
    simp only [WTree.occH, WTree.occC, WTree.subst, hne, if_false, occHs_eq, occCs_eq,
      substs_eq, hhit, Option.isSome_none, Bool.false_eq_true]
    exact ⟨by rw [sum_map_eq_zero fun a ha => (hk a ha).1, ht1],
      by rw [sum_map_eq_zero fun a ha => (hk a ha).2.1, ht2],
      by rw [map_eq_self fun a ha => (hk a ha).2.2, ht3]⟩

/-! ## The continuation bound -/

/-- Facts about the spine from its `k`-th node on. -/
theorem PrepWF.spine_shift {p : Prep} (hp : PrepWF p) {x k : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hk : k < p.spineLen[x]!) :
    spineAt p x k < p.dag.size ∧ p.family[spineAt p x k]! = p.family[x]! ∧
      p.spineLen[spineAt p x k]! = p.spineLen[x]! - k ∧
      p.tail[spineAt p x k]! = p.tail[x]! ∧
      (∀ i, spineAt p (spineAt p x k) i = spineAt p x (k + i)) ∧
      (∀ i, sideAt p (spineAt p x k) i = sideAt p x (k + i)) ∧
      (p.dag.node (spineAt p x k)).sideExtra = (p.dag.node x).sideExtra := by
  obtain ⟨_, hsp, _, _, _⟩ := hp.spine x hx hf
  obtain ⟨hle, hfam, hlen, htl⟩ := hsp k hk
  refine ⟨by omega, hfam, hlen, htl, fun i => (spineAt_add p k i x).symm, fun i => ?_,
    hp.sideExtra_spine hx hf hk⟩
  unfold sideAt
  rw [spineAt_add]

theorem costs_drop_getElem (p : Prep) (w : Nat) (l : List WTree) (k : Nat) :
    ((l.drop k).map (WTree.cost p w)).sum =
      ((List.range (l.length - k)).map fun i => (l[k + i]?.getD default).cost p w).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_drop, List.getElem_range]
  rw [List.getElem?_eq_getElem (by simp at h1; omega)]
  rfl

/-- The part of a telescope writing from its `k`-th spine node on is at
least `M_S` of that node. -/
theorem PrepWF.merged_le_rest {p : Prep} (hp : PrepWF p) (w : Nat) (S : Nat → Bool)
    {x j : Nat} {sides : List WTree} {tail : WTree} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hlen : sides.length = j)
    (hsides : ∀ (k : Nat) (h : k < sides.length), Valid p S (sideAt p x k) sides[k])
    (htail : (j < p.spineLen[x]! ∧ S (spineAt p x j) = true ∧ tail = .share (spineAt p x j)) ∨
      (j = p.spineLen[x]! ∧ Valid p S p.tail[x]! tail))
    {k : Nat} (hkj : k < j) (hjl : j ≤ p.spineLen[x]!) :
    mergedOf p w S (uCost p w S) (spineAt p x k) ≤
      (j - k) * (p.dag.node x).sideExtra + ((sides.drop k).map (WTree.cost p w)).sum +
        tail.cost p w := by
  obtain ⟨hts, htf, htlen, httail, hspat, hsideat, hext⟩ := hp.spine_shift hx hf (k := k) (by omega)
  have htf' : p.family[spineAt p x k]! ≠ .none := by rw [htf]; exact hf
  have hpre : prefixSides p (uCost p w S) (spineAt p x k) (j - k) ≤
      (j - k) * (p.dag.node x).sideExtra + ((sides.drop k).map (WTree.cost p w)).sum := by
    rw [hp.prefixSides_eq _ hts htf' (by omega), hext, costs_drop_getElem, hlen]
    have : ∀ i ∈ List.range (j - k), uCost p w S (sideAt p (spineAt p x k) i) ≤
        (sides[k + i]?.getD default).cost p w := by
      intro i hi
      rw [List.mem_range] at hi
      rw [hsideat, List.getElem?_eq_getElem (by omega)]
      exact (hp.valid_cost w S (hsides (k + i) (by omega))
        (by have := hp.sideAt_lt hx hf (k := k + i) (by omega); omega)).1
    have := sum_le_sum_of_le _ this
    omega
  unfold mergedOf
  rcases htail with ⟨hjl', hS, rfl⟩ | ⟨hjeq, hvt⟩
  · have hmem := merged_mem_mergedCuts p w S (uCost p w S) (x := spineAt p x k) (j := j - k)
      (by omega) (by omega) (by rw [hspat, show k + (j - k) = j by omega]; exact hS)
    have := foldl_min_le _ (prefixSides p (uCost p w S) (spineAt p x k)
      p.spineLen[spineAt p x k]! + uCost p w S p.tail[spineAt p x k]!) _
      (List.mem_cons_of_mem _ hmem)
    simp only [WTree.cost]
    omega
  · have := foldl_min_le (mergedCuts p w S (uCost p w S) (spineAt p x k))
      (prefixSides p (uCost p w S) (spineAt p x k) p.spineLen[spineAt p x k]! +
        uCost p w S p.tail[spineAt p x k]!) _ List.mem_cons_self
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    have htc := (hp.valid_cost w S hvt (by omega)).1
    rw [htlen, httail, ← hjeq] at this ⊢
    omega

/-! ## The substitution lemma -/

theorem sum_ineq {α : Type} (f g h c : α → Nat) (A B : Nat) :
    ∀ (l : List α), (∀ a ∈ l, f a + g a * A + h a * B ≤ c a) →
      (l.map f).sum + (l.map g).sum * A + (l.map h).sum * B ≤ (l.map c).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hl
    have h1 := hl x List.mem_cons_self
    have h2 := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    omega

theorem sum_take_drop {α : Type} (f : α → Nat) (l : List α) (k : Nat) :
    (l.map f).sum = ((l.take k).map f).sum + ((l.drop k).map f).sum := by
  have := congrArg (fun l => (l.map f).sum) (List.take_append_drop k l)
  simp only [List.map_append, List.sum_append] at this
  exact this.symm

/-- The stored set with `t` added. -/
def addT (S : Nat → Bool) (t : Nat) : Nat → Bool := fun y => S y || y == t

theorem addT_le (S : Nat → Bool) (t : Nat) : ∀ y, S y = true → addT S t y = true := by
  intro y h; simp [addT, h]

theorem addT_self (S : Nat → Bool) (t : Nat) : addT S t t = true := by simp [addT]

/-- **Substitution.** Replacing the occurrences of `t ∉ S` in a writing gives
a writing for `S ∪ {t}`, shorter by `I_S(t) - w` per replaced head
occurrence and by `M_S(t) - w` per replaced continuation occurrence. -/
theorem PrepWF.subst_spec {p : Prep} (hp : PrepWF p) (w : Nat) {S : Nat → Bool} {t : Nat}
    (hSt : S t = false) (htn : t < p.dag.size) (rh rc : Bool)
    (hrh : rh = true → w ≤ uInl p w S t)
    (hrc : rc = true → w ≤ mergedOf p w S (uCost p w S) t) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      Valid p (addT S t) x (T.subst p t rh rc) ∧
        (T.subst p t rh rc).cost p w +
            T.occH t * (if rh then uInl p w S t - w else 0) +
            T.occC p t * (if rc then mergedOf p w S (uCost p w S) t - w else 0) ≤
          T.cost p w := by
  -- writings of `t` itself
  have hself : ∀ {T : WTree}, Valid p S t T → T.isShare = false →
      T.occC p t = 0 → T.occH t = 1 →
      Valid p (addT S t) t (if rh then .share t else T) ∧
        (if rh then .share t else T).cost p w + T.occH t * (if rh then uInl p w S t - w else 0) +
            T.occC p t * (if rc then mergedOf p w S (uCost p w S) t - w else 0) ≤ T.cost p w := by
    intro T hT hTs hC hH
    rw [hC, hH]
    have hI := (hp.valid_cost w S hT htn).2 hTs
    cases rh with
    | true =>
      refine ⟨.share (addT_self S t), ?_⟩
      have := hrh rfl
      simp only [if_true, WTree.cost]
      omega
    | false =>
      exact ⟨hT.mono (addT_le S t), by simp⟩
  intro x T h
  induction h with
  | @share x hS =>
    intro _
    exact ⟨.share (addT_le S t _ hS), by simp [WTree.subst, WTree.occH, WTree.occC]⟩
  | @node x kids hf hlen hkids ih =>
    intro hx
    by_cases hxt : x = t
    · subst hxt
      have := hself (Valid.node hf hlen hkids) rfl (by simp [WTree.occC]) (by simp [WTree.occH])
      simpa [WTree.subst] using this
    · have hk : ∀ (i : Nat) (hi : i < kids.length),
          Valid p (addT S t) ((p.dag.node x).child i) (kids[i].subst p t rh rc) ∧
            (kids[i].subst p t rh rc).cost p w +
              kids[i].occH t * (if rh then uInl p w S t - w else 0) +
              kids[i].occC p t * (if rc then mergedOf p w S (uCost p w S) t - w else 0) ≤
            kids[i].cost p w := fun i hi =>
        ih i hi (by have := hp.dag.childAt_lt hx (k := i) (by omega); omega)
      simp only [WTree.subst, hxt, if_false, WTree.occH, WTree.occC, WTree.cost, substs_eq,
        occHs_eq, occCs_eq, WTree.costs_eq]
      refine ⟨.node hf (by simp [hlen]) fun i hi => by
        simp only [List.getElem_map]
        exact (hk i (by simpa using hi)).1, ?_⟩
      have := sum_ineq (fun a => (a.subst p t rh rc).cost p w) (WTree.occH t) (WTree.occC p t)
        (WTree.cost p w) _ _ kids (forall_mem_of_getElem (l := kids)
          (P := fun a => (a.subst p t rh rc).cost p w + a.occH t * _ + a.occC p t * _ ≤ a.cost p w)
          fun i hi => (hk i hi).2)
      simp only [List.map_map, Function.comp_def]
      omega
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx
    by_cases hxt : x = t
    · subst hxt
      have := hself (Valid.teleCut hf hj1 hj hlen hsides hS) rfl (by simp [WTree.occC])
        (by simp [WTree.occH])
      simpa [WTree.subst] using this
    · have hk : ∀ (i : Nat) (hi : i < sides.length),
          Valid p (addT S t) (sideAt p x i) (sides[i].subst p t rh rc) ∧
            (sides[i].subst p t rh rc).cost p w +
              sides[i].occH t * (if rh then uInl p w S t - w else 0) +
              sides[i].occC p t * (if rc then mergedOf p w S (uCost p w S) t - w else 0) ≤
            sides[i].cost p w := fun i hi =>
        ih i hi (by have := hp.sideAt_lt hx hf (k := i) (by omega); omega)
      have hvalid : ∀ (i : Nat) (hi : i < (sides.map (WTree.subst p t rh rc)).length),
          Valid p (addT S t) (sideAt p x i) (sides.map (WTree.subst p t rh rc))[i] := by
        intro i hi
        simp only [List.getElem_map]
        exact (hk i (by simpa using hi)).1
      have hsum := sum_ineq (fun a => (a.subst p t rh rc).cost p w) (WTree.occH t)
        (WTree.occC p t) (WTree.cost p w) (if rh then uInl p w S t - w else 0)
        (if rc then mergedOf p w S (uCost p w S) t - w else 0) sides
        (forall_mem_of_getElem (l := sides)
          (P := fun a => (a.subst p t rh rc).cost p w + a.occH t * _ + a.occC p t * _ ≤
            a.cost p w) fun i hi => (hk i hi).2)
      cases hhit : spineHit p x j t with
      | none =>
        simp only [WTree.subst, hxt, if_false, hhit, WTree.occH, WTree.occC, WTree.cost,
          substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_none, Bool.false_eq_true,
          if_false, Nat.add_zero, Nat.zero_add]
        refine ⟨.teleCut hf hj1 hj (by simp [hlen]) hvalid (addT_le S t _ hS), ?_⟩
        simp only [List.map_map, Function.comp_def]
        omega
      | some k =>
        obtain ⟨hk1, hkj, hkt⟩ := spineHit_spec hhit
        cases rc with
        | false =>
          simp only [WTree.subst, hxt, if_false, hhit, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Bool.false_eq_true, Nat.add_zero,
            Nat.zero_add]
          refine ⟨.teleCut hf hj1 hj (by simp [hlen]) hvalid (addT_le S t _ hS), ?_⟩
          simp only [List.map_map, Function.comp_def] at hsum ⊢
          simp only [Bool.false_eq_true, if_false, Nat.mul_zero] at hsum ⊢
          omega
        | true =>
          simp only [WTree.subst, hxt, if_false, hhit, if_true, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_some, Nat.add_zero,
            Nat.zero_add]
          have hM := hp.merged_le_rest w S hx hf hlen hsides
            (Or.inl ⟨hj, hS, rfl⟩) (k := k) hkj (by omega)
          rw [hkt] at hM
          have hMw := hrc rfl
          -- the sides from `k` on contain no occurrence of `t`
          have hdrop : ∀ a ∈ sides.drop k, a.occH t = 0 ∧ a.occC p t = 0 := by
            intro a ha
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
            simp only [List.getElem_drop]
            obtain ⟨_, _, hlen', _, _, hsideat, _⟩ := hp.spine_shift hx hf (k := k) (by omega)
            have hsl := hp.sideAt_lt hx hf (k := k + i) (by simp at hi; omega)
            have hst : sideAt p x (k + i) < t := by
              rw [← hkt, ← hsideat]
              exact hp.sideAt_lt (by rw [hkt]; omega) (by
                  obtain ⟨_, hfam, _⟩ := hp.spine_shift hx hf (k := k) (by omega)
                  rw [hfam]; exact hf)
                (by rw [hlen']; simp at hi; omega)
            have := hp.below_t (S := S) (t := t) rh true
              (hsides (k + i) (by simp at hi; omega)) hst (by omega)
            exact ⟨this.1, this.2.1⟩
          have hH : (sides.map (WTree.occH t)).sum = ((sides.take k).map (WTree.occH t)).sum := by
            rw [sum_take_drop _ sides k, sum_map_eq_zero fun a ha => (hdrop a ha).1]
            simp
          have hC : (sides.map (WTree.occC p t)).sum =
              ((sides.take k).map (WTree.occC p t)).sum := by
            rw [sum_take_drop _ sides k, sum_map_eq_zero fun a ha => (hdrop a ha).2]
            simp
          have hcost : (sides.map (WTree.cost p w)).sum = ((sides.take k).map (WTree.cost p w)).sum +
              ((sides.drop k).map (WTree.cost p w)).sum := sum_take_drop _ sides k
          have hsumk := sum_ineq (fun a => (a.subst p t rh true).cost p w) (WTree.occH t)
            (WTree.occC p t) (WTree.cost p w) (if rh then uInl p w S t - w else 0)
            (mergedOf p w S (uCost p w S) t - w) (sides.take k) (fun a ha => by
              have := hsum
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
              simp only [List.getElem_take]
              have := (hk i (by simp at hi; omega)).2
              simpa using this)
          have htag := tag4Size_mono (show k ≤ j by omega)
          refine ⟨?_, ?_⟩
          · rw [show WTree.share t = WTree.share (spineAt p x k) by rw [hkt]]
            refine .teleCut hf hk1 (by omega) (by simp [hlen]; omega) (fun i hi => ?_)
              (by rw [hkt]; exact addT_self S t)
            simp only [List.getElem_take, List.getElem_map]
            exact (hk i (by simp at hi; omega)).1
          · rw [hH, hC, hcost, ← List.map_take]
            simp only [List.map_map, Function.comp_def, WTree.cost] at hsumk hM ⊢
            have hjk : k * (p.dag.node x).sideExtra + (j - k) * (p.dag.node x).sideExtra =
                j * (p.dag.node x).sideExtra := by
              rw [← Nat.add_mul]; congr 1; omega
            rw [Nat.add_mul, Nat.one_mul]
            omega
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    by_cases hxt : x = t
    · subst hxt
      have := hself (Valid.teleFull hf hlen hsides htail) rfl (by simp [WTree.occC])
        (by simp [WTree.occH])
      simpa [WTree.subst] using this
    · have hk : ∀ (i : Nat) (hi : i < sides.length),
          Valid p (addT S t) (sideAt p x i) (sides[i].subst p t rh rc) ∧
            (sides[i].subst p t rh rc).cost p w +
              sides[i].occH t * (if rh then uInl p w S t - w else 0) +
              sides[i].occC p t * (if rc then mergedOf p w S (uCost p w S) t - w else 0) ≤
            sides[i].cost p w := fun i hi =>
        ih i hi (by have := hp.sideAt_lt hx hf (k := i) (by omega); omega)
      have hvalid : ∀ (i : Nat) (hi : i < (sides.map (WTree.subst p t rh rc)).length),
          Valid p (addT S t) (sideAt p x i) (sides.map (WTree.subst p t rh rc))[i] := by
        intro i hi
        simp only [List.getElem_map]
        exact (hk i (by simpa using hi)).1
      have hsum := sum_ineq (fun a => (a.subst p t rh rc).cost p w) (WTree.occH t)
        (WTree.occC p t) (WTree.cost p w) (if rh then uInl p w S t - w else 0)
        (if rc then mergedOf p w S (uCost p w S) t - w else 0) sides
        (forall_mem_of_getElem (l := sides)
          (P := fun a => (a.subst p t rh rc).cost p w + a.occH t * _ + a.occC p t * _ ≤
            a.cost p w) fun i hi => (hk i hi).2)
      obtain ⟨htv, htc⟩ := iht (by omega)
      cases hhit : spineHit p x p.spineLen[x]! t with
      | none =>
        simp only [WTree.subst, hxt, if_false, hhit, WTree.occH, WTree.occC, WTree.cost,
          substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_none, Bool.false_eq_true,
          if_false, Nat.add_zero, Nat.zero_add]
        refine ⟨.teleFull hf (by simp [hlen]) hvalid htv, ?_⟩
        simp only [List.map_map, Function.comp_def, Nat.add_mul] at hsum htc ⊢
        omega
      | some k =>
        obtain ⟨hk1, hkj, hkt⟩ := spineHit_spec hhit
        cases rc with
        | false =>
          simp only [WTree.subst, hxt, if_false, hhit, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Bool.false_eq_true, Nat.add_zero,
            Nat.zero_add]
          refine ⟨.teleFull hf (by simp [hlen]) hvalid htv, ?_⟩
          simp only [List.map_map, Function.comp_def, Nat.add_mul] at hsum htc ⊢
          simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hsum htc ⊢
          omega
        | true =>
          simp only [WTree.subst, hxt, if_false, hhit, if_true, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_some, Nat.add_zero,
            Nat.zero_add]
          obtain ⟨hts, htf, hlen', httail, _, hsideat, _⟩ :=
            hp.spine_shift hx hf (k := k) (by omega)

          have hM := hp.merged_le_rest w S hx hf hlen hsides
            (Or.inr ⟨rfl, htail⟩) (k := k) hkj (Nat.le_refl _)
          rw [hkt] at hM
          have hMw := hrc rfl
          have htf' : p.family[t]! ≠ .none := by rw [← hkt, htf]; exact hf
          have httl : p.tail[x]! < t := by
            rw [← httail, hkt]
            exact (hp.spine t (by omega) htf').2.2.2.1
          obtain ⟨hto1, hto2, _⟩ := hp.below_t (S := S) (t := t) rh true htail httl (by omega)
          have hdrop : ∀ a ∈ sides.drop k, a.occH t = 0 ∧ a.occC p t = 0 := by
            intro a ha
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
            simp only [List.getElem_drop]
            have hst : sideAt p x (k + i) < t := by
              rw [← hkt, ← hsideat]
              exact hp.sideAt_lt (by rw [hkt]; omega) (by rw [hkt]; exact htf')
                (by rw [hlen']; simp at hi; omega)
            have := hp.below_t (S := S) (t := t) rh true
              (hsides (k + i) (by simp at hi; omega)) hst (by omega)
            exact ⟨this.1, this.2.1⟩
          have hH : (sides.map (WTree.occH t)).sum = ((sides.take k).map (WTree.occH t)).sum := by
            rw [sum_take_drop _ sides k, sum_map_eq_zero fun a ha => (hdrop a ha).1]
            simp
          have hC : (sides.map (WTree.occC p t)).sum =
              ((sides.take k).map (WTree.occC p t)).sum := by
            rw [sum_take_drop _ sides k, sum_map_eq_zero fun a ha => (hdrop a ha).2]
            simp
          have hcost : (sides.map (WTree.cost p w)).sum = ((sides.take k).map (WTree.cost p w)).sum +
              ((sides.drop k).map (WTree.cost p w)).sum := sum_take_drop _ sides k
          have hsumk := sum_ineq (fun a => (a.subst p t rh true).cost p w) (WTree.occH t)
            (WTree.occC p t) (WTree.cost p w) (if rh then uInl p w S t - w else 0)
            (mergedOf p w S (uCost p w S) t - w) (sides.take k) (fun a ha => by
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
              simp only [List.getElem_take]
              have := (hk i (by simp at hi; omega)).2
              simpa using this)
          have htag := tag4Size_mono (show k ≤ p.spineLen[x]! by omega)
          refine ⟨?_, ?_⟩
          · rw [show WTree.share t = WTree.share (spineAt p x k) by rw [hkt]]
            refine .teleCut hf hk1 (by omega) (by simp [hlen]; omega) (fun i hi => ?_)
              (by rw [hkt]; exact addT_self S t)
            simp only [List.getElem_take, List.getElem_map]
            exact (hk i (by simp at hi; omega)).1
          · rw [hH, hC, hcost, ← List.map_take, hto1, hto2]
            simp only [List.map_map, Function.comp_def, WTree.cost] at hsumk hM ⊢
            have hjk : k * (p.dag.node x).sideExtra +
                (p.spineLen[x]! - k) * (p.dag.node x).sideExtra =
                p.spineLen[x]! * (p.dag.node x).sideExtra := by
              rw [← Nat.add_mul]; congr 1; omega
            simp only [Nat.zero_mul, Nat.add_zero, Nat.add_mul, Nat.one_mul]
            omega

end Ix.Compile.Verify.UniformModel
