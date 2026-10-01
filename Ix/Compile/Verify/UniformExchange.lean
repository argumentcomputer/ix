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

theorem tag4Size_pos (n : Nat) : 1 ≤ tag4Size n :=
  Ix.Compile.Verify.TagN.tagNByteWidth_pos 4 n

theorem tag4Size_mono {a b : Nat} (h : a ≤ b) : tag4Size a ≤ tag4Size b :=
  Ix.Compile.Verify.TagN.tagNByteWidth_mono 4 h

theorem tag0Size_mono {a b : Nat} (h : a ≤ b) : tag0Size a ≤ tag0Size b :=
  Ix.Compile.Verify.TagN.tagNByteWidth_mono 0 h

/-- One more table entry grows the TagN (`f = 0`) table count by at most
`tag0StepBound n` bytes, for every count below `n`. -/
theorem tag0Size_succ_le {k n : Nat} (h : k < n) :
    tag0Size (k + 1) ≤ tag0Size k + tag0StepBound n := by
  unfold tag0Size tag0StepBound Ixon.tagNByteWidth
  simp only [Ix.Compile.Verify.TagN.tagNEnd1_eq_0, Ix.Compile.Verify.TagN.tagNEnd2_eq_0,
    Ix.Compile.Verify.TagN.tagNEnd3_eq_0, Ix.Compile.Verify.TagN.tagNEnd4_eq_0,
    Ix.Compile.Verify.TagN.tagNEnd5_eq_0]
  repeat' split
  all_goals omega

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
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Bool.false_eq_true,
            Nat.add_zero]
          refine ⟨.teleCut hf hj1 hj (by simp [hlen]) hvalid (addT_le S t _ hS), ?_⟩
          simp only [List.map_map, Function.comp_def] at hsum ⊢
          simp only [Bool.false_eq_true, if_false, Nat.mul_zero] at hsum ⊢
          omega
        | true =>
          simp only [WTree.subst, hxt, if_false, hhit, if_true, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_some,
            Nat.add_zero]
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
          if_false, Nat.zero_add]
        refine ⟨.teleFull hf (by simp [hlen]) hvalid htv, ?_⟩
        simp only [List.map_map, Function.comp_def, Nat.add_mul] at hsum htc ⊢
        omega
      | some k =>
        obtain ⟨hk1, hkj, hkt⟩ := spineHit_spec hhit
        cases rc with
        | false =>
          simp only [WTree.subst, hxt, if_false, hhit, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Bool.false_eq_true]
          refine ⟨.teleFull hf (by simp [hlen]) hvalid htv, ?_⟩
          simp only [List.map_map, Function.comp_def, Nat.add_mul] at hsum htc ⊢
          simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at hsum htc ⊢
          omega
        | true =>
          simp only [WTree.subst, hxt, if_false, hhit, if_true, WTree.occH, WTree.occC, WTree.cost,
            substs_eq, occHs_eq, occCs_eq, WTree.costs_eq, Option.isSome_some]
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
            simp only [List.map_map, Function.comp_def] at hsumk hM ⊢
            have hjk : k * (p.dag.node x).sideExtra +
                (p.spineLen[x]! - k) * (p.dag.node x).sideExtra =
                p.spineLen[x]! * (p.dag.node x).sideExtra := by
              rw [← Nat.add_mul]; congr 1; omega
            simp only [Nat.add_zero, Nat.add_mul, Nat.one_mul]
            omega

/-! ## Edges into `t` -/

/-- The number of edges from `y` to `t` that are (`cont = true`) or are not
(`cont = false`) telescope continuations, as `graphFacts` counts them. -/
def edgeMult (p : Prep) (y t : Nat) (cont : Bool) : Nat :=
  ((List.range (p.dag.node y).head.arity).filter fun i =>
    (p.dag.node y).child i == t &&
      continuationEdge (p.dag.node y) i (p.dag.node t) == cont).length

theorem PrepWF.edgeMult_node {p : Prep} (hp : PrepWF p) {y : Nat} (hy : y < p.dag.size)
    (hf : p.family[y]! = .none) (t : Nat) :
    edgeMult p y t true = 0 ∧
      edgeMult p y t false = ((List.range (p.dag.node y).head.arity).filter fun i =>
        (p.dag.node y).child i == t).length := by
  have hfy : (p.dag.node y).head.family = .none := by rw [← hp.family y hy]; exact hf
  have hc : ∀ i, continuationEdge (p.dag.node y) i (p.dag.node t) = false := by
    intro i
    unfold continuationEdge
    cases hh : (p.dag.node y).head <;> simp_all [Head.family]
  unfold edgeMult
  simp only [hc]
  constructor
  · simp
  · congr 1
    apply List.filter_congr
    intro i _
    simp

theorem PrepWF.edgeMult_tele {p : Prep} (hp : PrepWF p) {y t : Nat} (hy : y < p.dag.size)
    (ht : t < p.dag.size) (hf : p.family[y]! ≠ .none) :
    edgeMult p y t true =
        (if snext p y = t ∧ p.family[t]! = p.family[y]! then 1 else 0) ∧
      edgeMult p y t false = (if (p.dag.node y).sideChild = t then 1 else 0) +
        (if snext p y = t ∧ p.family[t]! ≠ p.family[y]! then 1 else 0) := by
  have hfy : (p.dag.node y).head.family ≠ .none := by rw [← hp.family y hy]; exact hf
  rw [hp.family y hy, hp.family t ht]
  unfold edgeMult snext Node.spineNext Node.sideChild continuationEdge
  cases hh : (p.dag.node y).head <;> simp only [hh, Head.family, ne_eq, not_true_eq_false] at hfy
  all_goals cases ht' : (p.dag.node t).head <;>
    simp [Head.arity, Head.family, List.range_succ, List.filter_cons]
  all_goals (repeat' split) <;> simp_all

theorem edgeMult_zero_of_le {p : Prep} (hp : PrepWF p) {y t : Nat} (hyt : y ≤ t) (c : Bool) :
    edgeMult p y t c = 0 := by
  unfold edgeMult
  by_cases hy : y < p.dag.size
  · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro i hi
    rw [List.mem_range] at hi
    have := hp.dag.childAt_lt hy hi
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro h; omega
  · have : p.dag.node y = default := by
      simp [Dag.node, Dag.size] at hy ⊢; simp [hy]
    rw [this]
    rfl

/-- The spine nodes of a telescope strictly decrease. -/
theorem PrepWF.spineAt_strict {p : Prep} (hp : PrepWF p) {x : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) :
    ∀ {a b : Nat}, a < b → b ≤ p.spineLen[x]! → spineAt p x b < spineAt p x a := by
  intro a b hab hb
  obtain ⟨hts, htf, htlen, httail, hspat, _, _⟩ := hp.spine_shift hx hf (k := a) (by omega)
  have htf' : p.family[spineAt p x a]! ≠ .none := by rw [htf]; exact hf
  by_cases hbl : b = p.spineLen[x]!
  · subst hbl
    rw [(hp.spine x hx hf).2.2.1, ← httail]
    exact (hp.spine (spineAt p x a) hts htf').2.2.2.1
  · have := hp.spineAt_lt (t := spineAt p x a) (k := b - a) hts htf' (by omega)
      (by rw [htlen]; omega)
    rw [hspat, show a + (b - a) = b by omega] at this
    exact this

theorem snext_spineAt (p : Prep) (t k : Nat) : snext p (spineAt p t k) = spineAt p t (k + 1) := by
  rw [spineAt_add p k 1]
  rfl

theorem sum_range_succ' (f : Nat → Nat) (j : Nat) :
    ((List.range (j + 1)).map f).sum = ((List.range j).map f).sum + f j := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- A sum of indicators of a property holding at most once. -/
theorem sum_indicator_unique (P : Nat → Prop) [DecidablePred P] (j : Nat)
    (huniq : ∀ a b, a < j → b < j → P a → P b → a = b) :
    ((List.range j).map fun k => if P k then 1 else 0).sum =
      if ∃ k, k < j ∧ P k then 1 else 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ', ih (fun a b ha hb => huniq a b (by omega) (by omega))]
    by_cases hj : P j
    · have hnone : ¬ ∃ k, k < j ∧ P k := by
        rintro ⟨k, hk, hPk⟩
        have := huniq k j (by omega) (by omega) hPk hj
        omega
      rw [if_neg hnone, if_pos hj, if_pos ⟨j, by omega, hj⟩]
    · rw [if_neg hj, Nat.add_zero]
      by_cases hex : ∃ k, k < j ∧ P k
      · obtain ⟨k, hk, hPk⟩ := hex
        rw [if_pos ⟨k, hk, hPk⟩, if_pos ⟨k, by omega, hPk⟩]
      · rw [if_neg hex, if_neg]
        rintro ⟨k, hk, hPk⟩
        by_cases hkj : k = j
        · subst hkj; exact hj hPk
        · exact hex ⟨k, by omega, hPk⟩

theorem sum_zero_of_forall {f : Nat → Nat} {j : Nat} (h : ∀ k, k < j → f k = 0) :
    ((List.range j).map f).sum = 0 :=
  sum_map_eq_zero fun k hk => h k (List.mem_range.mp hk)

theorem spineHit_isSome_iff {p : Prep} {x j t : Nat} :
    (spineHit p x j t).isSome = true ↔ ∃ k, 1 ≤ k ∧ k < j ∧ spineAt p x k = t := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨h1, h2, h3⟩ := spineHit_spec hk
    exact ⟨k, h1, h2, h3⟩
  · rintro ⟨k, h1, h2, h3⟩
    cases hs : spineHit p x j t with
    | some _ => rfl
    | none =>
      unfold spineHit at hs
      rw [List.find?_eq_none] at hs
      have := hs k (List.mem_range'_1.mpr ⟨h1, by omega⟩)
      simp [h3] at this

/-- The non-continuation spine edges of a telescope prefix: only the last
node of a full telescope has one (into the natural tail). -/
theorem PrepWF.spine_head_edges {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!) :
    ((List.range j).map fun k =>
        if snext p (spineAt p x k) = t ∧ p.family[t]! ≠ p.family[spineAt p x k]! then 1 else 0).sum =
      if j = p.spineLen[x]! ∧ p.tail[x]! = t then 1 else 0 := by
  obtain ⟨hl1, hk, hend, _, htf⟩ := hp.spine x hx hf
  have hzero : ∀ k, k + 1 < p.spineLen[x]! →
      (if snext p (spineAt p x k) = t ∧ p.family[t]! ≠ p.family[spineAt p x k]! then 1 else 0) = 0 := by
    intro k hk1
    rw [if_neg]
    rintro ⟨hn, hne⟩
    rw [snext_spineAt] at hn
    apply hne
    rw [← hn, (hk (k + 1) hk1).2.1, (hk k (by omega)).2.1]
  by_cases hjl : j = p.spineLen[x]!
  · subst hjl
    obtain ⟨m, hm⟩ : ∃ m, p.spineLen[x]! = m + 1 := ⟨p.spineLen[x]! - 1, by omega⟩
    rw [hm, sum_range_succ', sum_zero_of_forall fun k hk => hzero k (by omega), Nat.zero_add,
      snext_spineAt, ← hm, hend]
    have hfm := (hk m (by omega)).2.1
    by_cases htt : p.tail[x]! = t
    · subst htt
      rw [if_pos ⟨rfl, by rw [hfm]; exact htf⟩, if_pos ⟨rfl, rfl⟩]
    · rw [if_neg (fun h => htt h.1), if_neg (fun h => htt h.2)]
  · rw [sum_zero_of_forall fun k hk => hzero k (by omega), if_neg (fun h => hjl h.1)]

/-- The continuation spine edges of a telescope prefix into `t`: one if `t`
is among its inner spine nodes. -/
theorem PrepWF.spine_cont_edges {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!)
    (hjt : j < p.spineLen[x]! → spineAt p x j ≠ t) :
    ((List.range j).map fun k =>
        if snext p (spineAt p x k) = t ∧ p.family[t]! = p.family[spineAt p x k]! then 1 else 0).sum =
      if (spineHit p x j t).isSome then 1 else 0 := by
  obtain ⟨hl1, hk, hend, _, htf⟩ := hp.spine x hx hf
  have heq : ∀ k ∈ List.range j,
      (if snext p (spineAt p x k) = t ∧ p.family[t]! = p.family[spineAt p x k]! then 1 else 0) =
        (if spineAt p x (k + 1) = t ∧ k + 1 < j then 1 else 0) := by
    intro k hk'
    rw [List.mem_range] at hk'
    rw [snext_spineAt]
    by_cases hkj : k + 1 < j
    · have hfam : p.family[spineAt p x (k + 1)]! = p.family[spineAt p x k]! := by
        rw [(hk (k + 1) (by omega)).2.1, (hk k (by omega)).2.1]
      by_cases ht : spineAt p x (k + 1) = t
      · rw [if_pos ⟨ht, by rw [← ht, hfam]⟩, if_pos ⟨ht, hkj⟩]
      · rw [if_neg (fun h => ht h.1), if_neg (fun h => ht h.1)]
    · rw [if_neg (show ¬(spineAt p x (k + 1) = t ∧ k + 1 < j) from fun h => hkj h.2)]
      rw [if_neg]
      rintro ⟨ht, hfam⟩
      have hkj' : k + 1 = j := by omega
      by_cases hjl : j < p.spineLen[x]!
      · exact hjt hjl (by rw [← hkj']; exact ht)
      · have : k + 1 = p.spineLen[x]! := by omega
        rw [this, hend] at ht
        apply htf
        rw [ht, hfam, (hk k (by omega)).2.1]
  rw [List.map_congr_left heq]
  rw [sum_indicator_unique (fun k => spineAt p x (k + 1) = t ∧ k + 1 < j) j (by
    intro a b ha hb ⟨hPa, _⟩ ⟨hPb, _⟩
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · have := hp.spineAt_strict hx hf (a := a + 1) (b := b + 1) (by omega) (by omega)
      omega
    · exact hab
    · have := hp.spineAt_strict hx hf (a := b + 1) (b := a + 1) (by omega) (by omega)
      omega)]
  congr 1
  apply propext
  rw [spineHit_isSome_iff]
  constructor
  · rintro ⟨k, _, ht, hkj⟩
    exact ⟨k + 1, by omega, hkj, ht⟩
  · rintro ⟨k, hk1, hkj, ht⟩
    exact ⟨k - 1, by omega, by rw [show k - 1 + 1 = k by omega]; exact ht, by omega⟩

/-! ## Occurrences are edges of written nodes -/

mutual
/-- The terms a writing writes inline (each spine node of a telescope). -/
def WTree.written (p : Prep) : WTree → List Nat
  | .share _ => []
  | .node x kids => x :: WTree.writtens p kids
  | .tele x j sides tail =>
    (List.range j).map (spineAt p x) ++ WTree.writtens p sides ++ WTree.written p tail
def WTree.writtens (p : Prep) : List WTree → List Nat
  | [] => []
  | k :: ks => WTree.written p k ++ WTree.writtens p ks
end

/-- Whether a writing writes `t` itself inline at its top. -/
def WTree.topIs (t : Nat) : WTree → Bool
  | .share _ => false
  | .node x _ => x == t
  | .tele x _ _ _ => x == t

theorem writtens_sum (p : Prep) (f : Nat → Nat) (l : List WTree) :
    ((WTree.writtens p l).map f).sum = (l.map fun T => ((T.written p).map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons k ks ih => simp [WTree.writtens, ih]

theorem sum_map_eq_range {α : Type} [Inhabited α] (f : α → Nat) (l : List α) :
    (l.map f).sum = ((List.range l.length).map fun i => f (l[i]?.getD default)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getElem?_eq_getElem (by simpa using h1)]
  rfl

theorem filter_length_eq_sum (P : Nat → Bool) (l : List Nat) :
    (l.filter P).length = (l.map fun i => if P i = true then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split <;> simp [ih] <;> omega

theorem sum_map_add' {α : Type} (f g : α → Nat) (l : List α) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem top_iff {p : Prep} {S : Nat → Bool} {t : Nat} (hSt : S t = false) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → (T.topIs t = true ↔ x = t) := by
  intro x T h
  cases h with
  | share hS =>
    simp only [WTree.topIs, Bool.false_eq_true, false_iff]
    intro hxt; subst hxt; rw [hS] at hSt; cases hSt
  | node => simp [WTree.topIs]
  | teleCut => simp [WTree.topIs]
  | teleFull => simp [WTree.topIs]

theorem writtens_mem {p : Prep} {y : Nat} {l : List WTree} (h : y ∈ WTree.writtens p l) :
    ∃ T ∈ l, y ∈ T.written p := by
  induction l with
  | nil => simp [WTree.writtens] at h
  | cons k ks ih =>
    simp only [WTree.writtens, List.mem_append] at h
    rcases h with h | h
    · exact ⟨k, List.mem_cons_self, h⟩
    · obtain ⟨T, hT, hy⟩ := ih h
      exact ⟨T, List.mem_cons_of_mem _ hT, hy⟩

/-- The edges into `t` from the first `j` spine nodes of `x`. -/
theorem PrepWF.spine_edges {p : Prep} (hp : PrepWF p) {x j t : Nat} (hx : x < p.dag.size)
    (ht : t < p.dag.size) (hf : p.family[x]! ≠ .none) (hj : j ≤ p.spineLen[x]!)
    (hjt : j < p.spineLen[x]! → spineAt p x j ≠ t) :
    (((List.range j).map (spineAt p x)).map fun y => edgeMult p y t false).sum =
        ((List.range j).map fun k => if sideAt p x k = t then 1 else 0).sum +
          (if j = p.spineLen[x]! ∧ p.tail[x]! = t then 1 else 0) ∧
      (((List.range j).map (spineAt p x)).map fun y => edgeMult p y t true).sum =
        if (spineHit p x j t).isSome then 1 else 0 := by
  have hk : ∀ k ∈ List.range j, spineAt p x k < p.dag.size ∧ p.family[spineAt p x k]! ≠ .none := by
    intro k hk
    rw [List.mem_range] at hk
    obtain ⟨hts, htf, _⟩ := hp.spine_shift hx hf (k := k) (by omega)
    exact ⟨hts, by rw [htf]; exact hf⟩
  simp only [List.map_map, Function.comp_def]
  constructor
  · rw [List.map_congr_left fun k hk1 => (hp.edgeMult_tele (hk k hk1).1 ht (hk k hk1).2).2]
    rw [sum_map_add', hp.spine_head_edges hx hf hj]
    rfl
  · rw [List.map_congr_left fun k hk1 => (hp.edgeMult_tele (hk k hk1).1 ht (hk k hk1).2).1]
    exact hp.spine_cont_edges hx hf hj hjt

/-- **Occurrences are edges.** In a writing for `S ∌ t`, the head occurrences
of `t` are the writing itself (if it writes `t`) plus one per non-continuation
edge from a written node into `t`, and the continuation occurrences are one
per continuation edge from a written node into `t`. -/
theorem PrepWF.occ_edges {p : Prep} (hp : PrepWF p) {S : Nat → Bool} {t : Nat}
    (hSt : S t = false) (htn : t < p.dag.size) :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      T.occH t = (if T.topIs t then 1 else 0) +
          ((T.written p).map fun y => edgeMult p y t false).sum ∧
        T.occC p t = ((T.written p).map fun y => edgeMult p y t true).sum ∧
        (∀ y ∈ T.written p, y ≤ x) := by
  have hzero : ∀ (c : Bool) (l : List Nat), (∀ y ∈ l, y ≤ t) →
      (l.map fun y => edgeMult p y t c).sum = 0 :=
    fun c l hl => sum_map_eq_zero fun y hy => edgeMult_zero_of_le hp (hl y hy) c
  intro x T h
  induction h with
  | share _ => intro _; simp [WTree.occH, WTree.occC, WTree.topIs, WTree.written]
  | @node x kids hf hlen hkids ih =>
    intro hx
    have hk : ∀ (i : Nat) (hi : i < kids.length),
        kids[i].occH t = (if (p.dag.node x).child i = t then 1 else 0) +
            ((kids[i].written p).map fun y => edgeMult p y t false).sum ∧
          kids[i].occC p t = ((kids[i].written p).map fun y => edgeMult p y t true).sum ∧
          (∀ y ∈ kids[i].written p, y ≤ (p.dag.node x).child i) := by
      intro i hi
      have hc := hp.dag.childAt_lt hx (k := i) (by omega)
      obtain ⟨h1, h2, h3⟩ := ih i hi (by omega)
      refine ⟨?_, h2, h3⟩
      rw [h1]
      congr 1
      by_cases hct : (p.dag.node x).child i = t
      · rw [if_pos ((top_iff hSt (hkids i hi)).mpr hct), if_pos hct]
      · rw [if_neg (fun h => hct ((top_iff hSt (hkids i hi)).mp (by simpa using h))),
          if_neg hct]
    have hwle : ∀ y ∈ (WTree.node x kids).written p, y ≤ x := by
      intro y hy
      simp only [WTree.written] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have := (hk i hi).2.2 y hyT
        have := hp.dag.childAt_lt hx (k := i) (by omega)
        omega
    refine ⟨?_, ?_, hwle⟩
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero false _ hwle]
        simp [WTree.occH, WTree.topIs]
      · simp only [WTree.occH, hxt, if_false, WTree.topIs, occHs_eq, WTree.written,
          List.map_cons, List.sum_cons, writtens_sum, beq_iff_eq]
        have hper : ∀ T ∈ kids, T.occH t = (if T.topIs t then 1 else 0) +
            ((T.written p).map fun y => edgeMult p y t false).sum := by
          intro T hT
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
          have := (ih i hi (by have := hp.dag.childAt_lt hx (k := i) (by omega); omega)).1
          exact this
        rw [List.map_congr_left hper, sum_map_add']
        have hind : (kids.map fun T => if T.topIs t then 1 else 0).sum =
            edgeMult p x t false := by
          rw [(hp.edgeMult_node hx hf t).2, filter_length_eq_sum, sum_map_eq_range, hlen]
          congr 1
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          by_cases hct : (p.dag.node x).child i = t
          · rw [if_pos ((top_iff hSt (hkids i (by omega))).mpr hct)]; simp [hct]
          · rw [if_neg (fun h => hct ((top_iff hSt (hkids i (by omega))).mp (by simpa using h)))]
            simp [hct]
        rw [hind]
        omega
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero true _ hwle]
        simp [WTree.occC]
      · simp only [WTree.occC, hxt, if_false, occCs_eq, WTree.written, List.map_cons,
          List.sum_cons, writtens_sum]
        rw [(hp.edgeMult_node hx hf t).1, Nat.zero_add]
        congr 1
        apply List.map_congr_left
        intro T hT
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        exact (hk i hi).2.1
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx
    have hside : ∀ T ∈ sides, T.occH t = (if T.topIs t then 1 else 0) +
          ((T.written p).map fun y => edgeMult p y t false).sum ∧
        T.occC p t = ((T.written p).map fun y => edgeMult p y t true).sum ∧
        (∀ y ∈ T.written p, y < x) := by
      intro T hT
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      obtain ⟨h1, h2, h3⟩ := ih i hi (by omega)
      exact ⟨h1, h2, fun y hy => by have := h3 y hy; omega⟩
    have hwle : ∀ y ∈ (WTree.tele x j sides (.share (spineAt p x j))).written p, y ≤ x := by
      intro y hy
      simp only [WTree.written, List.append_nil, List.mem_append] at hy
      rcases hy with hy | hy
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        exact hp.spineAt_le hx hf (by rw [List.mem_range] at hk; omega)
      · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
        exact Nat.le_of_lt ((hside T hT).2.2 y hyT)
    refine ⟨?_, ?_, hwle⟩
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero false _ hwle]
        simp [WTree.occH, WTree.topIs]
      · have hjt : spineAt p x j ≠ t := by intro h; rw [h] at hS; rw [hS] at hSt; cases hSt
        obtain ⟨hF, _⟩ := hp.spine_edges hx htn hf (Nat.le_of_lt hj) (fun _ => hjt)
        simp only [WTree.occH, hxt, if_false, WTree.topIs, occHs_eq, WTree.written,
          List.map_append, List.sum_append, writtens_sum, beq_iff_eq, List.append_nil]
        rw [hF, List.map_congr_left (fun T hT => (hside T hT).1), sum_map_add']
        have hind : (sides.map fun T => if T.topIs t then 1 else 0).sum =
            ((List.range j).map fun k => if sideAt p x k = t then 1 else 0).sum := by
          rw [sum_map_eq_range, hlen]
          congr 1
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          by_cases hct : sideAt p x i = t
          · rw [if_pos ((top_iff hSt (hsides i (by omega))).mpr hct), if_pos hct]
          · rw [if_neg (fun h => hct ((top_iff hSt (hsides i (by omega))).mp (by simpa using h))),
              if_neg hct]
        rw [hind, if_neg (fun h => by omega)]
        simp
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero true _ hwle]
        simp [WTree.occC]
      · have hjt : spineAt p x j ≠ t := by intro h; rw [h] at hS; rw [hS] at hSt; cases hSt
        obtain ⟨_, hT⟩ := hp.spine_edges hx htn hf (Nat.le_of_lt hj) (fun _ => hjt)
        simp only [WTree.occC, hxt, if_false, occCs_eq, WTree.written, List.map_append,
          List.sum_append, writtens_sum, List.append_nil]
        rw [hT, List.map_congr_left (fun T hT => (hside T hT).2.1)]
        simp
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    have hside : ∀ T ∈ sides, T.occH t = (if T.topIs t then 1 else 0) +
          ((T.written p).map fun y => edgeMult p y t false).sum ∧
        T.occC p t = ((T.written p).map fun y => edgeMult p y t true).sum ∧
        (∀ y ∈ T.written p, y < x) := by
      intro T hT
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      obtain ⟨h1, h2, h3⟩ := ih i hi (by omega)
      exact ⟨h1, h2, fun y hy => by have := h3 y hy; omega⟩
    obtain ⟨ht1, ht2, ht3⟩ := iht (by omega)
    have hwle : ∀ y ∈ (WTree.tele x p.spineLen[x]! sides tail).written p, y ≤ x := by
      intro y hy
      simp only [WTree.written, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        exact hp.spineAt_le hx hf (by rw [List.mem_range] at hk; omega)
      · obtain ⟨T, hT, hyT⟩ := writtens_mem hy
        exact Nat.le_of_lt ((hside T hT).2.2 y hyT)
      · have := ht3 y hy; omega
    refine ⟨?_, ?_, hwle⟩
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero false _ hwle]
        simp [WTree.occH, WTree.topIs]
      · obtain ⟨hF, _⟩ := hp.spine_edges hx htn hf (Nat.le_refl _) (fun h => absurd h (by omega))
        simp only [WTree.occH, hxt, if_false, WTree.topIs, occHs_eq, WTree.written,
          List.map_append, List.sum_append, writtens_sum, beq_iff_eq]
        rw [hF, List.map_congr_left (fun T hT => (hside T hT).1), sum_map_add', ht1]
        have hind : (sides.map fun T => if T.topIs t then 1 else 0).sum =
            ((List.range p.spineLen[x]!).map fun k => if sideAt p x k = t then 1 else 0).sum := by
          rw [sum_map_eq_range, hlen]
          congr 1
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          by_cases hct : sideAt p x i = t
          · rw [if_pos ((top_iff hSt (hsides i (by omega))).mpr hct), if_pos hct]
          · rw [if_neg (fun h => hct ((top_iff hSt (hsides i (by omega))).mp (by simpa using h))),
              if_neg hct]
        have htop : (if tail.topIs t then 1 else 0) =
            (if p.spineLen[x]! = p.spineLen[x]! ∧ p.tail[x]! = t then 1 else 0) := by
          by_cases htt : p.tail[x]! = t
          · rw [if_pos ((top_iff hSt htail).mpr htt), if_pos ⟨rfl, htt⟩]
          · rw [if_neg (fun h => htt ((top_iff hSt htail).mp (by simpa using h))),
              if_neg (fun h => htt h.2)]
        rw [hind, htop]
        omega
    · by_cases hxt : x = t
      · subst hxt
        rw [hzero true _ hwle]
        simp [WTree.occC]
      · obtain ⟨_, hT⟩ := hp.spine_edges hx htn hf (Nat.le_refl _) (fun h => absurd h (by omega))
        simp only [WTree.occC, hxt, if_false, occCs_eq, WTree.written, List.map_append,
          List.sum_append, writtens_sum]
        rw [hT, List.map_congr_left (fun T hT => (hside T hT).2.1), ht2]
/-! ## Every reachable term is written -/

open Ix.Compile.Verify.SharingExact (Desc)

mutual
/-- The Shares a writing uses. -/
def WTree.shares : WTree → List Nat
  | .share x => [x]
  | .node _ kids => WTree.sharess kids
  | .tele _ _ sides tail => WTree.sharess sides ++ WTree.shares tail
def WTree.sharess : List WTree → List Nat
  | [] => []
  | k :: ks => WTree.shares k ++ WTree.sharess ks
end

theorem sharess_mem {y : Nat} {l : List WTree} (h : y ∈ WTree.sharess l) :
    ∃ T ∈ l, y ∈ T.shares := by
  induction l with
  | nil => simp [WTree.sharess] at h
  | cons k ks ih =>
    simp only [WTree.sharess, List.mem_append] at h
    rcases h with h | h
    · exact ⟨k, List.mem_cons_self, h⟩
    · obtain ⟨T, hT, hy⟩ := ih h
      exact ⟨T, List.mem_cons_of_mem _ hT, hy⟩

theorem mem_sharess {y : Nat} {l : List WTree} {T : WTree} (hT : T ∈ l) (h : y ∈ T.shares) :
    y ∈ WTree.sharess l := by
  induction l with
  | nil => cases hT
  | cons k ks ih =>
    simp only [WTree.sharess, List.mem_append]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl h
    · exact Or.inr (ih hT)

theorem mem_writtens {p : Prep} {y : Nat} {l : List WTree} {T : WTree} (hT : T ∈ l)
    (h : y ∈ T.written p) : y ∈ WTree.writtens p l := by
  induction l with
  | nil => cases hT
  | cons k ks ih =>
    simp only [WTree.writtens, List.mem_append]
    rcases List.mem_cons.mp hT with rfl | hT
    · exact Or.inl h
    · exact Or.inr (ih hT)

/-- The Shares of a writing of `x` are stored terms below `x` (strictly, for
an inline writing). -/
theorem PrepWF.shares_lt {p : Prep} (hp : PrepWF p) {S : Nat → Bool} :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      ∀ s ∈ T.shares, S s = true ∧ (s ≤ x) ∧ (T.isShare = false → s < x) := by
  intro x T h
  induction h with
  | share hS =>
    intro _ s hs
    simp only [WTree.shares, List.mem_singleton] at hs
    subst hs
    exact ⟨hS, Nat.le_refl _, fun h => by simp [WTree.isShare] at h⟩
  | @node x kids hf hlen _ ih =>
    intro hx s hs
    simp only [WTree.shares] at hs
    obtain ⟨T, hT, hsT⟩ := sharess_mem hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
    have hc := hp.dag.childAt_lt hx (k := i) (by omega)
    obtain ⟨h1, h2, _⟩ := ih i hi (by omega) s hsT
    exact ⟨h1, by omega, fun _ => by omega⟩
  | @teleCut x j sides hf hj1 hj hlen _ hS ih =>
    intro hx s hs
    simp only [WTree.shares, List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · obtain ⟨T, hT, hsT⟩ := sharess_mem hs
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      obtain ⟨h1, h2, _⟩ := ih i hi (by omega) s hsT
      exact ⟨h1, by omega, fun _ => by omega⟩
    · have := hp.spineAt_lt hx hf hj1 hj
      exact ⟨hS, by omega, fun _ => this⟩
  | @teleFull x sides tail hf hlen _ _ ih iht =>
    intro hx s hs
    obtain ⟨_, _, _, htl, _⟩ := hp.spine x hx hf
    simp only [WTree.shares, List.mem_append] at hs
    rcases hs with hs | hs
    · obtain ⟨T, hT, hsT⟩ := sharess_mem hs
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
      have hsl := hp.sideAt_lt hx hf (k := i) (by omega)
      obtain ⟨h1, h2, _⟩ := ih i hi (by omega) s hsT
      exact ⟨h1, by omega, fun _ => by omega⟩
    · obtain ⟨h1, h2, _⟩ := iht (by omega) s hs
      exact ⟨h1, by omega, fun _ => by omega⟩

theorem PrepWF.tele_child {p : Prep} (hp : PrepWF p) {y k : Nat} (hy : y < p.dag.size)
    (hf : p.family[y]! ≠ .none) (hk : k < (p.dag.node y).children.size) :
    (p.dag.node y).child k = (p.dag.node y).sideChild ∨ (p.dag.node y).child k = snext p y := by
  have ha := hp.dag.arity y hy
  rw [← dag_node_eq hy] at ha
  have hfy : (p.dag.node y).head.family ≠ .none := by rw [← hp.family y hy]; exact hf
  unfold Node.sideChild snext Node.spineNext
  cases hh : (p.dag.node y).head <;> simp only [hh, Head.family, ne_eq, not_true_eq_false] at hfy <;>
    simp only [hh, Head.arity] at ha <;> rw [ha] at hk <;>
    (rcases k with _ | _ | k) <;> simp_all <;> omega

/-- **Coverage.** Every term below `x` is written by a writing of `x` or lies
below one of its Shares. -/
theorem PrepWF.cover {p : Prep} (hp : PrepWF p) {S : Nat → Bool} :
    ∀ {x : Nat} {T : WTree}, Valid p S x T → x < p.dag.size →
      ∀ y, Desc p.dag x y → y ∈ T.written p ∨ ∃ s ∈ T.shares, Desc p.dag s y := by
  intro x T h
  induction h with
  | @share x _ =>
    intro _ y hd
    exact Or.inr ⟨x, by simp [WTree.shares], hd⟩
  | @node x kids hf hlen _ ih =>
    intro hx y hd
    cases hd with
    | refl => exact Or.inl (by simp [WTree.written])
    | @child _ _ k hk hd' =>
      have ha := hp.dag.arity x hx
      rw [← dag_node_eq hx] at ha
      have hkl : k < kids.length := by omega
      have hc := hp.dag.childAt_lt hx (k := k) (by omega)
      rcases ih k hkl (by omega) y hd' with hw | ⟨s, hs, hds⟩
      · exact Or.inl (by
          simp only [WTree.written, List.mem_cons]
          exact Or.inr (mem_writtens (List.getElem_mem hkl) hw))
      · exact Or.inr ⟨s, by simp only [WTree.shares]; exact mem_sharess (List.getElem_mem hkl) hs,
          hds⟩
  | @teleCut x j sides hf hj1 hj hlen hsides hS ih =>
    intro hx y hd
    have hside : ∀ m, m < j → Desc p.dag (sideAt p x m) y →
        y ∈ (WTree.tele x j sides (.share (spineAt p x j))).written p ∨
          ∃ s ∈ (WTree.tele x j sides (.share (spineAt p x j))).shares, Desc p.dag s y := by
      intro m hm hd'
      have hsl := hp.sideAt_lt hx hf (k := m) (by omega)
      rcases ih m (by omega) (by omega) y hd' with hw | ⟨s, hs, hds⟩
      · exact Or.inl (by
          simp only [WTree.written, List.mem_append]
          exact Or.inl (Or.inr (mem_writtens (List.getElem_mem (by omega)) hw)))
      · exact Or.inr ⟨s, by
          simp only [WTree.shares, List.mem_append]
          exact Or.inl (mem_sharess (List.getElem_mem (by omega)) hs), hds⟩
    have key : ∀ i m, m + i = j - 1 → Desc p.dag (spineAt p x m) y →
        y ∈ (WTree.tele x j sides (.share (spineAt p x j))).written p ∨
          ∃ s ∈ (WTree.tele x j sides (.share (spineAt p x j))).shares, Desc p.dag s y := by
      intro i
      induction i with
      | zero =>
        intro m hm hd'
        obtain ⟨hms, hmf, _⟩ := hp.spine_shift hx hf (k := m) (by omega)
        have hmf' : p.family[spineAt p x m]! ≠ .none := by rw [hmf]; exact hf
        cases hd' with
        | refl =>
          exact Or.inl (by
            simp only [WTree.written, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩)))
        | @child _ _ k hk hd'' =>
          rcases hp.tele_child hms hmf' hk with hc | hc
          · rw [hc] at hd''; exact hside m (by omega) hd''
          · rw [hc, snext_spineAt, show m + 1 = j by omega] at hd''
            exact Or.inr ⟨spineAt p x j, by simp [WTree.shares], hd''⟩
      | succ i ihi =>
        intro m hm hd'
        obtain ⟨hms, hmf, _⟩ := hp.spine_shift hx hf (k := m) (by omega)
        have hmf' : p.family[spineAt p x m]! ≠ .none := by rw [hmf]; exact hf
        cases hd' with
        | refl =>
          exact Or.inl (by
            simp only [WTree.written, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩)))
        | @child _ _ k hk hd'' =>
          rcases hp.tele_child hms hmf' hk with hc | hc
          · rw [hc] at hd''; exact hside m (by omega) hd''
          · rw [hc, snext_spineAt] at hd''
            exact ihi (m + 1) (by omega) hd''
    exact key (j - 1) 0 (by omega) hd
  | @teleFull x sides tail hf hlen hsides htail ih iht =>
    intro hx y hd
    obtain ⟨hl1, _, hend, htl, _⟩ := hp.spine x hx hf
    have hside : ∀ m, m < p.spineLen[x]! → Desc p.dag (sideAt p x m) y →
        y ∈ (WTree.tele x p.spineLen[x]! sides tail).written p ∨
          ∃ s ∈ (WTree.tele x p.spineLen[x]! sides tail).shares, Desc p.dag s y := by
      intro m hm hd'
      have hsl := hp.sideAt_lt hx hf (k := m) (by omega)
      rcases ih m (by omega) (by omega) y hd' with hw | ⟨s, hs, hds⟩
      · exact Or.inl (by
          simp only [WTree.written, List.mem_append]
          exact Or.inl (Or.inr (mem_writtens (List.getElem_mem (by omega)) hw)))
      · exact Or.inr ⟨s, by
          simp only [WTree.shares, List.mem_append]
          exact Or.inl (mem_sharess (List.getElem_mem (by omega)) hs), hds⟩
    have key : ∀ i m, m + i = p.spineLen[x]! - 1 → Desc p.dag (spineAt p x m) y →
        y ∈ (WTree.tele x p.spineLen[x]! sides tail).written p ∨
          ∃ s ∈ (WTree.tele x p.spineLen[x]! sides tail).shares, Desc p.dag s y := by
      intro i
      induction i with
      | zero =>
        intro m hm hd'
        obtain ⟨hms, hmf, _⟩ := hp.spine_shift hx hf (k := m) (by omega)
        have hmf' : p.family[spineAt p x m]! ≠ .none := by rw [hmf]; exact hf
        cases hd' with
        | refl =>
          exact Or.inl (by
            simp only [WTree.written, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩)))
        | @child _ _ k hk hd'' =>
          rcases hp.tele_child hms hmf' hk with hc | hc
          · rw [hc] at hd''; exact hside m (by omega) hd''
          · rw [hc, snext_spineAt, show m + 1 = p.spineLen[x]! by omega, hend] at hd''
            rcases iht (by omega) y hd'' with hw | ⟨s, hs, hds⟩
            · exact Or.inl (by simp only [WTree.written, List.mem_append]; exact Or.inr hw)
            · exact Or.inr ⟨s, by simp only [WTree.shares, List.mem_append]; exact Or.inr hs, hds⟩
      | succ i ihi =>
        intro m hm hd'
        obtain ⟨hms, hmf, _⟩ := hp.spine_shift hx hf (k := m) (by omega)
        have hmf' : p.family[spineAt p x m]! ≠ .none := by rw [hmf]; exact hf
        cases hd' with
        | refl =>
          exact Or.inl (by
            simp only [WTree.written, List.mem_append]
            exact Or.inl (Or.inl (List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩)))
        | @child _ _ k hk hd'' =>
          rcases hp.tele_child hms hmf' hk with hc | hc
          · rw [hc] at hd''; exact hside m (by omega) hd''
          · rw [hc, snext_spineAt] at hd''
            exact ihi (m + 1) (by omega) hd''
    exact key (p.spineLen[x]! - 1) 0 (by omega) hd

end Ix.Compile.Verify.UniformModel
