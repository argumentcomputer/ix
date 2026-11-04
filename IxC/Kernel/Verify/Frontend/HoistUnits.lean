module

public import IxC.Kernel.Verify.Frontend.Prepare
public import IxC.Kernel.Verify.Rename.UnionUnits

public section

/-!
# The ground hoist's order (S1)

`applyHoist` sorts the records' indices by a key: a moved record `k` sorts at
its target `t` just ahead of the operation there (`(t, 0, k)`), every other
record at its own position (`(k, 1, k)`). This file reads the sorted order
off its specification: the keys are a strict total order (`KLt`), the sorted
list is sorted (`List.pairwise_mergeSort`), and a sorted permutation of the
indices is the sorted order (`List.Perm.eq_of_pairwise`). So any list of the
indices sorted by key is the hoist's order (`order_eq`).
-/

namespace Ix.Kernel.Frontend

open Ix.Kernel

/-! ## Keys -/

/-- The hoist's key of record `k` under `target`. -/
def hkey (target : Std.HashMap Nat Nat) (k : Nat) : Nat × Nat × Nat :=
  match target[k]? with
  | some t => (t, 0, k)
  | none => (k, 1, k)

/-- The hoist's comparison, as `applyHoist` spells it. -/
def hlt (target : Std.HashMap Nat Nat) (a b : Nat) : Bool :=
  let (ta, sa, ka) := hkey target a
  let (tb, sb, kb) := hkey target b
  ta < tb || (ta == tb && (sa < sb || (sa == sb && ka < kb)))

/-- The lexicographic order on keys. -/
def KLt (x y : Nat × Nat × Nat) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))

theorem hlt_iff (target : Std.HashMap Nat Nat) (a b : Nat) :
    hlt target a b = true ↔ KLt (hkey target a) (hkey target b) := by
  unfold hlt KLt
  generalize hkey target a = x
  generalize hkey target b = y
  obtain ⟨ta, sa, ka⟩ := x
  obtain ⟨tb, sb, kb⟩ := y
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

theorem KLt.irrefl {x : Nat × Nat × Nat} : ¬ KLt x x := by
  obtain ⟨a, b, c⟩ := x
  unfold KLt; omega

theorem KLt.trans {x y z : Nat × Nat × Nat} (h₁ : KLt x y) (h₂ : KLt y z) : KLt x z := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y; obtain ⟨g, h, i⟩ := z
  unfold KLt at *; omega

theorem KLt.total {x y : Nat × Nat × Nat} (h : x ≠ y) : KLt x y ∨ KLt y x := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨d, e, f⟩ := y
  unfold KLt
  dsimp only
  simp only [ne_eq, Prod.mk.injEq] at h
  omega

theorem KLt.asymm {x y : Nat × Nat × Nat} (h : KLt x y) : ¬ KLt y x := fun h' =>
  KLt.irrefl (h.trans h')

@[simp] theorem hkey_third (target : Std.HashMap Nat Nat) (k : Nat) : (hkey target k).2.2 = k := by
  unfold hkey; split <;> rfl

theorem hkey_inj {target : Std.HashMap Nat Nat} {a b : Nat} (h : hkey target a = hkey target b) :
    a = b := by
  have := congrArg (·.2.2) h
  simpa using this

/-- The hoist's order relation: `a` sorts no later than `b`. -/
def hle (target : Std.HashMap Nat Nat) (a b : Nat) : Bool := !hlt target b a

theorem hle_iff (target : Std.HashMap Nat Nat) (a b : Nat) :
    hle target a b = true ↔ ¬ KLt (hkey target b) (hkey target a) := by
  unfold hle
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hlt_iff]

theorem hle_trans (target : Std.HashMap Nat Nat) (a b c : Nat) :
    hle target a b = true → hle target b c = true → hle target a c = true := by
  simp only [hle_iff]
  intro h₁ h₂ h₃
  by_cases hab : hkey target a = hkey target b
  · rw [hab] at h₃; exact h₂ h₃
  · rcases KLt.total hab with h | h
    · exact h₂ (h₃.trans h)
    · exact h₁ h

theorem hle_total (target : Std.HashMap Nat Nat) (a b : Nat) :
    (hle target a b || hle target b a) = true := by
  simp only [Bool.or_eq_true, hle_iff]
  by_cases h : KLt (hkey target b) (hkey target a)
  · exact Or.inr h.asymm
  · exact Or.inl h

/-- **`applyHoist` reads the records in the hoist's order.** -/
theorem applyHoist_toList (ds : Array (Declaration md)) (target : Std.HashMap Nat Nat) :
    (applyHoist ds target).1.toList =
      ((List.range ds.size).mergeSort (hle target)).map (ds[·]!) := by
  simp only [applyHoist, List.toList_toArray]
  rfl

/-- **A list of the indices sorted by key is the hoist's order.** -/
theorem order_eq (target : Std.HashMap Nat Nat) (n : Nat) {L : List Nat}
    (hperm : L.Perm (List.range n)) (hsort : L.Pairwise fun a b => hle target a b = true) :
    (List.range n).mergeSort (hle target) = L := by
  refine List.Perm.eq_of_pairwise (le := fun a b => hle target a b = true) (fun a b _ _ hab hba => ?_)
    (List.pairwise_mergeSort (hle_trans target) (hle_total target) _) hsort
    ((List.mergeSort_perm _ _).trans hperm.symm)
  rw [hle_iff] at hab hba
  refine Classical.byContradiction fun hne => ?_
  have hk : hkey target a ≠ hkey target b := fun h => hne (hkey_inj h)
  rcases KLt.total hk with h | h
  · exact hba h
  · exact hab h

/-! ## Blocks of indices -/

/-- **A block the hoist keeps whole**: the indices `s .. s + len - 1`, at least
one, and, when there are several, none of them moved and no moved record
landing strictly inside. -/
structure BlockOk (target : Std.HashMap Nat Nat) (B : List Nat) : Prop where
  shape : ∃ s len, 0 < len ∧ B = List.range' s len ∧
    (2 ≤ len → (∀ i ∈ B, target[i]? = none) ∧
      ∀ k t : Nat, target[k]? = some t → ¬ (s < t ∧ t < s + len))

theorem BlockOk.head_mem {target : Std.HashMap Nat Nat} {B : List Nat} (h : BlockOk target B) :
    B.headD 0 ∈ B := by
  obtain ⟨s, len, hlen, rfl, -⟩ := h.shape
  obtain ⟨n, rfl⟩ : ∃ n, len = n + 1 := ⟨len - 1, by omega⟩
  simp [List.range'_succ]

/-- **Inside a block, keys increase.** -/
theorem BlockOk.sorted {target : Std.HashMap Nat Nat} {B : List Nat} (h : BlockOk target B) :
    B.Pairwise fun a b => hle target a b = true := by
  obtain ⟨s, len, _, rfl, hm⟩ := h.shape
  by_cases h2 : 2 ≤ len
  · obtain ⟨hun, -⟩ := hm h2
    refine (List.pairwise_lt_range' (s := s) (n := len)).imp_of_mem fun {a b} ha hb hab => ?_
    rw [hle_iff]
    unfold hkey
    rw [hun a ha, hun b hb]
    unfold KLt; dsimp only; omega
  · obtain rfl : len = 1 := by omega
    simp

/-- **Two blocks the hoist keeps whole, disjoint, sorted by their heads**: every
key of the first is below every key of the second. -/
theorem BlockOk.sep {target : Std.HashMap Nat Nat} {B B' : List Nat} (hB : BlockOk target B)
    (hB' : BlockOk target B') (hdisj : ∀ x ∈ B, x ∉ B')
    (hhead : hle target (B.headD 0) (B'.headD 0) = true) :
    ∀ x ∈ B, ∀ y ∈ B', hle target x y = true := by
  obtain ⟨s, len, hlen, rfl, hm⟩ := hB.shape
  obtain ⟨s', len', hlen', rfl, hm'⟩ := hB'.shape
  have hh : (List.range' s len).headD 0 = s := by
    obtain ⟨n, rfl⟩ : ∃ n, len = n + 1 := ⟨len - 1, by omega⟩
    simp [List.range'_succ]
  have hh' : (List.range' s' len').headD 0 = s' := by
    obtain ⟨n, rfl⟩ : ∃ n, len' = n + 1 := ⟨len' - 1, by omega⟩
    simp [List.range'_succ]
  rw [hh, hh', hle_iff] at hhead
  intro x hx y hy
  rw [hle_iff]
  simp only [List.mem_range'_1] at hx hy
  -- the head of the second block is not the first's
  have hs' : ¬ (s ≤ s' ∧ s' < s + len) := fun h =>
    hdisj s' (List.mem_range'_1.mpr h) (List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩)
  by_cases h2 : 2 ≤ len
  · obtain ⟨hun, hin⟩ := hm h2
    have hx0 : target[x]? = none := hun x (List.mem_range'_1.mpr hx)
    have hs0 : target[s]? = none := hun s (List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩)
    by_cases h2' : 2 ≤ len'
    · obtain ⟨hun', -⟩ := hm' h2'
      have hy0 : target[y]? = none := hun' y (List.mem_range'_1.mpr hy)
      have hs'0 : target[s']? = none := hun' s' (List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩)
      unfold hkey at hhead ⊢
      rw [hs0, hs'0] at hhead
      rw [hx0, hy0]
      unfold KLt at hhead ⊢; dsimp only at hhead ⊢; omega
    · obtain rfl : len' = 1 := by omega
      obtain rfl : s' = y := by omega
      unfold hkey at hhead ⊢
      rw [hs0] at hhead
      rw [hx0]
      cases ht : target[s']? with
      | none => rw [ht] at hhead; unfold KLt at hhead ⊢; dsimp only at hhead ⊢; omega
      | some t =>
        rw [ht] at hhead
        have := hin s' t ht
        unfold KLt at hhead ⊢; dsimp only at hhead ⊢; omega
  · obtain rfl : len = 1 := by omega
    obtain rfl : s = x := by omega
    by_cases h2' : 2 ≤ len'
    · obtain ⟨hun', -⟩ := hm' h2'
      have hy0 : target[y]? = none := hun' y (List.mem_range'_1.mpr hy)
      have hs'0 : target[s']? = none := hun' s' (List.mem_range'_1.mpr ⟨Nat.le_refl _, by omega⟩)
      unfold hkey at hhead ⊢
      rw [hs'0] at hhead
      rw [hy0]
      cases ht : target[s]? with
      | none => rw [ht] at hhead; unfold KLt at hhead ⊢; dsimp only at hhead ⊢; omega
      | some t => rw [ht] at hhead; unfold KLt at hhead ⊢; dsimp only at hhead ⊢; omega
    · obtain rfl : len' = 1 := by omega
      obtain rfl : s' = y := by omega
      intro hk
      have hne : hkey target s ≠ hkey target s' := fun h => by
        have := hkey_inj h; omega
      rcases KLt.total hne with h | h
      · exact h.asymm hk
      · exact hhead h

/-! ## A stream of lowerings -/

/-- The index blocks of lists laid end to end from position `s`. -/
def blocksFrom {α : Type} : Nat → List (List α) → List (List Nat)
  | _, [] => []
  | s, l :: ls => List.range' s l.length :: blocksFrom (s + l.length) ls

theorem blocksFrom_flatten {α : Type} : ∀ (s : Nat) (ls : List (List α)),
    (blocksFrom s ls).flatten = List.range' s ls.flatten.length
  | s, [] => by simp [blocksFrom]
  | s, l :: ls => by
    rw [blocksFrom, List.flatten_cons, blocksFrom_flatten, List.flatten_cons, List.length_append]
    simp

theorem blocksFrom_ge {α : Type} : ∀ (s : Nat) (ls : List (List α)),
    ∀ B ∈ blocksFrom s ls, ∀ x ∈ B, s ≤ x
  | s, [], _, h, _, _ => nomatch h
  | s, l :: ls, B, hB, x, hx => by
    rcases List.mem_cons.mp hB with rfl | hB
    · exact (List.mem_range'_1.mp hx).1
    · have := blocksFrom_ge (s + l.length) ls B hB x hx; omega

theorem blocksFrom_disj {α : Type} : ∀ (s : Nat) (ls : List (List α)),
    (blocksFrom s ls).Pairwise fun B B' => ∀ x ∈ B, x ∉ B'
  | s, [] => List.Pairwise.nil
  | s, l :: ls => by
    refine List.pairwise_cons.mpr ⟨fun B' hB' x hx hx' => ?_, blocksFrom_disj _ ls⟩
    have h1 := (List.mem_range'_1.mp hx).2
    have h2 := blocksFrom_ge (s + l.length) ls B' hB' x hx'
    omega

/-- A declaration of the array, read at an index its list holds. -/
theorem getElem!_of_toList {ds : Array (Declaration md)} {pre l rest : List (Declaration md)}
    (h : ds.toList = pre ++ (l ++ rest)) {j : Nat} (hj : j < l.length) :
    ds[pre.length + j]! = l[j] := by
  have hlt : pre.length + j < ds.size := by
    rw [← Array.length_toList, h]; simp; omega
  rw [getElem!_pos ds _ hlt, ← Array.getElem_toList]
  simp only [h]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left hj]

theorem blocksFrom_map (ds : Array (Declaration md)) : ∀ (pre : List (Declaration md))
    (ls : List (List (Declaration md))), ds.toList = pre ++ ls.flatten →
      (blocksFrom pre.length ls).map (·.map fun k => ds[k]!) = ls
  | pre, [], _ => rfl
  | pre, l :: ls, h => by
    rw [List.flatten_cons] at h
    have ih := blocksFrom_map ds (pre ++ l) ls (by rw [h, List.append_assoc])
    rw [List.length_append] at ih
    rw [blocksFrom, List.map_cons, ih]
    congr 1
    apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range']
    rw [Nat.one_mul]
    exact getElem!_of_toList h (by simpa using h₁)

/-- **The guard's facts**: a record it lets the hoist move is not generated,
nor right after a generated record, and neither is the record before its
target. -/
theorem guard_facts {ds : Array (Declaration md)} {target : Std.HashMap Nat Nat}
    (hg : splitsUnit ds target = false) {k t : Nat} (h : target[k]? = some t) :
    ds[k]!.isGenerated = false ∧ (0 < k → ds[k - 1]!.isGenerated = false) ∧
      (0 < t → ds[t - 1]!.isGenerated = false) := by
  unfold splitsUnit at hg
  have hm : (k, t) ∈ target.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
  have := List.any_eq_false.mp hg (k, t) hm
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and,
    Bool.not_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem blocksFrom_ok {ds : Array (Declaration md)} {target : Std.HashMap Nat Nat}
    (hg : splitsUnit ds target = false) : ∀ (pre : List (Declaration md))
    (ls : List (List (Declaration md))), ds.toList = pre ++ ls.flatten →
      (∀ l ∈ ls, IsLowering l) → ∀ B ∈ blocksFrom pre.length ls, BlockOk target B
  | pre, [], _, _, _, h => nomatch h
  | pre, l :: ls, h, hl, B, hB => by
    rw [List.flatten_cons] at h
    rcases List.mem_cons.mp hB with rfl | hB
    · obtain ⟨gs, d, rfl, hgs, hd⟩ := hl _ List.mem_cons_self
      have hlen : (gs ++ [d]).length = gs.length + 1 := by simp
      have hgen : ∀ j, j < gs.length → ds[pre.length + j]!.isGenerated = true := fun j hj => by
        rw [getElem!_of_toList h (by simp; omega), List.getElem_append_left hj]
        exact hgs _ (List.getElem_mem _)
      refine ⟨pre.length, (gs ++ [d]).length, by simp, rfl, fun h2 => ⟨fun i hi => ?_, fun k t hk ht => ?_⟩⟩
      · rw [hlen] at h2 hi
        obtain ⟨hi1, hi2⟩ := List.mem_range'_1.mp hi
        cases hk : target[i]? with
        | none => rfl
        | some t =>
          exfalso
          obtain ⟨g1, g2, -⟩ := guard_facts hg hk
          by_cases hlast : i < pre.length + gs.length
          · have := hgen (i - pre.length) (by omega)
            rw [show pre.length + (i - pre.length) = i by omega, g1] at this
            exact nomatch this
          · have := hgen (i - 1 - pre.length) (by omega)
            rw [show pre.length + (i - 1 - pre.length) = i - 1 by omega, g2 (by omega)] at this
            exact nomatch this
      · rw [hlen] at h2 ht
        obtain ⟨-, -, g3⟩ := guard_facts hg hk
        have := hgen (t - 1 - pre.length) (by omega)
        rw [show pre.length + (t - 1 - pre.length) = t - 1 by omega, g3 (by omega)] at this
        exact nomatch this
    · have := blocksFrom_ok hg (pre ++ l) ls (by rw [h, List.append_assoc])
        (fun l' h' => hl l' (List.mem_cons_of_mem _ h'))
      rw [List.length_append] at this
      exact this B hB

/-! ## The hoist keeps lowerings whole -/

/-- **The hoist keeps lowerings whole and in order**: a stream of lowerings
(`IsLowering`: generated records, then one declaration that is not) comes out
of the ground hoist as the same lowerings, reordered as wholes. -/
theorem hoistNatOpGround_lowerings {ds : Array (Declaration md)}
    {ls : List (List (Declaration md))} (hds : ds.toList = ls.flatten)
    (hl : ∀ l ∈ ls, IsLowering l) :
    ∃ ls' : List (List (Declaration md)), ls'.Perm ls ∧ (hoistNatOpGround ds).1.toList = ls'.flatten := by
  unfold hoistNatOpGround
  dsimp only
  split
  · exact ⟨ls, List.Perm.refl _, hds⟩
  · rename_i hguard
    have hg : splitsUnit ds (hoistTargets ds) = false := by
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguard
      exact hguard.2
    generalize hoistTargets ds = target at hg ⊢
    have hds' : ds.toList = [] ++ ls.flatten := by simpa using hds
    let bs := blocksFrom 0 ls
    have hok : ∀ B ∈ bs, BlockOk target B := blocksFrom_ok hg [] ls hds' hl
    let headLe : List Nat → List Nat → Bool := fun B B' => hle target (B.headD 0) (B'.headD 0)
    let bs' := bs.mergeSort headLe
    have hperm' : bs'.Perm bs := List.mergeSort_perm _ _
    have hok' : ∀ B ∈ bs', BlockOk target B := fun B hB => hok B (hperm'.mem_iff.mp hB)
    have hsize : ds.size = ls.flatten.length := by rw [← Array.length_toList, hds]
    -- the blocks' indices, sorted, are the hoist's order
    have hL : (List.range ds.size).mergeSort (hle target) = bs'.flatten := by
      apply order_eq
      · rw [hsize, List.range_eq_range', ← blocksFrom_flatten 0 ls]
        exact hperm'.flatten
      · rw [List.pairwise_flatten]
        refine ⟨fun B hB => (hok' B hB).sorted, ?_⟩
        have hsorted : bs'.Pairwise fun B B' => headLe B B' = true :=
          List.pairwise_mergeSort (le := headLe)
            (fun a b c h₁ h₂ => hle_trans target (a.headD 0) (b.headD 0) (c.headD 0) h₁ h₂)
            (fun a b => hle_total target (a.headD 0) (b.headD 0)) bs
        have hdisj : bs'.Pairwise fun B B' => ∀ x ∈ B, x ∉ B' :=
          (blocksFrom_disj 0 ls).perm hperm'.symm fun {B B'} h x hx hx' => h x hx' hx
        exact (hsorted.and hdisj).imp_of_mem fun {B B'} hB hB' h =>
          (hok' B hB).sep (hok' B' hB') h.2 h.1
    refine ⟨bs'.map (·.map fun k => ds[k]!), ?_, ?_⟩
    · have hbs : bs = blocksFrom 0 ls := rfl
      have := hperm'.map (·.map fun k => ds[k]!)
      have hmap := blocksFrom_map ds [] ls hds'
      rw [List.length_nil, ← hbs] at hmap
      rwa [hmap] at this
    · rw [applyHoist_toList, hL, List.map_flatten]

/-- **The units of the prepared rest are the stream's lowerings**: when the
rest of the stream is a list of lowerings, the units the fold's check reads off
the hoisted rest are those lowerings, reordered as wholes. -/
theorem unitsOf_hoist_lowerings {ds : Array (Declaration md)}
    {ls : List (List (Declaration md))} (hds : ds.toList = ls.flatten)
    (hl : ∀ l ∈ ls, IsLowering l) :
    (unitsOf (hoistNatOpGround ds).1.toList).Perm ls := by
  obtain ⟨ls', hperm, h⟩ := hoistNatOpGround_lowerings hds hl
  rw [h, unitsOf_lowerings ls' (fun l hl' => hl l (hperm.mem_iff.mp hl'))]
  exact hperm

end Ix.Kernel.Frontend
