import Compilatrix.Xv.Validate.NatMap

/-!
# `NatMap` lemmas

The lookup behaviour of the validator's trie (`Validate.NatMap`): pruned
nodes, updates (`alter`, `insert`, `erase`), entry-wise maps (`filterMap`)
and the entry-wise test (`all`). A traversal visits the subtrie at depth `d`
with its offset `key` and step `pow = 2^d`; its local key `m` is the global
key `key + pow * m` (`find?_filterMapAux`, `allAux_find?`).
-/

namespace Compilatrix.Xv.Validate.NatMap

variable {α β : Type}

@[simp] theorem find?_leaf (k : Nat) : find? (.leaf : NatMap α) k = none := rfl

/-- The root entry and children, a leaf read as an empty node. -/
def rootVal : NatMap α → Option α
  | .leaf => none
  | .node v _ _ => v

def leftChild : NatMap α → NatMap α
  | .leaf => .leaf
  | .node _ l _ => l

def rightChild : NatMap α → NatMap α
  | .leaf => .leaf
  | .node _ _ r => r

theorem find?_eq (m : NatMap α) (k : Nat) :
    find? m k = if k = 0 then m.rootVal
      else if k % 2 = 1 then find? m.leftChild (k / 2) else find? m.rightChild (k / 2 - 1) := by
  cases m <;> simp [find?, rootVal, leftChild, rightChild]

theorem find?_node (v : Option α) (l r : NatMap α) (k : Nat) :
    find? (.node v l r) k =
      if k = 0 then v else if k % 2 = 1 then find? l (k / 2) else find? r (k / 2 - 1) :=
  find?_eq _ k

theorem find?_mk (v : Option α) (l r : NatMap α) (k : Nat) :
    find? (mk v l r) k =
      if k = 0 then v else if k % 2 = 1 then find? l (k / 2) else find? r (k / 2 - 1) := by
  unfold mk
  split
  · simp
  · exact find?_node _ _ _ k

/-- The key `k`'s three cases, as `find?` reads them. -/
private theorem key_cases (k : Nat) :
    k = 0 ∨ (k % 2 = 1 ∧ k = 2 * (k / 2) + 1) ∨ (k ≠ 0 ∧ k % 2 = 0 ∧ k = 2 * (k / 2 - 1) + 2) := by
  omega

theorem alterAux_succ (f : Option α → Option α) (fuel : Nat) (m : NatMap α) (k : Nat) :
    alterAux f (fuel + 1) m k =
      if k = 0 then mk (f m.rootVal) m.leftChild m.rightChild
      else if k % 2 = 1 then mk m.rootVal (alterAux f fuel m.leftChild (k / 2)) m.rightChild
      else mk m.rootVal m.leftChild (alterAux f fuel m.rightChild (k / 2 - 1)) := by
  cases m <;> simp [alterAux, rootVal, leftChild, rightChild]

theorem find?_alterAux (f : Option α → Option α) (fuel : Nat) (m : NatMap α) (k k' : Nat)
    (h : k < fuel) :
    find? (alterAux f fuel m k) k' = if k' = k then f (find? m k) else find? m k' := by
  induction fuel generalizing m k k' with
  | zero => omega
  | succ fuel ih =>
    rw [alterAux_succ, find?_eq m k, find?_eq m k']
    rcases key_cases k with hk | ⟨hk1, hk⟩ | ⟨hk0, hk1, hk⟩
    · subst hk
      simp only [↓reduceIte, find?_mk]
      by_cases h0 : k' = 0 <;> simp [h0]
    · have hk0 : k ≠ 0 := by omega
      simp only [hk0, hk1, ↓reduceIte, find?_mk]
      rw [ih _ _ _ (by omega)]
      rcases key_cases k' with hk' | ⟨hk1', hk'⟩ | ⟨hk0', hk1', hk'⟩
      · subst hk'; simp; omega
      · have h0' : k' ≠ 0 := by omega
        simp only [h0', hk1', ↓reduceIte]
        by_cases e : k' / 2 = k / 2
        · have : k' = k := by omega
          simp [this]
        · have : k' ≠ k := by omega
          simp [e, this]
      · have hne : k' ≠ k := by omega
        have : k' % 2 ≠ 1 := by omega
        simp [hk0', this, hne]
    · have hk2 : k % 2 ≠ 1 := by omega
      simp only [hk0, hk2, ↓reduceIte, find?_mk]
      rw [ih _ _ _ (by omega)]
      rcases key_cases k' with hk' | ⟨hk1', hk'⟩ | ⟨hk0', hk1', hk'⟩
      · subst hk'; simp; omega
      · have hne : k' ≠ k := by omega
        have h0' : k' ≠ 0 := by omega
        simp [h0', hk1', hne]
      · have h2' : k' % 2 ≠ 1 := by omega
        simp only [hk0', h2', ↓reduceIte]
        by_cases e : k' / 2 - 1 = k / 2 - 1
        · have : k' = k := by omega
          simp [this]
        · have : k' ≠ k := by omega
          simp [e, this]

theorem find?_alter (m : NatMap α) (k : Nat) (f : Option α → Option α) (k' : Nat) :
    find? (m.alter k f) k' = if k' = k then f (find? m k) else find? m k' :=
  find?_alterAux f (k + 1) m k k' (by omega)

theorem find?_insert (m : NatMap α) (k : Nat) (a : α) (k' : Nat) :
    find? (m.insert k a) k' = if k' = k then some a else find? m k' :=
  find?_alter m k _ k'

theorem find?_erase (m : NatMap α) (k : Nat) (k' : Nat) :
    find? (m.erase k) k' = if k' = k then none else find? m k' :=
  find?_alter m k _ k'

/-- A local key of the subtrie at offset `key` and step `pow`, as a global
key: the left child's offset is `key + pow`, the right's `key + 2 pow`,
both with step `2 pow`. -/
private theorem key_left (key pow m : Nat) (h : m % 2 = 1) :
    key + pow * m = key + pow + 2 * pow * (m / 2) := by
  have hm : m = 2 * (m / 2) + 1 := by omega
  conv => lhs; rw [hm]
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm pow 2]
  omega

private theorem key_right (key pow m : Nat) (h0 : m ≠ 0) (h : m % 2 = 0) :
    key + pow * m = key + 2 * pow + 2 * pow * (m / 2 - 1) := by
  have hm : m = 2 * (m / 2 - 1) + 2 := by omega
  conv => lhs; rw [hm]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm pow 2]
  omega

theorem find?_filterMapAux (f : Nat → α → Option β) (t : NatMap α) (key pow m : Nat) :
    find? (filterMapAux f t key pow) m = (find? t m).bind (f (key + pow * m)) := by
  induction t generalizing key pow m with
  | leaf => rfl
  | node v l r ihl ihr =>
    simp only [filterMapAux, find?_mk, find?_node]
    rcases key_cases m with hm | ⟨hm1, _⟩ | ⟨hm0, hm1, _⟩
    · subst hm; simp
    · have : m ≠ 0 := by omega
      simp only [this, hm1, ↓reduceIte, ihl, key_left key pow m hm1]
    · have : m % 2 ≠ 1 := by omega
      simp only [hm0, this, ↓reduceIte, ihr, key_right key pow m hm0 hm1]

theorem find?_filterMap (m : NatMap α) (f : Nat → α → Option β) (k : Nat) :
    find? (m.filterMap f) k = (find? m k).bind (f k) := by
  simp [filterMap, find?_filterMapAux]

theorem allAux_find? (p : Nat → α → Bool) (t : NatMap α) (key pow : Nat)
    (h : allAux p t key pow = true) (m : Nat) (a : α) (hm : find? t m = some a) :
    p (key + pow * m) a = true := by
  induction t generalizing key pow m with
  | leaf => simp at hm
  | node v l r ihl ihr =>
    simp only [allAux, Bool.and_eq_true] at h
    obtain ⟨⟨hv, hl⟩, hr⟩ := h
    rw [find?_node] at hm
    rcases key_cases m with hm' | ⟨hm1, _⟩ | ⟨hm0, hm1, _⟩
    · subst hm'
      simp only [↓reduceIte] at hm
      subst hm
      simpa using hv
    · have : m ≠ 0 := by omega
      simp only [this, hm1, ↓reduceIte] at hm
      rw [key_left key pow m hm1]
      exact ihl _ _ hl _ hm
    · have : m % 2 ≠ 1 := by omega
      simp only [hm0, this, ↓reduceIte] at hm
      rw [key_right key pow m hm0 hm1]
      exact ihr _ _ hr _ hm

theorem all_find? {m : NatMap α} {p : Nat → α → Bool} (h : m.all p = true) {k : Nat} {a : α}
    (hk : find? m k = some a) : p k a = true := by
  have := allAux_find? p m 0 1 h k a hk
  simpa using this

end Compilatrix.Xv.Validate.NatMap
