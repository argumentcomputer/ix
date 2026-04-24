module
public import Std.Data.HashMap

public section

structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  pairs : Array (α × β)
  indices : Std.HashMap α Nat
  validIndices : ∀ a : α, indices[a]? = some i →
    (h : i < pairs.size) ×' ((pairs[i]'h : α × β).1 == a) = true
  pairsIndexed : ∀ i (h : i < pairs.size),
    indices[(pairs[i]'h).1]? = some i

namespace IndexMap

variable [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : IndexMap α β) (a : α) (b : β)

instance : Inhabited (IndexMap α β) where
  default :=
    let indices : Std.HashMap α Nat := default
    let pairs : Array (α × β) := #[]
    let valid : ∀ {i} (a : α), indices[a]? = some i →
        (h : i < pairs.size) ×' ((pairs[i]'h).1 == a) = true := by
      intro i a ha
      have hnone : indices[a]? = none := Std.HashMap.getElem?_empty
      simp [hnone] at ha
    let pairsIdx : ∀ i (h : i < pairs.size),
        indices[(pairs[i]'h).1]? = some i := by
      intro i h
      exact absurd h (Nat.not_lt_zero _)
    ⟨pairs, indices, fun a ha => valid a ha, pairsIdx⟩

@[expose]
def insert : IndexMap α β := by
  refine
    match h : m.indices[a]? with
    | none => ⟨m.pairs.push (a, b), m.indices.insert a m.pairs.size, ?_, ?_⟩
    | some idx => ⟨m.pairs.set idx (a, b) (m.validIndices a h).1, m.indices, ?_, ?_⟩
  -- Goals: four cases alternating between validIndices and pairsIndexed.
  · -- none/validIndices
    intro i a' ha'
    simp [Std.HashMap.getElem?_insert] at ha'
    split at ha'
    · rename_i hbeq
      have hi : i = m.pairs.size := (Option.some.inj ha').symm
      subst hi
      have hlt : m.pairs.size < (m.pairs.push (a, b)).size := by simp [Array.size_push]
      refine ⟨hlt, ?_⟩
      have heq : (m.pairs.push (a, b))[m.pairs.size]'hlt = (a, b) := by
        simp [Array.getElem_push]
      rw [heq]
      exact hbeq
    · have hv := m.validIndices a' ha'
      have hlt : i < (m.pairs.push (a, b)).size := by
        rw [Array.size_push]; exact Nat.lt_succ_of_lt hv.1
      refine ⟨hlt, ?_⟩
      rw [Array.getElem_push_lt (h := hv.1)]
      exact hv.2
  · -- none/pairsIndexed
    intro i hi
    rw [Std.HashMap.getElem?_insert]
    by_cases hi_new : i = m.pairs.size
    · subst hi_new
      have heq : (m.pairs.push (a, b))[m.pairs.size]'hi = (a, b) := by
        simp [Array.getElem_push]
      rw [heq]; simp
    · have hi_old : i < m.pairs.size := by
        have : i < m.pairs.size + 1 := Array.size_push _ ▸ hi
        omega
      rw [Array.getElem_push_lt (h := hi_old)]
      have hpi := m.pairsIndexed i hi_old
      split
      · rename_i hbeq
        have ha_eq : m.indices[a]? = some i := by
          rw [Std.HashMap.getElem?_congr hbeq]; exact hpi
        rw [ha_eq] at h; cases h
      · exact hpi
  · -- some idx/validIndices
    intro i a' ha'
    have hv := m.validIndices a' ha'
    have hlt : i < (m.pairs.set idx (a, b) (m.validIndices a h).1).size := by
      rw [Array.size_set]; exact hv.1
    refine ⟨hlt, ?_⟩
    by_cases hi : i = idx
    · subst hi
      simp [Array.getElem_set_self]
      have hva := m.validIndices a h
      exact BEq.trans (BEq.symm hva.2) hv.2
    · have hne : idx ≠ i := fun heq => hi heq.symm
      have := Array.getElem_set_ne (xs := m.pairs) (i := idx) (j := i)
        (v := (a, b)) (h' := (m.validIndices a h).1) (pj := hv.1) hne
      rw [this]
      exact hv.2
  · -- some idx/pairsIndexed
    intro i hi
    have hi' : i < m.pairs.size := by rw [Array.size_set] at hi; exact hi
    by_cases hi_eq : i = idx
    · subst hi_eq
      have hfst : ((m.pairs.set i (a, b) (m.validIndices a h).1)[i]'hi).1 = a := by
        simp [Array.getElem_set_self]
      rw [hfst]; exact h
    · have hne : idx ≠ i := fun heq => hi_eq heq.symm
      have hset := Array.getElem_set_ne (xs := m.pairs) (i := idx) (j := i)
        (v := (a, b)) (h' := (m.validIndices a h).1) (pj := hi') hne
      rw [hset]
      exact m.pairsIndexed i hi'

def map (f : β → β) : IndexMap α β := by
  refine ⟨m.pairs.map fun p => (p.1, f p.2), m.indices, ?_, ?_⟩
  · intro i a' ha'
    have hv := m.validIndices a' ha'
    refine ⟨?_, ?_⟩
    · rw [Array.size_map]; exact hv.1
    · simp [Array.getElem_map]
      exact hv.2
  · intro i hi
    have hi' : i < m.pairs.size := by rw [Array.size_map] at hi; exact hi
    have hfst : ((m.pairs.map fun p => (p.1, f p.2))[i]'hi).1 = (m.pairs[i]'hi').1 := by
      rw [Array.getElem_map]
    rw [hfst]
    exact m.pairsIndexed i hi'

@[inline, expose] def size : Nat :=
  m.pairs.size

@[inline, expose] def getByKey : Option β :=
  m.indices[a]? >>= (m.pairs[·]?.map Prod.snd)

@[inline] def getByIdx (i : Nat) : Option (α × β) :=
  m.pairs[i]?

@[inline] def getIdxOf : Option Nat :=
  m.indices[a]?

@[inline, expose] def containsKey : Bool :=
  m.indices.contains a

@[inline] def foldl (f : γ → α × β → γ) (init : γ) : γ :=
  m.pairs.foldl f init

@[inline] def foldr (f : α × β → γ → γ) (init : γ) : γ :=
  m.pairs.foldr f init

@[inline, expose] def foldlM [Monad μ] (f : γ → α × β → μ γ) (init : γ) : μ γ :=
  m.pairs.foldlM f init

@[inline] def foldrM [Monad μ] (f : α × β → γ → μ γ) (init : γ) : μ γ :=
  m.pairs.foldrM f init

@[inline] def forM [Monad μ] (f : α × β → μ PUnit) : μ PUnit :=
  m.pairs.forM f

/-! ## Proof helpers -/

section Proofs

/-- `getByKey` returns `some _` iff the key is in the index. -/
theorem getByKey_isSome_iff_containsKey (m : IndexMap α β) (a : α) :
    (m.getByKey a).isSome ↔ m.containsKey a := by
  unfold getByKey containsKey
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  constructor
  · intro h
    cases hi : m.indices[a]? with
    | none => simp [hi] at h
    | some i => simp
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨i, hi⟩
    have hlt := (m.validIndices a hi).1
    simp [hi, Option.bind]
    have : m.pairs[i]?.isSome := by simp [hlt]
    cases hp : m.pairs[i]? with
    | none => simp [hp] at this
    | some p => simp [hlt]

/-- Inserting a key makes `containsKey` return true for that key. -/
theorem containsKey_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).containsKey a := by
  unfold containsKey insert
  split
  · simp only [Std.HashMap.contains_insert, BEq.rfl, Bool.true_or]
  · rename_i _ _ idx hidx
    rw [Std.HashMap.contains_eq_isSome_getElem?, hidx]; rfl

/-- Inserting any key preserves `containsKey` for previously-contained keys. -/
theorem containsKey_insert_preserves
    (m : IndexMap α β) (a a' : α) (b' : β) (h : m.containsKey a) :
    (m.insert a' b').containsKey a := by
  unfold containsKey insert at *
  split
  · simp [Std.HashMap.contains_insert, h]
  · exact h

/-- `default : IndexMap α β` does not contain any key. -/
theorem containsKey_default (a : α) :
    (default : IndexMap α β).containsKey a = false := by
  unfold containsKey
  simp only [default]
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  rw [Std.HashMap.getElem?_empty]; rfl

/-- Inserting into an IndexMap: the resulting key set is the old one plus `a`. -/
theorem containsKey_insert_iff (m : IndexMap α β) (a a' : α) (b : β) :
    (m.insert a b).containsKey a' ↔ (a == a') = true ∨ m.containsKey a' := by
  unfold containsKey insert
  split
  · rename_i _ _ h
    simp only [Std.HashMap.contains_insert, Bool.or_eq_true]
  · rename_i _ _ idx hidx
    constructor
    · intro hc
      by_cases hab : (a == a') = true
      · exact Or.inl hab
      · exact Or.inr hc
    · intro hc
      cases hc with
      | inl hab =>
        have : m.indices.contains a = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hidx]; rfl
        rwa [Std.HashMap.contains_congr (hab := hab)] at this
      | inr h => exact h

/-- `containsKey a` iff some pair in `pairs.toList` has first-component
equivalent to `a` under `==`. Uses both `validIndices` and `pairsIndexed`. -/
theorem containsKey_iff_exists_pair (m : IndexMap α β) (a : α) :
    m.containsKey a ↔ ∃ p ∈ m.pairs.toList, (p.1 == a) = true := by
  unfold containsKey
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨i, hi⟩
    have hv := m.validIndices a hi
    refine ⟨m.pairs[i]'hv.1, ?_, hv.2⟩
    exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
  · intro ⟨p, hp, hpeq⟩
    obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem hp
    rw [Array.length_toList] at hi
    have hget : m.pairs[i]'hi = p := by rw [← hi_eq, Array.getElem_toList]
    have hpi := m.pairsIndexed i hi
    rw [hget] at hpi
    have : m.indices[a]? = some i := by
      rw [← Std.HashMap.getElem?_congr hpeq]; exact hpi
    rw [this]; rfl

omit [EquivBEq α] [LawfulHashable α] in
/-- Converse of `getByKey_of_indices_eq`: if `(a, b)` is a pair in the map,
then `getByKey a = some b`. Relies on the `pairsIndexed` invariant. -/
theorem getByKey_of_mem_pairs (m : IndexMap α β) (a : α) (b : β)
    (h : (a, b) ∈ m.pairs.toList) : m.getByKey a = some b := by
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem h
  rw [Array.length_toList] at hi
  have hget : m.pairs[i]'hi = (a, b) := by
    rw [← hi_eq, Array.getElem_toList]
  have hpi : m.indices[a]? = some i := by
    have := m.pairsIndexed i hi
    rw [hget] at this
    exact this
  unfold getByKey
  rw [hpi]
  have hget? : m.pairs[i]? = some (a, b) := by
    rw [Array.getElem?_eq_some_iff]; exact ⟨hi, hget⟩
  simp [hget?]

/-- `getByKey ≠ none` iff `containsKey`. -/
theorem getByKey_ne_none_iff_containsKey (m : IndexMap α β) (g : α) :
    m.getByKey g ≠ none ↔ m.containsKey g :=
  Iff.trans (Iff.symm Option.isSome_iff_ne_none)
    (IndexMap.getByKey_isSome_iff_containsKey m g)

omit [EquivBEq α] in
/-- Converse of `getByKey_of_mem_pairs`: `getByKey a = some b` implies
`(a, b) ∈ pairs.toList`. Follows from `indices[a]?` + `validIndices` +
`LawfulBEq` (keys decide equality on the nose). -/
theorem mem_pairs_of_getByKey [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β)
    (h : m.getByKey a = some b) : (a, b) ∈ m.pairs.toList := by
  unfold getByKey at h
  cases hi : m.indices[a]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    have hbind : (some i >>= (fun j => m.pairs[j]?.map Prod.snd))
                  = m.pairs[i]?.map Prod.snd := rfl
    rw [hbind] at h
    have hlt : i < m.pairs.size := (m.validIndices a hi).1
    have hget? : m.pairs[i]? = some (m.pairs[i]'hlt) := by
      rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
    rw [hget?] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hfstBeq : (m.pairs[i]'hlt).1 == a := (m.validIndices a hi).2
    have hfstEq : (m.pairs[i]'hlt).1 = a := LawfulBEq.eq_of_beq hfstBeq
    rw [Array.mem_toList_iff, Array.mem_iff_getElem]
    refine ⟨i, hlt, ?_⟩
    cases hp : m.pairs[i]'hlt with
    | mk a' b' =>
      rw [hp] at hfstEq h
      simp only at h
      subst hfstEq
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, h⟩

/-- Swapped-order form of `containsKey_insert_iff`. -/
theorem containsKey_insert_iff_or (m : IndexMap α β) (a g : α) (b : β) :
    (m.insert a b).containsKey g ↔ m.containsKey g ∨ (a == g) = true := by
  rw [IndexMap.containsKey_insert_iff]
  constructor
  · rintro (h | h); exact Or.inr h; exact Or.inl h
  · rintro (h | h); exact Or.inr h; exact Or.inl h

/-- `IndexMap.insert a b`: point-lookup at `a` returns `some b`. -/
theorem getByKey_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).getByKey a = some b := by
  have hmem : (a, b) ∈ (m.insert a b).pairs.toList := by
    rw [Array.mem_toList_iff]
    unfold IndexMap.insert
    split
    · exact Array.mem_push_self
    · rename_i _ _ idx h
      have hlt : idx < m.pairs.size := (m.validIndices a h).1
      rw [Array.mem_iff_getElem]
      refine ⟨idx, ?_, ?_⟩
      · rw [Array.size_set]; exact hlt
      · simp [Array.getElem_set_self]
  exact IndexMap.getByKey_of_mem_pairs _ a b hmem

/-- `IndexMap.insert a b`: point-lookup at `a'` with `(a == a') = false` is
unchanged. -/
theorem getByKey_insert_of_beq_false
    (m : IndexMap α β) {a a' : α} (b : β) (hne : (a == a') = false) :
    (m.insert a b).getByKey a' = m.getByKey a' := by
  unfold IndexMap.getByKey IndexMap.insert
  split
  · rename_i _ _ hnone
    show ((m.indices.insert a m.pairs.size)[a']?.bind
        ((m.pairs.push (a, b))[·]?.map Prod.snd)) = _
    rw [Std.HashMap.getElem?_insert]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    cases hi : m.indices[a']? with
    | none => simp [Option.bind]
    | some idx' =>
      have hlt : idx' < m.pairs.size := (m.validIndices a' hi).1
      have hlt_push : idx' < (m.pairs.push (a, b)).size := by
        rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt
      show Option.map Prod.snd (m.pairs.push (a, b))[idx']? =
        Option.map Prod.snd m.pairs[idx']?
      rw [Array.getElem?_eq_getElem hlt_push, Array.getElem?_eq_getElem hlt]
      simp only [Option.map_some]
      congr 1
      rw [Array.getElem_push_lt hlt]
  · rename_i _ _ idx h
    show (m.indices[a']?.bind
        ((m.pairs.set idx (a, b) (m.validIndices a h).1)[·]?.map Prod.snd)) = _
    cases hi : m.indices[a']? with
    | none => simp [Option.bind]
    | some idx' =>
      have hlt' : idx' < m.pairs.size := (m.validIndices a' hi).1
      have hpa : (m.pairs[idx]'(m.validIndices a h).1).1 == a := (m.validIndices a h).2
      have hpa' : (m.pairs[idx']'hlt').1 == a' := (m.validIndices a' hi).2
      have hidx_ne : idx ≠ idx' := by
        intro heq
        subst heq
        have : a == a' := BEq.trans (BEq.symm hpa) hpa'
        rw [this] at hne; cases hne
      have hltSet : idx' < (m.pairs.set idx (a, b) (m.validIndices a h).1).size := by
        rw [Array.size_set]; exact hlt'
      show Option.map Prod.snd (m.pairs.set idx (a, b) (m.validIndices a h).1)[idx']? =
        Option.map Prod.snd m.pairs[idx']?
      rw [Array.getElem?_eq_getElem hltSet, Array.getElem?_eq_getElem hlt']
      simp only [Option.map_some]
      congr 1
      rw [Array.getElem_set_ne (xs := m.pairs) (i := idx) (j := idx')
        (v := (a, b)) (h' := (m.validIndices a h).1) (pj := hlt') hidx_ne]

end Proofs

end IndexMap

end
