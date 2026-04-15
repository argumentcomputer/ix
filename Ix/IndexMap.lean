module
public import Ix.Lib
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

@[inline] def size : Nat :=
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

/-- Swapped-order form of `containsKey_insert_iff`. -/
theorem containsKey_insert_iff_or (m : IndexMap α β) (a g : α) (b : β) :
    (m.insert a b).containsKey g ↔ m.containsKey g ∨ (a == g) = true := by
  rw [IndexMap.containsKey_insert_iff]
  constructor
  · rintro (h | h); exact Or.inr h; exact Or.inl h
  · rintro (h | h); exact Or.inr h; exact Or.inl h

end Proofs

/-! ## Generic `foldlM` key-preservation

`List.foldlM` / `IndexMap.foldlM` over an insert-only step function preserves
keys modulo the pairs seen. The three lemmas below package this as
insert-only key-set invariants for folds that build up an `IndexMap`. -/

section FoldlM

variable {α : Type _} {β γ : Type _} [BEq α] [Hashable α]

/-- `List.foldlM` over an `insert`-only step preserves keys modulo pairs seen. -/
theorem List.foldlM_insertKey_iff
    {ε : Type}
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (pairs : List (α × β)) :
    ∀ (init : IndexMap α γ) (result : IndexMap α γ),
    _root_.List.foldlM step init pairs = .ok result →
    (result.containsKey g ↔
     init.containsKey g ∨ ∃ p ∈ pairs, (p.1 == g) = true) := by
  induction pairs with
  | nil =>
    intro init result h
    simp only [_root_.List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons hd tl ih =>
    intro init result h
    simp only [_root_.List.foldlM_cons, bind, Except.bind] at h
    rcases hok : step init hd with _ | acc'
    · rw [hok] at h; simp at h
    · rw [hok] at h
      have hihv := ih acc' result h
      have hkeys := hstep init hd acc' hok g
      constructor
      · intro hres
        rcases hihv.mp hres with h1 | ⟨p, hp, hpe⟩
        · rcases hkeys.mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨hd, _root_.List.mem_cons_self, h2⟩
        · exact Or.inr ⟨p, _root_.List.mem_cons_of_mem _ hp, hpe⟩
      · rintro (h1 | ⟨p, hp, hpe⟩)
        · exact hihv.mpr (Or.inl (hkeys.mpr (Or.inl h1)))
        · rcases _root_.List.mem_cons.mp hp with rfl | htl'
          · exact hihv.mpr (Or.inl (hkeys.mpr (Or.inr hpe)))
          · exact hihv.mpr (Or.inr ⟨p, htl', hpe⟩)

variable [EquivBEq α] [LawfulHashable α]

/-- Specialisation to `init := default`. -/
theorem List.foldlM_insertKey_default_iff
    {ε : Type}
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (pairs : List (α × β)) (result : IndexMap α γ)
    (h : _root_.List.foldlM step default pairs = .ok result) :
    result.containsKey g ↔ ∃ p ∈ pairs, (p.1 == g) = true := by
  have := List.foldlM_insertKey_iff step hstep g pairs default result h
  rw [this]; simp [IndexMap.containsKey_default]

/-- Lift `IndexMap.foldlM` (via its `.pairs : Array`) to `List.foldlM`. -/
theorem indexMap_foldlM_eq_list_foldlM.{ua, ub, us, ue}
    {α : Type ua} {β : Type ub} {State : Type us} {Err : Type ue}
    [BEq α] [Hashable α]
    (m : IndexMap α β) (step : State → α × β → Except Err State) (init : State) :
    m.foldlM (init := init) step =
    _root_.List.foldlM step init m.pairs.toList := by
  unfold IndexMap.foldlM
  rw [← Array.foldlM_toList]

/-- IndexMap-form of `List.foldlM_insertKey_default_iff`. -/
theorem indexMap_foldlM_insertKey_default_iff
    {ε : Type}
    (m : IndexMap α β)
    (step : IndexMap α γ → α × β → Except ε (IndexMap α γ))
    (hstep : ∀ (acc : IndexMap α γ) (p : α × β) (r : IndexMap α γ),
      step acc p = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (p.1 == g) = true)
    (g : α) (result : IndexMap α γ)
    (h : m.foldlM (init := default) step = .ok result) :
    result.containsKey g ↔ ∃ p ∈ m.pairs.toList, (p.1 == g) = true := by
  have hlist : _root_.List.foldlM step default m.pairs.toList = .ok result := by
    have := indexMap_foldlM_eq_list_foldlM (State := IndexMap α γ) (Err := ε) m step default
    rw [this] at h; exact h
  exact List.foldlM_insertKey_default_iff step hstep g m.pairs.toList result hlist

end FoldlM

end IndexMap

end
