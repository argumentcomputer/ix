module
public import Std.Data.HashMap

public section

structure IndexMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  pairs : Array (α × β)
  indices : Std.HashMap α Nat
  validIndices : ∀ a : α, indices[a]? = some i → i < pairs.size

namespace IndexMap

variable [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : IndexMap α β) (a : α) (b : β)

instance : Inhabited (IndexMap α β) where
  default :=
    let indices := default
    let pairs := #[]
    have {i} : ∀ (a : α), indices[a]? = some i → i < pairs.size := by
      intro a ha
      have : indices[a]? = none := Std.HashMap.getElem?_empty
      simp [this] at ha
    ⟨pairs, indices, this⟩

def insert : IndexMap α β := by
  refine
    match h : m.indices[a]? with
    | none => ⟨m.pairs.push (a, b), m.indices.insert a m.pairs.size, ?_⟩
    | some idx => ⟨m.pairs.set idx (a, b) (m.validIndices a h), m.indices, ?_⟩
  all_goals
    intro i a' ha'
    simp [Std.HashMap.getElem?_insert] at *
  · split at ha'
    simp_all
    exact Nat.lt_succ_of_lt (m.validIndices a' ha')
  · exact m.validIndices a' ha'

def map (f : β → β) : IndexMap α β := by
  refine ⟨m.pairs.map fun (a, b) => (a, f b), m.indices, ?_⟩
  intro i a' ha'
  rw [Array.size_map]
  exact m.validIndices a' ha'

@[inline] def size : Nat :=
  m.pairs.size

@[inline] def getByKey : Option β :=
  m.indices[a]? >>= (m.pairs[·]?.map Prod.snd)

@[inline] def getByIdx (i : Nat) : Option (α × β) :=
  m.pairs[i]?

@[inline] def getIdxOf : Option Nat :=
  m.indices[a]?

@[inline] def containsKey : Bool :=
  m.indices.contains a

@[inline] def foldl (f : γ → α × β → γ) (init : γ) : γ :=
  m.pairs.foldl f init

@[inline] def foldr (f : α × β → γ → γ) (init : γ) : γ :=
  m.pairs.foldr f init

@[inline] def foldlM [Monad μ] (f : γ → α × β → μ γ) (init : γ) : μ γ :=
  m.pairs.foldlM f init

@[inline] def foldrM [Monad μ] (f : α × β → γ → μ γ) (init : γ) : μ γ :=
  m.pairs.foldrM f init

end IndexMap

end
