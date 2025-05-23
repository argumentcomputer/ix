/-- A map meant for very few entries, preserving insertion order. -/
structure SmallMap (α : Type u) (β : Type v) where
  pairs : Array (α × β)
  deriving Inhabited

namespace SmallMap

variable (m : SmallMap α β) [BEq α] (a : α) (b : β)

def insert : SmallMap α β :=
  match m.pairs.findFinIdx? (·.fst == a) with
  | some idx => ⟨m.pairs.set idx.val (a, b) idx.is_lt⟩
  | none => ⟨m.pairs.push (a, b)⟩

def update (f : β → β) : SmallMap α β :=
  match m.pairs.findFinIdx? (·.fst == a) with
  | some idx => ⟨m.pairs.set idx.val (a, f m.pairs[idx.val].snd) idx.is_lt⟩
  | none => m

@[inline] def get : Option β :=
  Prod.snd <$> m.pairs.find? (·.fst == a)

@[inline] def size : Nat :=
  m.pairs.size

@[inline] def map (f : β → β) : SmallMap α β :=
  ⟨m.pairs.map fun (a, b) => (a, f b)⟩

@[inline] def toList : List (α × β) :=
  m.pairs.toList

end SmallMap
