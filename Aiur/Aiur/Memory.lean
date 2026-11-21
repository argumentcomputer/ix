import Aiur.AST

namespace Aiur

/-- A runtime store appends a value; locations are indices, never source field values. -/
abbrev Heap (F : Type) := List (SourceValue F)

/-- The prover supplies one finite heterogeneous table for the whole circuit proof. -/
structure ROM (F : Type) where
  entries : List (F × Value F) := []
  deriving Repr, BEq

def ROM.lookup [DecidableEq F] (rom : ROM F) (type : Ty) (address : F) : Option (Value F) :=
  (rom.entries.find? (fun entry => decide (entry.1 = address ∧ entry.2.type = type))).map Prod.snd

/-- An address determines one value at each nominal type. Opaque pointers of
different types may reuse an address; identical repeated entries are harmless. -/
def ROM.Valid (rom : ROM F) : Prop :=
  ∀ a ∈ rom.entries, ∀ b ∈ rom.entries,
    a.1 = b.1 → a.2.type = b.2.type → a.2 = b.2

instance [DecidableEq F] (rom : ROM F) : Decidable rom.Valid :=
  inferInstanceAs (Decidable (∀ a ∈ rom.entries, ∀ b ∈ rom.entries,
    a.1 = b.1 → a.2.type = b.2.type → a.2 = b.2))

end Aiur
