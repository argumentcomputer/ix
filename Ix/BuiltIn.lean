import Ix.Address

structure Commitment (α : Type) where
  adr : Address
  deriving Inhabited

opaque commit (secret : Address) (payload : α) : Commitment α
opaque secret (comm : Commitment α) : Address
opaque reveal [Inhabited α] (comm : Commitment α) : α
opaque revealThen [Inhabited β] (comm : Commitment α) (f : β) : β
