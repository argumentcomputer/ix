import Ix.Basic

structure Commitment (α : Type) where
  digest : Digest
  deriving Inhabited

opaque commit (secret : Digest) (payload : α) : Commitment α
opaque secret (comm : Commitment α) : Digest
opaque reveal [Inhabited α] (comm : Commitment α) : α
opaque revealThen [Inhabited β] (comm : Commitment α) (f : β) : β
