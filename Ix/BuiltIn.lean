import Blake3
import Ix.Address
import Ix.Meta

structure Commitment (α : Type _) where
  adr : Address
  deriving Inhabited

instance : ToString (Commitment α) where
  toString comm := "c" ++ toString comm.adr

def Commitment.ofString (s : String) : Option $ Commitment α :=
  match s.data with
  | 'c' :: adrChars => .mk <$> Address.ofChars adrChars
  | _ => none

-- TODO: secrets should be 32-bytes long
opaque commit (secret : Address) (payload : α) : Commitment α
opaque secret (comm : Commitment α) : Address
opaque reveal [Inhabited α] (comm : Commitment α) : α
opaque revealThen [Inhabited β] (comm : Commitment α) (f : β) : β

--def commitIO (secret : Address) (payload : α) : IO $ Commitment α :=
--  let payloadAdr := ix_adr payload
--  let bytes := secret.hash ++ payloadAdr.hash
--  let commAdr := Blake3.hash bytes
--  -- TODO: persist commitment preimages as private data
--  return ⟨⟨commAdr.val⟩⟩
