import Blake3
import Ix.Address
import Ix.Meta

structure Commitment (α : Type _) where
  adr : Address
  deriving Inhabited, Lean.ToExpr

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

def persistCommit (secret : Address) (payload : Address) : IO $ Commitment α :=
  let commAdr := Blake3.hash $ secret.hash ++ payload.hash
  -- TODO: persist commitment preimages as private data
  return ⟨⟨commAdr.val⟩⟩

def mkCommitRaw (secret : Address) (type : Lean.Expr) (value : Lean.Expr)
    (consts : Lean.ConstMap) : IO $ Commitment α :=
  persistCommit secret $ computeIxAddress (mkAnonDefInfoRaw type value) consts

def mkCommit [Lean.ToExpr α] (secret : Address) (a : α) (consts : Lean.ConstMap) :
    IO $ Commitment α :=
  persistCommit secret $ computeIxAddress (mkAnonDefInfo a) consts
