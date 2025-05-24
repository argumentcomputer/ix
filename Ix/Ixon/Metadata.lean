import Ix.Common
import Ix.Ixon.Serialize
import Ix.Ixon.Expr
import Ix.Address
import Batteries.Data.RBMap

namespace Ixon

inductive Metadatum where
| name : Lean.Name -> Metadatum
| info : Lean.BinderInfo -> Metadatum
| link : Address -> Metadatum
| hints : Lean.ReducibilityHints -> Metadatum
| all : List Lean.Name -> Metadatum
| mutCtx : List (List Lean.Name) -> Metadatum
deriving BEq, Repr, Ord, Inhabited

structure Metadata where
  map: Batteries.RBMap Nat (List Metadatum) compare
  deriving BEq, Repr

inductive NamePart where
| str (s: String)
| num (n: Nat)
deriving Inhabited

def nameToParts: Lean.Name → List NamePart
| .anonymous => []
| .str n s => NamePart.str s :: nameToParts n
| .num n i => NamePart.num i :: nameToParts n

def nameFromParts: List NamePart → Lean.Name
| [] => .anonymous
| (.str n)::ns => .str (nameFromParts ns) n
| (.num i)::ns => .num (nameFromParts ns) i

def putNamePart : NamePart → PutM
| .str s => putExpr (.strl s)
| .num i => putExpr (.natl i)

def getNamePart : GetM NamePart := do
  match (← getExpr) with
  | .strl s => return (.str s)
  | .natl s => return (.num s)
  | e => throw s!"expected NamePart from .strl or .natl, got {repr e}"

def putName (n: Lean.Name): PutM := putArray putNamePart (nameToParts n)
def getName: GetM Lean.Name := nameFromParts <$> getArray getNamePart

def putMetadatum : Metadatum → PutM
| .name n => putUInt8 0 *> putName n
| .info i => putUInt8 1 *> putBinderInfo i
| .link l => putUInt8 2 *> putBytes l.hash
| .hints h => putUInt8 3 *> putReducibilityHints h
| .all ns => putUInt8 4 *> putArray putName ns
| .mutCtx ctx => putUInt8 5 *> (putArray (putArray putName) ctx)

def getMetadatum : GetM Metadatum := do
  match (<- getUInt8) with
  | 0 => .name <$> getName
  | 1 => .info <$> getBinderInfo
  | 2 => .link <$> (.mk <$> getBytes 32)
  | 3 => .hints <$> getReducibilityHints
  | 4 => .all <$> getArray getName
  | 5 => .mutCtx <$> getArray (getArray getName)
  | e => throw s!"expected Metadatum encoding between 0 and 4, got {e}"

def putMetadata (m: Metadata) : PutM := putArray putEntry m.map.toList
  where
    putEntry e := putNatl e.fst *> putArray putMetadatum e.snd

def getMetadata : GetM Metadata := do
  let xs <- getArray (Prod.mk <$> getNatl <*> getArray getMetadatum)
  return Metadata.mk (Batteries.RBMap.ofList xs compare)

instance : Serialize Metadatum where
  put := runPut ∘ putMetadatum
  get := runGet getMetadatum

end Ixon
