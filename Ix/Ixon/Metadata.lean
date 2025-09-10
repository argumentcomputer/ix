import Ix.Common
import Ix.Ixon.Serialize
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

open Serialize

def putNamePart : NamePart → PutM Unit
| .str s => put s
| .num i => put i

def getNamePart : GetM NamePart := do
  match (← getTag4) with
  | ⟨0x7, x⟩ => .str <$> getString' ⟨0x7, x⟩
  | ⟨0x8, x⟩ => .num <$> getNat' ⟨0x8, x⟩
  | e => throw s!"expected NamePart from 0x7 or 0x8 got {repr e}"

instance : Serialize NamePart where
  put := putNamePart
  get := getNamePart

def putName (n: Lean.Name): PutM Unit := put (nameToParts n)
def getName: GetM Lean.Name := nameFromParts <$> get

instance : Serialize Lean.Name where
  put := putName
  get := getName

def putMetadatum : Metadatum → PutM Unit
| .name n => putUInt8 0 *> putName n
| .info i => putUInt8 1 *> putBinderInfo i
| .link l => putUInt8 2 *> putBytes l.hash
| .hints h => putUInt8 3 *> putReducibilityHints h
| .all ns => putUInt8 4 *> put ns
| .mutCtx ctx => putUInt8 5 *> put ctx

def getMetadatum : GetM Metadatum := do
  match (<- getUInt8) with
  | 0 => .name <$> get
  | 1 => .info <$> get
  | 2 => .link <$> (.mk <$> getBytes 32)
  | 3 => .hints <$> get
  | 4 => .all <$> get
  | 5 => .mutCtx <$> get
  | e => throw s!"expected Metadatum encoding between 0 and 4, got {e}"

instance : Serialize Metadatum where
  put := putMetadatum
  get := getMetadatum

def putMetadata (m: Metadata) : PutM Unit := put m.map.toList

def getMetadata : GetM Metadata := do
  let xs <- Serialize.get
  return Metadata.mk (Batteries.RBMap.ofList xs compare)

instance : Serialize Metadata where
  put := putMetadata
  get := getMetadata

end Ixon
