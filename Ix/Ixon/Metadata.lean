import Ix.Common
import Ix.Ixon.Serialize
import Ix.Ixon.Expr
import Ix.Address
import Batteries.Data.RBMap

namespace Ixon

structure MetaNode where
  name : Option Lean.Name
  bind : Option Lean.BinderInfo
  link : Option Address
  deriving BEq, Repr, Ord

structure Metadata where
  meta: Batteries.RBMap Nat MetaNode compare
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

def putName (n: Lean.Name): PutM := putArray (putNamePart <$> (nameToParts n))
def getName: GetM Lean.Name := nameFromParts <$> getArray getNamePart

def putMetaNode: MetaNode → PutM
| ⟨n, b, l⟩ => putArray 
  [ putOption putName n,
    putOption putBinderInfo b,
    putOption (putBytes ·.hash) l
  ]

def getMetaNode: GetM MetaNode := do
  let tagByte ← getUInt8
  let tag := UInt8.shiftRight tagByte 4
  let small := UInt8.land tagByte 0b111
  let isLarge := (UInt8.land tagByte 0b1000 != 0)
  match tag with
  | 0xB => do
    let _ ← UInt64.toNat <$> getExprTag isLarge small
    let n ← getOption getName
    let b ← getOption getBinderInfo
    let l ← getOption (Address.mk <$> getBytes 32)
    return MetaNode.mk n b l
  | e => throw s!"expected metanode Array with tag 0xB, got {e}"

def putMetadata (m: Metadata) : PutM := putArray (putEntry <$> m.meta.toList)
  where
    putEntry e := putNatl e.fst *> putMetaNode e.snd

def getMetadata : GetM Metadata := do
  let xs <- getArray (Prod.mk <$> getNatl <*> getMetaNode)
  return Metadata.mk (Batteries.RBMap.ofList xs compare)

end Ixon
