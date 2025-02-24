import Lean

-- TODO: move to a utils namespace
def compareList [Ord α] : List α -> List α -> Ordering
| a::as, b::bs => match compare a b with
  | .eq => compareList as bs
  | x => x
| _::_, [] => .gt
| [], _::_ => .lt
| [], [] => .eq

instance [Ord α] : Ord (List α) where 
  compare := compareList

instance : Ord Lean.Name where
  compare := Lean.Name.quickCmp

deriving instance Ord for Lean.Literal
deriving instance Ord for Lean.BinderInfo
deriving instance Ord for Lean.QuotKind

def UInt8.MAX : UInt64 := 0xFF
def UInt16.MAX : UInt64 := 0xFFFF
def UInt32.MAX : UInt64 := 0xFFFFFFFF
def UInt64.MAX : UInt64 := 0xFFFFFFFFFFFFFFFF


