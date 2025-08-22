import Ix.Ixon.Serialize

namespace Ixon

-- 0xTTLX_XXXX
inductive Univ where
  -- 0x0X 1
  | const : UInt64 -> Univ
  -- 0x1X ^1
  | var : UInt64 -> Univ
  -- 0x2X (+ x y)
  | add : UInt64 -> Univ -> Univ
  -- 0x30 (max x y)
  | max : Univ -> Univ -> Univ
  -- 0x31 (imax x y)
  | imax : Univ -> Univ -> Univ
  deriving Repr, Inhabited, BEq

open Serialize

def putUniv : Univ -> PutM Unit
  | .const i => put (Tag2.mk 0x0 i)
  | .var i => put (Tag2.mk 0x1 i)
  | .add i x => put (Tag2.mk 0x2 i) *> putUniv x
  | .max x y => put (Tag2.mk 0x3 0) *> putUniv x *> putUniv y
  | .imax x y => put (Tag2.mk 0x3 1) *> putUniv x *> putUniv y

def getUniv : GetM Univ := do
  let st ← get
  go (st.bytes.size - st.idx)
  where
    go : Nat → GetM Univ
    | 0 => throw "Out of fuel"
    | Nat.succ f => do
      let tag ← getTag2
      match tag with
      | ⟨0x0, x⟩ => pure (.const x)
      | ⟨0x1, x⟩ => pure (.var x)
      | ⟨0x2, x⟩ => .add x <$> go f
      | ⟨0x3, 0⟩ => .max <$> go f <*> go f
      | ⟨0x3, 1⟩ => .imax <$> go f <*> go f
      | x => throw s!"Unknown Ixon Universe tag {repr x}"

instance : Serialize Univ where
  put := putUniv
  get := getUniv

end Ixon
