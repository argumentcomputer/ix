import Ix.Ixon.Serialize

namespace Ixon

-- 0xTTTL_XXXX
inductive Univ where
  -- 0x0 1
  | const : UInt64 -> Univ
  -- 0x1 ^1
  | var : UInt64 -> Univ
  -- 0x2 (+ x y)
  | add : UInt64 -> Univ -> Univ
  -- 0x3 (max x y)
  | max : Univ -> Univ -> Univ
  -- 0x4 (imax x y)
  | imax : Univ -> Univ -> Univ
  deriving Repr, Inhabited, BEq

def putUnivTag (tag: UInt8) (val: UInt64) : PutM :=
  let t := UInt8.shiftLeft tag 5
  if val < 16
  then putUInt8 (UInt8.lor t (Nat.toUInt8 (UInt64.toNat val))) *> pure ()
  else do
    putUInt8 (UInt8.lor (UInt8.lor t 0b10000) (byteCount val - 1))
    putTrimmedLE val

def putUniv : Univ -> PutM
  | .const i => putUnivTag 0x0 i
  | .var i => putUnivTag 0x1 i
  | .add i x => putUnivTag 0x2 i *> putUniv x
  | .max x y => putUnivTag 0x3 0 *> putUniv x *> putUniv y
  | .imax x y => putUnivTag 0x4 0 *> putUniv x *> putUniv y

def getUnivTag (isLarge: Bool) (small: UInt8) : GetM UInt64 := do
  if isLarge then (fromTrimmedLE ·.data) <$> getBytes (UInt8.toNat small + 1)
  else return Nat.toUInt64 (UInt8.toNat small)

def getUniv : GetM Univ := do
  let st ← get
  go (st.bytes.size - st.index)
  where
    go : Nat → GetM Univ
    | 0 => throw "Out of fuel"
    | Nat.succ f => do
      let tagByte ← getUInt8
      let tag := UInt8.shiftRight tagByte 5
      let smallSize := UInt8.land tagByte 0b1111
      let isLarge := UInt8.land tagByte 0b10000 != 0
      match tag with
      | 0x0 => .const <$> getUnivTag isLarge smallSize
      | 0x1 => .var <$> getUnivTag isLarge smallSize
      | 0x2 => .add <$> getUnivTag isLarge smallSize <*> go f
      | 0x3 => .max <$> go f <*> go f
      | 0x4 => .imax <$> go f <*> go f
      | x => throw s!"Unknown Ixon Universe tag {x}"

instance : Serialize Univ where
  put := runPut ∘ putUniv
  get := runGet getUniv

end Ixon
