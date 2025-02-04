namespace Ixon

class Serialize (A: Type) where
  put : A -> ByteArray
  get : ByteArray -> Except String A

abbrev PutM A := StateM ByteArray A

structure GetState where
  index : Nat
  bytes : ByteArray

abbrev GetM A := EStateM String GetState A

def runGet (getm: GetM A) (bytes: ByteArray) : Except String A :=
  match EStateM.run getm { index := 0, bytes } with
  | .ok a _ => .ok a
  | .error e _ => .error e

def runPut (putm: PutM A) : ByteArray :=
  (·.2) <$> StateT.run putm ByteArray.empty

def putUInt8 (x: UInt8) : PutM UInt8 := StateT.modifyGet (fun s => (x, s.push x))

def getUInt8 : GetM UInt8 := do
  let st ← get
  if st.index < st.bytes.size then
    let b := st.bytes[st.index]!
    set { st with index := st.index + 1 }
    return b
  else
    throw "EOF"

def getBytes (len: Nat) : GetM ByteArray := do
  let st ← get
  if st.index + len <= st.bytes.size then
    let chunk := st.bytes.extract st.index (st.index + len)
    set { st with index := st.index + len }
    return chunk
  else throw s!"EOF: need {len} bytes at index {st.index}, but size is {st.bytes.size}"


def byteCount (x: UInt64) : UInt8 :=
  if      x < 0x0000000000000100 then 1
  else if x < 0x0000000000010000 then 2
  else if x < 0x0000000001000000 then 3
  else if x < 0x0000000100000000 then 4
  else if x < 0x0000010000000000 then 5
  else if x < 0x0001000000000000 then 6
  else if x < 0x0100000000000000 then 7
  else 8

def trimmedLE (x: UInt64) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go 8 x)
  where
    go : Nat -> UInt64 -> List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x =>
      Nat.toUInt8 (UInt64.toNat x) :: go f (UInt64.shiftRight x 8)

def fromTrimmedLE (xs: Array UInt8) : UInt64 := List.foldr step 0 xs.toList
  where
    step byte acc := UInt64.shiftLeft acc 8 + Nat.toUInt64 (UInt8.toNat byte)

def putTrimmedLE (x: UInt64) : PutM UInt64 := do
  let _ <- List.mapM putUInt8 (trimmedLE x).toList
  pure x

end Ixon
