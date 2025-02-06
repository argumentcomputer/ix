namespace Ixon

class Serialize (A: Type) where
  put : A -> ByteArray
  get : ByteArray -> Except String A

abbrev PutM := StateM ByteArray Unit

structure GetState where
  index : Nat
  bytes : ByteArray

abbrev GetM A := EStateM String GetState A

def runGet (getm: GetM A) (bytes: ByteArray) : Except String A :=
  match EStateM.run getm { index := 0, bytes } with
  | .ok a _ => .ok a
  | .error e _ => .error e

def runPut (putm: PutM) : ByteArray :=
  (·.2) <$> StateT.run putm ByteArray.empty

def putUInt8 (x: UInt8) : PutM := StateT.modifyGet (fun s => ((), s.push x))

def putUInt64LE (x: UInt64) : PutM := do
  List.forM (List.range 8) fun i =>
    let b := UInt64.toUInt8 (UInt64.shiftRight x ((UInt64.ofNat i) * 8)) % 256
    putUInt8 b
  pure ()

def putBytes (x: ByteArray) : PutM :=
  StateT.modifyGet (fun s => ((), s.append x))

def getUInt8 : GetM UInt8 := do
  let st ← get
  if st.index < st.bytes.size then
    let b := st.bytes[st.index]!
    set { st with index := st.index + 1 }
    return b
  else
    throw "EOF"

def getUInt64LE : GetM UInt64 := do
  let mut x : UInt64 := 0
  for i in List.range 8 do
    let b ← getUInt8
    x := x + UInt64.shiftLeft (UInt8.toUInt64 b) ((UInt64.ofNat i) * 8)
  pure x

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

def natToBytesLE (x: Nat) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go x x)
  where
    go : Nat -> Nat -> List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x => Nat.toUInt8 x:: go f (x / 256)

def natFromBytesLE (xs: Array UInt8) : Nat :=
  xs.toList.enum.foldl (fun acc (i, b) => acc + (UInt8.toNat b) * 256 ^ i) 0

def fromTrimmedLE (xs: Array UInt8) : UInt64 := List.foldr step 0 xs.toList
  where
    step byte acc := UInt64.shiftLeft acc 8 + Nat.toUInt64 (UInt8.toNat byte)

def putTrimmedLE (x: UInt64) : PutM := List.forM (trimmedLE x).toList putUInt8

def putList {A: Type} (put : A -> PutM) (xs: List A) : PutM := List.forM xs put

def getList {A: Type} (x: UInt64) (getm : GetM A) : GetM (List A) :=
  (List.range x.toNat).mapM (fun _ => getm)

end Ixon
