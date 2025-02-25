import Lean.Declaration

namespace Ixon

-- TODO: move to `Ix`
class Serialize (α : Type) where
  put : α → ByteArray
  get : ByteArray → Except String α

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
    let b := UInt64.toUInt8 (x >>> (i.toUInt64 * 8))
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
    x := x + (UInt8.toUInt64 b) <<< ((UInt64.ofNat i) * 8)
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
    go : Nat → UInt64 → List UInt8
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
    step byte acc := UInt64.shiftLeft acc 8 + (UInt8.toUInt64 byte)

def putTrimmedLE (x: UInt64) : PutM := List.forM (trimmedLE x).toList putUInt8

def putList {A: Type} (put : A -> PutM) (xs: List A) : PutM := List.forM xs put

def getList {A: Type} (x: UInt64) (getm : GetM A) : GetM (List A) :=
  (List.range x.toNat).mapM (fun _ => getm)

def putBool : Bool → PutM
| .false => putUInt8 0
| .true => putUInt8 1

def getBool : GetM Bool := do
  match (← getUInt8) with
  | 0 => return .false
  | 1 => return .true
  | e => throw s!"expected Bool encoding between 0 and 1, got {e}"

def packBools (bools : List Bool) : UInt8 :=
  List.foldl (λ acc (i, b) => 
    acc ||| (if b then 1 <<< UInt8.ofNat i else 0)) 0 (bools.take 8).enum

def unpackBools (n: Nat) (b: UInt8) : List Bool :=
  ((List.range 8).map (λ i => (b &&& (1 <<< UInt8.ofNat i)) != 0)).take n

def putBools: List Bool → PutM := putUInt8 ∘ packBools
def getBools (n: Nat): GetM (List Bool) := unpackBools n <$> getUInt8

def putQuotKind : Lean.QuotKind → PutM
| .type => putUInt8 0
| .ctor => putUInt8 1
| .lift => putUInt8 2
| .ind => putUInt8 3

def getQuotKind : GetM Lean.QuotKind := do
  match (← getUInt8) with
  | 0 => return .type
  | 1 => return .ctor
  | 2 => return .lift
  | 3 => return .ind
  | e => throw s!"expected QuotKind encoding between 0 and 3, got {e}"

def putBinderInfo : Lean.BinderInfo → PutM
| .default => putUInt8 0
| .implicit => putUInt8 1
| .strictImplicit => putUInt8 2
| .instImplicit => putUInt8 3

def getBinderInfo : GetM Lean.BinderInfo := do
  match (← getUInt8) with
  | 0 => return .default
  | 1 => return .implicit
  | 2 => return .strictImplicit
  | 3 => return .instImplicit
  | e => throw s!"expected QuotKind encoding between 0 and 3, got {e}"

end Ixon
