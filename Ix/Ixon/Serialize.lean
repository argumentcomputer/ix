import Ix.Common
import Lean.Declaration
import Ix.Address
import Ix.Ixon.Tag

namespace Ixon

abbrev PutM := StateM ByteArray

structure GetState where
  idx : Nat := 0
  bytes : ByteArray := .empty

abbrev GetM := EStateM String GetState

class Serialize (α : Type) where
  put : α → PutM Unit
  get : GetM α

def runPut (p: PutM Unit) : ByteArray := (p.run ByteArray.empty).2

def runGet (getm: GetM A) (bytes: ByteArray) : Except String A :=
  match getm.run { idx := 0, bytes } with
  | .ok a _ => .ok a
  | .error e _ => .error e

def putUInt8 (x: UInt8) : PutM Unit :=
  StateT.modifyGet (fun s => ((), s.push x))

def getUInt8 : GetM UInt8 := do
  let st ← get
  if st.idx < st.bytes.size then
    let b := st.bytes[st.idx]!
    set { st with idx := st.idx + 1 }
    return b
  else
    throw "EOF"

instance : Serialize UInt8 where
  put := putUInt8
  get := getUInt8

def putUInt16LE (x: UInt16) : PutM Unit := do
  List.forM (List.range 2) fun i =>
    let b := UInt16.toUInt8 (x >>> (i.toUInt16 * 8))
    putUInt8 b
  pure ()

def getUInt16LE : GetM UInt16 := do
  let mut x : UInt16 := 0
  for i in List.range 2 do
    let b ← getUInt8
    x := x + (UInt8.toUInt16 b) <<< ((UInt16.ofNat i) * 8)
  pure x

instance : Serialize UInt16 where
  put := putUInt16LE
  get := getUInt16LE

def putUInt32LE (x: UInt32) : PutM Unit := do
  List.forM (List.range 4) fun i =>
    let b := UInt32.toUInt8 (x >>> (i.toUInt32 * 8))
    putUInt8 b
  pure ()

def getUInt32LE : GetM UInt32 := do
  let mut x : UInt32 := 0
  for i in List.range 4 do
    let b ← getUInt8
    x := x + (UInt8.toUInt32 b) <<< ((UInt32.ofNat i) * 8)
  pure x

instance : Serialize UInt32 where
  put := putUInt32LE
  get := getUInt32LE

def putUInt64LE (x: UInt64) : PutM Unit := do
  List.forM (List.range 8) fun i =>
    let b := UInt64.toUInt8 (x >>> (i.toUInt64 * 8))
    putUInt8 b
  pure ()

def getUInt64LE : GetM UInt64 := do
  let mut x : UInt64 := 0
  for i in List.range 8 do
    let b ← getUInt8
    x := x + (UInt8.toUInt64 b) <<< ((UInt64.ofNat i) * 8)
  pure x

instance : Serialize UInt64 where
  put := putUInt64LE
  get := getUInt64LE

def putBytes (x: ByteArray) : PutM Unit :=
  StateT.modifyGet (fun s => ((), s.append x))

def getBytes (len: Nat) : GetM ByteArray := do
  let st ← get
  if st.idx + len <= st.bytes.size then
    let chunk := st.bytes.extract st.idx (st.idx + len)
    set { st with idx := st.idx + len }
    return chunk
  else throw s!"EOF: need {len} bytes at index {st.idx}, but size is {st.bytes.size}"

def putTag2 (tag: Tag2) : PutM Unit := do
  putUInt8 (encodeTag2Head tag)
  if tag.size < 8
  then pure ()
  else putBytes (.mk (trimmedLE tag.size))

def getTagSize (large: Bool) (small: UInt8) : GetM UInt64 := do
  if large then (fromTrimmedLE ·.data) <$> getBytes (small.toNat + 1)
  else return small.toNat.toUInt64

def getTag2 : GetM Tag2 := do
  let (flag, largeBit, small) <- decodeTag2Head <$> getUInt8
  let size <- getTagSize largeBit small
  pure (Tag2.mk flag size)

instance : Serialize Tag2 where
  put := putTag2
  get := getTag2

def putTag4 (tag: Tag4) : PutM Unit := do
  putUInt8 (encodeTag4Head tag)
  if tag.size < 8
  then pure ()
  else putBytes (.mk (trimmedLE tag.size))

def getTag4 : GetM Tag4 := do
  let (flag, largeBit, small) <- decodeTag4Head <$> getUInt8
  let size <- getTagSize largeBit small
  pure (Tag4.mk flag size)

instance : Serialize Tag4 where
  put := putTag4
  get := getTag4

def putList [Serialize A] (xs : List A) : PutM Unit := do
  Serialize.put (Tag4.mk 0xA (UInt64.ofNat xs.length))
  List.forM xs Serialize.put

def getList [Serialize A] : GetM (List A) := do
  let tag : Tag4 <- Serialize.get
  match tag with
  | ⟨0xA, size⟩ => do
    List.mapM (λ _ => Serialize.get) (List.range size.toNat)
  | e => throw s!"expected List with tag 0xA, got {repr e}"

instance [Serialize A] : Serialize (List A) where
  put := putList
  get := getList

instance : Serialize ByteArray where
  put x := putList x.toList
  get := ByteArray.mk <$> Array.mk <$> getList

def putMany {A: Type} (put : A -> PutM Unit) (xs: List A) : PutM Unit := 
  List.forM xs put

def getMany {A: Type} (x: UInt64) (getm : GetM A) : GetM (List A) :=
  (List.range x.toNat).mapM (fun _ => getm)

def putString (x: String) : PutM Unit := do
  let bytes := x.toUTF8
  Serialize.put (Tag4.mk 0x7 bytes.size.toUInt64)
  putBytes bytes

def getString' (tag: Tag4) : GetM String := do
  match tag with
  | ⟨0x7, size⟩ => do
    let bs ← getBytes size.toNat
    match String.fromUTF8? bs with
    | .some s => return s
    | .none => throw s!"invalid UTF8 bytes {bs}"
  | e => throw s!"expected String with tag 0x7, got {repr e}"

def getString : GetM String := getTag4 >>= getString'

instance : Serialize String where
  put := putString
  get := getString

def natToBytesLE (x: Nat) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go x x)
  where
    go : Nat -> Nat -> List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x => Nat.toUInt8 x:: go f (x / 256)

def natFromBytesLE (xs: Array UInt8) : Nat :=
  (xs.toList.zipIdx 0).foldl (fun acc (b, i) => acc + (UInt8.toNat b) * 256 ^ i) 0

def putNat (x: Nat) : PutM Unit := do
  let bytes := natToBytesLE x
  putTag4 (Tag4.mk 0x8 bytes.size.toUInt64)
  putBytes { data := bytes }

def getNat' (tag: Tag4) : GetM Nat := do
  match tag with
  | ⟨0x8, size⟩ => do
    let bs ← getBytes size.toNat
    return natFromBytesLE bs.data
  | e => throw s!"expected Nat with tag 0x8, got {repr e}"

def getNat : GetM Nat := getTag4 >>= getNat'

instance : Serialize Nat where
  put := putNat
  get := getNat

def natPackAsAddress (x: Nat) : Option Address := 
  let bytes := natToBytesLE x
  if bytes.size > 32 then .none
  else .some (Address.mk ⟨bytes.append (Array.replicate (32 - bytes.size) 0)⟩)

def natUnpackFromAddress (x: Address) : Nat := 
  natFromBytesLE x.hash.data

def putBool : Bool → PutM Unit
| .false => putUInt8 0
| .true => putUInt8 1

def getBool : GetM Bool := do
  match (← getUInt8) with
  | 0 => return .false
  | 1 => return .true
  | e => throw s!"expected Bool encoding between 0 and 1, got {e}"

instance : Serialize Bool where
  put := putBool
  get := getBool

def packBools (bools : List Bool) : UInt8 :=
  List.foldl
    (λ acc (b, i) => acc ||| (if b then 1 <<< UInt8.ofNat i else 0))
    0
    ((bools.take 8).zipIdx 0)

def unpackBools (n: Nat) (b: UInt8) : List Bool :=
  ((List.range 8).map (λ i => (b &&& (1 <<< UInt8.ofNat i)) != 0)).take n

def putBools: List Bool → PutM Unit := putUInt8 ∘ packBools
def getBools (n: Nat): GetM (List Bool) := unpackBools n <$> getUInt8

instance (priority := default + 100) : Serialize (Bool × Bool) where
  put := fun (a, b) => putBools [a, b]
  get := do match (<- getBools 2) with
    | [a, b] => pure (a, b)
    | e => throw s!"expected packed (Bool × Bool), got {e}" 

instance (priority := default + 101): Serialize (Bool × Bool × Bool) where
  put := fun (a, b, c) => putBools [a, b, c]
  get := do match (<- getBools 3) with
    | [a, b, c] => pure (a, b, c)
    | e => throw s!"expected packed (Bool × Bool × Bool), got {e}" 

instance (priority := default + 102): Serialize (Bool × Bool × Bool × Bool) where
  put := fun (a, b, c,d) => putBools [a, b, c, d]
  get := do match (<- getBools 4) with
    | [a, b, c, d] => pure (a, b, c, d)
    | e => throw s!"expected packed (Bool × Bool × Bool × Bool), got {e}" 

instance (priority := default + 103): Serialize (Bool × Bool × Bool × Bool × Bool) where
  put := fun (a, b, c, d, e) => putBools [a, b, c, d, e]
  get := do match (<- getBools 5) with
    | [a, b, c, d, e] => pure (a, b, c, d, e)
    | e => throw s!"expected packed (Bool × Bool × Bool × Bool × Bool), got {e}" 

instance (priority := default + 104)
  : Serialize (Bool × Bool × Bool × Bool × Bool × Bool) where
  put := fun (a, b, c, d, e, f) => putBools [a, b, c, d, e, f]
  get := do match (<- getBools 6) with
    | [a, b, c, d, e, f] => pure (a, b, c, d, e, f)
    | e => throw s!"expected packed (Bool × Bool × Bool × Bool × Bool × Bool), got {e}" 

instance (priority := default + 106)
  : Serialize (Bool × Bool × Bool × Bool × Bool × Bool × Bool) where
  put := fun (a, b, c, d, e, f, g) => putBools [a, b, c, d, e, f, g]
  get := do match (<- getBools 7) with
    | [a, b, c, d, e, f, g] => pure (a, b, c, d, e, f, g)
    | e => throw s!"expected packed (Bool × Bool × Bool × Bool × Bool × Bool × Bool), got {e}" 

instance (priority := default + 105)
  : Serialize (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) where
  put := fun (a, b, c, d, e, f, g, h) => putBools [a, b, c, d, e, f, g, h]
  get := do match (<- getBools 8) with
    | [a, b, c, d, e, f, g, h] => pure (a, b, c, d, e, f, g, h)
    | e => throw s!"expected packed (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool), got {e}" 

def putQuotKind : Lean.QuotKind → PutM Unit
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

instance : Serialize Lean.QuotKind where
  put := putQuotKind
  get := getQuotKind

def putDefKind : Ix.DefKind → PutM Unit
| .«definition» => putUInt8 0
| .«opaque» => putUInt8 1
| .«theorem» => putUInt8 2

def getDefKind : GetM Ix.DefKind := do
  match (← getUInt8) with
  | 0 => return .definition
  | 1 => return .opaque
  | 2 => return .theorem
  | e => throw s!"expected DefKind encoding between 0 and 3, got {e}"

instance : Serialize Ix.DefKind where
  put := putDefKind
  get := getDefKind

def putBinderInfo : Lean.BinderInfo → PutM Unit
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
  | e => throw s!"expected BinderInfo encoding between 0 and 3, got {e}"

instance : Serialize Lean.BinderInfo where
  put := putBinderInfo
  get := getBinderInfo

def putReducibilityHints : Lean.ReducibilityHints → PutM Unit
| .«opaque» => putUInt8 0
| .«abbrev» => putUInt8 1
| .regular x => putUInt8 2 *> putUInt32LE x

def getReducibilityHints : GetM Lean.ReducibilityHints := do
  match (← getUInt8) with
  | 0 => return .«opaque»
  | 1 => return .«abbrev» 
  | 2 => .regular <$> getUInt32LE
  | e => throw s!"expected ReducibilityHints encoding between 0 and 2, got {e}"

instance : Serialize Lean.ReducibilityHints where
  put := putReducibilityHints
  get := getReducibilityHints

def putDefinitionSafety : Lean.DefinitionSafety → PutM Unit
| .«unsafe» => putUInt8 0
| .«safe» => putUInt8 1
| .«partial» => putUInt8 2

def getDefinitionSafety : GetM Lean.DefinitionSafety := do
  match (← getUInt8) with
  | 0 => return .«unsafe»
  | 1 => return .«safe»
  | 2 => return .«partial» 
  | e => throw s!"expected DefinitionSafety encoding between 0 and 2, got {e}"

instance : Serialize Lean.DefinitionSafety where
  put := putDefinitionSafety
  get := getDefinitionSafety

instance [Serialize A] [Serialize B] : Serialize (A × B) where
  put := fun (a, b) => Serialize.put a *> Serialize.put b
  get := (·,·) <$> Serialize.get <*> Serialize.get

def putOption [Serialize A]: Option A → PutM Unit
| .none => Serialize.put ([] : List A)
| .some x => Serialize.put [x]

def getOption [Serialize A] : GetM (Option A) := do
  match ← Serialize.get with
  | [] => return .none
  | [x] => return .some x
  | _ => throw s!"Expected Option"

instance [Serialize A] : Serialize (Option A) where
  put := putOption
  get := getOption

instance: Serialize Unit where
  put _ := pure ()
  get := pure ()

instance : Serialize Address where
  put x := putBytes x.hash
  get := Address.mk <$> getBytes 32

end Ixon
