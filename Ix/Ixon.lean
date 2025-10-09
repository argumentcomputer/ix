import Ix.Address
import Lean.Declaration
import Lean.Data.KVMap

namespace Ixon

-- putter monad
abbrev PutM := StateM ByteArray

structure GetState where
  idx : Nat := 0
  bytes : ByteArray := .empty

-- getter monad
abbrev GetM := EStateM String GetState

-- serialization typeclass
class Serialize (α : Type) where
  put : α → PutM Unit
  get : GetM α

def runPut (p: PutM Unit) : ByteArray := (p.run ByteArray.empty).2

def runGet (getm: GetM A) (bytes: ByteArray) : Except String A :=
  match getm.run { idx := 0, bytes } with
  | .ok a _ => .ok a
  | .error e _ => .error e

def ser [Serialize α] (a: α): ByteArray := runPut (Serialize.put a)
def de [Serialize α] (bytes: ByteArray): Except String α :=
  runGet Serialize.get bytes

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

def getBytesToEnd : GetM ByteArray := do
  let st ← get
  return st.bytes

def getBytes (len: Nat) : GetM ByteArray := do
  let st ← get
  if st.idx + len <= st.bytes.size then
    let chunk := st.bytes.extract st.idx (st.idx + len)
    set { st with idx := st.idx + len }
    return chunk
  else throw s!"EOF: need {len} bytes at index {st.idx}, but size is {st.bytes.size}"

--  F := flag, L := large-bit, X := small-field, A := large_field
-- 0xFFFF_LXXX {AAAA_AAAA, ...}
-- "Tag" means the whole thing
-- "Head" means the first byte of the tag
-- "Flag" means the first nibble of the head
structure Tag4 where
  flag: Fin 16
  size: UInt64
  deriving Inhabited, Repr, BEq, Ord, Hashable

def Tag4.encodeHead (tag: Tag4): UInt8 :=
  let t := UInt8.shiftLeft (UInt8.ofNat tag.flag.val) 4
  if tag.size < 8
  then t + tag.size.toUInt8
  else t + 0b1000 + (tag.size.byteCount - 1)

def flag4_to_Fin16 (x: UInt8) : Fin 16 :=
  ⟨ x.toNat / 16, by
      have h256 : x.toNat < 256 := UInt8.toNat_lt x
      have h : x.toNat < 16 * 16 := by simpa using h256
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  ⟩

def Tag4.decodeHead (head: UInt8) : (Fin 16 × Bool × UInt8) :=
  let flag : Fin 16 := flag4_to_Fin16 head
  let largeBit := UInt8.land head 0b1000 != 0
  let small := head % 0b1000
  (flag, largeBit, small)

def getTagSize (large: Bool) (small: UInt8) : GetM UInt64 := do
  if large then (UInt64.fromTrimmedLE ·.data) <$> getBytes (small.toNat + 1)
  else return small.toNat.toUInt64

def putTag4 (tag: Tag4) : PutM Unit := do
  putUInt8 (Tag4.encodeHead tag)
  if tag.size < 8
  then pure ()
  else putBytes (.mk (UInt64.trimmedLE tag.size))

def getTag4 : GetM Tag4 := do
  let (flag, largeBit, small) <- Tag4.decodeHead <$> getUInt8
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

def putBytesTagged (x: ByteArray) : PutM Unit := Serialize.put x.toList
def getBytesTagged : GetM ByteArray := (.mk ∘ .mk) <$> Serialize.get

instance : Serialize ByteArray where
  put := putBytesTagged
  get := getBytesTagged

def putMany {A: Type} (put : A -> PutM Unit) (xs: List A) : PutM Unit :=
  List.forM xs put

def getMany {A: Type} (x: Nat) (getm : GetM A) : GetM (List A) :=
  (List.range x).mapM (fun _ => getm)

def puts {A: Type} [Serialize A] (xs: List A) : PutM Unit :=
  putMany Serialize.put xs

def gets {A: Type} [Serialize A] (x: Nat) : GetM (List A) :=
  getMany x Serialize.get

-- parameterized on a way to put a ByteArray
def putString (put: ByteArray -> PutM Unit) (x: String) : PutM Unit :=
  put x.toUTF8

def getString (get: GetM ByteArray) : GetM String := do
  let bytes <- get
  match String.fromUTF8? bytes with
  | .some s => return s
  | .none => throw s!"invalid UTF8 bytes {bytes}"

instance : Serialize String where
  put := putString putBytesTagged
  get := getString getBytesTagged

-- parameterized on a way to put a ByteArray
def putNat (put: ByteArray -> PutM Unit) (x: Nat) : PutM Unit :=
  let bytes := x.toBytesLE
  put { data := bytes }

def getNat (get: GetM ByteArray) : GetM Nat := do
  let bytes <- get
  return Nat.fromBytesLE bytes.data

instance : Serialize Nat where
  put := putNat putBytesTagged
  get := getNat getBytesTagged

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

instance : Serialize MetaAddress where
  put x := Serialize.put x.data *> Serialize.put x.meta
  get := MetaAddress.mk <$> Serialize.get <*> Serialize.get

structure Quotient where
  kind : Lean.QuotKind
  lvls : Nat
  type : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Quotient where
  put := fun x => Serialize.put (x.kind, x.lvls, x.type)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Axiom where
  isUnsafe: Bool
  lvls : Nat
  type : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Axiom where
  put := fun x => Serialize.put (x.isUnsafe, x.lvls, x.type)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure Definition where
  kind : Ix.DefKind
  safety : Lean.DefinitionSafety
  lvls : Nat
  type : Address
  value : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Definition where
  put x := Serialize.put (x.kind, x.safety, x.lvls, x.type, x.value)
  get := (fun (a,b,c,d,e) => .mk a b c d e) <$> Serialize.get

structure Constructor where
  isUnsafe: Bool
  lvls : Nat
  cidx : Nat
  params : Nat
  fields : Nat
  type : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Constructor where
  put x := Serialize.put (x.isUnsafe, x.lvls, x.cidx, x.params, x.fields, x.type)
  get := (fun (a,b,c,d,e,f) => .mk a b c d e f) <$> Serialize.get

structure RecursorRule where
  fields : Nat
  rhs : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize RecursorRule where
  put x := Serialize.put (x.fields, x.rhs)
  get := (fun (a,b) => .mk a b) <$> Serialize.get

structure Recursor where
  k : Bool
  isUnsafe: Bool
  lvls : Nat
  params : Nat
  indices : Nat
  motives : Nat
  minors : Nat
  type : Address
  rules : List RecursorRule
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Recursor where
  put x := Serialize.put ((x.k, x.isUnsafe), x.lvls, x.params, x.indices, x.motives, x.minors, x.type, x.rules)
  get := (fun ((a,b),c,d,e,f,g,h,i) => .mk a b c d e f g h i) <$> Serialize.get

structure Inductive where
  recr : Bool
  refl : Bool
  isUnsafe: Bool
  lvls : Nat
  params : Nat
  indices : Nat
  nested : Nat
  type : Address
  ctors : List Constructor
  recrs : List Recursor
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Inductive where
  put x := Serialize.put ((x.recr,x.refl,x.isUnsafe), x.lvls, x.params, x.indices, x.nested, x.type, x.ctors, x.recrs)
  get := (fun ((a,b,c),d,e,f,g,h,i,j) => .mk a b c d e f g h i j) <$> Serialize.get

structure InductiveProj where
  idx : Nat
  block : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize InductiveProj where
  put := fun x => Serialize.put (x.idx, x.block)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure ConstructorProj where
  idx : Nat
  cidx : Nat
  block : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize ConstructorProj where
  put := fun x => Serialize.put (x.idx, x.cidx, x.block)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure RecursorProj where
  idx : Nat
  ridx : Nat
  block : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize RecursorProj where
  put := fun x => Serialize.put (x.idx, x.ridx, x.block)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

structure DefinitionProj where
  idx : Nat
  block : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize DefinitionProj where
  put := fun x => Serialize.put (x.idx, x.block)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Comm where
  put := fun x => Serialize.put (x.secret, x.payload)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure Env where
  env : List MetaAddress
  deriving BEq, Repr, Inhabited, Ord, Hashable

instance : Serialize Env where
  put x := Serialize.put x.env
  get := .mk <$> Serialize.get

structure EvalClaim where
  lvls : Address
  input: Address
  output: Address
  type : Address
deriving BEq, Repr, Inhabited, Ord, Hashable

structure CheckClaim where
  lvls : Address
  type : Address
  value : Address
deriving BEq, Repr, Inhabited, Ord, Hashable

inductive Claim where
| evals : EvalClaim -> Claim
| checks : CheckClaim -> Claim
deriving BEq, Repr, Inhabited, Ord, Hashable

instance : ToString CheckClaim where
  toString x := s!"#{x.value} : #{x.type} @ #{x.lvls}"

instance : ToString EvalClaim where
  toString x := s!"#{x.input} ~> #{x.output} : #{x.type} @ #{x.lvls}"

instance : ToString Claim where
  toString
  | .checks x => toString x
  | .evals x => toString x

instance : Serialize CheckClaim where
  put x := Serialize.put (x.lvls, x.type, x.value)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

instance : Serialize EvalClaim where
  put x := Serialize.put (x.lvls, x.input, x.output, x.type)
  get := (fun (w,x,y,z) => .mk w x y z) <$> Serialize.get

instance : Serialize Claim where
  put
  | .evals x => putTag4 ⟨0xE, 1⟩ *> Serialize.put x
  | .checks x => putTag4 ⟨0xE, 2⟩ *> Serialize.put x
  get := do match <- getTag4 with
  | ⟨0xE,1⟩ => .evals <$> Serialize.get
  | ⟨0xE,2⟩ => .checks <$> Serialize.get
  | e => throw s!"expected Claim with tag 0xE2 or 0xE3, got {repr e}"

structure Proof where
  claim: Claim
  /-- Bytes of the Binius proof -/
  bin : ByteArray
  deriving Inhabited, BEq, Ord, Hashable

instance : ToString Proof where
  toString p := s!"<{toString p.claim} := {hexOfBytes p.bin}>"

instance : Repr Proof where
  reprPrec p _ := toString p

instance : Serialize Proof where
  put := fun x => Serialize.put (x.claim, x.bin)
  get := (fun (x,y) => .mk x y) <$> Serialize.get

structure Substring where
  str: Address
  startPos: Nat
  stopPos: Nat

instance : Serialize Substring where
  put := fun x => Serialize.put (x.str, x.startPos, x.stopPos)
  get := (fun (x,y,z) => .mk x y z) <$> Serialize.get

inductive SourceInfo where
| original (leading: Substring) (pos: Nat) (trailing: Substring) (endPos: Nat)
| synthetic (pos endPos: Nat) (canonical: Bool)
| none

open Serialize
def putSourceInfo : SourceInfo → PutM Unit
| .original l p t e => putUInt8 0 *> put l *> put p *> put t *> put e
| .synthetic p e c => putUInt8 1 *> put p *> put e *> put c
| .none => putUInt8 2

def getSourceInfo : GetM SourceInfo := do
  match (← getUInt8) with
  | 0 => .original <$> get <*> get <*> get <*> get
  | 1 => .synthetic <$> get <*> get <*> get
  | 2 => pure .none
  | e => throw s!"expected SourceInfo encoding between 0 and 2, got {e}"

instance : Serialize SourceInfo where
  put := putSourceInfo
  get := getSourceInfo

inductive Preresolved where
| «namespace» (ns: Address)
| decl (n: Address) (fields: List Address)

def putPreresolved : Preresolved → PutM Unit
| .namespace ns => putUInt8 0 *> put ns
| .decl n fs => putUInt8 1 *> put n *> put fs

def getPreresolved : GetM Preresolved := do
  match (← getUInt8) with
  | 0 => .namespace <$> get
  | 1 => .decl <$> get <*> get
  | e => throw s!"expected Preresolved encoding between 0 and 2, got {e}"

instance : Serialize Preresolved where
  put := putPreresolved
  get := getPreresolved

inductive Syntax where
| missing
| node (info: SourceInfo) (kind: Address) (args: List Address)
| atom (info: SourceInfo) (val: Address)
| ident (info: SourceInfo) (rawVal: Substring) (val: Address) (preresolved: List Preresolved)

def putSyntax : Syntax → PutM Unit
| .missing => putUInt8 0
| .node i k as => putUInt8 1 *> put i *> put k *> put as
| .atom i v => putUInt8 2 *> put i *> put v
| .ident i r v ps => putUInt8 3 *> put i *> put r *> put v *> put ps

def getSyntax : GetM Syntax := do
  match (← getUInt8) with
  | 0 => pure .missing
  | 1 => .node <$> get <*> get <*> get
  | 2 => .atom <$> get <*> get
  | 3 => .ident <$> get <*> get <*> get <*> get
  | e => throw s!"expected Syntax encoding between 0 and 2, got {e}"

instance : Serialize Syntax where
  put := putSyntax
  get := getSyntax

def putInt : Int -> PutM Unit
| .ofNat n => putUInt8 0 *> put n
| .negSucc n => putUInt8 1 *> put n

def getInt : GetM Int := do
  match (<- getUInt8) with
  | 0 => .ofNat <$> get
  | 1 => .negSucc <$> get
  | e => throw s!"expected Int encoding between 0 and 1, got {e}"

instance : Serialize Int where
  put := putInt
  get := getInt

inductive DataValue where
| ofString (v: Address)
| ofBool (v: Bool)
| ofName (v: Address)
| ofNat (v: Address)
| ofInt (v: Address)
| ofSyntax (v: Address)
deriving BEq, Repr, Ord, Inhabited, Ord, Hashable

def putDataValue : DataValue → PutM Unit
| .ofString v => putUInt8 0 *> put v
| .ofBool v => putUInt8 1 *> put v
| .ofName v => putUInt8 2 *> put v
| .ofNat v => putUInt8 3 *> put v
| .ofInt v => putUInt8 4 *> put v
| .ofSyntax v => putUInt8 5 *> put v

def getDataValue : GetM DataValue := do
  match (← getUInt8) with
  | 0 => .ofString <$> get
  | 1 => .ofBool <$> get
  | 2 => .ofName <$> get
  | 3 => .ofNat <$> get
  | 4 => .ofInt <$> get
  | 5 => .ofSyntax <$> get
  | e => throw s!"expected DataValue encoding between 0 and 5, got {e}"

instance : Serialize DataValue where
  put := putDataValue
  get := getDataValue

inductive Metadatum where
| link : Address -> Metadatum
| info : Lean.BinderInfo -> Metadatum
| hints : Lean.ReducibilityHints -> Metadatum
| links : List Address -> Metadatum
| rules : List (Address × Address) -> Metadatum
| kvmap : List (Address × DataValue) -> Metadatum
deriving BEq, Repr, Ord, Inhabited, Ord, Hashable

structure Metadata where
  nodes: List Metadatum
  deriving BEq, Repr, Inhabited, Ord, Hashable

def putMetadatum : Metadatum → PutM Unit
| .link n => putUInt8 0 *> put n
| .info i => putUInt8 1 *> putBinderInfo i
| .hints h => putUInt8 2 *> putReducibilityHints h
| .links ns => putUInt8 3 *> put ns
| .rules ns => putUInt8 4 *> put ns
| .kvmap map => putUInt8 5 *> put map

def getMetadatum : GetM Metadatum := do
  match (<- getUInt8) with
  | 0 => .link <$> get
  | 1 => .info <$> get
  | 2 => .hints <$> get
  | 3 => .links <$> get
  | 4 => .rules <$> get
  | 5 => .kvmap <$> get
  | e => throw s!"expected Metadatum encoding between 0 and 5, got {e}"

instance : Serialize Metadatum where
  put := putMetadatum
  get := getMetadatum

instance : Serialize Metadata where
  put m := put (Tag4.mk 0xF m.nodes.length.toUInt64) *> putMany put m.nodes
  get := do
    let tag <- getTag4
    match tag with
    | ⟨0xF, x⟩ => do
      let nodes <- getMany x.toNat Serialize.get
      return ⟨nodes⟩
    | x => throw s!"Expected metadata tag, got {repr x}"

-- TODO: docs
inductive Ixon where
| nanon : Ixon                                          -- 0x00 anon name
| nstr  : Address -> Address -> Ixon                    -- 0x01 str name
| nnum  : Address -> Address -> Ixon                    -- 0x02 num name
| uzero : Ixon                                          -- 0x03 univ zero
| usucc : Address -> Ixon                               -- 0x04 univ succ
| umax  : Address -> Address -> Ixon                    -- 0x05 univ max
| uimax : Address -> Address -> Ixon                    -- 0x06 univ imax
| uvar  : Nat -> Ixon                                   -- 0x1X
| evar  : Nat -> Ixon                                   -- 0x2X, variables
| eref  : Address -> List Address -> Ixon               -- 0x3X, global reference
| erec  : Nat -> List Address -> Ixon                   -- 0x4X, local recursion
| eprj  : Address -> Nat -> Address -> Ixon             -- 0x5X, structure projection
| esort : Address -> Ixon                               -- 0x90, universes
| estr  : Address -> Ixon                               -- 0x91, utf8 string
| enat  : Address -> Ixon                               -- 0x92, natural number
| eapp  : Address -> Address -> Ixon                    -- 0x93, application
| elam  : Address -> Address -> Ixon                    -- 0x94, lambda
| eall  : Address -> Address -> Ixon                    -- 0x95, forall
| elet  : Bool -> Address -> Address -> Address -> Ixon -- 0x96, 0x97, let
| list : List Ixon -> Ixon                              -- 0xAX, list
| defn : Definition -> Ixon                             -- 0xB0, definition
| axio : Axiom -> Ixon                                  -- 0xB1, axiom
| quot : Quotient -> Ixon                               -- 0xB2, quotient
| cprj : ConstructorProj -> Ixon                        -- 0xB3, ctor projection
| rprj : RecursorProj -> Ixon                           -- 0xB4, recr projection
| iprj : InductiveProj -> Ixon                          -- 0xB5, indc projection
| dprj : DefinitionProj -> Ixon                         -- 0xB6, defn projection
| inds : List Inductive -> Ixon                         -- 0xCX, mutual inductive types
| defs : List Definition -> Ixon                        -- 0xDX, mutual definitions
| prof : Proof -> Ixon                                  -- 0xE0, zero-knowledge proof
| eval : EvalClaim -> Ixon                              -- 0xE1, cryptographic claim
| chck : CheckClaim -> Ixon                             -- 0xE2, cryptographic claim
| comm : Comm -> Ixon                                   -- 0xE3, cryptographic commitment
| envn : Env -> Ixon                                    -- 0xE4, Lean4 environment
| meta : Metadata -> Ixon                               -- 0xFX, Lean4 metadata
deriving BEq, Repr, Inhabited, Ord, Hashable


partial def putIxon : Ixon -> PutM Unit
| .nanon => put (Tag4.mk 0x0 0)
| .nstr n s => put (Tag4.mk 0x0 1) *> put n *> put s
| .nnum n i => put (Tag4.mk 0x0 2) *> put n *> put i
| .uzero => put (Tag4.mk 0x0 3)
| .usucc u => put (Tag4.mk 0x0 4) *> put u
| .umax x y => put (Tag4.mk 0x0 5) *> put x *> put y
| .uimax x y => put (Tag4.mk 0x0 6) *> put x *> put y
| .uvar x =>
  let bytes := x.toBytesLE
  put (Tag4.mk 0x1 bytes.size.toUInt64) *> putBytes ⟨bytes⟩
| .evar x =>
  let bytes := x.toBytesLE
  put (Tag4.mk 0x2 bytes.size.toUInt64) *> putBytes ⟨bytes⟩
| .eref a ls => put (Tag4.mk 0x3 ls.length.toUInt64) *> put a *> puts ls
| .erec i ls =>
  let bytes := i.toBytesLE
  put (Tag4.mk 0x4 bytes.size.toUInt64) *> putBytes ⟨bytes⟩ *> putList ls
| .eprj t n x =>
  let bytes := n.toBytesLE
  put (Tag4.mk 0x5 bytes.size.toUInt64) *> put t *> putBytes ⟨bytes⟩ *> put x
| .esort u => put (Tag4.mk 0x9 0x0) *> put u
| .estr s => put (Tag4.mk 0x9 0x1) *> put s
| .enat n => put (Tag4.mk 0x9 0x2) *> put n
| .eapp f a => put (Tag4.mk 0x9 0x3) *> put f *> put a
| .elam t b => put (Tag4.mk 0x9 0x4) *> put t *> put b
| .eall t b => put (Tag4.mk 0x9 0x5) *> put t *> put b
| .elet nD t d b => if nD
  then put (Tag4.mk 0x9 0x6) *> put t *> put d *> put b
  else put (Tag4.mk 0x9 0x7) *> put t *> put d *> put b
| .list xs => put (Tag4.mk 0xA xs.length.toUInt64) *> (List.forM xs putIxon)
| .defn x => put (Tag4.mk 0xB 0x0) *> put x
| .axio x => put (Tag4.mk 0xB 0x1) *> put x
| .quot x => put (Tag4.mk 0xB 0x2) *> put x
| .cprj x => put (Tag4.mk 0xB 0x3) *> put x
| .rprj x => put (Tag4.mk 0xB 0x4) *> put x
| .iprj x => put (Tag4.mk 0xB 0x5) *> put x
| .dprj x => put (Tag4.mk 0xB 0x6) *> put x
| .inds xs => put (Tag4.mk 0xC xs.length.toUInt64) *> puts xs
| .defs xs => put (Tag4.mk 0xD xs.length.toUInt64) *> puts xs
| .prof x => put (Tag4.mk 0xE 0x0) *> put x
| .eval x => put (Tag4.mk 0xE 0x1) *> put x
| .chck x => put (Tag4.mk 0xE 0x2) *> put x
| .comm x => put (Tag4.mk 0xE 0x3) *> put x
| .envn x => put (Tag4.mk 0xE 0x4) *> put x
| .meta m => put m

def getIxon : GetM Ixon := do
  let st ← MonadState.get
  go (st.bytes.size - st.idx)
  where
    go : Nat → GetM Ixon
    | 0 => throw "Out of fuel"
    | Nat.succ f => do
      let tag <- getTag4
      match tag with
      | ⟨0x0, 0⟩ => pure <| .nanon
      | ⟨0x0, 1⟩ => .nstr <$> get <*> get
      | ⟨0x0, 2⟩ => .nnum <$> get <*> get
      | ⟨0x0, 3⟩ => pure <| .uzero
      | ⟨0x0, 4⟩ => .usucc <$> get
      | ⟨0x0, 5⟩ => .umax <$> get <*> get
      | ⟨0x0, 6⟩ => .uimax <$> get <*> get
      | ⟨0x1, x⟩ => .uvar <$> getNat (getBytes x.toNat)
      | ⟨0x2, x⟩ => .evar <$> getNat (getBytes x.toNat)
      | ⟨0x3, x⟩ => .eref <$> get <*> gets x.toNat
      | ⟨0x4, x⟩ => .erec <$> getNat (getBytes x.toNat) <*> get
      | ⟨0x5, x⟩ => .eprj <$> get <*> getNat (getBytes x.toNat) <*> get
      | ⟨0x9, 0⟩ => .esort <$> get
      | ⟨0x9, 1⟩ => .estr <$> get
      | ⟨0x9, 2⟩ => .enat <$> get
      | ⟨0x9, 3⟩ => .eapp <$> get <*> get
      | ⟨0x9, 4⟩ => .elam <$> get <*> get
      | ⟨0x9, 5⟩ => .eall <$> get <*> get
      | ⟨0x9, 6⟩ => .elet true <$> get <*> get <*> get
      | ⟨0x9, 7⟩ => .elet false <$> get <*> get <*> get
      | ⟨0xA, x⟩ => .list <$> getMany x.toNat (go f)
      | ⟨0xB, 0x0⟩ => .defn <$> get
      | ⟨0xB, 0x1⟩ => .axio <$> get
      | ⟨0xB, 0x2⟩ => .quot <$> get
      | ⟨0xB, 0x3⟩ => .cprj <$> get
      | ⟨0xB, 0x4⟩ => .rprj <$> get
      | ⟨0xB, 0x5⟩ => .iprj <$> get
      | ⟨0xB, 0x6⟩ => .dprj <$> get
      | ⟨0xC, x⟩ => .inds <$> getMany x.toNat get
      | ⟨0xD, x⟩ => .defs <$> getMany x.toNat get
      | ⟨0xE, 0x0⟩ => .prof <$> get
      | ⟨0xE, 0x1⟩ => .eval <$> get
      | ⟨0xE, 0x2⟩ => .chck <$> get
      | ⟨0xE, 0x3⟩ => .comm <$> get
      | ⟨0xE, 0x4⟩ => .envn <$> get
      | ⟨0xF, x⟩ => do
        let nodes <- getMany x.toNat Serialize.get
        return .meta ⟨nodes⟩
      | x => throw s!"Unknown Ixon tag {repr x}"

instance : Serialize Ixon where
  put := putIxon
  get := getIxon

def Ixon.address (ixon: Ixon): Address := Address.blake3 (ser ixon)


--
----section FFI
----
----/--
----# Ixon FFI types
----
----This section defines FFI-friendly versions of the original Ixon datatypes by
----* Replacing `Nat` by `ByteArray` containing the corresponding bytes in LE
----* Replacing `List` by `Array`
----* Replacing maps by `Array`s of pairs
-----/
----
----@[inline] def nat2Bytes (n : Nat) : ByteArray :=
----  ⟨natToBytesLE n⟩
----
----structure DefinitionFFI where
----  kind: Ix.DefKind
----  safety : Lean.DefinitionSafety
----  lvls : ByteArray
----  type : Address
----  value : Address
----
----def Definition.toFFI : Definition → DefinitionFFI
----  | ⟨kind, safety, lvls, type, value⟩ =>
----    ⟨kind, safety, nat2Bytes lvls, type, value⟩
----
----structure AxiomFFI where
----  lvls : ByteArray
----  type : Address
----  isUnsafe: Bool
----
----def Axiom.toFFI : Axiom → AxiomFFI
----  | ⟨isUnsafe, lvls, type⟩ => ⟨nat2Bytes lvls, type, isUnsafe⟩
----
----structure QuotientFFI where
----  lvls : ByteArray
----  type : Address
----  kind : Lean.QuotKind
----
----def Quotient.toFFI : Quotient → QuotientFFI
----  | ⟨kind, lvls, type⟩ => ⟨nat2Bytes lvls, type, kind⟩
----
----structure ConstructorProjFFI where
----  block : Address
----  idx : ByteArray
----  cidx : ByteArray
----
----def ConstructorProj.toFFI : ConstructorProj → ConstructorProjFFI
----  | ⟨idx, cidx, block⟩ => ⟨block, nat2Bytes idx, nat2Bytes cidx⟩
----
----structure RecursorProjFFI where
----  block : Address
----  idx : ByteArray
----  ridx : ByteArray
----
----def RecursorProj.toFFI : RecursorProj → RecursorProjFFI
----  | ⟨idx, ridx, block⟩ => ⟨block, nat2Bytes idx, nat2Bytes ridx⟩
----
----structure InductiveProjFFI where
----  block : Address
----  idx : ByteArray
----
----def InductiveProj.toFFI : InductiveProj → InductiveProjFFI
----  | ⟨idx, block⟩ => ⟨block, nat2Bytes idx⟩
----
----structure DefinitionProjFFI where
----  block : Address
----  idx : ByteArray
----
----def DefinitionProj.toFFI : DefinitionProj → DefinitionProjFFI
----  | ⟨idx, block⟩ => ⟨block, nat2Bytes idx⟩
----
----structure RecursorRuleFFI where
----  fields : ByteArray
----  rhs : Address
----
----def RecursorRule.toFFI : RecursorRule → RecursorRuleFFI
----  | ⟨fields, rhs⟩ => ⟨nat2Bytes fields, rhs⟩
----
----structure RecursorFFI where
----  lvls : ByteArray
----  type : Address
----  params : ByteArray
----  indices : ByteArray
----  motives : ByteArray
----  minors : ByteArray
----  rules : Array RecursorRuleFFI
----  k : Bool
----  isUnsafe: Bool
----
----def Recursor.toFFI : Recursor → RecursorFFI
----  | ⟨k, isUnsafe, lvls, params, indices, motives, minors, type, rules⟩ =>
----    ⟨nat2Bytes lvls, type, nat2Bytes params, nat2Bytes indices,
----      nat2Bytes motives, nat2Bytes minors, rules.toArray.map RecursorRule.toFFI,
----      k, isUnsafe⟩
----
----structure ConstructorFFI where
----  lvls : ByteArray
----  type : Address
----  cidx : ByteArray
----  params : ByteArray
----  fields : ByteArray
----  isUnsafe: Bool
----
----def Constructor.toFFI : Constructor → ConstructorFFI
----  | ⟨isUnsafe, lvls, cidx, params, fields, type⟩ =>
----    ⟨nat2Bytes lvls, type, nat2Bytes cidx, nat2Bytes params, nat2Bytes fields, isUnsafe⟩
----
----structure InductiveFFI where
----  lvls : ByteArray
----  type : Address
----  params : ByteArray
----  indices : ByteArray
----  ctors : Array ConstructorFFI
----  recrs : Array RecursorFFI
----  nested : ByteArray
----  recr : Bool
----  refl : Bool
----  isUnsafe: Bool
----
----def Inductive.toFFI : Inductive → InductiveFFI
----  | ⟨recr, refl, isUnsafe, lvls, params, indices, nested, type, ctors, recrs⟩ =>
----    ⟨nat2Bytes lvls, type, nat2Bytes params, nat2Bytes indices,
----      ctors.toArray.map Constructor.toFFI, recrs.toArray.map Recursor.toFFI,
----      nat2Bytes nested, recr, refl, isUnsafe⟩
----
----inductive NameFFI
----  | anonymous
----  | str : NameFFI → String → NameFFI
----  | num : NameFFI → ByteArray → NameFFI
----
----def _root_.Lean.Name.toFFI : Lean.Name → NameFFI
----  | .anonymous => .anonymous
----  | .str name s => .str name.toFFI s
----  | .num name n => .num name.toFFI (nat2Bytes n)
----
----inductive MetadatumFFI where
----| name : NameFFI -> MetadatumFFI
----| info : Lean.BinderInfo -> MetadatumFFI
----| link : Address -> MetadatumFFI
----| hints : Lean.ReducibilityHints -> MetadatumFFI
----| all : Array NameFFI -> MetadatumFFI
----| mutCtx : Array (Array NameFFI) -> MetadatumFFI
----
----def Metadatum.toFFI : Metadatum → MetadatumFFI
----  | .name n => .name n.toFFI
----  | .info i => .info i
----  | .link addr => .link addr
----  | .hints h => .hints h
----  | .all ns => .all (ns.toArray.map Lean.Name.toFFI)
----  | .mutCtx ctx => .mutCtx $ ctx.toArray.map (·.toArray.map Lean.Name.toFFI)
----
----inductive IxonFFI where
----| vari : UInt64 -> IxonFFI
----| refr : Address -> Array Univ -> IxonFFI
----| recr : UInt64 -> Array Univ -> IxonFFI
----| proj : Address -> UInt64 -> Address -> IxonFFI
----| sort : Univ -> IxonFFI
----| strl : Address -> IxonFFI
----| natl : Address -> IxonFFI
----| appl : Address -> Address -> IxonFFI
----| lamb : Address -> Address -> IxonFFI
----| allE : Address -> Address -> IxonFFI
----| letE : Address -> Address -> Address -> IxonFFI
----| letD : Address -> Address -> Address -> IxonFFI
----| list : Array IxonFFI -> IxonFFI
----| defn : DefinitionFFI -> IxonFFI
----| axio : AxiomFFI -> IxonFFI
----| quot : QuotientFFI -> IxonFFI
----| cprj : ConstructorProjFFI -> IxonFFI
----| rprj : RecursorProjFFI -> IxonFFI
----| iprj : InductiveProjFFI -> IxonFFI
----| dprj : DefinitionProjFFI -> IxonFFI
----| inds : Array InductiveFFI -> IxonFFI
----| defs : Array DefinitionFFI -> IxonFFI
----| meta : Array (ByteArray × (Array MetadatumFFI)) -> IxonFFI
----| prof : Proof -> IxonFFI
----| eval : EvalClaim -> IxonFFI
----| chck : CheckClaim -> IxonFFI
----| comm : Comm -> IxonFFI
----| envn : Array (Address × Address) -> IxonFFI
----
----def Ixon.toFFI : Ixon → IxonFFI
----  | .vari i => .vari i
----  | .sort u => .sort u
----  | .refr addr univs => .refr addr univs.toArray
----  | .recr i us => .recr i us.toArray
----  | .appl f a => .appl f a
----  | .lamb t b => .lamb t b
----  | .allE t b => .allE t b
----  | .proj addr i x => .proj addr i x
----  | .strl s => .strl s
----  | .natl n => .natl n
----  | .letE v t b => .letE v t b
----  | .letD v t b => .letD v t b
----  | .list xs => .list (xs.map Ixon.toFFI).toArray
----  | .defn d => .defn d.toFFI
----  | .axio a => .axio a.toFFI
----  | .quot q => .quot q.toFFI
----  | .cprj c => .cprj c.toFFI
----  | .rprj r => .rprj r.toFFI
----  | .iprj i => .iprj i.toFFI
----  | .dprj d => .dprj d.toFFI
----  | .inds is => .inds (is.map Inductive.toFFI).toArray
----  | .defs d => .defs (d.map Definition.toFFI).toArray
----  | .meta ⟨map⟩ => .meta $ map.toArray.map
----      fun (x, y) => (nat2Bytes x, y.toArray.map Metadatum.toFFI)
----  | .prof p => .prof p
----  | .eval x => .eval x
----  | .chck x => .chck x
----  | .comm x => .comm x
----  | .envn x => .envn x.env.toArray
----
----end FFI
--
end Ixon
