/-
Extracted from Ix/Ixon.lean at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f, with the Ixon v3 changes from
Ix/Ixon.lean at Ix revision b413cd93a43d75a37c358491ca65cd79f1a2a42c, and the
Ixon v4 codec (TagN integers) from Ix/Ixon.lean at Ix revision
22afee6d9245bd5f974ad59019affed034d84615 (introduced in
0c08dba94d028ca5fd7939de57523ad194513adf).
-/

module
public import IxKernel.Ixon.Types

public section

/-! Pure production Ixon v4 codecs. Anonymous encodings and decoder
behavior are shared with the host; metadata, environments, hashing,
and lazy transport remain in `Ix.Ixon`. -/

namespace Ixon

open Ix (DefKind DefinitionSafety QuotKind)

/-- Stable identifier for the Ixon wire format, version 4 (`Env.VERSION`).
Mirrors Rust `WIRE_FORMAT_ID`. -/
def wireFormatId : String := "ixon-v4"

/-! ## Serialization Monad and Typeclass -/

abbrev PutM := StateM ByteArray

structure GetState where
  idx : Nat := 0
  bytes : ByteArray := .empty

abbrev GetM := EStateM String GetState

class Serialize (α : Type) where
  put : α → PutM Unit
  get : GetM α

def runPut (p : PutM Unit) : ByteArray := (p.run ByteArray.empty).2

def runGet (getm : GetM A) (bytes : ByteArray) : Except String A :=
  match getm.run { idx := 0, bytes } with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Run a decoder against one complete buffer.  Unlike `runGet`, successful
    prefix decoding is rejected when bytes remain. -/
def runGetExact (getm : GetM A) (bytes : ByteArray) : Except String A :=
  match getm.run { idx := 0, bytes } with
  | .ok a state =>
    if state.idx = bytes.size then .ok a
    else .error s!"trailing bytes: consumed {state.idx} of {bytes.size}"
  | .error e _ => .error e

def ser [Serialize α] (a : α) : ByteArray := runPut (Serialize.put a)
def de [Serialize α] (bytes : ByteArray) : Except String α :=
  runGet Serialize.get bytes

/-! ## Serialization Error Type -/

/-- Serialization/deserialization error. Variant order matches Rust SerializeError (tags 0–6). -/
inductive SerializeError where
  | unexpectedEof (expected : String)
  | invalidTag (tag : UInt8) (context : String)
  | invalidFlag (flag : UInt8) (context : String)
  | invalidVariant (variant : UInt64) (context : String)
  | invalidBool (value : UInt8)
  | addressError
  | invalidShareIndex (idx : UInt64) (max : Nat)
  deriving Repr, BEq

def SerializeError.toString : SerializeError → String
  | .unexpectedEof expected => s!"unexpected EOF, expected {expected}"
  | .invalidTag tag context => s!"invalid tag 0x{String.ofList <| tag.toNat.toDigits 16} in {context}"
  | .invalidFlag flag context => s!"invalid flag {flag} in {context}"
  | .invalidVariant variant context => s!"invalid variant {variant} in {context}"
  | .invalidBool value => s!"invalid bool value {value}"
  | .addressError => "address parsing error"
  | .invalidShareIndex idx max => s!"invalid Share index {idx}, max is {max}"

instance : ToString SerializeError := ⟨SerializeError.toString⟩

/-! ## Primitive Serialization -/

def putU8 (x : UInt8) : PutM Unit :=
  StateT.modifyGet (fun s => ((), s.push x))

def getU8 : GetM UInt8 := do
  let st ← get
  if st.idx < st.bytes.size then
    let b := st.bytes[st.idx]!
    set { st with idx := st.idx + 1 }
    return b
  else
    throw "EOF"

instance : Serialize UInt8 where
  put := putU8
  get := getU8

def putU64LE (x : UInt64) : PutM Unit := do
  for i in [0:8] do
    putU8 ((x >>> (i.toUInt64 * 8)).toUInt8)

def getU64LE : GetM UInt64 := do
  let mut x : UInt64 := 0
  for i in [0:8] do
    let b ← getU8
    x := x ||| (b.toUInt64 <<< (i.toUInt64 * 8))
  return x

instance : Serialize UInt64 where
  put := putU64LE
  get := getU64LE

def putBytes (x : ByteArray) : PutM Unit :=
  StateT.modifyGet (fun s => ((), s.append x))

def getBytes (len : Nat) : GetM ByteArray := do
  let st ← get
  if st.idx + len <= st.bytes.size then
    let chunk := st.bytes.extract st.idx (st.idx + len)
    set { st with idx := st.idx + len }
    return chunk
  else throw s!"EOF: need {len} bytes at index {st.idx}, but size is {st.bytes.size}"

instance : Serialize Bool where
  put | .false => putU8 0 | .true => putU8 1
  get := do match ← getU8 with
    | 0 => return .false
    | 1 => return .true
    | e => throw s!"expected Bool (0 or 1), got {e}"

instance : Serialize Address where
  put x := putBytes x.hash
  get := Address.mk <$> getBytes 32

/-! ## Tag Encoding -/

/-- Write the requested low bytes of a `UInt64`, least significant first. -/
def putU64TrimmedLEAux (x : UInt64) : Nat → PutM Unit
  | 0 => pure ()
  | len + 1 => do
    putU8 x.toUInt8
    putU64TrimmedLEAux (x >>> 8) len

/-- Read exactly `len` little-endian bytes into a `UInt64`. -/
def getU64TrimmedLEAux : Nat → GetM UInt64
  | 0 => pure 0
  | len + 1 => do
    let low ← getU8
    let high ← getU64TrimmedLEAux len
    return low.toUInt64 ||| (high <<< 8)

/-! ### TagN: the Ixon integer code

Every integer field of the wire format is a TagN integer: `f = 4` for
expression, constant, environment, commitment, claim and proof headers (the
flag selects the variant), `f = 2` for universe terms and `f = 0` (no flag)
for counts, indices and every other unsigned integer. A TagN integer is one
header byte `[flag : f bits][payload : r = 8 − f bits]` (`f ∈ {0, 2, 4}`)
followed by 0, 1, 2, 3, 4 or 8 little-endian bytes. With `L` the top payload
bit and `M` the next one:

* `L = 0`: the low `r − 1` payload bits are the value (rung 1, `[0, R₁)`,
  `R₁ = 2^(r−1)`);
* `L = 1, M = 0`: the low `r − 2` bits followed by one byte hold `value − R₁`
  (rung 2, `[R₁, R₂)`, `R₂ = R₁ + 2^(r−2+8)`);
* `L = 1, M = 1`: the low `r − 2` bits are a code `c`; `c = 0, 1, 2, 3`
  select 2, 3, 4, 8 following bytes holding `value − R₂`, `value − R₃`,
  `value − R₄`, `value − R₅` (rungs `[R₂, R₃)`, `[R₃, R₄)`, `[R₄, R₅)`,
  `[R₅, R₆)` with `R₃ = R₂ + 2^16`, `R₄ = R₃ + 2^24`, `R₅ = R₄ + 2^32`,
  `R₆ = R₅ + 2^64`); every other code is invalid (none for `f = 4`, whose
  code has two bits).

Each rung starts where the previous one ends, so a value has exactly one
encoding. Rung ends and widths (1, 2, 3, 4, 5, 9 bytes):

| f | R₁ | R₂ | R₃ | R₄ | R₅ |
|---|---|---|---|---|---|
| 0 | 128 | 16512 | 82048 | 16859264 | 4311826560 |
| 2 | 32 | 4128 | 69664 | 16846880 | 4311814176 |
| 4 | 8 | 1032 | 66568 | 16843784 | 4311811080 |

The code itself represents `[0, R₆)`. Since `R₅ < 2^33`, `R₆ > 2^64`: every
`UInt64` is representable for each `f`, and the decoder rejects 8-byte
payloads whose value would reach `2^64`. -/

/-- End of TagN rung 1 for an `f`-bit flag. -/
def tagNEnd1 (f : Nat) : Nat := 2 ^ (8 - f - 1)
/-- End of TagN rung 2 (one trailing byte). -/
def tagNEnd2 (f : Nat) : Nat := tagNEnd1 f + 2 ^ (8 - f - 2 + 8)
/-- End of TagN rung 3 (two trailing bytes). -/
def tagNEnd3 (f : Nat) : Nat := tagNEnd2 f + 2 ^ 16
/-- End of TagN rung 4 (three trailing bytes). -/
def tagNEnd4 (f : Nat) : Nat := tagNEnd3 f + 2 ^ 24
/-- End of TagN rung 5 (four trailing bytes). -/
def tagNEnd5 (f : Nat) : Nat := tagNEnd4 f + 2 ^ 32
/-- End of TagN rung 6 (eight trailing bytes; beyond every `UInt64`). -/
def tagNEnd6 (f : Nat) : Nat := tagNEnd5 f + 2 ^ 64

/-- Byte width of the TagN encoding of `value`: the single width-by-index
function for the TagN code. -/
def tagNByteWidth (f value : Nat) : Nat :=
  if value < tagNEnd1 f then 1
  else if value < tagNEnd2 f then 2
  else if value < tagNEnd3 f then 3
  else if value < tagNEnd4 f then 4
  else if value < tagNEnd5 f then 5
  else 9

/-- A decoded TagN flag and value. -/
structure TagN where
  flag : UInt8
  value : UInt64
  deriving BEq, Repr, Inhabited

/-- Header byte: `flag` in the high `f` bits, `payload` in the low `8 − f`. -/
def tagNHeader (f : Nat) (flag : UInt8) (payload : Nat) : UInt8 :=
  (flag.toNat * 2 ^ (8 - f) + payload).toUInt8

/-- Write `value` in the TagN code with an `f`-bit `flag` (`flag < 2^f`). -/
def putTagN (f : Nat) (flag : UInt8) (value : UInt64) : PutM Unit :=
  let v := value.toNat
  let lead := 2 ^ (8 - f - 1)
  let mbit := 2 ^ (8 - f - 2)
  if v < tagNEnd1 f then
    putU8 (tagNHeader f flag v)
  else if v < tagNEnd2 f then do
    putU8 (tagNHeader f flag (lead + (v - tagNEnd1 f) / 256))
    putU8 ((v - tagNEnd1 f) % 256).toUInt8
  else if v < tagNEnd3 f then do
    putU8 (tagNHeader f flag (lead + mbit))
    putU64TrimmedLEAux (v - tagNEnd2 f).toUInt64 2
  else if v < tagNEnd4 f then do
    putU8 (tagNHeader f flag (lead + mbit + 1))
    putU64TrimmedLEAux (v - tagNEnd3 f).toUInt64 3
  else if v < tagNEnd5 f then do
    putU8 (tagNHeader f flag (lead + mbit + 2))
    putU64TrimmedLEAux (v - tagNEnd4 f).toUInt64 4
  else do
    putU8 (tagNHeader f flag (lead + mbit + 3))
    putU64TrimmedLEAux (v - tagNEnd5 f).toUInt64 8

/-- The multi-byte TagN rungs, selected by the code `c` in the low `8 − f − 2`
header bits. -/
def getTagNWide (f : Nat) (flag : UInt8) (c : Nat) : GetM TagN :=
  if c = 0 then do
    let x ← getU64TrimmedLEAux 2
    pure ⟨flag, (tagNEnd2 f + x.toNat).toUInt64⟩
  else if c = 1 then do
    let x ← getU64TrimmedLEAux 3
    pure ⟨flag, (tagNEnd3 f + x.toNat).toUInt64⟩
  else if c = 2 then do
    let x ← getU64TrimmedLEAux 4
    pure ⟨flag, (tagNEnd4 f + x.toNat).toUInt64⟩
  else if c = 3 then do
    let x ← getU64TrimmedLEAux 8
    if tagNEnd5 f + x.toNat < 2 ^ 64 then
      pure ⟨flag, (tagNEnd5 f + x.toNat).toUInt64⟩
    else
      throw "TagN value exceeds UInt64"
  else
    throw s!"invalid TagN code {c}"

/-- Read a TagN integer with an `f`-bit flag. Invalid codes and values
reaching `2^64` are rejected. -/
def getTagN (f : Nat) : GetM TagN := do
  let b ← getU8
  let flag := (b.toNat / 2 ^ (8 - f)).toUInt8
  let p := b.toNat % 2 ^ (8 - f)
  if p < 2 ^ (8 - f - 1) then
    pure ⟨flag, p.toUInt64⟩
  else if p - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2) then do
    let lo ← getU8
    pure ⟨flag, (tagNEnd1 f + (p - 2 ^ (8 - f - 1)) * 256 + lo.toNat).toUInt64⟩
  else
    getTagNWide f flag (p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2))

/-! ## Contract serialization -/

/-- Counts must fit the remaining input before a reader allocates or iterates. -/
def checkCount (count : UInt64) (minBytes : Nat := 1) : GetM Unit := do
  let st ← get
  if count.toNat * minBytes > st.bytes.size - st.idx then
    throw "count exceeds remaining bytes"

def putValueContract (v : ValueContract) : PutM Unit := putU8 v.toBits

def getValueContract : GetM ValueContract := do
  let bits ← getU8
  let some contract := ValueContract.ofBits? bits
    | throw s!"invalid value contract {bits}"
  return contract

def putBinderContract (b : BinderContract) : PutM Unit := putU8 b.toBits

def getBinderContract : GetM BinderContract := do
  let bits ← getU8
  let some contract := BinderContract.ofBits? bits
    | throw s!"invalid binder contract {bits}"
  return contract

instance : Serialize ValueContract := ⟨putValueContract, getValueContract⟩
instance : Serialize BinderContract := ⟨putBinderContract, getBinderContract⟩

/-! ## Univ Serialization -/

/-- Count successive `.succ` constructors without machine-word overflow. -/
def Univ.succCountNat : Univ → Nat
  | .succ inner => 1 + inner.succCountNat
  | _ => 0

/-- Wire-sized view of `succCountNat`.  The codec well-formedness boundary
    records when this conversion is lossless. -/
def Univ.succCount (u : Univ) : UInt64 := u.succCountNat.toUInt64

/-- Get the base of a .succ chain -/
def Univ.succBase : Univ → Univ
  | .succ inner => inner.succBase
  | u => u

/-- Removing a successor prefix never increases structural size. -/
theorem Univ.succBase_sizeOf_le (u : Univ) :
    sizeOf u.succBase ≤ sizeOf u := by
  induction u with
  | zero => simp [Univ.succBase]
  | succ u ih => simp [Univ.succBase]; omega
  | max a b => simp [Univ.succBase]
  | imax a b => simp [Univ.succBase]
  | var idx => simp [Univ.succBase]

/-- Total universe writer.  Successor telescopes retain the production
    compressed representation; `succBase_sizeOf_le` supplies the non-obvious
    structural decrease. -/
def putUniv : Univ → PutM Unit
  | .zero => putTagN 2 Univ.FLAG_ZERO_SUCC 0
  | u@(.succ _) => do
    putTagN 2 Univ.FLAG_ZERO_SUCC u.succCount
    putUniv u.succBase
  | .max a b => do
    putTagN 2 Univ.FLAG_MAX 0
    putUniv a
    putUniv b
  | .imax a b => do
    putTagN 2 Univ.FLAG_IMAX 0
    putUniv a
    putUniv b
  | .var idx => putTagN 2 Univ.FLAG_VAR idx
termination_by u => sizeOf u
decreasing_by
  all_goals simp_wf
  all_goals try omega
  rename_i inner heq
  subst u
  change sizeOf inner.succBase < 1 + sizeOf inner
  have hbase := Univ.succBase_sizeOf_le inner
  omega

/-- Add `count` successor constructors outside a universe. -/
def Univ.addSucc : Nat → Univ → Univ
  | 0, base => base
  | count + 1, base => .succ (addSucc count base)

/-- Decode the payload selected by one universe tag, using `recur` for every
    recursive child.  Naming the post-tag continuation keeps its wire grammar
    directly available to codec proofs. -/
def getUnivFromTag (recur : GetM Univ) (tag : TagN) : GetM Univ := do
  match tag.flag with
  | 0 =>  -- ZERO_SUCC
    if tag.value == 0 then
      return .zero
    else
      let base ← recur
      return base.addSucc tag.value.toNat
  | 1 =>  -- MAX
    let a ← recur
    let b ← recur
    return .max a b
  | 2 =>  -- IMAX
    let a ← recur
    let b ← recur
    return .imax a b
  | 3 =>  -- VAR
    return .var tag.value
  | f => throw s!"getUniv: invalid flag {f}"

/-- Total universe reader.  Each recursive layer consumes a tag byte, so
    a caller-supplied byte budget is a complete termination measure. -/
def getUnivFuel : Nat → GetM Univ
  | 0 => throw "getUniv: recursion budget exhausted"
  | fuel + 1 => getTagN 2 >>= getUnivFromTag (getUnivFuel fuel)

/-- Decode one universe from the current cursor.  Remaining bytes plus one
    are sufficient fuel because every recursive layer consumes a tag. -/
def getUniv : GetM Univ := do
  let state ← get
  getUnivFuel (state.bytes.size - state.idx + 1)

instance : Serialize Univ where
  put := putUniv
  get := getUniv

/-! ## Expr Serialization -/

/-- Collect all mode/type pairs in a lambda telescope. -/
def Expr.collectLamBinders : Expr → List (BinderContract × Expr) × Expr
  | .lam uses ty body =>
    let (binders, base) := body.collectLamBinders
    ((uses, ty) :: binders, base)
  | e => ([], e)

/-- Collect all mode/type triples in a forall telescope. -/
def Expr.collectAllBinders : Expr → List (BinderContract × ValueContract × Expr) × Expr
  | .all uses owned ty body =>
    let (binders, base) := body.collectAllBinders
    ((uses, owned, ty) :: binders, base)
  | e => ([], e)

/-- Collect all arguments in an application telescope (in application order). -/
def Expr.collectAppArgs : Expr → List Expr × Expr
  | .app f a =>
    let (args, base) := f.collectAppArgs
    (args ++ [a], base)
  | e => ([], e)

/-- Structural node count used to totalize the canonical telescope writer.
    Unlike the generic `sizeOf`, leaf payloads do not contribute: recursive
    descent depends only on the expression tree. -/
def Expr.nodeCount : Expr → Nat
  | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ |
      .share _ => 1
  | .prj _ _ val => val.nodeCount + 1
  | .app fn arg | .lam _ fn arg | .all _ _ fn arg =>
      fn.nodeCount + arg.nodeCount + 1
  | .letE _ ty val body =>
      ty.nodeCount + val.nodeCount + body.nodeCount + 1

/-- The base of a collected lambda telescope has no more nodes than its
    input. -/
theorem Expr.collectLamBinders_base_nodeCount_le (e : Expr) :
    e.collectLamBinders.2.nodeCount ≤ e.nodeCount := by
  induction e with
  | lam uses binder body ihBinder ihBody =>
    simp only [Expr.collectLamBinders, Expr.nodeCount]
    exact Nat.le_trans ihBody <|
      Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    exact Nat.le_refl _

/-- A lambda telescope's base has fewer nodes than a lambda node. -/
theorem Expr.collectLamBinders_base_nodeCount_lt (uses : BinderContract)
    (binder body : Expr) :
    (Expr.lam uses binder body).collectLamBinders.2.nodeCount <
      (Expr.lam uses binder body).nodeCount := by
  simp only [Expr.collectLamBinders]
  have hle := Expr.collectLamBinders_base_nodeCount_le body
  exact Nat.lt_of_le_of_lt hle <|
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_succ_self _)

/-- Every type collected from a lambda telescope has fewer nodes than the
    input. -/
theorem Expr.collectLamBinders_mem_nodeCount_lt (e ty : Expr)
    (h : ∃ uses, (uses, ty) ∈ e.collectLamBinders.1) :
    ty.nodeCount < e.nodeCount := by
  induction e with
  | lam uses binder body ihBinder ihBody =>
    simp only [Expr.collectLamBinders] at h
    rcases h with ⟨u, h⟩
    rcases List.mem_cons.mp h with hhead | htail
    · have hty : ty = binder := congrArg Prod.snd hhead
      subst ty
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_succ_self _)
    · have hlt := ihBody ⟨u, htail⟩
      exact Nat.lt_of_lt_of_le hlt <|
        Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
  | sort | var | ref | recur | prj | str | nat | app | all | letE | share =>
    rcases h with ⟨_, hmem⟩
    exact nomatch hmem

/-- The base of a collected forall telescope has no more nodes than its
    input. -/
theorem Expr.collectAllBinders_base_nodeCount_le (e : Expr) :
    e.collectAllBinders.2.nodeCount ≤ e.nodeCount := by
  induction e with
  | all uses owned binder body ihBinder ihBody =>
    simp only [Expr.collectAllBinders, Expr.nodeCount]
    exact Nat.le_trans ihBody <|
      Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    exact Nat.le_refl _

/-- A forall telescope's base has fewer nodes than a forall node. -/
theorem Expr.collectAllBinders_base_nodeCount_lt (uses : BinderContract) (owned : ValueContract)
    (binder body : Expr) :
    (Expr.all uses owned binder body).collectAllBinders.2.nodeCount <
      (Expr.all uses owned binder body).nodeCount := by
  simp only [Expr.collectAllBinders]
  have hle := Expr.collectAllBinders_base_nodeCount_le body
  exact Nat.lt_of_le_of_lt hle <|
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_succ_self _)

/-- Every type collected from a forall telescope has fewer nodes than the
    input. -/
theorem Expr.collectAllBinders_mem_nodeCount_lt (e ty : Expr)
    (h : ∃ uses owned, (uses, owned, ty) ∈ e.collectAllBinders.1) :
    ty.nodeCount < e.nodeCount := by
  induction e with
  | all uses owned binder body ihBinder ihBody =>
    simp only [Expr.collectAllBinders] at h
    rcases h with ⟨u, o, h⟩
    rcases List.mem_cons.mp h with hhead | htail
    · have hty : ty = binder := congrArg (fun x => x.2.2) hhead
      subst ty
      exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_succ_self _)
    · have hlt := ihBody ⟨u, o, htail⟩
      exact Nat.lt_of_lt_of_le hlt <|
        Nat.le_trans (Nat.le_add_left _ _) (Nat.le_succ _)
  | sort | var | ref | recur | prj | str | nat | app | lam | letE | share =>
    rcases h with ⟨_, _, hmem⟩
    exact nomatch hmem

/-- The head of a collected application telescope has no more nodes than its
    input. -/
theorem Expr.collectAppArgs_base_nodeCount_le (e : Expr) :
    e.collectAppArgs.2.nodeCount ≤ e.nodeCount := by
  induction e with
  | app fn arg ihFn ihArg =>
    simp only [Expr.collectAppArgs, Expr.nodeCount]
    exact Nat.le_trans ihFn <|
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    exact Nat.le_refl _

/-- An application telescope's head has fewer nodes than an app node. -/
theorem Expr.collectAppArgs_base_nodeCount_lt (fn arg : Expr) :
    (Expr.app fn arg).collectAppArgs.2.nodeCount <
      (Expr.app fn arg).nodeCount := by
  simp only [Expr.collectAppArgs]
  have hle := Expr.collectAppArgs_base_nodeCount_le fn
  exact Nat.lt_of_le_of_lt hle <|
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_succ_self _)

/-- Every collected application argument has fewer nodes than the input. -/
theorem Expr.collectAppArgs_mem_nodeCount_lt (e arg : Expr)
    (h : arg ∈ e.collectAppArgs.1) :
    arg.nodeCount < e.nodeCount := by
  induction e with
  | app fn actual ihFn ihActual =>
    simp only [Expr.collectAppArgs] at h
    rcases List.mem_append.mp h with hfn | hactual
    · have hlt := ihFn hfn
      exact Nat.lt_of_lt_of_le hlt <|
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
    · have heq : arg = actual := by simpa using hactual
      subst arg
      exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_succ_self _)
  | sort | var | ref | recur | prj | str | nat | lam | all | letE | share =>
    exact nomatch h

private theorem nodeCount_left_lt_sum3 (left middle right : Nat) :
    left < left + middle + right + 1 :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_add_right left middle)
      (Nat.le_add_right (left + middle) right))
    (Nat.lt_succ_self _)

private theorem nodeCount_middle_lt_sum3 (left middle right : Nat) :
    middle < left + middle + right + 1 :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.le_add_left middle left)
      (Nat.le_add_right (left + middle) right))
    (Nat.lt_succ_self _)

private theorem nodeCount_right_lt_sum3 (left middle right : Nat) :
    right < left + middle + right + 1 :=
  Nat.lt_of_le_of_lt (Nat.le_add_left right (left + middle))
    (Nat.lt_succ_self _)

/-- Total canonical expression writer. Telescope collection preserves the
    Rust byte grammar; the node-count lemmas above expose its recursive calls
    to the kernel termination checker. -/
def putExpr : Expr → PutM Unit
  | .sort idx => putTagN 4 Expr.FLAG_SORT idx
  | .var idx => putTagN 4 Expr.FLAG_VAR idx
  | .ref refIdx univIdxs => do
    -- Rust format: TagN(4, flag, array_len), TagN(0, ref_idx), then elements
    putTagN 4 Expr.FLAG_REF univIdxs.size.toUInt64
    putTagN 0 0 refIdx
    for idx in univIdxs do putTagN 0 0 idx
  | .recur recIdx univIdxs => do
    -- Rust format: TagN(4, flag, array_len), TagN(0, rec_idx), then elements
    putTagN 4 Expr.FLAG_REC univIdxs.size.toUInt64
    putTagN 0 0 recIdx
    for idx in univIdxs do putTagN 0 0 idx
  | .prj typeRefIdx fieldIdx val => do
    -- Rust format: TagN(4, flag, field_idx), TagN(0, type_ref_idx), then val
    putTagN 4 Expr.FLAG_PRJ fieldIdx
    putTagN 0 0 typeRefIdx
    putExpr val
  | .str refIdx => putTagN 4 Expr.FLAG_STR refIdx
  | .nat refIdx => putTagN 4 Expr.FLAG_NAT refIdx
  | e@(.app _ _) => do
    putTagN 4 Expr.FLAG_APP e.collectAppArgs.1.length.toUInt64
    putExpr e.collectAppArgs.2
    for arg in e.collectAppArgs.1 do putExpr arg
  | e@(.lam _ _ _) => do
    putTagN 4 Expr.FLAG_LAM e.collectLamBinders.1.length.toUInt64
    for binder in e.collectLamBinders.1 do
      putU8 binder.1.toBits
      putExpr binder.2
    putExpr e.collectLamBinders.2
  | e@(.all _ _ _ _) => do
    putTagN 4 Expr.FLAG_ALL e.collectAllBinders.1.length.toUInt64
    for binder in e.collectAllBinders.1 do
      putU8 (packAllContract binder.1 binder.2.1)
      putExpr binder.2.2
    putExpr e.collectAllBinders.2
  | .letE contract ty val body => do
    putTagN 4 Expr.FLAG_LET contract.flags
    putBinderContract contract.binder
    putExpr ty
    putExpr val
    putExpr body
  | .share idx => putTagN 4 Expr.FLAG_SHARE idx
termination_by e => e.nodeCount
decreasing_by
  all_goals simp_wf
  all_goals simp only [Expr.nodeCount]
  all_goals try exact Nat.lt_succ_self _
  all_goals try exact nodeCount_left_lt_sum3 _ _ _
  all_goals try exact nodeCount_middle_lt_sum3 _ _ _
  all_goals try exact nodeCount_right_lt_sum3 _ _ _
  · subst e
    simpa only [Expr.nodeCount] using
      Expr.collectAppArgs_base_nodeCount_lt _ _
  · subst e
    rename_i fn actual hmem
    simpa only [Expr.nodeCount] using Expr.collectAppArgs_mem_nodeCount_lt
      (.app fn actual) arg hmem
  · subst e
    rename_i uses ty body hmem
    simpa only [Expr.nodeCount] using Expr.collectLamBinders_mem_nodeCount_lt
      (.lam uses ty body) binder.2 ⟨binder.1, hmem⟩
  · subst e
    simpa only [Expr.nodeCount] using
      Expr.collectLamBinders_base_nodeCount_lt _ _ _
  · subst e
    rename_i uses owned ty body hmem
    simpa only [Expr.nodeCount] using Expr.collectAllBinders_mem_nodeCount_lt
      (.all uses owned ty body) binder.2.2
      ⟨binder.1, binder.2.1, hmem⟩
  · subst e
    simpa only [Expr.nodeCount] using
      Expr.collectAllBinders_base_nodeCount_lt _ _ _ _

/-- Read `count` TagN (`f = 0`) values in wire order. -/
def getTagN0Values : Nat → GetM (List UInt64)
  | 0 => pure []
  | count + 1 => do
    let head := (← getTagN 0).value
    let tail ← getTagN0Values count
    return head :: tail

/-- Read and apply one canonical application argument at a time. -/
def getExprAppArgs (recur : GetM Expr) : Nat → Expr → GetM Expr
  | 0, result => pure result
  | count + 1, result => do
    let arg ← recur
    getExprAppArgs recur count (.app result arg)

/-- Read a lambda telescope in outer-to-inner wire order. -/
def getExprLamBinders (recur : GetM Expr) : Nat → GetM (List (BinderContract × Expr))
  | 0 => pure []
  | count + 1 => do
    let contract ← getBinderContract
    let ty ← recur
    let tail ← getExprLamBinders recur count
    return (contract, ty) :: tail

/-- Read a forall telescope in outer-to-inner wire order. -/
def getExprAllBinders (recur : GetM Expr) :
    Nat → GetM (List (BinderContract × ValueContract × Expr))
  | 0 => pure []
  | count + 1 => do
    let bits ← getU8
    let some (contract, result) := unpackAllContract? bits
      | throw s!"getExpr: invalid forall contract {bits}"
    let ty ← recur
    let tail ← getExprAllBinders recur count
    return (contract, result, ty) :: tail

/-- Parse an expression after its leading TagN (`f = 4`) header. Recursive reads are
    supplied explicitly so `getExprFuel` below remains structurally total. -/
def getExprFromTag (recur : GetM Expr) (tag : TagN) : GetM Expr := do
  match tag.flag with
  | 0x0 => return .sort tag.value
  | 0x1 => return .var tag.value
  | 0x2 => do  -- REF: tag.value is array_len, then ref_idx, then elements
    let refIdx := (← getTagN 0).value
    checkCount tag.value
    let univIdxs ← getTagN0Values tag.value.toNat
    return .ref refIdx univIdxs.toArray
  | 0x3 => do  -- REC: tag.value is array_len, then rec_idx, then elements
    let recIdx := (← getTagN 0).value
    checkCount tag.value
    let univIdxs ← getTagN0Values tag.value.toNat
    return .recur recIdx univIdxs.toArray
  | 0x4 => do  -- PRJ: tag.value is field_idx, then type_ref_idx, then val
    let typeRefIdx := (← getTagN 0).value
    let val ← recur
    return .prj typeRefIdx tag.value val
  | 0x5 => return .str tag.value
  | 0x6 => return .nat tag.value
  | 0x7 => do  -- APP (telescope)
    if tag.value == 0 then
      throw "getExpr: empty app spine"
    checkCount tag.value
    let base ← recur
    match base with
    | .app .. => throw "getExpr: non-canonical app base"
    | _ => pure ()
    getExprAppArgs recur tag.value.toNat base
  | 0x8 => do  -- LAM (telescope)
    if tag.value == 0 then
      throw "getExpr: Lam with zero binders"
    checkCount tag.value 2
    let binders ← getExprLamBinders recur tag.value.toNat
    let body ← recur
    match body with
    | .lam .. => throw "getExpr: non-canonical lam telescope"
    | _ => pure ()
    return binders.foldr (fun (uses, ty) result => .lam uses ty result) body
  | 0x9 => do  -- ALL (telescope)
    if tag.value == 0 then
      throw "getExpr: All with zero binders"
    checkCount tag.value 2
    let binders ← getExprAllBinders recur tag.value.toNat
    let body ← recur
    match body with
    | .all .. => throw "getExpr: non-canonical all telescope"
    | _ => pure ()
    return binders.foldr
      (fun (uses, owned, ty) result => .all uses owned ty result) body
  | 0xA => do  -- LET
    if tag.value > 3 then
      throw s!"getExpr: invalid let flags {tag.value}"
    let binder ← getBinderContract
    let some contract := LetContract.ofFlags? tag.value binder
      | throw "getExpr: invalid let flags"
    let ty ← recur
    let val ← recur
    let body ← recur
    return .letE contract ty val body
  | 0xB => return .share tag.value
  | f => throw s!"getExpr: invalid flag {f}"

/-- Total expression reader. Every recursive layer consumes a TagN (`f = 4`) header
    header, so a caller-supplied byte budget is a complete termination
    measure even for telescope-compressed applications and binders. -/
def getExprFuel : Nat → GetM Expr
  | 0 => throw "getExpr: recursion budget exhausted"
  | fuel + 1 => getTagN 4 >>= getExprFromTag (getExprFuel fuel)

/-- Decode one expression from the current cursor. Remaining bytes plus one
    are sufficient fuel because every recursive expression consumes a tag. -/
def getExpr : GetM Expr := do
  let state ← get
  getExprFuel (state.bytes.size - state.idx + 1)

instance : Serialize Expr where
  put := putExpr
  get := getExpr

/-! ## Constant Type Serialization -/

def packBools (bs : List Bool) : UInt8 :=
  bs.zipIdx.foldl (fun acc (b, i) =>
    if b then acc ||| ((1 : UInt8) <<< (UInt8.ofNat i)) else acc) 0

def unpackBools (n : Nat) (byte : UInt8) : List Bool :=
  (List.range n).map fun i => (byte &&& ((1 : UInt8) <<< (UInt8.ofNat i))) != 0

def packDefKindSafety (kind : DefKind) (safety : DefinitionSafety) : UInt8 :=
  let k : UInt8 := match kind with | .defn => 0 | .opaq => 1 | .thm => 2
  let s : UInt8 := match safety with | .unsaf => 0 | .safe => 1 | .part => 2
  (k <<< 2) ||| s

def unpackDefKindSafety (b : UInt8) : DefKind × DefinitionSafety :=
  let kind := match b >>> 2 with | 0 => .defn | 1 => .opaq | _ => .thm
  let safety := match b &&& 0x3 with | 0 => .unsaf | 1 => .safe | _ => .part
  (kind, safety)

def putDefinition (d : Definition) : PutM Unit := do
  putU8 (packDefKindSafety d.kind d.safety)
  putTagN 0 0 d.lvls
  putExpr d.typ
  putExpr d.value

def getDefinition : GetM Definition := do
  let flags ← getU8
  if flags >>> 2 > 2 || (flags &&& 3) > 2 then
    throw "invalid definition kind/safety"
  let (kind, safety) := unpackDefKindSafety flags
  let lvls := (← getTagN 0).value
  let typ ← getExpr
  let value ← getExpr
  return ⟨kind, safety, lvls, typ, value⟩

instance : Serialize Definition where
  put := putDefinition
  get := getDefinition

def putRecursorRule (r : RecursorRule) : PutM Unit := do
  putTagN 0 0 r.fields
  putExpr r.rhs

def getRecursorRule : GetM RecursorRule := do
  let fields := (← getTagN 0).value
  let rhs ← getExpr
  return ⟨fields, rhs⟩

instance : Serialize RecursorRule where
  put := putRecursorRule
  get := getRecursorRule

def putRecursor (r : Recursor) : PutM Unit := do
  putU8 (packBools [r.k, r.isUnsafe])
  putTagN 0 0 r.lvls
  putTagN 0 0 r.params
  putTagN 0 0 r.indices
  putTagN 0 0 r.motives
  putTagN 0 0 r.minors
  putExpr r.typ
  putTagN 0 0 r.rules.size.toUInt64
  for rule in r.rules do putRecursorRule rule

def getRecursor : GetM Recursor := do
  let flags ← getU8
  if flags > 3 then throw "invalid recursor flags"
  let bools := unpackBools 2 flags
  let k := bools[0]!
  let isUnsafe := bools[1]!
  let lvls := (← getTagN 0).value
  let params := (← getTagN 0).value
  let indices := (← getTagN 0).value
  let motives := (← getTagN 0).value
  let minors := (← getTagN 0).value
  let typ ← getExpr
  let numRules := (← getTagN 0).value.toNat
  checkCount numRules.toUInt64 2
  let mut rules := #[]
  for _ in [0:numRules] do
    rules := rules.push (← getRecursorRule)
  return ⟨k, isUnsafe, lvls, params, indices, motives, minors, typ, rules⟩

instance : Serialize Recursor where
  put := putRecursor
  get := getRecursor

def putAxiom (a : Axiom) : PutM Unit := do
  putU8 (if a.isUnsafe then 1 else 0)
  putTagN 0 0 a.lvls
  putExpr a.typ

def getAxiom : GetM Axiom := do
  let isUnsafe ← Serialize.get
  let lvls := (← getTagN 0).value
  let typ ← getExpr
  return ⟨isUnsafe, lvls, typ⟩

instance : Serialize Axiom where
  put := putAxiom
  get := getAxiom

def putQuotient (q : Quotient) : PutM Unit := do
  let k : UInt8 := match q.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
  putU8 k
  putTagN 0 0 q.lvls
  putExpr q.typ

def getQuotient : GetM Quotient := do
  let v ← getU8
  let k : QuotKind ← match v with
    | 0 => pure .type | 1 => pure .ctor | 2 => pure .lift | 3 => pure .ind
    | _ => throw s!"invalid QuotKind tag {v}"
  let lvls := (← getTagN 0).value
  let typ ← getExpr
  return ⟨k, lvls, typ⟩

instance : Serialize Quotient where
  put := putQuotient
  get := getQuotient

def putConstructor (c : Constructor) : PutM Unit := do
  putU8 (if c.isUnsafe then 1 else 0)
  putTagN 0 0 c.lvls
  putTagN 0 0 c.cidx
  putTagN 0 0 c.params
  putTagN 0 0 c.fields
  putExpr c.typ

def getConstructor : GetM Constructor := do
  let isUnsafe ← Serialize.get
  let lvls := (← getTagN 0).value
  let cidx := (← getTagN 0).value
  let params := (← getTagN 0).value
  let fields := (← getTagN 0).value
  let typ ← getExpr
  return ⟨isUnsafe, lvls, cidx, params, fields, typ⟩

instance : Serialize Constructor where
  put := putConstructor
  get := getConstructor

def putInductive (i : Inductive) : PutM Unit := do
  putU8 (packBools [i.isUnsafe])
  putTagN 0 0 i.lvls
  putTagN 0 0 i.params
  putTagN 0 0 i.indices
  putExpr i.typ
  putTagN 0 0 i.ctors.size.toUInt64
  for c in i.ctors do putConstructor c

def getInductive : GetM Inductive := do
  let isUnsafe ← Serialize.get
  let lvls := (← getTagN 0).value
  let params := (← getTagN 0).value
  let indices := (← getTagN 0).value
  let typ ← getExpr
  let numCtors := (← getTagN 0).value.toNat
  checkCount numCtors.toUInt64 6
  let mut ctors := #[]
  for _ in [0:numCtors] do
    ctors := ctors.push (← getConstructor)
  return ⟨isUnsafe, lvls, params, indices, typ, ctors⟩

instance : Serialize Inductive where
  put := putInductive
  get := getInductive

def putInductiveProj (p : InductiveProj) : PutM Unit := do
  putTagN 0 0 p.idx
  Serialize.put p.block

def getInductiveProj : GetM InductiveProj := do
  let idx := (← getTagN 0).value
  let block ← Serialize.get
  return ⟨idx, block⟩

instance : Serialize InductiveProj where
  put := putInductiveProj
  get := getInductiveProj

def putConstructorProj (p : ConstructorProj) : PutM Unit := do
  putTagN 0 0 p.idx
  putTagN 0 0 p.cidx
  Serialize.put p.block

def getConstructorProj : GetM ConstructorProj := do
  let idx := (← getTagN 0).value
  let cidx := (← getTagN 0).value
  let block ← Serialize.get
  return ⟨idx, cidx, block⟩

instance : Serialize ConstructorProj where
  put := putConstructorProj
  get := getConstructorProj

def putRecursorProj (p : RecursorProj) : PutM Unit := do
  putTagN 0 0 p.idx
  Serialize.put p.block

def getRecursorProj : GetM RecursorProj := do
  let idx := (← getTagN 0).value
  let block ← Serialize.get
  return ⟨idx, block⟩

instance : Serialize RecursorProj where
  put := putRecursorProj
  get := getRecursorProj

def putDefinitionProj (p : DefinitionProj) : PutM Unit := do
  putTagN 0 0 p.idx
  Serialize.put p.block

def getDefinitionProj : GetM DefinitionProj := do
  let idx := (← getTagN 0).value
  let block ← Serialize.get
  return ⟨idx, block⟩

instance : Serialize DefinitionProj where
  put := putDefinitionProj
  get := getDefinitionProj

def putMutConst : MutConst → PutM Unit
  | .defn d => putU8 0 *> putDefinition d
  | .indc i => putU8 1 *> putInductive i
  | .recr r => putU8 2 *> putRecursor r

def getMutConst : GetM MutConst := do
  match ← getU8 with
  | 0 => .defn <$> getDefinition
  | 1 => .indc <$> getInductive
  | 2 => .recr <$> getRecursor
  | t => throw s!"getMutConst: invalid tag {t}"

instance : Serialize MutConst where
  put := putMutConst
  get := getMutConst

def putConstantInfo : ConstantInfo → PutM Unit
  | .defn d => putTagN 4 Constant.FLAG ConstantInfo.CONST_DEFN *> putDefinition d
  | .recr r => putTagN 4 Constant.FLAG ConstantInfo.CONST_RECR *> putRecursor r
  | .axio a => putTagN 4 Constant.FLAG ConstantInfo.CONST_AXIO *> putAxiom a
  | .quot q => putTagN 4 Constant.FLAG ConstantInfo.CONST_QUOT *> putQuotient q
  | .cPrj p => putTagN 4 Constant.FLAG ConstantInfo.CONST_CPRJ *> putConstructorProj p
  | .rPrj p => putTagN 4 Constant.FLAG ConstantInfo.CONST_RPRJ *> putRecursorProj p
  | .iPrj p => putTagN 4 Constant.FLAG ConstantInfo.CONST_IPRJ *> putInductiveProj p
  | .dPrj p => putTagN 4 Constant.FLAG ConstantInfo.CONST_DPRJ *> putDefinitionProj p
  | .muts ms => do
    putTagN 4 Constant.FLAG_MUTS ms.size.toUInt64
    for m in ms do putMutConst m

def getConstantInfo : GetM ConstantInfo := do
  let tag ← getTagN 4
  if tag.flag == Constant.FLAG_MUTS then
    let mut ms := #[]
    for _ in [0:tag.value.toNat] do
      ms := ms.push (← getMutConst)
    return .muts ms
  else if tag.flag == Constant.FLAG then
    match tag.value with
    | 0 => .defn <$> getDefinition
    | 1 => .recr <$> getRecursor
    | 2 => .axio <$> getAxiom
    | 3 => .quot <$> getQuotient
    | 4 => .cPrj <$> getConstructorProj
    | 5 => .rPrj <$> getRecursorProj
    | 6 => .iPrj <$> getInductiveProj
    | 7 => .dPrj <$> getDefinitionProj
    | v => throw s!"getConstantInfo: invalid variant {v}"
  else
    throw s!"getConstantInfo: invalid flag {tag.flag}"

instance : Serialize ConstantInfo where
  put := putConstantInfo
  get := getConstantInfo

def putConstant (c : Constant) : PutM Unit := do
  putConstantInfo c.info
  putTagN 0 0 c.sharing.size.toUInt64
  for e in c.sharing do putExpr e
  putTagN 0 0 c.refs.size.toUInt64
  for a in c.refs do Serialize.put a
  putTagN 0 0 c.univs.size.toUInt64
  for u in c.univs do putUniv u

/-- Read a counted array by consuming each entry before appending it. -/
def getArray (getm : GetM α) (count : Nat) : GetM (Array α) := do
  let mut values := #[]
  for _ in [0:count] do
    values := values.push (← getm)
  return values

/-- Shared constant grammar with an explicit universe-table reader. This
keeps the record prefix identical for production and bounded decoding. -/
def getConstantWithUnivs (readUnivs : Nat → GetM (Array Univ)) : GetM Constant := do
  let info ← getConstantInfo
  let numSharing := (← getTagN 0).value.toNat
  let sharing ← getArray getExpr numSharing
  let numRefs := (← getTagN 0).value.toNat
  let refs ← getArray Serialize.get numRefs
  let numUnivs := (← getTagN 0).value.toNat
  let univs ← readUnivs numUnivs
  return ⟨info, sharing, refs, univs⟩

def getConstant : GetM Constant := getConstantWithUnivs (getArray getUniv)

instance : Serialize Constant where
  put := putConstant
  get := getConstant

/-! ## Convenience functions for serialization -/

def serUniv (u : Univ) : ByteArray := runPut (putUniv u)
def deUniv (bytes : ByteArray) : Except String Univ := runGetExact getUniv bytes

def serExpr (e : Expr) : ByteArray := runPut (putExpr e)
def deExpr (bytes : ByteArray) : Except String Expr := runGetExact getExpr bytes

def serConstant (c : Constant) : ByteArray := runPut (putConstant c)
def deConstant (bytes : ByteArray) : Except String Constant := runGet getConstant bytes

/-- Decode one complete anonymous record, rejecting any trailing bytes. The
host's prefix decoder remains available as `deConstant`. -/
def deConstantExact (bytes : ByteArray) : Except String Constant := runGetExact getConstant bytes

end Ixon
