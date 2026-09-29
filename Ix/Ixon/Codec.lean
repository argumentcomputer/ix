/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0

Extracted from Ix/Ixon.lean at Ix revision
b067697b9d97552c6f52b2f72c892f84e4c7170f.
-/

module
public import Ix.Ixon.Types

public section

/-! Pure production Ixon v2 codecs. Anonymous encodings and decoder
behavior are shared with the host; metadata, environments, hashing,
and lazy transport remain in `Ix.Ixon`. -/

namespace Ixon

open Ix (DefKind DefinitionSafety QuotKind)

/-- Stable identifier for the v2 Ixon wire grammar. -/
def wireFormatId : String := "ixon-v2"

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

/-- Count bytes needed to represent a u64 in minimal little-endian form. -/
def u64ByteCount (x : UInt64) : UInt8 :=
  if x == 0 then 0
  else if x < 0x100 then 1
  else if x < 0x10000 then 2
  else if x < 0x1000000 then 3
  else if x < 0x100000000 then 4
  else if x < 0x10000000000 then 5
  else if x < 0x1000000000000 then 6
  else if x < 0x100000000000000 then 7
  else 8

/-- Write the requested low bytes of a `UInt64`, least significant first. -/
def putU64TrimmedLEAux (x : UInt64) : Nat → PutM Unit
  | 0 => pure ()
  | len + 1 => do
    putU8 x.toUInt8
    putU64TrimmedLEAux (x >>> 8) len

/-- Write a u64 in minimal little-endian bytes. -/
def putU64TrimmedLE (x : UInt64) : PutM Unit :=
  putU64TrimmedLEAux x (u64ByteCount x).toNat

/-- Read exactly `len` little-endian bytes into a `UInt64`. -/
def getU64TrimmedLEAux : Nat → GetM UInt64
  | 0 => pure 0
  | len + 1 => do
    let low ← getU8
    let high ← getU64TrimmedLEAux len
    return low.toUInt64 ||| (high <<< 8)

/-- Read a u64 from minimal little-endian bytes.

    Widths past 8 are rejected, matching Rust `u64_get_trimmed_le`.
    Without the guard the shift below wraps — `UInt64.shiftLeft` is taken
    mod 64 — so byte 8 would OR back into bits 0-7 and a `Tag0` whose
    payload claims nine bytes would read as a *different value* here than
    in the kernel, which discards the surplus. Same bytes, same address,
    two constants. -/
def getU64TrimmedLE (len : Nat) : GetM UInt64 := do
  if len > 8 then
    throw "getU64TrimmedLE: len > 8"
  getU64TrimmedLEAux len

/-- Tag0: Variable-length encoding for small integers.
    Header byte: [large:1][size:7]
    - If large=0: size is in low 7 bits (0-127)
    - If large=1: (size+1) bytes follow containing actual size -/
structure Tag0 where
  size : UInt64
  deriving BEq, Repr

def putTag0 (t : Tag0) : PutM Unit := do
  if t.size < 128 then
    putU8 t.size.toUInt8
  else
    let byteCount := u64ByteCount t.size
    putU8 (0x80 ||| (byteCount - 1))
    putU64TrimmedLE t.size

def getTag0 : GetM Tag0 := do
  let b ← getU8
  let large := b &&& 0x80 != 0
  let small := b &&& 0x7F
  let size ← if large then
    getU64TrimmedLE (small.toNat + 1)
  else
    pure small.toUInt64
  return ⟨size⟩

/-- Tag2: 2-bit flag + size.
    Header byte: [flag:2][large:1][size:5]
    - If large=0: size is in low 5 bits (0-31)
    - If large=1: (size+1) bytes follow containing actual size -/
structure Tag2 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr

def putTag2 (t : Tag2) : PutM Unit := do
  if t.size < 32 then
    putU8 ((t.flag <<< 6) ||| t.size.toUInt8)
  else
    let byteCount := u64ByteCount t.size
    putU8 ((t.flag <<< 6) ||| 0x20 ||| (byteCount - 1))
    putU64TrimmedLE t.size

def getTag2 : GetM Tag2 := do
  let b ← getU8
  let flag := b >>> 6
  let large := b &&& 0x20 != 0
  let small := b &&& 0x1F
  let size ← if large then
    getU64TrimmedLE (small.toNat + 1)
  else
    pure small.toUInt64
  return ⟨flag, size⟩

/-- Tag4: 4-bit flag + size.
    Header byte: [flag:4][large:1][size:3]
    - If large=0: size is in low 3 bits (0-7)
    - If large=1: (size+1) bytes follow containing actual size -/
structure Tag4 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr, Inhabited, Ord, Hashable

def putTag4 (t : Tag4) : PutM Unit := do
  if t.size < 8 then
    putU8 ((t.flag <<< 4) ||| t.size.toUInt8)
  else
    let byteCount := u64ByteCount t.size
    putU8 ((t.flag <<< 4) ||| 0x08 ||| (byteCount - 1))
    putU64TrimmedLE t.size

def getTag4 : GetM Tag4 := do
  let b ← getU8
  let flag := b >>> 4
  let large := b &&& 0x08 != 0
  let small := b &&& 0x07
  let size ← if large then
    getU64TrimmedLE (small.toNat + 1)
  else
    pure small.toUInt64
  return ⟨flag, size⟩

instance : Serialize Tag4 where
  put := putTag4
  get := getTag4

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

/-- Total v2 universe writer.  Successor telescopes retain the production
    compressed representation; `succBase_sizeOf_le` supplies the non-obvious
    structural decrease. -/
def putUniv : Univ → PutM Unit
  | .zero => putTag2 ⟨Univ.FLAG_ZERO_SUCC, 0⟩
  | u@(.succ _) => do
    putTag2 ⟨Univ.FLAG_ZERO_SUCC, u.succCount⟩
    putUniv u.succBase
  | .max a b => do
    putTag2 ⟨Univ.FLAG_MAX, 0⟩
    putUniv a
    putUniv b
  | .imax a b => do
    putTag2 ⟨Univ.FLAG_IMAX, 0⟩
    putUniv a
    putUniv b
  | .var idx => putTag2 ⟨Univ.FLAG_VAR, idx⟩
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
def getUnivFromTag (recur : GetM Univ) (tag : Tag2) : GetM Univ := do
  match tag.flag with
  | 0 =>  -- ZERO_SUCC
    if tag.size == 0 then
      return .zero
    else
      let base ← recur
      return base.addSucc tag.size.toNat
  | 1 =>  -- MAX
    let a ← recur
    let b ← recur
    return .max a b
  | 2 =>  -- IMAX
    let a ← recur
    let b ← recur
    return .imax a b
  | 3 =>  -- VAR
    return .var tag.size
  | f => throw s!"getUniv: invalid flag {f}"

/-- Total v2 universe reader.  Each recursive layer consumes a tag byte, so
    a caller-supplied byte budget is a complete termination measure. -/
def getUnivFuel : Nat → GetM Univ
  | 0 => throw "getUniv: recursion budget exhausted"
  | fuel + 1 => getTag2 >>= getUnivFromTag (getUnivFuel fuel)

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
def Expr.collectLamBinders : Expr → List (Uses × Expr) × Expr
  | .lam uses ty body =>
    let (binders, base) := body.collectLamBinders
    ((uses, ty) :: binders, base)
  | e => ([], e)

/-- Collect all mode/type triples in a forall telescope. -/
def Expr.collectAllBinders : Expr → List (Uses × Owned × Expr) × Expr
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
theorem Expr.collectLamBinders_base_nodeCount_lt (uses : Uses)
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
theorem Expr.collectAllBinders_base_nodeCount_lt (uses : Uses) (owned : Owned)
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

/-- Total canonical v2 expression writer. Telescope collection preserves the
    Rust byte grammar; the node-count lemmas above expose its recursive calls
    to the kernel termination checker. -/
def putExpr : Expr → PutM Unit
  | .sort idx => putTag4 ⟨Expr.FLAG_SORT, idx⟩
  | .var idx => putTag4 ⟨Expr.FLAG_VAR, idx⟩
  | .ref refIdx univIdxs => do
    -- Rust format: Tag4(flag, array_len), Tag0(ref_idx), then elements
    putTag4 ⟨Expr.FLAG_REF, univIdxs.size.toUInt64⟩
    putTag0 ⟨refIdx⟩
    for idx in univIdxs do putTag0 ⟨idx⟩
  | .recur recIdx univIdxs => do
    -- Rust format: Tag4(flag, array_len), Tag0(rec_idx), then elements
    putTag4 ⟨Expr.FLAG_REC, univIdxs.size.toUInt64⟩
    putTag0 ⟨recIdx⟩
    for idx in univIdxs do putTag0 ⟨idx⟩
  | .prj typeRefIdx fieldIdx val => do
    -- Rust format: Tag4(flag, field_idx), Tag0(type_ref_idx), then val
    putTag4 ⟨Expr.FLAG_PRJ, fieldIdx⟩
    putTag0 ⟨typeRefIdx⟩
    putExpr val
  | .str refIdx => putTag4 ⟨Expr.FLAG_STR, refIdx⟩
  | .nat refIdx => putTag4 ⟨Expr.FLAG_NAT, refIdx⟩
  | e@(.app _ _) => do
    putTag4 ⟨Expr.FLAG_APP, e.collectAppArgs.1.length.toUInt64⟩
    putExpr e.collectAppArgs.2
    for arg in e.collectAppArgs.1 do putExpr arg
  | e@(.lam _ _ _) => do
    putTag4 ⟨Expr.FLAG_LAM, e.collectLamBinders.1.length.toUInt64⟩
    for binder in e.collectLamBinders.1 do
      putU8 binder.1.toBits
      putExpr binder.2
    putExpr e.collectLamBinders.2
  | e@(.all _ _ _ _) => do
    putTag4 ⟨Expr.FLAG_ALL, e.collectAllBinders.1.length.toUInt64⟩
    for binder in e.collectAllBinders.1 do
      putU8 (binder.1.toBits ||| (binder.2.1.toBits <<< 2))
      putExpr binder.2.2
    putExpr e.collectAllBinders.2
  | .letE nonDep ty val body => do
    putTag4 ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
    putExpr ty
    putExpr val
    putExpr body
  | .share idx => putTag4 ⟨Expr.FLAG_SHARE, idx⟩
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

/-- Read `count` `Tag0` sizes in wire order. -/
def getTag0Sizes : Nat → GetM (List UInt64)
  | 0 => pure []
  | count + 1 => do
    let head := (← getTag0).size
    let tail ← getTag0Sizes count
    return head :: tail

/-- Read and apply one canonical application argument at a time. -/
def getExprAppArgs (recur : GetM Expr) : Nat → Expr → GetM Expr
  | 0, result => pure result
  | count + 1, result => do
    let arg ← recur
    getExprAppArgs recur count (.app result arg)

/-- Read a lambda telescope in outer-to-inner wire order. -/
def getExprLamBinders (recur : GetM Expr) : Nat → GetM (List (Uses × Expr))
  | 0 => pure []
  | count + 1 => do
    let mode ← getU8
    let some uses := Uses.ofBits? mode
      | throw s!"getExpr: invalid lambda mode {mode}"
    let ty ← recur
    let tail ← getExprLamBinders recur count
    return (uses, ty) :: tail

/-- Read a forall telescope in outer-to-inner wire order. -/
def getExprAllBinders (recur : GetM Expr) :
    Nat → GetM (List (Uses × Owned × Expr))
  | 0 => pure []
  | count + 1 => do
    let mode ← getU8
    if mode > 7 then
      throw s!"getExpr: invalid forall mode {mode}"
    let some uses := Uses.ofBits? (mode &&& 0x03)
      | throw s!"getExpr: invalid forall usage mode {mode}"
    let some owned := Owned.ofBits? ((mode >>> 2) &&& 0x01)
      | throw s!"getExpr: invalid forall ownership mode {mode}"
    let ty ← recur
    let tail ← getExprAllBinders recur count
    return (uses, owned, ty) :: tail

/-- Parse a v2 expression after its leading `Tag4`. Recursive reads are
    supplied explicitly so `getExprFuel` below remains structurally total. -/
def getExprFromTag (recur : GetM Expr) (tag : Tag4) : GetM Expr := do
  match tag.flag with
  | 0x0 => return .sort tag.size
  | 0x1 => return .var tag.size
  | 0x2 => do  -- REF: tag.size is array_len, then ref_idx, then elements
    let refIdx := (← getTag0).size
    let univIdxs ← getTag0Sizes tag.size.toNat
    return .ref refIdx univIdxs.toArray
  | 0x3 => do  -- REC: tag.size is array_len, then rec_idx, then elements
    let recIdx := (← getTag0).size
    let univIdxs ← getTag0Sizes tag.size.toNat
    return .recur recIdx univIdxs.toArray
  | 0x4 => do  -- PRJ: tag.size is field_idx, then type_ref_idx, then val
    let typeRefIdx := (← getTag0).size
    let val ← recur
    return .prj typeRefIdx tag.size val
  | 0x5 => return .str tag.size
  | 0x6 => return .nat tag.size
  | 0x7 => do  -- APP (telescope)
    if tag.size == 0 then
      throw "getExpr: empty app spine"
    let base ← recur
    match base with
    | .app .. => throw "getExpr: non-canonical app base"
    | _ => pure ()
    getExprAppArgs recur tag.size.toNat base
  | 0x8 => do  -- LAM (telescope)
    if tag.size == 0 then
      throw "getExpr: Lam with zero binders"
    let binders ← getExprLamBinders recur tag.size.toNat
    let body ← recur
    match body with
    | .lam .. => throw "getExpr: non-canonical lam telescope"
    | _ => pure ()
    return binders.foldr (fun (uses, ty) result => .lam uses ty result) body
  | 0x9 => do  -- ALL (telescope)
    if tag.size == 0 then
      throw "getExpr: All with zero binders"
    let binders ← getExprAllBinders recur tag.size.toNat
    let body ← recur
    match body with
    | .all .. => throw "getExpr: non-canonical all telescope"
    | _ => pure ()
    return binders.foldr
      (fun (uses, owned, ty) result => .all uses owned ty result) body
  | 0xA => do  -- LET
    if tag.size > 1 then
      throw s!"getExpr: invalid letE nonDep {tag.size}"
    let nonDep := tag.size == 1
    let ty ← recur
    let val ← recur
    let body ← recur
    return .letE nonDep ty val body
  | 0xB => return .share tag.size
  | f => throw s!"getExpr: invalid flag {f}"

/-- Total v2 expression reader. Every recursive layer consumes a `Tag4`
    header, so a caller-supplied byte budget is a complete termination
    measure even for telescope-compressed applications and binders. -/
def getExprFuel : Nat → GetM Expr
  | 0 => throw "getExpr: recursion budget exhausted"
  | fuel + 1 => getTag4 >>= getExprFromTag (getExprFuel fuel)

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
  putTag0 ⟨d.lvls⟩
  putExpr d.typ
  putExpr d.value

def getDefinition : GetM Definition := do
  let (kind, safety) := unpackDefKindSafety (← getU8)
  let lvls := (← getTag0).size
  let typ ← getExpr
  let value ← getExpr
  return ⟨kind, safety, lvls, typ, value⟩

instance : Serialize Definition where
  put := putDefinition
  get := getDefinition

def putRecursorRule (r : RecursorRule) : PutM Unit := do
  putTag0 ⟨r.fields⟩
  putExpr r.rhs

def getRecursorRule : GetM RecursorRule := do
  let fields := (← getTag0).size
  let rhs ← getExpr
  return ⟨fields, rhs⟩

instance : Serialize RecursorRule where
  put := putRecursorRule
  get := getRecursorRule

def putRecursor (r : Recursor) : PutM Unit := do
  putU8 (packBools [r.k, r.isUnsafe])
  putTag0 ⟨r.lvls⟩
  putTag0 ⟨r.params⟩
  putTag0 ⟨r.indices⟩
  putTag0 ⟨r.motives⟩
  putTag0 ⟨r.minors⟩
  putExpr r.typ
  putTag0 ⟨r.rules.size.toUInt64⟩
  for rule in r.rules do putRecursorRule rule

def getRecursor : GetM Recursor := do
  let bools := unpackBools 2 (← getU8)
  let k := bools[0]!
  let isUnsafe := bools[1]!
  let lvls := (← getTag0).size
  let params := (← getTag0).size
  let indices := (← getTag0).size
  let motives := (← getTag0).size
  let minors := (← getTag0).size
  let typ ← getExpr
  let numRules := (← getTag0).size.toNat
  let mut rules := #[]
  for _ in [0:numRules] do
    rules := rules.push (← getRecursorRule)
  return ⟨k, isUnsafe, lvls, params, indices, motives, minors, typ, rules⟩

instance : Serialize Recursor where
  put := putRecursor
  get := getRecursor

def putAxiom (a : Axiom) : PutM Unit := do
  putU8 (if a.isUnsafe then 1 else 0)
  putTag0 ⟨a.lvls⟩
  putExpr a.typ

def getAxiom : GetM Axiom := do
  let isUnsafe := (← getU8) != 0
  let lvls := (← getTag0).size
  let typ ← getExpr
  return ⟨isUnsafe, lvls, typ⟩

instance : Serialize Axiom where
  put := putAxiom
  get := getAxiom

def putQuotient (q : Quotient) : PutM Unit := do
  let k : UInt8 := match q.kind with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
  putU8 k
  putTag0 ⟨q.lvls⟩
  putExpr q.typ

def getQuotient : GetM Quotient := do
  let v ← getU8
  let k : QuotKind ← match v with
    | 0 => pure .type | 1 => pure .ctor | 2 => pure .lift | 3 => pure .ind
    | _ => throw s!"invalid QuotKind tag {v}"
  let lvls := (← getTag0).size
  let typ ← getExpr
  return ⟨k, lvls, typ⟩

instance : Serialize Quotient where
  put := putQuotient
  get := getQuotient

def putConstructor (c : Constructor) : PutM Unit := do
  putU8 (if c.isUnsafe then 1 else 0)
  putTag0 ⟨c.lvls⟩
  putTag0 ⟨c.cidx⟩
  putTag0 ⟨c.params⟩
  putTag0 ⟨c.fields⟩
  putExpr c.typ

def getConstructor : GetM Constructor := do
  let isUnsafe := (← getU8) != 0
  let lvls := (← getTag0).size
  let cidx := (← getTag0).size
  let params := (← getTag0).size
  let fields := (← getTag0).size
  let typ ← getExpr
  return ⟨isUnsafe, lvls, cidx, params, fields, typ⟩

instance : Serialize Constructor where
  put := putConstructor
  get := getConstructor

def putInductive (i : Inductive) : PutM Unit := do
  putU8 (packBools [i.isUnsafe])
  putTag0 ⟨i.lvls⟩
  putTag0 ⟨i.params⟩
  putTag0 ⟨i.indices⟩
  putExpr i.typ
  putTag0 ⟨i.ctors.size.toUInt64⟩
  for c in i.ctors do putConstructor c

def getInductive : GetM Inductive := do
  let bools := unpackBools 1 (← getU8)
  let isUnsafe := bools[0]!
  let lvls := (← getTag0).size
  let params := (← getTag0).size
  let indices := (← getTag0).size
  let typ ← getExpr
  let numCtors := (← getTag0).size.toNat
  let mut ctors := #[]
  for _ in [0:numCtors] do
    ctors := ctors.push (← getConstructor)
  return ⟨isUnsafe, lvls, params, indices, typ, ctors⟩

instance : Serialize Inductive where
  put := putInductive
  get := getInductive

def putInductiveProj (p : InductiveProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getInductiveProj : GetM InductiveProj := do
  let idx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, block⟩

instance : Serialize InductiveProj where
  put := putInductiveProj
  get := getInductiveProj

def putConstructorProj (p : ConstructorProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  putTag0 ⟨p.cidx⟩
  Serialize.put p.block

def getConstructorProj : GetM ConstructorProj := do
  let idx := (← getTag0).size
  let cidx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, cidx, block⟩

instance : Serialize ConstructorProj where
  put := putConstructorProj
  get := getConstructorProj

def putRecursorProj (p : RecursorProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getRecursorProj : GetM RecursorProj := do
  let idx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, block⟩

instance : Serialize RecursorProj where
  put := putRecursorProj
  get := getRecursorProj

def putDefinitionProj (p : DefinitionProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getDefinitionProj : GetM DefinitionProj := do
  let idx := (← getTag0).size
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
  | .defn d => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_DEFN⟩ *> putDefinition d
  | .recr r => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_RECR⟩ *> putRecursor r
  | .axio a => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩ *> putAxiom a
  | .quot q => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_QUOT⟩ *> putQuotient q
  | .cPrj p => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_CPRJ⟩ *> putConstructorProj p
  | .rPrj p => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_RPRJ⟩ *> putRecursorProj p
  | .iPrj p => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_IPRJ⟩ *> putInductiveProj p
  | .dPrj p => putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_DPRJ⟩ *> putDefinitionProj p
  | .muts ms => do
    putTag4 ⟨Constant.FLAG_MUTS, ms.size.toUInt64⟩
    for m in ms do putMutConst m

def getConstantInfo : GetM ConstantInfo := do
  let tag ← getTag4
  if tag.flag == Constant.FLAG_MUTS then
    let mut ms := #[]
    for _ in [0:tag.size.toNat] do
      ms := ms.push (← getMutConst)
    return .muts ms
  else if tag.flag == Constant.FLAG then
    match tag.size with
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
  putTag0 ⟨c.sharing.size.toUInt64⟩
  for e in c.sharing do putExpr e
  putTag0 ⟨c.refs.size.toUInt64⟩
  for a in c.refs do Serialize.put a
  putTag0 ⟨c.univs.size.toUInt64⟩
  for u in c.univs do putUniv u

def getConstant : GetM Constant := do
  let info ← getConstantInfo
  let numSharing := (← getTag0).size.toNat
  let mut sharing := #[]
  for _ in [0:numSharing] do
    sharing := sharing.push (← getExpr)
  let numRefs := (← getTag0).size.toNat
  let mut refs := #[]
  for _ in [0:numRefs] do
    refs := refs.push (← Serialize.get)
  let numUnivs := (← getTag0).size.toNat
  let mut univs := #[]
  for _ in [0:numUnivs] do
    univs := univs.push (← getUniv)
  return ⟨info, sharing, refs, univs⟩

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
