/-
  Ixon: Alpha-invariant serialization format for Lean constants.

  This module defines:
  - Serialize typeclass and primitive serialization
  - Tag0/Tag2/Tag4 encoding
  - Expr, Univ, and Constant types matching Rust exactly
  - All numeric fields use UInt64 (matching Rust's u64)
-/
import Ix.Address
import Ix.Common
import Ix.Environment

namespace Ixon

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

def putU32LE (x : UInt32) : PutM Unit := do
  for i in [0:4] do
    putU8 ((x >>> (i.toUInt32 * 8)).toUInt8)

def getU32LE : GetM UInt32 := do
  let mut x : UInt32 := 0
  for i in [0:4] do
    let b ← getU8
    x := x ||| (b.toUInt32 <<< (i.toUInt32 * 8))
  return x

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

/-- Write a u64 in minimal little-endian bytes. -/
def putU64TrimmedLE (x : UInt64) : PutM Unit := do
  let n := u64ByteCount x
  for i in [0:n.toNat] do
    putU8 ((x >>> (i.toUInt64 * 8)).toUInt8)

/-- Read a u64 from minimal little-endian bytes. -/
def getU64TrimmedLE (len : Nat) : GetM UInt64 := do
  let mut x : UInt64 := 0
  for i in [0:len] do
    let b ← getU8
    x := x ||| (b.toUInt64 <<< (i.toUInt64 * 8))
  return x

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

/-! ## Universe Levels -/

/-- Universe levels for Lean's type system. -/
inductive Univ where
  | zero : Univ
  | succ : Univ → Univ
  | max : Univ → Univ → Univ
  | imax : Univ → Univ → Univ
  | var : UInt64 → Univ
  deriving BEq, Repr, Inhabited, Hashable

namespace Univ
  def FLAG_ZERO_SUCC : UInt8 := 0
  def FLAG_MAX : UInt8 := 1
  def FLAG_IMAX : UInt8 := 2
  def FLAG_VAR : UInt8 := 3
end Univ

/-! ## Expressions -/

/-- Expression in the Ixon format.
    Alpha-invariant representation of Lean expressions.
    Names are stripped, binder info is stored in metadata. -/
inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | all : Expr → Expr → Expr
  | letE : Bool → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, Repr, Inhabited, Hashable

namespace Expr
  def FLAG_SORT : UInt8 := 0x0
  def FLAG_VAR : UInt8 := 0x1
  def FLAG_REF : UInt8 := 0x2
  def FLAG_REC : UInt8 := 0x3
  def FLAG_PRJ : UInt8 := 0x4
  def FLAG_STR : UInt8 := 0x5
  def FLAG_NAT : UInt8 := 0x6
  def FLAG_APP : UInt8 := 0x7
  def FLAG_LAM : UInt8 := 0x8
  def FLAG_ALL : UInt8 := 0x9
  def FLAG_LET : UInt8 := 0xA
  def FLAG_SHARE : UInt8 := 0xB
end Expr

/-! ## Constant Types -/

-- DefKind, DefinitionSafety, QuotKind are defined in Ix.Common

open Ix (DefKind DefinitionSafety QuotKind)

structure Definition where
  kind : DefKind
  safety : DefinitionSafety
  lvls : UInt64
  typ : Expr
  value : Expr
  deriving BEq, Repr, Inhabited

structure RecursorRule where
  fields : UInt64
  rhs : Expr
  deriving BEq, Repr, Inhabited

structure Recursor where
  k : Bool
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  motives : UInt64
  minors : UInt64
  typ : Expr
  rules : Array RecursorRule
  deriving BEq, Repr, Inhabited

structure Axiom where
  isUnsafe : Bool
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Quotient where
  kind : QuotKind
  lvls : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Constructor where
  isUnsafe : Bool
  lvls : UInt64
  cidx : UInt64
  params : UInt64
  fields : UInt64
  typ : Expr
  deriving BEq, Repr, Inhabited

structure Inductive where
  recr : Bool
  refl : Bool
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  nested : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, Repr, Inhabited

/-! ## Projection Types -/

structure InductiveProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited, Hashable

structure ConstructorProj where
  idx : UInt64
  cidx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited, Hashable

structure RecursorProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited, Hashable

structure DefinitionProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited, Hashable

/-! ## Constant Info -/

inductive MutConst where
  | defn : Definition → MutConst
  | indc : Inductive → MutConst
  | recr : Recursor → MutConst
  deriving BEq, Repr, Inhabited

inductive ConstantInfo where
  | defn : Definition → ConstantInfo
  | recr : Recursor → ConstantInfo
  | axio : Axiom → ConstantInfo
  | quot : Quotient → ConstantInfo
  | cPrj : ConstructorProj → ConstantInfo
  | rPrj : RecursorProj → ConstantInfo
  | iPrj : InductiveProj → ConstantInfo
  | dPrj : DefinitionProj → ConstantInfo
  | muts : Array MutConst → ConstantInfo
  deriving BEq, Repr, Inhabited

namespace ConstantInfo
  def CONST_DEFN : UInt64 := 0
  def CONST_RECR : UInt64 := 1
  def CONST_AXIO : UInt64 := 2
  def CONST_QUOT : UInt64 := 3
  def CONST_CPRJ : UInt64 := 4
  def CONST_RPRJ : UInt64 := 5
  def CONST_IPRJ : UInt64 := 6
  def CONST_DPRJ : UInt64 := 7
end ConstantInfo

/-- A top-level constant with sharing, refs, and univs tables. -/
structure Constant where
  info : ConstantInfo
  sharing : Array Expr
  refs : Array Address
  univs : Array Univ
  deriving BEq, Repr, Inhabited

/-! ## Metadata Types -/

/-- Data values for KVMap metadata -/
inductive DataValue where
  | ofString (addr : Address)
  | ofBool (b : Bool)
  | ofName (addr : Address)
  | ofNat (addr : Address)
  | ofInt (addr : Address)
  | ofSyntax (addr : Address)
  deriving BEq, Repr, Inhabited, Hashable

/-- Key-value map for Lean.Expr.mdata -/
abbrev KVMap := Array (Address × DataValue)

/-- Arena node for per-expression metadata.
    Nodes are allocated bottom-up (children before parents) in the arena.
    Arena indices are UInt64 values pointing into `ExprMetaArena.nodes`. -/
inductive ExprMetaData where
  | leaf
  | app (fun_ : UInt64) (arg : UInt64)
  | binder (name : Address) (info : Lean.BinderInfo)
           (tyChild : UInt64) (bodyChild : UInt64)
  | letBinder (name : Address)
              (tyChild : UInt64) (valChild : UInt64) (bodyChild : UInt64)
  | ref (name : Address)
  | prj (structName : Address) (child : UInt64)
  | mdata (mdata : Array KVMap) (child : UInt64)
  deriving BEq, Repr, Inhabited

/-- Arena for expression metadata within a single constant. -/
structure ExprMetaArena where
  nodes : Array ExprMetaData := #[]
  deriving BEq, Repr, Inhabited

def ExprMetaArena.alloc (arena : ExprMetaArena) (node : ExprMetaData)
    : ExprMetaArena × UInt64 :=
  let idx := arena.nodes.size.toUInt64
  ({ nodes := arena.nodes.push node }, idx)

/-- Count ExprMetaData nodes by type: (leaf, app, binder, letBinder, ref, prj, mdata) -/
def ExprMetaArena.countByType (arena : ExprMetaArena) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  arena.nodes.foldl (init := (0, 0, 0, 0, 0, 0, 0)) fun (le, ap, bi, lb, rf, pj, md) node =>
    match node with
    | .leaf => (le + 1, ap, bi, lb, rf, pj, md)
    | .app .. => (le, ap + 1, bi, lb, rf, pj, md)
    | .binder .. => (le, ap, bi + 1, lb, rf, pj, md)
    | .letBinder .. => (le, ap, bi, lb + 1, rf, pj, md)
    | .ref .. => (le, ap, bi, lb, rf + 1, pj, md)
    | .prj .. => (le, ap, bi, lb, rf, pj + 1, md)
    | .mdata .. => (le, ap, bi, lb, rf, pj, md + 1)

/-- Count mdata items in an arena. -/
def ExprMetaArena.mdataItemCount (arena : ExprMetaArena) : Nat :=
  arena.nodes.foldl (init := 0) fun acc node =>
    match node with
    | .mdata mdata _ => acc + mdata.foldl (fun a kv => a + kv.size) 0
    | _ => acc

/-- Per-constant metadata with arena-based expression metadata.
    Each variant stores an ExprMetaArena covering all expressions in
    that constant, plus root indices pointing into the arena. -/
inductive ConstantMeta where
  | empty
  | defn (name : Address) (lvls : Array Address) (hints : Lean.ReducibilityHints)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64) (valueRoot : UInt64)
  | axio (name : Address) (lvls : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | quot (name : Address) (lvls : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | indc (name : Address) (lvls : Array Address) (ctors : Array Address)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | ctor (name : Address) (lvls : Array Address) (induct : Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
  | recr (name : Address) (lvls : Array Address) (rules : Array Address)
         (all : Array Address) (ctx : Array Address)
         (arena : ExprMetaArena) (typeRoot : UInt64)
         (ruleRoots : Array UInt64)
  deriving Inhabited, BEq, Repr

/-- Count total arena nodes in this ConstantMeta. -/
def ConstantMeta.exprMetaCount : ConstantMeta → Nat
  | .empty => 0
  | .defn _ _ _ _ _ arena _ _ => arena.nodes.size
  | .axio _ _ arena _ => arena.nodes.size
  | .quot _ _ arena _ => arena.nodes.size
  | .indc _ _ _ _ _ arena _ => arena.nodes.size
  | .ctor _ _ _ arena _ => arena.nodes.size
  | .recr _ _ _ _ _ arena _ _ => arena.nodes.size

/-- Count total arena nodes and mdata items in this ConstantMeta. -/
def ConstantMeta.exprMetaStats : ConstantMeta → Nat × Nat
  | .empty => (0, 0)
  | .defn _ _ _ _ _ arena _ _ => (arena.nodes.size, arena.mdataItemCount)
  | .axio _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .quot _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .indc _ _ _ _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .ctor _ _ _ arena _ => (arena.nodes.size, arena.mdataItemCount)
  | .recr _ _ _ _ _ arena _ _ => (arena.nodes.size, arena.mdataItemCount)

/-- Count ExprMetaData nodes by type: (binder, letBinder, ref, prj, mdata)
    (compatible signature with old ExprMetas.countByType for comparison) -/
def ConstantMeta.exprMetaByType : ConstantMeta → Nat × Nat × Nat × Nat × Nat
  | .empty => (0, 0, 0, 0, 0)
  | cm =>
    let arena := match cm with
      | .defn _ _ _ _ _ a _ _ => a
      | .axio _ _ a _ => a
      | .quot _ _ a _ => a
      | .indc _ _ _ _ _ a _ => a
      | .ctor _ _ _ a _ => a
      | .recr _ _ _ _ _ a _ _ => a
      | .empty => {}
    let (_, _, bi, lb, rf, pj, md) := arena.countByType
    (bi, lb, rf, pj, md)

/-- A named constant with metadata -/
structure Named where
  addr : Address
  constMeta : ConstantMeta := .empty
  deriving Inhabited, BEq, Repr

/-- A cryptographic commitment -/
structure Comm where
  secret : Address
  payload : Address
  deriving BEq, Repr, Inhabited

namespace Constant
  def FLAG_MUTS : UInt8 := 0xC
  def FLAG : UInt8 := 0xD
end Constant

/-! ## Univ Serialization -/

/-- Count successive .succ constructors -/
def Univ.succCount : Univ → UInt64
  | .succ inner => 1 + inner.succCount
  | _ => 0

/-- Get the base of a .succ chain -/
def Univ.succBase : Univ → Univ
  | .succ inner => inner.succBase
  | u => u

partial def putUniv : Univ → PutM Unit
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

partial def getUniv : GetM Univ := do
  let tag ← getTag2
  match tag.flag with
  | 0 =>  -- ZERO_SUCC
    if tag.size == 0 then
      return .zero
    else
      let base ← getUniv
      let mut result := base
      for _ in [0:tag.size.toNat] do
        result := .succ result
      return result
  | 1 =>  -- MAX
    let a ← getUniv
    let b ← getUniv
    return .max a b
  | 2 =>  -- IMAX
    let a ← getUniv
    let b ← getUniv
    return .imax a b
  | 3 =>  -- VAR
    return .var tag.size
  | f => throw s!"getUniv: invalid flag {f}"

instance : Serialize Univ where
  put := putUniv
  get := getUniv

/-! ## Expr Serialization -/

/-- Collect all types in a lambda telescope. -/
def Expr.collectLamTypes : Expr → List Expr × Expr
  | .lam ty body =>
    let (tys, base) := body.collectLamTypes
    (ty :: tys, base)
  | e => ([], e)

/-- Collect all types in a forall telescope. -/
def Expr.collectAllTypes : Expr → List Expr × Expr
  | .all ty body =>
    let (tys, base) := body.collectAllTypes
    (ty :: tys, base)
  | e => ([], e)

/-- Collect all arguments in an application telescope (in application order). -/
def Expr.collectAppArgs : Expr → List Expr × Expr
  | .app f a =>
    let (args, base) := f.collectAppArgs
    (args ++ [a], base)
  | e => ([], e)

partial def putExpr : Expr → PutM Unit
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
    let (args, base) := e.collectAppArgs
    putTag4 ⟨Expr.FLAG_APP, args.length.toUInt64⟩
    putExpr base
    for arg in args do putExpr arg
  | e@(.lam _ _) => do
    let (tys, base) := e.collectLamTypes
    putTag4 ⟨Expr.FLAG_LAM, tys.length.toUInt64⟩
    for ty in tys do putExpr ty
    putExpr base
  | e@(.all _ _) => do
    let (tys, base) := e.collectAllTypes
    putTag4 ⟨Expr.FLAG_ALL, tys.length.toUInt64⟩
    for ty in tys do putExpr ty
    putExpr base
  | .letE nonDep ty val body => do
    putTag4 ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
    putExpr ty
    putExpr val
    putExpr body
  | .share idx => putTag4 ⟨Expr.FLAG_SHARE, idx⟩

partial def getExpr : GetM Expr := do
  let tag ← getTag4
  match tag.flag with
  | 0x0 => return .sort tag.size
  | 0x1 => return .var tag.size
  | 0x2 => do  -- REF: tag.size is array_len, then ref_idx, then elements
    let refIdx := (← getTag0).size
    let mut univIdxs := #[]
    for _ in [0:tag.size.toNat] do
      univIdxs := univIdxs.push ((← getTag0).size)
    return .ref refIdx univIdxs
  | 0x3 => do  -- REC: tag.size is array_len, then rec_idx, then elements
    let recIdx := (← getTag0).size
    let mut univIdxs := #[]
    for _ in [0:tag.size.toNat] do
      univIdxs := univIdxs.push ((← getTag0).size)
    return .recur recIdx univIdxs
  | 0x4 => do  -- PRJ: tag.size is field_idx, then type_ref_idx, then val
    let typeRefIdx := (← getTag0).size
    let val ← getExpr
    return .prj typeRefIdx tag.size val
  | 0x5 => return .str tag.size
  | 0x6 => return .nat tag.size
  | 0x7 => do  -- APP (telescope)
    let base ← getExpr
    let mut result := base
    for _ in [0:tag.size.toNat] do
      let arg ← getExpr
      result := .app result arg
    return result
  | 0x8 => do  -- LAM (telescope)
    let mut tys := #[]
    for _ in [0:tag.size.toNat] do
      tys := tys.push (← getExpr)
    let body ← getExpr
    let mut result := body
    for ty in tys.reverse do
      result := .lam ty result
    return result
  | 0x9 => do  -- ALL (telescope)
    let mut tys := #[]
    for _ in [0:tag.size.toNat] do
      tys := tys.push (← getExpr)
    let body ← getExpr
    let mut result := body
    for ty in tys.reverse do
      result := .all ty result
    return result
  | 0xA => do  -- LET
    let nonDep := tag.size != 0
    let ty ← getExpr
    let val ← getExpr
    let body ← getExpr
    return .letE nonDep ty val body
  | 0xB => return .share tag.size
  | f => throw s!"getExpr: invalid flag {f}"

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
  putU8 (packBools [i.recr, i.refl, i.isUnsafe])
  putTag0 ⟨i.lvls⟩
  putTag0 ⟨i.params⟩
  putTag0 ⟨i.indices⟩
  putTag0 ⟨i.nested⟩
  putExpr i.typ
  putTag0 ⟨i.ctors.size.toUInt64⟩
  for c in i.ctors do putConstructor c

def getInductive : GetM Inductive := do
  let bools := unpackBools 3 (← getU8)
  let recr := bools[0]!
  let refl := bools[1]!
  let isUnsafe := bools[2]!
  let lvls := (← getTag0).size
  let params := (← getTag0).size
  let indices := (← getTag0).size
  let nested := (← getTag0).size
  let typ ← getExpr
  let numCtors := (← getTag0).size.toNat
  let mut ctors := #[]
  for _ in [0:numCtors] do
    ctors := ctors.push (← getConstructor)
  return ⟨recr, refl, isUnsafe, lvls, params, indices, nested, typ, ctors⟩

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
def desUniv (bytes : ByteArray) : Except String Univ := runGet getUniv bytes

def serExpr (e : Expr) : ByteArray := runPut (putExpr e)
def desExpr (bytes : ByteArray) : Except String Expr := runGet getExpr bytes

def serConstant (c : Constant) : ByteArray := runPut (putConstant c)
def desConstant (bytes : ByteArray) : Except String Constant := runGet getConstant bytes

/-! ## Metadata Serialization -/

/-- Type alias for name index (Address → u64). -/
abbrev NameIndex := Std.HashMap Address UInt64

/-- Type alias for reverse name index (position → Address). -/
abbrev NameReverseIndex := Array Address

/-- Put an address as an index. -/
def putIdx (addr : Address) (idx : NameIndex) : PutM Unit := do
  let i := idx.get? addr |>.getD 0
  putTag0 ⟨i⟩

/-- Get an address from an index. -/
def getIdx (rev : NameReverseIndex) : GetM Address := do
  let i := (← getTag0).size.toNat
  match rev[i]? with
  | some addr => pure addr
  | none => throw s!"invalid name index {i}, max {rev.size}"

/-- Put a vector of addresses as indices. -/
def putIdxVec (addrs : Array Address) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨addrs.size.toUInt64⟩
  for a in addrs do putIdx a idx

/-- Get a vector of addresses from indices. -/
def getIdxVec (rev : NameReverseIndex) : GetM (Array Address) := do
  let len := (← getTag0).size.toNat
  let mut v := #[]
  for _ in [0:len] do
    v := v.push (← getIdx rev)
  pure v

/-- Serialize BinderInfo. -/
def putBinderInfo : Lean.BinderInfo → PutM Unit
  | .default => putU8 0
  | .implicit => putU8 1
  | .strictImplicit => putU8 2
  | .instImplicit => putU8 3

def getBinderInfo : GetM Lean.BinderInfo := do
  match ← getU8 with
  | 0 => pure .default
  | 1 => pure .implicit
  | 2 => pure .strictImplicit
  | 3 => pure .instImplicit
  | x => throw s!"invalid BinderInfo {x}"

/-- Serialize ReducibilityHints. -/
def putReducibilityHints : Lean.ReducibilityHints → PutM Unit
  | .opaque => putU8 0
  | .abbrev => putU8 1
  | .regular n => do putU8 2; putU32LE n

def getReducibilityHints : GetM Lean.ReducibilityHints := do
  match ← getU8 with
  | 0 => pure .opaque
  | 1 => pure .abbrev
  | 2 => pure (.regular (← getU32LE))
  | x => throw s!"invalid ReducibilityHints {x}"

/-- Serialize DataValue with indexed addresses.
    OfString/OfNat/OfInt/OfSyntax use raw 32-byte addresses (blob addresses, not in name index). -/
def putDataValueIndexed (dv : DataValue) (idx : NameIndex) : PutM Unit := do
  match dv with
  | .ofString a => putU8 0 *> Serialize.put a
  | .ofBool b => putU8 1 *> Serialize.put b
  | .ofName a => putU8 2 *> putIdx a idx
  | .ofNat a => putU8 3 *> Serialize.put a
  | .ofInt a => putU8 4 *> Serialize.put a
  | .ofSyntax a => putU8 5 *> Serialize.put a

def getDataValueIndexed (rev : NameReverseIndex) : GetM DataValue := do
  match ← getU8 with
  | 0 => .ofString <$> Serialize.get
  | 1 => .ofBool <$> Serialize.get
  | 2 => .ofName <$> getIdx rev
  | 3 => .ofNat <$> Serialize.get
  | 4 => .ofInt <$> Serialize.get
  | 5 => .ofSyntax <$> Serialize.get
  | x => throw s!"invalid DataValue tag {x}"

/-- Serialize KVMap with indexed addresses. -/
def putKVMapIndexed (kvmap : KVMap) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨kvmap.size.toUInt64⟩
  for (k, v) in kvmap do
    putIdx k idx
    putDataValueIndexed v idx

def getKVMapIndexed (rev : NameReverseIndex) : GetM KVMap := do
  let len := (← getTag0).size.toNat
  let mut kvmap := #[]
  for _ in [0:len] do
    let k ← getIdx rev
    let v ← getDataValueIndexed rev
    kvmap := kvmap.push (k, v)
  pure kvmap

/-- Serialize mdata stack (Array KVMap) with indexed addresses. -/
def putMdataStackIndexed (mdata : Array KVMap) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨mdata.size.toUInt64⟩
  for kv in mdata do putKVMapIndexed kv idx

def getMdataStackIndexed (rev : NameReverseIndex) : GetM (Array KVMap) := do
  let len := (← getTag0).size.toNat
  let mut mdata := #[]
  for _ in [0:len] do
    mdata := mdata.push (← getKVMapIndexed rev)
  pure mdata

/-- Serialize ExprMetaData with indexed addresses. Arena indices use Tag0 encoding. -/
def putExprMetaDataIndexed (em : ExprMetaData) (idx : NameIndex) : PutM Unit := do
  match em with
  | .leaf => putU8 0
  | .app f a =>
    putU8 1
    putTag0 ⟨f⟩
    putTag0 ⟨a⟩
  | .binder name info tyChild bodyChild =>
    let tag : UInt8 := 2 + match info with
      | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
    putU8 tag
    putIdx name idx
    putTag0 ⟨tyChild⟩
    putTag0 ⟨bodyChild⟩
  | .letBinder name tyChild valChild bodyChild =>
    putU8 6
    putIdx name idx
    putTag0 ⟨tyChild⟩
    putTag0 ⟨valChild⟩
    putTag0 ⟨bodyChild⟩
  | .ref name =>
    putU8 7
    putIdx name idx
  | .prj structName child =>
    putU8 8
    putIdx structName idx
    putTag0 ⟨child⟩
  | .mdata mdata child =>
    putU8 9
    putMdataStackIndexed mdata idx
    putTag0 ⟨child⟩

def getExprMetaDataIndexed (rev : NameReverseIndex) : GetM ExprMetaData := do
  let tag ← getU8
  match tag with
  | 0 => pure .leaf
  | 1 =>
    let f := (← getTag0).size
    let a := (← getTag0).size
    pure (.app f a)
  | 2 | 3 | 4 | 5 =>
    let info := match tag with
      | 2 => Lean.BinderInfo.default | 3 => .implicit
      | 4 => .strictImplicit | _ => .instImplicit
    let name ← getIdx rev
    let tyChild := (← getTag0).size
    let bodyChild := (← getTag0).size
    pure (.binder name info tyChild bodyChild)
  | 6 =>
    let name ← getIdx rev
    let tyChild := (← getTag0).size
    let valChild := (← getTag0).size
    let bodyChild := (← getTag0).size
    pure (.letBinder name tyChild valChild bodyChild)
  | 7 =>
    let name ← getIdx rev
    pure (.ref name)
  | 8 =>
    let structName ← getIdx rev
    let child := (← getTag0).size
    pure (.prj structName child)
  | 9 =>
    let mdata ← getMdataStackIndexed rev
    let child := (← getTag0).size
    pure (.mdata mdata child)
  | x => throw s!"invalid ExprMetaData tag {x}"

/-- Serialize ExprMetaArena (length-prefixed array of ExprMetaData nodes). -/
def putExprMetaArenaIndexed (arena : ExprMetaArena) (idx : NameIndex) : PutM Unit := do
  putTag0 ⟨arena.nodes.size.toUInt64⟩
  for node in arena.nodes do
    putExprMetaDataIndexed node idx

def getExprMetaArenaIndexed (rev : NameReverseIndex) : GetM ExprMetaArena := do
  let len := (← getTag0).size.toNat
  let mut nodes : Array ExprMetaData := #[]
  for _ in [0:len] do
    nodes := nodes.push (← getExprMetaDataIndexed rev)
  pure ⟨nodes⟩

/-- Serialize ConstantMeta with indexed addresses. -/
def putConstantMetaIndexed (cm : ConstantMeta) (idx : NameIndex) : PutM Unit := do
  match cm with
  | .empty => putU8 255
  | .defn name lvls hints all ctx arena typeRoot valueRoot =>
    putU8 0
    putIdx name idx
    putIdxVec lvls idx
    putReducibilityHints hints
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
    putTag0 ⟨valueRoot⟩
  | .axio name lvls arena typeRoot =>
    putU8 1
    putIdx name idx
    putIdxVec lvls idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .quot name lvls arena typeRoot =>
    putU8 2
    putIdx name idx
    putIdxVec lvls idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .indc name lvls ctors all ctx arena typeRoot =>
    putU8 3
    putIdx name idx
    putIdxVec lvls idx
    putIdxVec ctors idx
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .ctor name lvls induct arena typeRoot =>
    putU8 4
    putIdx name idx
    putIdxVec lvls idx
    putIdx induct idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
  | .recr name lvls rules all ctx arena typeRoot ruleRoots =>
    putU8 5
    putIdx name idx
    putIdxVec lvls idx
    putIdxVec rules idx
    putIdxVec all idx
    putIdxVec ctx idx
    putExprMetaArenaIndexed arena idx
    putTag0 ⟨typeRoot⟩
    putTag0 ⟨ruleRoots.size.toUInt64⟩
    for r in ruleRoots do putTag0 ⟨r⟩

def getConstantMetaIndexed (rev : NameReverseIndex) : GetM ConstantMeta := do
  match ← getU8 with
  | 255 => pure .empty
  | 0 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let hints ← getReducibilityHints
    let all ← getIdxVec rev
    let ctx ← getIdxVec rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    let valueRoot := (← getTag0).size
    pure (.defn name lvls hints all ctx arena typeRoot valueRoot)
  | 1 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    pure (.axio name lvls arena typeRoot)
  | 2 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    pure (.quot name lvls arena typeRoot)
  | 3 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let ctors ← getIdxVec rev
    let all ← getIdxVec rev
    let ctx ← getIdxVec rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    pure (.indc name lvls ctors all ctx arena typeRoot)
  | 4 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let induct ← getIdx rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    pure (.ctor name lvls induct arena typeRoot)
  | 5 =>
    let name ← getIdx rev
    let lvls ← getIdxVec rev
    let rules ← getIdxVec rev
    let all ← getIdxVec rev
    let ctx ← getIdxVec rev
    let arena ← getExprMetaArenaIndexed rev
    let typeRoot := (← getTag0).size
    let numRuleRoots := (← getTag0).size.toNat
    let mut ruleRoots : Array UInt64 := #[]
    for _ in [0:numRuleRoots] do
      ruleRoots := ruleRoots.push (← getTag0).size
    pure (.recr name lvls rules all ctx arena typeRoot ruleRoots)
  | x => throw s!"invalid ConstantMeta tag {x}"

/-- Serialize Comm (simple - just two addresses). -/
def putComm (c : Comm) : PutM Unit := do
  Serialize.put c.secret
  Serialize.put c.payload

def getComm : GetM Comm := do
  let secret ← Serialize.get
  let payload ← Serialize.get
  pure ⟨secret, payload⟩

instance : Serialize Comm where
  put := putComm
  get := getComm

/-- Convenience serialization for Comm (untagged). -/
def serComm (c : Comm) : ByteArray := runPut (putComm c)
def desComm (bytes : ByteArray) : Except String Comm := runGet getComm bytes

/-- Serialize Comm with Tag4{0xE, 5} header. -/
def putCommTagged (c : Comm) : PutM Unit := do
  putTag4 ⟨0xE, 5⟩
  putComm c

/-- Serialize Comm with Tag4{0xE, 5} header to bytes. -/
def serCommTagged (c : Comm) : ByteArray := runPut (putCommTagged c)

/-- Compute commitment address: blake3(Tag4{0xE,5} + secret + payload). -/
def Comm.commit (c : Comm) : Address := Address.blake3 (serCommTagged c)

/-! ## Ixon Environment -/

/-- The Ixon environment, containing all compiled constants.
    Mirrors Rust's `ix::ixon::env::Env` structure. -/
structure Env where
  /-- Alpha-invariant constants: Address → Constant -/
  consts : Std.HashMap Address Constant := {}
  /-- Named references: Ix.Name → Named (includes address + metadata) -/
  named : Std.HashMap Ix.Name Named := {}
  /-- Raw data blobs: Address → bytes -/
  blobs : Std.HashMap Address ByteArray := {}
  /-- Hash-consed name components: Address → Ix.Name -/
  names : Std.HashMap Address Ix.Name := {}
  /-- Cryptographic commitments: Address → Comm -/
  comms : Std.HashMap Address Comm := {}
  /-- Reverse index: constant Address → Ix.Name -/
  addrToName : Std.HashMap Address Ix.Name := {}
  deriving Inhabited

namespace Env

/-- Store a constant at the given address. -/
def storeConst (env : Env) (addr : Address) (const : Constant) : Env :=
  { env with consts := env.consts.insert addr const }

/-- Get a constant by address. -/
def getConst? (env : Env) (addr : Address) : Option Constant :=
  env.consts.get? addr

/-- Register a name with full Named metadata. -/
def registerName (env : Env) (name : Ix.Name) (named : Named) : Env :=
  { env with
    named := env.named.insert name named
    addrToName := env.addrToName.insert named.addr name }

/-- Register a name with just an address (empty metadata). -/
def registerNameAddr (env : Env) (name : Ix.Name) (addr : Address) : Env :=
  env.registerName name { addr, constMeta := .empty }

/-- Look up a name's address. -/
def getAddr? (env : Env) (name : Ix.Name) : Option Address :=
  env.named.get? name |>.map (·.addr)

/-- Look up a name's Named entry. -/
def getNamed? (env : Env) (name : Ix.Name) : Option Named :=
  env.named.get? name

/-- Look up an address's name. -/
def getName? (env : Env) (addr : Address) : Option Ix.Name :=
  env.addrToName.get? addr

/-- Store a blob and return its content address. -/
def storeBlob (env : Env) (bytes : ByteArray) : Env × Address :=
  let addr := Address.blake3 bytes
  ({ env with blobs := env.blobs.insert addr bytes }, addr)

/-- Get a blob by address. -/
def getBlob? (env : Env) (addr : Address) : Option ByteArray :=
  env.blobs.get? addr

/-- Store a commitment. -/
def storeComm (env : Env) (addr : Address) (comm : Comm) : Env :=
  { env with comms := env.comms.insert addr comm }

/-- Get a commitment by address. -/
def getComm? (env : Env) (addr : Address) : Option Comm :=
  env.comms.get? addr

/-- Number of constants. -/
def constCount (env : Env) : Nat := env.consts.size

/-- Number of blobs. -/
def blobCount (env : Env) : Nat := env.blobs.size

/-- Number of named constants. -/
def namedCount (env : Env) : Nat := env.named.size

/-- Number of commitments. -/
def commCount (env : Env) : Nat := env.comms.size

instance : Repr Env where
  reprPrec env _ := s!"Env({env.constCount} consts, {env.blobCount} blobs, {env.namedCount} named)"

end Env

/-! ## Raw FFI Types for Env -/

/-- Raw FFI structure for a constant: Address → Constant.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawConst where
  addr : Address
  const : Constant
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a named entry: Ix.Name → (Address, ConstantMeta).
    Array-based version for FFI compatibility (no HashMap). -/
structure RawNamed where
  name : Ix.Name
  addr : Address
  constMeta : ConstantMeta
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a blob: Address → ByteArray.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawBlob where
  addr : Address
  bytes : ByteArray
  deriving Repr, Inhabited, BEq

/-- Raw FFI structure for a commitment: Address → Comm.
    Array-based version for FFI compatibility (no HashMap). -/
structure RawComm where
  addr : Address
  comm : Comm
  deriving Repr, Inhabited, BEq

/-- Raw FFI name entry: address → Ix.Name mapping.
    Used to transfer the full names table across FFI. -/
structure RawNameEntry where
  addr : Address
  name : Ix.Name
  deriving Repr, Inhabited, BEq

/-- Raw FFI environment structure using arrays instead of HashMaps.
    This is the array-based equivalent of `Env` for FFI compatibility. -/
structure RawEnv where
  consts : Array RawConst
  named : Array RawNamed
  blobs : Array RawBlob
  comms : Array RawComm
  names : Array RawNameEntry := #[]
  deriving Repr, Inhabited, BEq

namespace RawEnv

/-- Recursively add all name components to the names map.
    Uses Ix.Name.getHash for address computation. -/
partial def addNameComponents (names : Std.HashMap Address Ix.Name) (name : Ix.Name) : Std.HashMap Address Ix.Name :=
  let addr := name.getHash
  if names.contains addr then names
  else
    let names := names.insert addr name
    match name with
    | .anonymous _ => names
    | .str parent _ _ => addNameComponents names parent
    | .num parent _ _ => addNameComponents names parent

/-- Recursively add all name components to the names map AND store string components as blobs.
    This matches Rust's behavior for deduplication of string data. -/
partial def addNameComponentsWithBlobs
    (names : Std.HashMap Address Ix.Name)
    (blobs : Std.HashMap Address ByteArray)
    (name : Ix.Name)
    : Std.HashMap Address Ix.Name × Std.HashMap Address ByteArray :=
  let addr := name.getHash
  if names.contains addr then (names, blobs)
  else
    let names := names.insert addr name
    match name with
    | .anonymous _ => (names, blobs)
    | .str parent s _ =>
      -- Store string component as blob for deduplication
      let strBytes := s.toUTF8
      let strAddr := Address.blake3 strBytes
      let blobs := blobs.insert strAddr strBytes
      addNameComponentsWithBlobs names blobs parent
    | .num parent _ _ =>
      addNameComponentsWithBlobs names blobs parent

/-- Convert RawEnv to Env with HashMaps.
    This is done on the Lean side for correct hash function usage. -/
def toEnv (raw : RawEnv) : Env := Id.run do
  let mut env : Env := {}
  for ⟨addr, const⟩ in raw.consts do
    env := env.storeConst addr const
  -- Load the full names table (includes binder names, level params, etc.)
  -- Use addNameComponents to store at canonical addresses (name.getHash)
  -- and ensure all parent components are present for topological consistency.
  for ⟨_, name⟩ in raw.names do
    env := { env with names := addNameComponents env.names name }
  for ⟨name, addr, constMeta⟩ in raw.named do
    -- Also add name components for indexed serialization
    env := { env with names := addNameComponents env.names name }
    env := env.registerName name ⟨addr, constMeta⟩
  for ⟨addr, bytes⟩ in raw.blobs do
    env := { env with blobs := env.blobs.insert addr bytes }
  for ⟨addr, comm⟩ in raw.comms do
    env := env.storeComm addr comm
  return env

end RawEnv

/-! ## Env Serialization -/

namespace Env

/-- Convert Env with HashMaps to RawEnv with Arrays for FFI.
    Includes the full names table for round-trip fidelity. -/
def toRawEnv (env : Env) : RawEnv := {
  consts := env.consts.toArray.map fun (addr, const) => { addr, const }
  named := env.named.toArray.map fun (name, n) => { name, addr := n.addr, constMeta := n.constMeta }
  blobs := env.blobs.toArray.map fun (addr, bytes) => { addr, bytes }
  comms := env.comms.toArray.map fun (addr, comm) => { addr, comm }
  names := env.names.toArray.map fun (addr, name) => { addr, name }
}

/-- Tag4 flag for Env (0xE), variant 0. -/
def FLAG : UInt8 := 0xE

/-- Serialize a name component (references parent by address).
    Format: tag (1 byte) + parent_addr (32 bytes) + data -/
def putNameComponent (name : Ix.Name) : PutM Unit := do
  match name with
  | .anonymous _ => putU8 0
  | .str parent s _ =>
    putU8 1
    Serialize.put parent.getHash
    putTag0 ⟨s.utf8ByteSize.toUInt64⟩
    putBytes s.toUTF8
  | .num parent n _ =>
    putU8 2
    Serialize.put parent.getHash
    let bytes := ByteArray.mk (Nat.toBytesLE n)
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

/-- Deserialize a name component using a lookup table for parents. -/
def getNameComponent (namesLookup : Std.HashMap Address Ix.Name) : GetM Ix.Name := do
  let tag ← getU8
  match tag with
  | 0 => pure Ix.Name.mkAnon
  | 1 =>
    let parentAddr ← Serialize.get
    let parent ← match namesLookup.get? parentAddr with
      | some p => pure p
      | none => throw s!"getNameComponent: missing parent address {reprStr (toString parentAddr)}"
    let len := (← getTag0).size.toNat
    let sBytes ← getBytes len
    match String.fromUTF8? sBytes with
    | some s => pure (Ix.Name.mkStr parent s)
    | none => throw "getNameComponent: invalid UTF-8"
  | 2 =>
    let parentAddr ← Serialize.get
    let parent ← match namesLookup.get? parentAddr with
      | some p => pure p
      | none => throw s!"getNameComponent: missing parent address {reprStr (toString parentAddr)}"
    let len := (← getTag0).size.toNat
    let nBytes ← getBytes len
    pure (Ix.Name.mkNat parent (Nat.fromBytesLE nBytes.data))
  | t => throw s!"getNameComponent: invalid tag {t}"

/-- Topologically sort names so parents come before children. -/
partial def topologicalSortNames (names : Std.HashMap Address Ix.Name) : Array (Address × Ix.Name) :=
  -- DFS topological sort: visit parent before child
  -- This matches the Rust implementation
  let anonAddr := Ix.Name.mkAnon.getHash
  let rec visit (name : Ix.Name) (visited : Std.HashSet Address) (result : Array (Address × Ix.Name))
      : Std.HashSet Address × Array (Address × Ix.Name) :=
    let addr := name.getHash
    if visited.contains addr then (visited, result)
    else
      -- Visit parent first
      let (visited, result) := match name with
        | .anonymous _ => (visited, result)
        | .str parent _ _ => visit parent visited result
        | .num parent _ _ => visit parent visited result
      let visited := visited.insert addr
      let result := result.push (addr, name)
      (visited, result)
  -- Start with anonymous already visited (it's implicit)
  let initVisited : Std.HashSet Address := ({} : Std.HashSet Address).insert anonAddr
  -- Sort names by address before iterating to ensure deterministic DFS order
  let sortedEntries := names.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  let (_, result) := sortedEntries.foldl (init := (initVisited, #[])) fun (visited, result) (_, name) =>
    visit name visited result
  result

/-- Serialize an Env to bytes. -/
def putEnv (env : Env) : PutM Unit := do
  -- Header: Tag4 with flag=0xE, size=0 (Env variant)
  putTag4 ⟨FLAG, 0⟩

  -- Section 1: Blobs (Address -> bytes)
  let blobs := env.blobs.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨blobs.size.toUInt64⟩
  for (addr, bytes) in blobs do
    Serialize.put addr
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

  -- Section 2: Consts (Address -> Constant)
  let consts := env.consts.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨consts.size.toUInt64⟩
  for (addr, constant) in consts do
    Serialize.put addr
    putConstant constant

  -- Section 3: Names (Address -> Name component)
  -- Topologically sorted so parents come before children, with ties broken by address
  let sortedNames := topologicalSortNames env.names
  -- Build name index from sorted positions (matching Rust)
  let nameIdx := sortedNames.zipIdx.foldl
    (fun acc ((addr, _), i) => acc.insert addr i.toUInt64) {}
  putTag0 ⟨sortedNames.size.toUInt64⟩
  for (addr, name) in sortedNames do
    Serialize.put addr
    putNameComponent name

  -- Section 4: Named (name Address -> Named with metadata)
  let named := env.named.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨named.size.toUInt64⟩
  for (name, namedEntry) in named do
    -- Use the name's stored hash, which matches how it was stored in env.names
    Serialize.put name.getHash
    Serialize.put namedEntry.addr
    putConstantMetaIndexed namedEntry.constMeta nameIdx

  -- Section 5: Comms (Address -> Comm)
  let comms := env.comms.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
  putTag0 ⟨comms.size.toUInt64⟩
  for (addr, comm) in comms do
    Serialize.put addr
    putComm comm

/-- Deserialize an Env from bytes. -/
def getEnv : GetM Env := do
  -- Header
  let tag ← getTag4
  if tag.flag != FLAG then
    throw s!"Env.get: expected flag 0x{FLAG.toNat.toDigits 16}, got 0x{tag.flag.toNat.toDigits 16}"
  if tag.size != 0 then
    throw s!"Env.get: expected Env variant 0, got {tag.size}"

  let mut env : Env := {}

  -- Section 1: Blobs
  let numBlobs := (← getTag0).size
  for _ in [:numBlobs.toNat] do
    let addr ← Serialize.get
    let len := (← getTag0).size
    let bytes ← getBytes len.toNat
    env := { env with blobs := env.blobs.insert addr bytes }

  -- Section 2: Consts
  let numConsts := (← getTag0).size
  for _ in [:numConsts.toNat] do
    let addr ← Serialize.get
    let constant ← getConstant
    env := { env with consts := env.consts.insert addr constant }

  -- Section 3: Names (build lookup table AND reverse index)
  let numNames := (← getTag0).size
  let mut namesLookup : Std.HashMap Address Ix.Name := {}
  let mut nameRev : NameReverseIndex := #[]
  -- Always include anonymous name
  namesLookup := namesLookup.insert Ix.Name.mkAnon.getHash Ix.Name.mkAnon
  for _ in [:numNames.toNat] do
    let addr ← Serialize.get
    let name ← getNameComponent namesLookup
    nameRev := nameRev.push addr
    namesLookup := namesLookup.insert addr name
    env := { env with names := env.names.insert addr name }

  -- Section 4: Named (name Address -> Named with metadata)
  let numNamed := (← getTag0).size
  for _ in [:numNamed.toNat] do
    let nameAddr ← Serialize.get
    let constAddr : Address ← Serialize.get
    let constMeta ← getConstantMetaIndexed nameRev
    match namesLookup.get? nameAddr with
    | some name =>
      let namedEntry : Named := ⟨constAddr, constMeta⟩
      env := { env with
        named := env.named.insert name namedEntry
        addrToName := env.addrToName.insert constAddr name }
    | none =>
      throw s!"getEnv: named entry references unknown name address {reprStr (toString nameAddr)}"

  -- Section 5: Comms
  let numComms := (← getTag0).size
  for _ in [:numComms.toNat] do
    let addr ← Serialize.get (α := Address)
    let comm ← getComm
    env := { env with comms := env.comms.insert addr comm }

  pure env

end Env

/-- Serialize an Env to bytes. -/
def serEnv (env : Env) : ByteArray := runPut (Env.putEnv env)

/-- Deserialize an Env from bytes. -/
def desEnv (bytes : ByteArray) : Except String Env := runGet Env.getEnv bytes

/-- Compute section sizes for debugging. Returns (blobs, consts, names, named, comms). -/
def envSectionSizes (env : Env) : Nat × Nat × Nat × Nat × Nat := Id.run do
  -- Blobs section
  let blobsBytes := runPut do
    let blobs := env.blobs.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨blobs.size.toUInt64⟩
    for (addr, bytes) in blobs do
      Serialize.put addr
      putTag0 ⟨bytes.size.toUInt64⟩
      putBytes bytes

  -- Consts section
  let constsBytes := runPut do
    let consts := env.consts.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨consts.size.toUInt64⟩
    for (addr, constant) in consts do
      Serialize.put addr
      putConstant constant

  -- Names section
  let namesBytes := runPut do
    let sortedNames := Env.topologicalSortNames env.names
    putTag0 ⟨sortedNames.size.toUInt64⟩
    for (addr, name) in sortedNames do
      Serialize.put addr
      Env.putNameComponent name

  -- Named section
  let namedBytes := runPut do
    let sortedNames := Env.topologicalSortNames env.names
    let nameIdx : NameIndex := sortedNames.zipIdx.foldl
      (fun acc ((addr, _), i) => acc.insert addr i.toUInt64) {}
    let named := env.named.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨named.size.toUInt64⟩
    for (name, namedEntry) in named do
      Serialize.put name.getHash
      Serialize.put namedEntry.addr
      putConstantMetaIndexed namedEntry.constMeta nameIdx

  -- Comms section
  let commsBytes := runPut do
    let comms := env.comms.toList.toArray.qsort fun a b => (compare a.1 b.1).isLT
    putTag0 ⟨comms.size.toUInt64⟩
    for (addr, comm) in comms do
      Serialize.put addr
      putComm comm

  (blobsBytes.size, constsBytes.size, namesBytes.size, namedBytes.size, commsBytes.size)

/-! ## Rust FFI Serialization -/

@[extern "rs_ser_env"]
opaque rsSerEnvFFI : @& RawEnv → ByteArray

/-- Serialize an Ixon.Env to bytes using Rust. -/
def rsSerEnv (env : Env) : ByteArray :=
  rsSerEnvFFI env.toRawEnv

@[extern "rs_des_env"]
opaque rsDesEnvFFI : @& ByteArray → Except String RawEnv

/-- Deserialize bytes to an Ixon.Env using Rust. -/
def rsDesEnv (bytes : ByteArray) : Except String Env :=
  return (← rsDesEnvFFI bytes).toEnv

end Ixon
