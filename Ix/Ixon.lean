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
  def FLAG_RECUR : UInt8 := 0x3
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

inductive DefKind where
  | defn : DefKind
  | opaq : DefKind
  | thm : DefKind
  deriving BEq, Repr, Inhabited, Hashable, DecidableEq

inductive DefinitionSafety where
  | unsaf : DefinitionSafety
  | safe : DefinitionSafety
  | part : DefinitionSafety
  deriving BEq, Repr, Inhabited, Hashable, DecidableEq

inductive QuotKind where
  | type : QuotKind
  | ctor : QuotKind
  | lift : QuotKind
  | ind : QuotKind
  deriving BEq, Repr, Inhabited, Hashable, DecidableEq

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

namespace Constant
  def FLAG : UInt8 := 0xD
  def FLAG_MUTS : UInt8 := 0xC
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
  let k := match ← getU8 with | 0 => QuotKind.type | 1 => .ctor | 2 => .lift | _ => .ind
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

/-! ## Ixon Environment -/

/-- The Ixon environment, containing all compiled constants.
    Mirrors Rust's `ix::ixon::env::Env` structure. -/
structure Env where
  /-- Alpha-invariant constants: Address → Constant -/
  consts : Std.HashMap Address Constant := {}
  /-- Named references: Name → Address -/
  named : Std.HashMap Lean.Name Address := {}
  /-- Raw data blobs: Address → bytes -/
  blobs : Std.HashMap Address ByteArray := {}
  /-- Hash-consed name components: Address → Name -/
  names : Std.HashMap Address Lean.Name := {}
  /-- Reverse index: constant Address → Name -/
  addrToName : Std.HashMap Address Lean.Name := {}
  deriving Inhabited

namespace Env

/-- Store a constant at the given address. -/
def storeConst (env : Env) (addr : Address) (const : Constant) : Env :=
  { env with consts := env.consts.insert addr const }

/-- Get a constant by address. -/
def getConst? (env : Env) (addr : Address) : Option Constant :=
  env.consts.get? addr

/-- Register a name mapping. -/
def registerName (env : Env) (name : Lean.Name) (addr : Address) : Env :=
  { env with
    named := env.named.insert name addr
    addrToName := env.addrToName.insert addr name }

/-- Look up a name's address. -/
def getAddr? (env : Env) (name : Lean.Name) : Option Address :=
  env.named.get? name

/-- Look up an address's name. -/
def getName? (env : Env) (addr : Address) : Option Lean.Name :=
  env.addrToName.get? addr

/-- Store a blob and return its content address. -/
def storeBlob (env : Env) (bytes : ByteArray) : Env × Address :=
  let addr := Address.blake3 bytes
  ({ env with blobs := env.blobs.insert addr bytes }, addr)

/-- Get a blob by address. -/
def getBlob? (env : Env) (addr : Address) : Option ByteArray :=
  env.blobs.get? addr

/-- Number of constants. -/
def constCount (env : Env) : Nat := env.consts.size

/-- Number of blobs. -/
def blobCount (env : Env) : Nat := env.blobs.size

/-- Number of named constants. -/
def namedCount (env : Env) : Nat := env.named.size

instance : Repr Env where
  reprPrec env _ := s!"Env({env.constCount} consts, {env.blobCount} blobs, {env.namedCount} named)"

end Env

/-! ## Env Serialization -/

namespace Env

/-- Tag4 flag for Env (0xE). -/
def FLAG : UInt8 := 0xE

/-- Env format version. -/
def VERSION : UInt64 := 2

/-- Compute blake3 hash of a Lean.Name. -/
def hashName (name : Lean.Name) : Address :=
  -- Use the same approach as Rust: hash the name's components
  let rec hashRec : Lean.Name → ByteArray
    | .anonymous => ByteArray.mk #[0]
    | .str parent s =>
      let parentHash := hashRec parent
      let sBytes := s.toUTF8
      -- Combine: tag(1) + parent_hash + string
      ByteArray.mk #[1] ++ parentHash ++ sBytes
    | .num parent n =>
      let parentHash := hashRec parent
      let nBytes := ByteArray.mk (Nat.toBytesLE n)
      -- Combine: tag(2) + parent_hash + num
      ByteArray.mk #[2] ++ parentHash ++ nBytes
  Address.blake3 (hashRec name)

/-- Serialize a name component (references parent by address).
    Format: tag (1 byte) + parent_addr (32 bytes) + data -/
def putNameComponent (name : Lean.Name) : PutM Unit := do
  match name with
  | .anonymous => putU8 0
  | .str parent s =>
    putU8 1
    Serialize.put (hashName parent)
    putTag0 ⟨s.utf8ByteSize.toUInt64⟩
    putBytes s.toUTF8
  | .num parent n =>
    putU8 2
    Serialize.put (hashName parent)
    let bytes := ByteArray.mk (Nat.toBytesLE n)
    putTag0 ⟨bytes.size.toUInt64⟩
    putBytes bytes

/-- Deserialize a name component using a lookup table for parents. -/
def getNameComponent (namesLookup : Std.HashMap Address Lean.Name) : GetM Lean.Name := do
  let tag ← getU8
  match tag with
  | 0 => pure .anonymous
  | 1 =>
    let parentAddr ← Serialize.get
    let parent := namesLookup.getD parentAddr .anonymous
    let len := (← getTag0).size.toNat
    let sBytes ← getBytes len
    match String.fromUTF8? sBytes with
    | some s => pure (.str parent s)
    | none => throw "getNameComponent: invalid UTF-8"
  | 2 =>
    let parentAddr ← Serialize.get
    let parent := namesLookup.getD parentAddr .anonymous
    let len := (← getTag0).size.toNat
    let nBytes ← getBytes len
    pure (.num parent (Nat.fromBytesLE nBytes.data))
  | t => throw s!"getNameComponent: invalid tag {t}"

/-- Topologically sort names so parents come before children. -/
def topologicalSortNames (names : Std.HashMap Address Lean.Name) : Array (Address × Lean.Name) :=
  -- Sort by depth (anonymous=0, str/num = 1 + parent depth)
  let rec depth : Lean.Name → Nat
    | .anonymous => 0
    | .str parent _ => 1 + depth parent
    | .num parent _ => 1 + depth parent
  let pairs := names.toList.toArray
  pairs.qsort fun (_, n1) (_, n2) => depth n1 < depth n2

/-- Serialize an Env to bytes. -/
def putEnv (env : Env) : PutM Unit := do
  -- Header: Tag4 with flag=0xE, size=version
  putTag4 ⟨FLAG, VERSION⟩

  -- Section 1: Blobs (Address -> bytes)
  let blobs := env.blobs.toList.toArray
  putU64LE blobs.size.toUInt64
  for (addr, bytes) in blobs do
    Serialize.put addr
    putU64LE bytes.size.toUInt64
    putBytes bytes

  -- Section 2: Consts (Address -> Constant)
  let consts := env.consts.toList.toArray
  putU64LE consts.size.toUInt64
  for (addr, constant) in consts do
    Serialize.put addr
    putConstant constant

  -- Section 3: Names (Address -> Name component)
  -- Topologically sorted so parents come before children
  let sortedNames := topologicalSortNames env.names
  putU64LE sortedNames.size.toUInt64
  for (addr, name) in sortedNames do
    Serialize.put addr
    putNameComponent name

  -- Section 4: Named (name Address -> const Address)
  -- Simplified: just address, no metadata
  let named := env.named.toList.toArray
  putU64LE named.size.toUInt64
  for (name, constAddr) in named do
    let nameAddr := hashName name
    Serialize.put nameAddr
    Serialize.put constAddr
    -- Empty metadata placeholder (ConstantMeta default)
    putU8 0  -- ConstantMeta flag for empty

  -- Section 5: Comms (empty)
  putU64LE 0

/-- Deserialize an Env from bytes. -/
def getEnv : GetM Env := do
  -- Header
  let tag ← getTag4
  if tag.flag != FLAG then
    throw s!"Env.get: expected flag 0x{FLAG.toNat.toDigits 16}, got 0x{tag.flag.toNat.toDigits 16}"
  if tag.size != VERSION then
    throw s!"Env.get: unsupported version {tag.size}"

  let mut env : Env := {}

  -- Section 1: Blobs
  let numBlobs ← getU64LE
  for _ in [:numBlobs.toNat] do
    let addr ← Serialize.get
    let len ← getU64LE
    let bytes ← getBytes len.toNat
    env := { env with blobs := env.blobs.insert addr bytes }

  -- Section 2: Consts
  let numConsts ← getU64LE
  for _ in [:numConsts.toNat] do
    let addr ← Serialize.get
    let constant ← getConstant
    env := { env with consts := env.consts.insert addr constant }

  -- Section 3: Names (build lookup table)
  let numNames ← getU64LE
  let mut namesLookup : Std.HashMap Address Lean.Name := {}
  -- Always include anonymous name
  namesLookup := namesLookup.insert (hashName .anonymous) .anonymous
  for _ in [:numNames.toNat] do
    let addr ← Serialize.get
    let name ← getNameComponent namesLookup
    namesLookup := namesLookup.insert addr name
    env := { env with names := env.names.insert addr name }

  -- Section 4: Named
  let numNamed ← getU64LE
  for _ in [:numNamed.toNat] do
    let nameAddr ← Serialize.get
    let constAddr : Address ← Serialize.get
    let _ ← getU8  -- Skip metadata flag
    match namesLookup.get? nameAddr with
    | some name =>
      env := { env with
        named := env.named.insert name constAddr
        addrToName := env.addrToName.insert constAddr name }
    | none =>
      -- Name not in lookup, skip
      pure ()

  -- Section 5: Comms (skip)
  let numComms ← getU64LE
  for _ in [:numComms.toNat] do
    let _ ← Serialize.get (α := Address)
    -- Skip comm data - for now just fail if there are any
    throw "getEnv: comms not supported in Lean"

  pure env

end Env

/-- Serialize an Env to bytes. -/
def serEnv (env : Env) : ByteArray := runPut (Env.putEnv env)

/-- Deserialize an Env from bytes. -/
def desEnv (bytes : ByteArray) : Except String Env := runGet Env.getEnv bytes

end Ixon
