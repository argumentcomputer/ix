import Navigatrix.Ixon.Serialize
import Navigatrix.Ixon.Address
import Navigatrix.Ixon.Univ
import Navigatrix.Ixon.Expr

/-!
# Ixon constants, v2

The addressable unit: `Constant` = `ConstantInfo` payload + sharing,
refs, and univs tables. Mirrors ix's structures and wire format (modes
ride inside `Expr`; constants themselves are unchanged in v2 — per-field
constructor usages are deferred to modal inductives).

Object-level tag space: `ConstantInfo` serializes with Tag4 flag `0xD`
(variant index in the size field) or `0xC` for mutual blocks — shared
with the `Expr` flag namespace (`0x0`–`0xB`), leaving `0xE`/`0xF` free.

Strictness upgrades over ix's decoder (candidates for the upstream
delta): `DefKind`/`DefinitionSafety` bytes are validated exactly
(ix's unpack has catch-all arms), packed-bool bytes must have no stray
high bits, and standalone `Bool` bytes must be `0` or `1`.
-/

namespace Navigatrix.Ixon

/-! ## Kind enums -/

/-- Distinguish kinds of definitions. -/
inductive DefKind where
  | defn
  | opaq
  | thm
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace DefKind

def toBits : DefKind → UInt8
  | .defn => 0
  | .opaq => 1
  | .thm => 2

def ofBits? : UInt8 → Option DefKind
  | 0 => some .defn
  | 1 => some .opaq
  | 2 => some .thm
  | _ => none

protected theorem ofBits?_toBits (k : DefKind) : ofBits? k.toBits = some k := by
  cases k <;> rfl

end DefKind

inductive DefinitionSafety where
  | unsaf
  | safe
  | part
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace DefinitionSafety

def toBits : DefinitionSafety → UInt8
  | .unsaf => 0
  | .safe => 1
  | .part => 2

def ofBits? : UInt8 → Option DefinitionSafety
  | 0 => some .unsaf
  | 1 => some .safe
  | 2 => some .part
  | _ => none

protected theorem ofBits?_toBits (s : DefinitionSafety) :
    ofBits? s.toBits = some s := by
  cases s <;> rfl

end DefinitionSafety

/-- Mirrors `Lean.QuotKind`. -/
inductive QuotKind where
  | type
  | ctor
  | lift
  | ind
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace QuotKind

def toBits : QuotKind → UInt8
  | .type => 0
  | .ctor => 1
  | .lift => 2
  | .ind => 3

def ofBits? : UInt8 → Option QuotKind
  | 0 => some .type
  | 1 => some .ctor
  | 2 => some .lift
  | 3 => some .ind
  | _ => none

protected theorem ofBits?_toBits (q : QuotKind) : ofBits? q.toBits = some q := by
  cases q <;> rfl

end QuotKind

/-! ## Constant structures -/

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
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, Repr, Inhabited

structure InductiveProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure ConstructorProj where
  idx : UInt64
  cidx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure RecursorProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

structure DefinitionProj where
  idx : UInt64
  block : Address
  deriving BEq, Repr, Inhabited

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

def FLAG_MUTS : UInt8 := 0xC
def FLAG : UInt8 := 0xD

end Constant

/-! ## Serialization -/

def putDefinition (d : Definition) : PutM Unit := do
  putU8 ((d.kind.toBits <<< 2) ||| d.safety.toBits)
  putTag0 ⟨d.lvls⟩
  putExpr d.typ
  putExpr d.value

def getDefinition : GetM Definition := do
  let b ← getU8
  match DefKind.ofBits? (b >>> 2), DefinitionSafety.ofBits? (b &&& 0x3) with
  | some kind, some safety =>
    let lvls := (← getTag0).size
    let typ ← getExpr
    let value ← getExpr
    return ⟨kind, safety, lvls, typ, value⟩
  | _, _ => throw s!"getDefinition: invalid kind/safety byte {b}"

def putRecursorRule (r : RecursorRule) : PutM Unit := do
  putTag0 ⟨r.fields⟩
  putExpr r.rhs

def getRecursorRule : GetM RecursorRule := do
  let fields := (← getTag0).size
  let rhs ← getExpr
  return ⟨fields, rhs⟩

def putRecursor (r : Recursor) : PutM Unit := do
  putU8 ((if r.k then 1 else 0) ||| (if r.isUnsafe then 2 else 0))
  putTag0 ⟨r.lvls⟩
  putTag0 ⟨r.params⟩
  putTag0 ⟨r.indices⟩
  putTag0 ⟨r.motives⟩
  putTag0 ⟨r.minors⟩
  putExpr r.typ
  putTag0 ⟨r.rules.size.toUInt64⟩
  for rule in r.rules do putRecursorRule rule

def getRecursor : GetM Recursor := do
  let b ← getU8
  if b >= 4 then throw s!"getRecursor: invalid bool byte {b}"
  let k := b &&& 1 != 0
  let isUnsafe := b &&& 2 != 0
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

def putAxiom (a : Axiom) : PutM Unit := do
  putU8 (if a.isUnsafe then 1 else 0)
  putTag0 ⟨a.lvls⟩
  putExpr a.typ

def getAxiom : GetM Axiom := do
  let isUnsafe ← getBool01
  let lvls := (← getTag0).size
  let typ ← getExpr
  return ⟨isUnsafe, lvls, typ⟩

def putQuotient (q : Quotient) : PutM Unit := do
  putU8 q.kind.toBits
  putTag0 ⟨q.lvls⟩
  putExpr q.typ

def getQuotient : GetM Quotient := do
  let b ← getU8
  match QuotKind.ofBits? b with
  | none => throw s!"getQuotient: invalid QuotKind byte {b}"
  | some kind =>
    let lvls := (← getTag0).size
    let typ ← getExpr
    return ⟨kind, lvls, typ⟩

def putConstructor (c : Constructor) : PutM Unit := do
  putU8 (if c.isUnsafe then 1 else 0)
  putTag0 ⟨c.lvls⟩
  putTag0 ⟨c.cidx⟩
  putTag0 ⟨c.params⟩
  putTag0 ⟨c.fields⟩
  putExpr c.typ

def getConstructor : GetM Constructor := do
  let isUnsafe ← getBool01
  let lvls := (← getTag0).size
  let cidx := (← getTag0).size
  let params := (← getTag0).size
  let fields := (← getTag0).size
  let typ ← getExpr
  return ⟨isUnsafe, lvls, cidx, params, fields, typ⟩

def putInductive (i : Inductive) : PutM Unit := do
  putU8 (if i.isUnsafe then 1 else 0)
  putTag0 ⟨i.lvls⟩
  putTag0 ⟨i.params⟩
  putTag0 ⟨i.indices⟩
  putExpr i.typ
  putTag0 ⟨i.ctors.size.toUInt64⟩
  for c in i.ctors do putConstructor c

def getInductive : GetM Inductive := do
  let isUnsafe ← getBool01
  let lvls := (← getTag0).size
  let params := (← getTag0).size
  let indices := (← getTag0).size
  let typ ← getExpr
  let numCtors := (← getTag0).size.toNat
  let mut ctors := #[]
  for _ in [0:numCtors] do
    ctors := ctors.push (← getConstructor)
  return ⟨isUnsafe, lvls, params, indices, typ, ctors⟩

def putInductiveProj (p : InductiveProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getInductiveProj : GetM InductiveProj := do
  let idx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, block⟩

def putConstructorProj (p : ConstructorProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  putTag0 ⟨p.cidx⟩
  Serialize.put p.block

def getConstructorProj : GetM ConstructorProj := do
  let idx := (← getTag0).size
  let cidx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, cidx, block⟩

def putRecursorProj (p : RecursorProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getRecursorProj : GetM RecursorProj := do
  let idx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, block⟩

def putDefinitionProj (p : DefinitionProj) : PutM Unit := do
  putTag0 ⟨p.idx⟩
  Serialize.put p.block

def getDefinitionProj : GetM DefinitionProj := do
  let idx := (← getTag0).size
  let block ← Serialize.get
  return ⟨idx, block⟩

def putMutConst : MutConst → PutM Unit
  | .defn d => do putU8 0; putDefinition d
  | .indc i => do putU8 1; putInductive i
  | .recr r => do putU8 2; putRecursor r

def getMutConst : GetM MutConst := do
  match ← getU8 with
  | 0 => .defn <$> getDefinition
  | 1 => .indc <$> getInductive
  | 2 => .recr <$> getRecursor
  | t => throw s!"getMutConst: invalid tag {t}"

def putConstantInfo : ConstantInfo → PutM Unit
  | .defn d => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_DEFN⟩; putDefinition d
  | .recr r => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_RECR⟩; putRecursor r
  | .axio a => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩; putAxiom a
  | .quot q => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_QUOT⟩; putQuotient q
  | .cPrj p => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_CPRJ⟩; putConstructorProj p
  | .rPrj p => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_RPRJ⟩; putRecursorProj p
  | .iPrj p => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_IPRJ⟩; putInductiveProj p
  | .dPrj p => do putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_DPRJ⟩; putDefinitionProj p
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

/-! Elaboration-time roundtrip and canonicity checks. -/

private def constRoundtrips (c : Constant) : Bool :=
  match (de (ser c) : Except String Constant) with
  | .ok c' => c' == c
  | .error _ => false

private def addr (b : UInt8) : Address :=
  ⟨ByteArray.mk (Array.mk (List.replicate 32 b))⟩

#guard constRoundtrips
  { info := .defn
      { kind := .thm, safety := .safe, lvls := 2
        typ := .all .many .shared (.sort 1) (.sort 1)
        value := .lam .linear (.var 0) (.var 0) }
    sharing := #[.app (.var 0) (.var 1)]
    refs := #[addr 0xAB]
    univs := #[.var 0, .succ (.var 1)] }

#guard constRoundtrips
  { info := .axio { isUnsafe := false, lvls := 1, typ := .sort 3 }
    sharing := #[], refs := #[], univs := #[.zero] }

#guard constRoundtrips
  { info := .quot { kind := .lift, lvls := 0, typ := .var 0 }
    sharing := #[], refs := #[], univs := #[] }

#guard constRoundtrips
  { info := .cPrj { idx := 1, cidx := 2, block := addr 0x01 }
    sharing := #[], refs := #[], univs := #[] }

#guard constRoundtrips
  { info := .muts #[
      .defn { kind := .defn, safety := .part, lvls := 0
              typ := .sort 0, value := .nat 0 },
      .indc { isUnsafe := false, lvls := 1, params := 1, indices := 0
              typ := .all .many .shared (.sort 1) (.sort 1)
              ctors := #[{ isUnsafe := false, lvls := 1, cidx := 0
                           params := 1, fields := 2, typ := .var 0 }] },
      .recr { k := true, isUnsafe := false, lvls := 1, params := 1
              indices := 0, motives := 1, minors := 2, typ := .sort 0
              rules := #[{ fields := 2, rhs := .var 1 }] }]
    sharing := #[.share 0]
    refs := #[addr 0x02, addr 0x03]
    univs := #[.imax (.var 0) .zero] }

private def constRejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Constant) with
  | .ok _ => false
  | .error _ => true

-- ConstantInfo variant 8 (out of range; large-form Tag4 size)
#guard constRejects #[0xD8, 0x08]
-- defn with invalid kind bits (0x0F: kind = 3)
#guard constRejects #[0xD0, 0x0F]
-- recursor with stray high bits in the packed-bool byte
#guard constRejects #[0xD1, 0x04]
-- axiom with non-canonical Bool byte 2
#guard constRejects #[0xD2, 0x02]

end Navigatrix.Ixon
