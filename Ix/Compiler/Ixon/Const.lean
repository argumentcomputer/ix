import Ix.Compiler.Ixon.Serialize
import Ix.Compiler.Ixon.Address
import Ix.Compiler.Ixon.Univ
import Ix.Compiler.Ixon.Expr
import Ix.Compiler.Ixon.Sharing.Basic

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
high bits, standalone `Bool` bytes must be `0` or `1`, and sharing tables
must be acyclic/backward-only, non-aliasing, body-bounded, and free of dead
or singleton entries.
-/

namespace Ix.Compiler.Ixon

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
  deriving BEq, DecidableEq, Repr, Inhabited

structure RecursorRule where
  fields : UInt64
  rhs : Expr
  deriving BEq, DecidableEq, Repr, Inhabited

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
  deriving BEq, DecidableEq, Repr, Inhabited

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
  deriving BEq, DecidableEq, Repr, Inhabited

structure Inductive where
  isUnsafe : Bool
  lvls : UInt64
  params : UInt64
  indices : UInt64
  typ : Expr
  ctors : Array Constructor
  deriving BEq, DecidableEq, Repr, Inhabited

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
  deriving BEq, DecidableEq, Repr, Inhabited

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

/-- Recover the member table used when a constant is entered as its own
evaluation/checking frame. Standalone definitions and recursors behave as
singleton blocks; projections, axioms, quotients, and inductive projections
have no local `recur` members.

This belongs to the constant layer because both the evaluator and the usage
checker interpret the same serialized `ConstantInfo` shape. -/
def selfMutsOf : ConstantInfo → Array MutConst
  | .muts members => members
  | .defn definition => #[.defn definition]
  | .recr recursor => #[.recr recursor]
  | _ => #[]

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

/-! ## Embedded expression enumeration

This is the authoritative body order consumed by the sharing-table checker.
It covers every expression in a constant payload; projections contain none. -/

def Definition.exprs (d : Definition) : List Expr := [d.typ, d.value]

def Recursor.exprs (r : Recursor) : List Expr :=
  r.typ :: r.rules.toList.map (·.rhs)

def Axiom.exprs (a : Axiom) : List Expr := [a.typ]

def Quotient.exprs (q : Quotient) : List Expr := [q.typ]

def Constructor.exprs (c : Constructor) : List Expr := [c.typ]

def Inductive.exprs (i : Inductive) : List Expr :=
  i.typ :: i.ctors.toList.flatMap Constructor.exprs

def MutConst.exprs : MutConst → List Expr
  | .defn d => d.exprs
  | .indc i => i.exprs
  | .recr r => r.exprs

def ConstantInfo.exprs : ConstantInfo → List Expr
  | .defn d => d.exprs
  | .recr r => r.exprs
  | .axio a => a.exprs
  | .quot q => q.exprs
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => []
  | .muts ms => ms.toList.flatMap MutConst.exprs

/-- The cheap, decoder-enforced sharing invariant for a complete constant. -/
def Constant.sharingWF (c : Constant) : Bool :=
  Sharing.layer1WF c.sharing c.info.exprs.toArray

/-! ## Wire representability

Counted arrays are mathematical `Array`s in Lean but carry `UInt64` lengths
on the wire. These predicates state exactly the recursive fragment whose
encoder counts do not wrap. -/

def Definition.wireWF (d : Definition) : Prop :=
  d.typ.wireWF ∧ d.value.wireWF

def RecursorRule.wireWF (r : RecursorRule) : Prop :=
  r.rhs.wireWF

def Recursor.wireWF (r : Recursor) : Prop :=
  r.typ.wireWF ∧
    r.rules.size < UInt64.size ∧
    ∀ rule ∈ r.rules, rule.wireWF

def Axiom.wireWF (a : Axiom) : Prop :=
  a.typ.wireWF

def Quotient.wireWF (q : Quotient) : Prop :=
  q.typ.wireWF

def Constructor.wireWF (c : Constructor) : Prop :=
  c.typ.wireWF

def Inductive.wireWF (i : Inductive) : Prop :=
  i.typ.wireWF ∧
    i.ctors.size < UInt64.size ∧
    ∀ ctor ∈ i.ctors, ctor.wireWF

def MutConst.wireWF : MutConst → Prop
  | .defn d => d.wireWF
  | .indc i => i.wireWF
  | .recr r => r.wireWF

def ConstantInfo.wireWF : ConstantInfo → Prop
  | .defn d => d.wireWF
  | .recr r => r.wireWF
  | .axio a => a.wireWF
  | .quot q => q.wireWF
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => True
  | .muts ms =>
    ms.size < UInt64.size ∧ ∀ member ∈ ms, member.wireWF

def Constant.wireWF (c : Constant) : Prop :=
  c.info.wireWF ∧
    c.sharing.size < UInt64.size ∧
    (∀ e ∈ c.sharing, e.wireWF) ∧
    c.refs.size < UInt64.size ∧
    c.univs.size < UInt64.size

/-! ## Serialization -/

def encodedListBytes (encode : α → ByteArray) : List α → ByteArray
  | [] => ByteArray.empty
  | value :: values => encode value ++ encodedListBytes encode values

def encodedArrayBytes (encode : α → ByteArray) (values : Array α) : ByteArray :=
  encodedListBytes encode values.toList

def countedArrayBytes (encode : α → ByteArray) (values : Array α) : ByteArray :=
  tag0Bytes ⟨values.size.toUInt64⟩ ++ encodedArrayBytes encode values

def getListN (getOne : GetM α) : Nat → GetM (List α)
  | 0 => pure []
  | count + 1 => do
    let value ← getOne
    return value :: (← getListN getOne count)

def getArrayN (getOne : GetM α) (count : Nat) : GetM (Array α) := do
  return (← getListN getOne count).toArray

def getPairM (getLeft : GetM α) (getRight : GetM β) : GetM (α × β) := do
  let left ← getLeft
  let right ← getRight
  return (left, right)

def getCountedArray (getOne : GetM α) : GetM (Array α) := do
  let count ← getTag0
  getArrayN getOne count.size.toNat

def definitionModeByte (kind : DefKind) (safety : DefinitionSafety) : UInt8 :=
  (kind.toBits <<< 2) ||| safety.toBits

def recursorModeByte (k isUnsafe : Bool) : UInt8 :=
  (if k then 1 else 0) ||| (if isUnsafe then 2 else 0)

def boolBytes (value : Bool) : ByteArray :=
  u8Bytes (if value then 1 else 0)

def definitionModeOfByte? (b : UInt8) : Option (DefKind × DefinitionSafety) :=
  match DefKind.ofBits? (b >>> 2), DefinitionSafety.ofBits? (b &&& 0x3) with
  | some kind, some safety => some (kind, safety)
  | _, _ => none

def recursorModeOfByte? (b : UInt8) : Option (Bool × Bool) :=
  if b >= 4 then none else some (b &&& 1 != 0, b &&& 2 != 0)

def boolOfByte? : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def getDecodedU8 (what : String) (decode : UInt8 → Option α) : GetM α := do
  let b ← getU8
  match decode b with
  | some value => return value
  | none => throw s!"{what}: invalid byte {b}"

def definitionBytes (d : Definition) : ByteArray :=
  u8Bytes (definitionModeByte d.kind d.safety) ++
    tag0Bytes ⟨d.lvls⟩ ++ exprBytes d.typ ++ exprBytes d.value

def recursorRuleBytes (r : RecursorRule) : ByteArray :=
  tag0Bytes ⟨r.fields⟩ ++ exprBytes r.rhs

def recursorBytes (r : Recursor) : ByteArray :=
  u8Bytes (recursorModeByte r.k r.isUnsafe) ++
    tag0Bytes ⟨r.lvls⟩ ++ tag0Bytes ⟨r.params⟩ ++
    tag0Bytes ⟨r.indices⟩ ++ tag0Bytes ⟨r.motives⟩ ++
    tag0Bytes ⟨r.minors⟩ ++ exprBytes r.typ ++
    countedArrayBytes recursorRuleBytes r.rules

def axiomBytes (a : Axiom) : ByteArray :=
  boolBytes a.isUnsafe ++
    tag0Bytes ⟨a.lvls⟩ ++ exprBytes a.typ

def quotientBytes (q : Quotient) : ByteArray :=
  u8Bytes q.kind.toBits ++ tag0Bytes ⟨q.lvls⟩ ++ exprBytes q.typ

def constructorBytes (c : Constructor) : ByteArray :=
  boolBytes c.isUnsafe ++
    tag0Bytes ⟨c.lvls⟩ ++ tag0Bytes ⟨c.cidx⟩ ++
    tag0Bytes ⟨c.params⟩ ++ tag0Bytes ⟨c.fields⟩ ++ exprBytes c.typ

def inductiveBytes (i : Inductive) : ByteArray :=
  boolBytes i.isUnsafe ++
    tag0Bytes ⟨i.lvls⟩ ++ tag0Bytes ⟨i.params⟩ ++
    tag0Bytes ⟨i.indices⟩ ++ exprBytes i.typ ++
    countedArrayBytes constructorBytes i.ctors

def inductiveProjBytes (p : InductiveProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def constructorProjBytes (p : ConstructorProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ tag0Bytes ⟨p.cidx⟩ ++ p.block.hash

def recursorProjBytes (p : RecursorProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def definitionProjBytes (p : DefinitionProj) : ByteArray :=
  tag0Bytes ⟨p.idx⟩ ++ p.block.hash

def mutConstPayloadBytes : MutConst → ByteArray
  | .defn d => definitionBytes d
  | .indc i => inductiveBytes i
  | .recr r => recursorBytes r

def mutConstTag : MutConst → UInt8
  | .defn _ => 0
  | .indc _ => 1
  | .recr _ => 2

def mutConstBytes (m : MutConst) : ByteArray :=
  u8Bytes (mutConstTag m) ++ mutConstPayloadBytes m

def constantInfoTag : ConstantInfo → Tag4
  | .defn _ => ⟨Constant.FLAG, ConstantInfo.CONST_DEFN⟩
  | .recr _ => ⟨Constant.FLAG, ConstantInfo.CONST_RECR⟩
  | .axio _ => ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  | .quot _ => ⟨Constant.FLAG, ConstantInfo.CONST_QUOT⟩
  | .cPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_CPRJ⟩
  | .rPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_RPRJ⟩
  | .iPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_IPRJ⟩
  | .dPrj _ => ⟨Constant.FLAG, ConstantInfo.CONST_DPRJ⟩
  | .muts ms => ⟨Constant.FLAG_MUTS, ms.size.toUInt64⟩

def constantInfoPayloadBytes : ConstantInfo → ByteArray
  | .defn d => definitionBytes d
  | .recr r => recursorBytes r
  | .axio a => axiomBytes a
  | .quot q => quotientBytes q
  | .cPrj p => constructorProjBytes p
  | .rPrj p => recursorProjBytes p
  | .iPrj p => inductiveProjBytes p
  | .dPrj p => definitionProjBytes p
  | .muts ms => encodedArrayBytes mutConstBytes ms

def constantInfoBytes (info : ConstantInfo) : ByteArray :=
  tag4Bytes (constantInfoTag info) ++ constantInfoPayloadBytes info

def constantTablesBytes (c : Constant) : ByteArray :=
  countedArrayBytes exprBytes c.sharing ++
    countedArrayBytes (fun a : Address => a.hash) c.refs ++
    countedArrayBytes univBytes c.univs

def constantBytes (c : Constant) : ByteArray :=
  constantInfoBytes c.info ++ constantTablesBytes c

def putDefinition (d : Definition) : PutM Unit := putBytes (definitionBytes d)
def putRecursorRule (r : RecursorRule) : PutM Unit := putBytes (recursorRuleBytes r)
def putRecursor (r : Recursor) : PutM Unit := putBytes (recursorBytes r)
def putAxiom (a : Axiom) : PutM Unit := putBytes (axiomBytes a)
def putQuotient (q : Quotient) : PutM Unit := putBytes (quotientBytes q)
def putConstructor (c : Constructor) : PutM Unit := putBytes (constructorBytes c)
def putInductive (i : Inductive) : PutM Unit := putBytes (inductiveBytes i)
def putInductiveProj (p : InductiveProj) : PutM Unit :=
  putBytes (inductiveProjBytes p)
def putConstructorProj (p : ConstructorProj) : PutM Unit :=
  putBytes (constructorProjBytes p)
def putRecursorProj (p : RecursorProj) : PutM Unit :=
  putBytes (recursorProjBytes p)
def putDefinitionProj (p : DefinitionProj) : PutM Unit :=
  putBytes (definitionProjBytes p)
def putMutConst (m : MutConst) : PutM Unit := putBytes (mutConstBytes m)
def putConstantInfo (info : ConstantInfo) : PutM Unit :=
  putBytes (constantInfoBytes info)
def putConstant (c : Constant) : PutM Unit := putBytes (constantBytes c)

theorem putDefinition_spec (d : Definition) :
    PutSpec (putDefinition d) (definitionBytes d) := putBytes_spec _
theorem putRecursorRule_spec (r : RecursorRule) :
    PutSpec (putRecursorRule r) (recursorRuleBytes r) := putBytes_spec _
theorem putRecursor_spec (r : Recursor) :
    PutSpec (putRecursor r) (recursorBytes r) := putBytes_spec _
theorem putAxiom_spec (a : Axiom) :
    PutSpec (putAxiom a) (axiomBytes a) := putBytes_spec _
theorem putQuotient_spec (q : Quotient) :
    PutSpec (putQuotient q) (quotientBytes q) := putBytes_spec _
theorem putConstructor_spec (c : Constructor) :
    PutSpec (putConstructor c) (constructorBytes c) := putBytes_spec _
theorem putInductive_spec (i : Inductive) :
    PutSpec (putInductive i) (inductiveBytes i) := putBytes_spec _
theorem putInductiveProj_spec (p : InductiveProj) :
    PutSpec (putInductiveProj p) (inductiveProjBytes p) := putBytes_spec _
theorem putConstructorProj_spec (p : ConstructorProj) :
    PutSpec (putConstructorProj p) (constructorProjBytes p) := putBytes_spec _
theorem putRecursorProj_spec (p : RecursorProj) :
    PutSpec (putRecursorProj p) (recursorProjBytes p) := putBytes_spec _
theorem putDefinitionProj_spec (p : DefinitionProj) :
    PutSpec (putDefinitionProj p) (definitionProjBytes p) := putBytes_spec _
theorem putMutConst_spec (m : MutConst) :
    PutSpec (putMutConst m) (mutConstBytes m) := putBytes_spec _
theorem putConstantInfo_spec (info : ConstantInfo) :
    PutSpec (putConstantInfo info) (constantInfoBytes info) := putBytes_spec _
theorem putConstant_spec (c : Constant) :
    PutSpec (putConstant c) (constantBytes c) := putBytes_spec _

def getDefinitionMode : GetM (DefKind × DefinitionSafety) := do
  getDecodedU8 "getDefinition" definitionModeOfByte?

def getRecursorMode : GetM (Bool × Bool) := do
  getDecodedU8 "getRecursor" recursorModeOfByte?

def getQuotKind : GetM QuotKind := do
  getDecodedU8 "getQuotient" QuotKind.ofBits?

def getStrictBool (what : String) : GetM Bool := do
  getDecodedU8 what boolOfByte?

def getDefinition : GetM Definition :=
  (fun raw =>
    ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1, raw.2.2.2⟩) <$>
    getPairM getDefinitionMode
      (getPairM getTag0 (getPairM getExpr getExpr))

def getRecursorRule : GetM RecursorRule :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$> getPairM getTag0 getExpr

def getRecursor : GetM Recursor :=
  (fun raw =>
    ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1.size,
      raw.2.2.2.1.size, raw.2.2.2.2.1.size, raw.2.2.2.2.2.1.size,
      raw.2.2.2.2.2.2.1, raw.2.2.2.2.2.2.2⟩) <$>
    getPairM getRecursorMode
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getTag0
            (getPairM getTag0
              (getPairM getTag0
                (getPairM getExpr (getCountedArray getRecursorRule)))))))

def getAxiom : GetM Axiom :=
  (fun raw => ⟨raw.1, raw.2.1.size, raw.2.2⟩) <$>
    getPairM (getStrictBool "getAxiom") (getPairM getTag0 getExpr)

def getQuotient : GetM Quotient :=
  (fun raw => ⟨raw.1, raw.2.1.size, raw.2.2⟩) <$>
    getPairM getQuotKind (getPairM getTag0 getExpr)

def getConstructor : GetM Constructor :=
  (fun raw =>
    ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
      raw.2.2.2.2.1.size, raw.2.2.2.2.2⟩) <$>
    getPairM (getStrictBool "getConstructor")
      (getPairM getTag0
        (getPairM getTag0 (getPairM getTag0 (getPairM getTag0 getExpr))))

def getInductive : GetM Inductive :=
  (fun raw =>
    ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
      raw.2.2.2.2.1, raw.2.2.2.2.2⟩) <$>
    getPairM (getStrictBool "getInductive")
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getTag0
            (getPairM getExpr (getCountedArray getConstructor)))))

def getInductiveProj : GetM InductiveProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getConstructorProj : GetM ConstructorProj :=
  (fun raw => ⟨raw.1.size, raw.2.1.size, raw.2.2⟩) <$>
    getPairM getTag0 (getPairM getTag0 Serialize.get)

def getRecursorProj : GetM RecursorProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getDefinitionProj : GetM DefinitionProj :=
  (fun raw => ⟨raw.1.size, raw.2⟩) <$>
    getPairM getTag0 Serialize.get

def getMutConstTag (tag : UInt8) : GetM MutConst := do
  match tag with
  | 0 => .defn <$> getDefinition
  | 1 => .indc <$> getInductive
  | 2 => .recr <$> getRecursor
  | t => throw s!"getMutConst: invalid tag {t}"

def getMutConst : GetM MutConst := do
  getMutConstTag (← getU8)

def getConstantInfoVariant (variant : UInt64) : GetM ConstantInfo := do
  if variant == ConstantInfo.CONST_DEFN then .defn <$> getDefinition
  else if variant == ConstantInfo.CONST_RECR then .recr <$> getRecursor
  else if variant == ConstantInfo.CONST_AXIO then .axio <$> getAxiom
  else if variant == ConstantInfo.CONST_QUOT then .quot <$> getQuotient
  else if variant == ConstantInfo.CONST_CPRJ then .cPrj <$> getConstructorProj
  else if variant == ConstantInfo.CONST_RPRJ then .rPrj <$> getRecursorProj
  else if variant == ConstantInfo.CONST_IPRJ then .iPrj <$> getInductiveProj
  else if variant == ConstantInfo.CONST_DPRJ then .dPrj <$> getDefinitionProj
  else throw s!"getConstantInfo: invalid variant {variant}"

def getConstantInfoTag (tag : Tag4) : GetM ConstantInfo := do
  if tag.flag == Constant.FLAG_MUTS then
    return .muts (← getArrayN getMutConst tag.size.toNat)
  else if tag.flag == Constant.FLAG then
    getConstantInfoVariant tag.size
  else
    throw s!"getConstantInfo: invalid flag {tag.flag}"

def getConstantInfo : GetM ConstantInfo := do
  getConstantInfoTag (← getTag4)

instance : Serialize ConstantInfo where
  put := putConstantInfo
  get := getConstantInfo

def checkConstantSharing (info : ConstantInfo) (sharing : Array Expr) : GetM Unit := do
  if !Sharing.tableWF sharing then
    throw "getConstant: sharing table must be backward-only, in-bounds, and non-aliasing"
  let bodies := info.exprs.toArray
  if !bodies.all (Sharing.sharesBelow sharing.size) then
    throw "getConstant: sharing reference in a body is out of bounds"
  if !Sharing.entriesUsedTwice sharing bodies then
    throw "getConstant: sharing entries must each have at least two uses"

def getConstantRefsUnivs : GetM (Array Address × Array Univ) :=
  getPairM (getCountedArray Serialize.get) (getCountedArray getUniv)

abbrev ConstantRaw :=
  ConstantInfo × (Array Expr × (Array Address × Array Univ))

def getConstantAfterSharing (info : ConstantInfo)
    (sharing : Array Expr) : GetM (Array Expr × (Array Address × Array Univ)) := do
  checkConstantSharing info sharing
  return (sharing, ← getConstantRefsUnivs)

def getConstantAfterInfo
    (info : ConstantInfo) : GetM (Array Expr × (Array Address × Array Univ)) := do
  let sharing ← getCountedArray getExpr
  getConstantAfterSharing info sharing

def getConstantRaw : GetM ConstantRaw := do
  let info ← getConstantInfo
  return (info, ← getConstantAfterInfo info)

def buildConstant (raw : ConstantRaw) : Constant :=
  ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2⟩

def getConstant : GetM Constant :=
  buildConstant <$> getConstantRaw

instance : Serialize Constant where
  put := putConstant
  get := getConstant

namespace ConstLaws

attribute [local simp] encodedListBytes encodedArrayBytes
attribute [local simp] Constant.FLAG Constant.FLAG_MUTS
  ConstantInfo.CONST_DEFN ConstantInfo.CONST_RECR ConstantInfo.CONST_AXIO
  ConstantInfo.CONST_QUOT ConstantInfo.CONST_CPRJ ConstantInfo.CONST_RPRJ
  ConstantInfo.CONST_IPRJ ConstantInfo.CONST_DPRJ

theorem getListN_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : List α) :
    GetSpec (getListN getOne values.length)
      (encodedListBytes encode values) values := by
  induction values with
  | nil => exact GetSpec.pure []
  | cons value values ih =>
    intro pre suffix
    simp only [List.length_cons, getListN, StateT.run_bind]
    have hbytes :
        pre ++ encodedListBytes encode (value :: values) ++ suffix =
          pre ++ encode value ++ (encodedListBytes encode values ++ suffix) := by
      simp [ByteArray.append_assoc]
    rw [hbytes, hone value pre (encodedListBytes encode values ++ suffix)]
    simp only [bind, Except.bind]
    have htail := ih (pre ++ encode value) suffix
    have htail' :
        (getListN getOne values.length).run
            ⟨pre ++ encode value ++ (encodedListBytes encode values ++ suffix),
              pre.size + (encode value).size⟩ =
          .ok (values,
            ⟨pre ++ encode value ++ (encodedListBytes encode values ++ suffix),
              pre.size + (encode value).size +
                (encodedListBytes encode values).size⟩) := by
      simpa [ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc] using htail
    rw [htail']
    simp [ByteArray.size_append, Nat.add_assoc]
    rfl

theorem getListN_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : List α) (hvalues : ∀ value ∈ values, property value) :
    GetSpec (getListN getOne values.length)
      (encodedListBytes encode values) values := by
  induction values with
  | nil => exact GetSpec.pure []
  | cons value values ih =>
    have hvalue : property value := hvalues value (by simp)
    have htail : ∀ item ∈ values, property item := by
      intro item hitem
      exact hvalues item (by simp [hitem])
    intro pre suffix
    simp only [List.length_cons, getListN, StateT.run_bind]
    have hbytes :
        pre ++ encodedListBytes encode (value :: values) ++ suffix =
          pre ++ encode value ++ (encodedListBytes encode values ++ suffix) := by
      simp [ByteArray.append_assoc]
    rw [hbytes, hone value hvalue pre (encodedListBytes encode values ++ suffix)]
    simp only [bind, Except.bind]
    have hrun := ih htail (pre ++ encode value) suffix
    have hrun' :
        (getListN getOne values.length).run
            ⟨pre ++ encode value ++ (encodedListBytes encode values ++ suffix),
              pre.size + (encode value).size⟩ =
          .ok (values,
            ⟨pre ++ encode value ++ (encodedListBytes encode values ++ suffix),
              pre.size + (encode value).size +
                (encodedListBytes encode values).size⟩) := by
      simpa [ByteArray.append_assoc, ByteArray.size_append,
        Nat.add_assoc] using hrun
    rw [hrun']
    simp [ByteArray.size_append, Nat.add_assoc]
    rfl

theorem getListN_canonical (getOne : GetM α) (encode : α → ByteArray)
    (hone : GetCanonical getOne encode) (count : Nat) :
    GetCanonical (getListN getOne count) (encodedListBytes encode) := by
  induction count with
  | zero =>
    intro pre rest values st' h
    simp [getListN] at h
    cases h
    exact ⟨rest, by simp, by simp⟩
  | succ count ih =>
    intro pre rest values st' h
    simp only [getListN, StateT.run_bind] at h
    cases hh : getOne.run ⟨pre ++ rest, pre.size⟩ with
    | error err => rw [hh] at h; contradiction
    | ok headState =>
      rcases headState with ⟨head, afterHead⟩
      rw [hh] at h
      simp only [bind, Except.bind] at h
      obtain ⟨afterHeadBytes, hrestHead, hafterHead⟩ :=
        hone pre rest hh
      let headPre := pre ++ encode head
      have hafterHead' :
          afterHead = ⟨headPre ++ afterHeadBytes, headPre.size⟩ := by
        rw [hafterHead]
        simp [headPre, hrestHead, ByteArray.append_assoc]
      rw [hafterHead'] at h
      cases ht : (getListN getOne count).run
          ⟨headPre ++ afterHeadBytes, headPre.size⟩ with
      | error err => rw [ht] at h; contradiction
      | ok tailState =>
        rcases tailState with ⟨tail, afterTail⟩
        rw [ht] at h
        simp at h
        cases h
        obtain ⟨suffix, hrestTail, hafterTail⟩ :=
          ih headPre afterHeadBytes ht
        refine ⟨suffix, ?_, ?_⟩
        · rw [hrestHead, hrestTail]
          simp [ByteArray.append_assoc]
        · simpa [headPre, hrestHead, hrestTail,
            ByteArray.append_assoc, ByteArray.size_append,
            Nat.add_assoc] using hafterTail

theorem getListN_success_length (getOne : GetM α) (count : Nat) :
    ∀ (initial : GetState) {values : List α} {st' : GetState},
      (getListN getOne count).run initial = .ok (values, st') →
      values.length = count := by
  induction count with
  | zero =>
    intro initial values st' h
    simp [getListN] at h
    cases h
    rfl
  | succ count ih =>
    intro initial values st' h
    simp only [getListN, StateT.run_bind] at h
    cases hh : getOne.run initial with
    | error err => rw [hh] at h; contradiction
    | ok headState =>
      rcases headState with ⟨head, afterHead⟩
      rw [hh] at h
      simp only [bind, Except.bind] at h
      cases ht : (getListN getOne count).run afterHead with
      | error err => rw [ht] at h; contradiction
      | ok tailState =>
        rcases tailState with ⟨tail, afterTail⟩
        rw [ht] at h
        simp at h
        cases h
        simp [ih afterHead ht]

theorem getArrayN_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : Array α) :
    GetSpec (getArrayN getOne values.size)
      (encodedArrayBytes encode values) values := by
  have hlist := getListN_spec getOne encode hone values.toList
  have hmapped := ExprLaws.GetSpec.map hlist List.toArray
  simpa [getArrayN] using hmapped

theorem getArrayN_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : Array α) (hvalues : ∀ value ∈ values.toList, property value) :
    GetSpec (getArrayN getOne values.size)
      (encodedArrayBytes encode values) values := by
  have hlist := getListN_spec_of getOne encode property hone values.toList hvalues
  have hmapped := ExprLaws.GetSpec.map hlist List.toArray
  simpa [getArrayN] using hmapped

theorem getArrayN_canonical (getOne : GetM α) (encode : α → ByteArray)
    (hone : GetCanonical getOne encode) (count : Nat) :
    GetCanonical (getArrayN getOne count) (encodedArrayBytes encode) := by
  intro pre rest values st' h
  change (getListN getOne count >>= fun list => pure list.toArray).run
    ⟨pre ++ rest, pre.size⟩ = .ok (values, st') at h
  obtain ⟨list, after, hrest, hnext⟩ :=
    ExprLaws.GetCanonical.bind_inv
      (getListN_canonical getOne encode hone count) pre rest h
  simp at hnext
  cases hnext
  exact ⟨after, by simpa using hrest,
    by simp [hrest, ByteArray.append_assoc]⟩

theorem getArrayN_success_size (getOne : GetM α) (count : Nat) :
    ∀ (initial : GetState) {values : Array α} {st' : GetState},
      (getArrayN getOne count).run initial = .ok (values, st') →
      values.size = count := by
  intro initial values st' h
  change (getListN getOne count >>= fun list => pure list.toArray).run initial =
    .ok (values, st') at h
  simp only [StateT.run_bind] at h
  cases hl : (getListN getOne count).run initial with
  | error err => rw [hl] at h; contradiction
  | ok listState =>
    rcases listState with ⟨list, afterList⟩
    rw [hl] at h
    simp at h
    cases h
    simpa using getListN_success_length getOne count initial hl

theorem getCountedArray_spec (getOne : GetM α) (encode : α → ByteArray)
    (hone : ∀ value, GetSpec getOne (encode value) value)
    (values : Array α) (hsize : values.size < UInt64.size) :
    GetSpec (getCountedArray getOne) (countedArrayBytes encode values) values := by
  have hround : values.size.toUInt64.toNat = values.size :=
    UInt64.toNat_ofNat_of_lt hsize
  let afterCount : Tag0 → GetM (Array α) := fun count =>
    getArrayN getOne count.size.toNat
  have hafter : GetSpec (afterCount ⟨values.size.toUInt64⟩)
      (encodedArrayBytes encode values) values := by
    simpa [afterCount, hround] using getArrayN_spec getOne encode hone values
  have htotal := GetSpec.bind (next := afterCount)
    (getTag0_encoded_spec ⟨values.size.toUInt64⟩) hafter
  simpa [getCountedArray, countedArrayBytes, afterCount] using htotal

theorem getCountedArray_spec_of (getOne : GetM α) (encode : α → ByteArray)
    (property : α → Prop)
    (hone : ∀ value, property value → GetSpec getOne (encode value) value)
    (values : Array α) (hsize : values.size < UInt64.size)
    (hvalues : ∀ value ∈ values.toList, property value) :
    GetSpec (getCountedArray getOne) (countedArrayBytes encode values) values := by
  have hround : values.size.toUInt64.toNat = values.size :=
    UInt64.toNat_ofNat_of_lt hsize
  let afterCount : Tag0 → GetM (Array α) := fun count =>
    getArrayN getOne count.size.toNat
  have hafter : GetSpec (afterCount ⟨values.size.toUInt64⟩)
      (encodedArrayBytes encode values) values := by
    simpa [afterCount, hround] using
      getArrayN_spec_of getOne encode property hone values hvalues
  have htotal := GetSpec.bind (next := afterCount)
    (getTag0_encoded_spec ⟨values.size.toUInt64⟩) hafter
  simpa [getCountedArray, countedArrayBytes, afterCount] using htotal

theorem getCountedArray_canonical (getOne : GetM α)
    (encode : α → ByteArray) (hone : GetCanonical getOne encode) :
    GetCanonical (getCountedArray getOne) (countedArrayBytes encode) := by
  intro pre rest values st' h
  let afterCount : Tag0 → GetM (Array α) := fun count =>
    getArrayN getOne count.size.toNat
  change (getTag0 >>= afterCount).run ⟨pre ++ rest, pre.size⟩ =
    .ok (values, st') at h
  obtain ⟨count, afterCountBytes, hrestCount, hafterCount⟩ :=
    ExprLaws.GetCanonical.bind_inv getTag0_canonical pre rest h
  let countPre := pre ++ tag0Bytes count
  have hafterCount' :
      (getArrayN getOne count.size.toNat).run
        ⟨countPre ++ afterCountBytes, countPre.size⟩ = .ok (values, st') := by
    simpa [afterCount, countPre] using hafterCount
  obtain ⟨suffix, hrestValues, hstate⟩ :=
    getArrayN_canonical getOne encode hone count.size.toNat
      countPre afterCountBytes hafterCount'
  have hsize := getArrayN_success_size getOne count.size.toNat
    ⟨countPre ++ afterCountBytes, countPre.size⟩ hafterCount'
  have hcount : values.size.toUInt64 = count.size := by
    rw [hsize]
    exact UInt64.ofNat_toNat
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestCount, hrestValues]
    simp [countedArrayBytes, hcount, ByteArray.append_assoc]
  · simpa [countPre, hrestCount, hrestValues, countedArrayBytes, hcount,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc] using hstate

theorem getDecodedU8_spec (what : String) (decode : UInt8 → Option α)
    (encode : α → UInt8) (hdecode : ∀ value, decode (encode value) = some value)
    (value : α) :
    GetSpec (getDecodedU8 what decode) (u8Bytes (encode value)) value := by
  intro pre suffix
  simp only [getDecodedU8, StateT.run_bind]
  rw [getU8_spec (encode value) pre suffix]
  simp only [bind, Except.bind]
  rw [hdecode value]
  rfl

theorem getDecodedU8_canonical (what : String) (decode : UInt8 → Option α)
    (encode : α → UInt8)
    (hinv : ∀ {byte value}, decode byte = some value → byte = encode value) :
    GetCanonical (getDecodedU8 what decode) (fun value => u8Bytes (encode value)) := by
  intro pre rest value st' h
  simp only [getDecodedU8, StateT.run_bind] at h
  cases hb : getU8.run ⟨pre ++ rest, pre.size⟩ with
  | error err => rw [hb] at h; contradiction
  | ok byteState =>
    rcases byteState with ⟨byte, afterByte⟩
    rw [hb] at h
    simp only [bind, Except.bind] at h
    cases hd : decode byte with
    | none => rw [hd] at h; contradiction
    | some decoded =>
      rw [hd] at h
      simp at h
      cases h
      have hbyte := hinv hd
      subst byte
      exact getU8_canonical pre rest hb

namespace ModeBits

private theorem nat_lt_eight_cases {i : Nat} (h : i < 8) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
  omega

theorem split_low2 (byte : UInt8) :
    ((byte >>> 2) <<< 2) ||| (byte &&& 0x3) = byte := by
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    UInt8.toBitVec_shiftLeft, UInt8.toBitVec_shiftRight,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private theorem reconstruct_low2 (byte : UInt8) (h : byte < 4) :
    byte = (byte &&& 1) ||| (byte &&& 2) := by
  have hbn : byte.toNat < 2 ^ 2 := by
    simpa [UInt8.lt_iff_toNat_lt] using h
  have hbit (i : Nat) (hi : i < 8) (h2 : 2 ≤ i) :
      byte.toBitVec[i] = false := by
    rw [BitVec.getElem_eq_testBit_toNat]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le hbn
      (Nat.pow_le_pow_of_le (by decide : 1 < 2) h2)
  apply UInt8.toBitVec_inj.1
  ext i hi
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and,
    BitVec.getElem_or, BitVec.getElem_and, UInt8.toBitVec_ofNat]
  rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp
  all_goals exact hbit _ (by omega) (by omega)

private theorem and_one_cases (byte : UInt8) :
    byte &&& 1 = 0 ∨ byte &&& 1 = 1 := by
  by_cases hb : byte.toBitVec[0] = true
  · right
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb]
  · left
    have hb' : byte.toBitVec[0] = false := by
      cases hbit : byte.toBitVec[0] <;> simp_all
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb']

private theorem and_two_cases (byte : UInt8) :
    byte &&& 2 = 0 ∨ byte &&& 2 = 2 := by
  by_cases hb : byte.toBitVec[1] = true
  · right
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb]
  · left
    have hb' : byte.toBitVec[1] = false := by
      cases hbit : byte.toBitVec[1] <;> simp_all
    apply UInt8.toBitVec_inj.1
    ext i hi
    simp only [UInt8.toBitVec_and, BitVec.getElem_and,
      UInt8.toBitVec_ofNat]
    rcases nat_lt_eight_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hb']

theorem recursor_inverse (byte : UInt8) (k isUnsafe : Bool)
    (hlt : byte < 4)
    (hk : (byte &&& 1 != 0) = k)
    (hu : (byte &&& 2 != 0) = isUnsafe) :
    byte = recursorModeByte k isUnsafe := by
  have hr := reconstruct_low2 byte hlt
  cases k <;> cases isUnsafe
  · simp at hk hu
    calc
      byte = (byte &&& 1) ||| (byte &&& 2) := hr
      _ = 0 := by rw [hk, hu]; rfl
      _ = recursorModeByte false false := by rfl
  · simp at hk hu
    have htwo := (and_two_cases byte).resolve_left hu
    calc
      byte = (byte &&& 1) ||| (byte &&& 2) := hr
      _ = 2 := by rw [hk, htwo]; rfl
      _ = recursorModeByte false true := by rfl
  · simp at hk hu
    have hone := (and_one_cases byte).resolve_left hk
    calc
      byte = (byte &&& 1) ||| (byte &&& 2) := hr
      _ = 1 := by rw [hone, hu]; rfl
      _ = recursorModeByte true false := by rfl
  · simp at hk hu
    have hone := (and_one_cases byte).resolve_left hk
    have htwo := (and_two_cases byte).resolve_left hu
    calc
      byte = (byte &&& 1) ||| (byte &&& 2) := hr
      _ = 1 ||| 2 := by rw [hone, htwo]
      _ = recursorModeByte true true := by rfl

end ModeBits

theorem definitionMode_decode (kind : DefKind) (safety : DefinitionSafety) :
    definitionModeOfByte? (definitionModeByte kind safety) =
      some (kind, safety) := by
  cases kind <;> cases safety <;> rfl

theorem definitionMode_inverse {byte : UInt8}
    {mode : DefKind × DefinitionSafety}
    (h : definitionModeOfByte? byte = some mode) :
    byte = definitionModeByte mode.1 mode.2 := by
  simp only [definitionModeOfByte?] at h
  split at h
  next kind safety hkind hsafety =>
    simp at h
    cases h
    have hkind' : byte >>> 2 = kind.toBits := by
      cases kind <;> simp only [DefKind.ofBits?] at hkind
      all_goals split at hkind <;> simp_all [DefKind.toBits]
    have hsafety' : byte &&& 0x3 = safety.toBits := by
      cases safety <;> simp only [DefinitionSafety.ofBits?] at hsafety
      all_goals split at hsafety <;> simp_all [DefinitionSafety.toBits]
    change byte = definitionModeByte kind safety
    simp only [definitionModeByte]
    rw [← hkind', ← hsafety']
    exact (ModeBits.split_low2 byte).symm
  next => contradiction

theorem recursorMode_decode (k isUnsafe : Bool) :
    recursorModeOfByte? (recursorModeByte k isUnsafe) = some (k, isUnsafe) := by
  cases k <;> cases isUnsafe <;> decide

theorem recursorMode_inverse {byte : UInt8} {mode : Bool × Bool}
    (h : recursorModeOfByte? byte = some mode) :
    byte = recursorModeByte mode.1 mode.2 := by
  rcases mode with ⟨k, isUnsafe⟩
  cases k <;> cases isUnsafe <;>
    simp only [recursorModeOfByte?] at h
  all_goals split at h <;> simp_all [recursorModeByte]
  all_goals
    first
    | exact ModeBits.recursor_inverse byte false false (by assumption)
        (by simp_all) (by simp_all)
    | exact ModeBits.recursor_inverse byte false true (by assumption)
        (by simp_all) (by simp_all)
    | exact ModeBits.recursor_inverse byte true false (by assumption)
        (by simp_all) (by simp_all)
    | exact ModeBits.recursor_inverse byte true true (by assumption)
        (by simp_all) (by simp_all)

theorem bool_decode (value : Bool) :
    boolOfByte? (if value then 1 else 0) = some value := by
  cases value <;> rfl

theorem bool_inverse {byte : UInt8} {value : Bool}
    (h : boolOfByte? byte = some value) :
    byte = if value then 1 else 0 := by
  cases value <;> simp only [boolOfByte?] at h ⊢
  all_goals split at h <;> simp_all

theorem quotKind_decode (kind : QuotKind) :
    QuotKind.ofBits? kind.toBits = some kind :=
  QuotKind.ofBits?_toBits kind

theorem quotKind_inverse {byte : UInt8} {kind : QuotKind}
    (h : QuotKind.ofBits? byte = some kind) : byte = kind.toBits := by
  cases kind <;> simp only [QuotKind.ofBits?] at h
  all_goals split at h <;> simp_all [QuotKind.toBits]

theorem getDefinitionMode_spec (kind : DefKind) (safety : DefinitionSafety) :
    GetSpec getDefinitionMode
      (u8Bytes (definitionModeByte kind safety)) (kind, safety) := by
  simpa only [getDefinitionMode] using
    getDecodedU8_spec "getDefinition" definitionModeOfByte?
      (fun mode => definitionModeByte mode.1 mode.2)
      (fun mode => definitionMode_decode mode.1 mode.2) (kind, safety)

theorem getDefinitionMode_canonical :
    GetCanonical getDefinitionMode
      (fun mode => u8Bytes (definitionModeByte mode.1 mode.2)) := by
  simpa only [getDefinitionMode] using
    getDecodedU8_canonical "getDefinition" definitionModeOfByte?
      (fun mode => definitionModeByte mode.1 mode.2) definitionMode_inverse

theorem getRecursorMode_spec (k isUnsafe : Bool) :
    GetSpec getRecursorMode
      (u8Bytes (recursorModeByte k isUnsafe)) (k, isUnsafe) := by
  simpa only [getRecursorMode] using
    getDecodedU8_spec "getRecursor" recursorModeOfByte?
      (fun mode => recursorModeByte mode.1 mode.2)
      (fun mode => recursorMode_decode mode.1 mode.2) (k, isUnsafe)

theorem getRecursorMode_canonical :
    GetCanonical getRecursorMode
      (fun mode => u8Bytes (recursorModeByte mode.1 mode.2)) := by
  simpa only [getRecursorMode] using
    getDecodedU8_canonical "getRecursor" recursorModeOfByte?
      (fun mode => recursorModeByte mode.1 mode.2) recursorMode_inverse

theorem getStrictBool_spec (what : String) (value : Bool) :
    GetSpec (getStrictBool what) (boolBytes value) value := by
  exact getDecodedU8_spec _ _ _ bool_decode value

theorem getStrictBool_canonical (what : String) :
    GetCanonical (getStrictBool what) boolBytes := by
  exact getDecodedU8_canonical _ _ _ bool_inverse

theorem getQuotKind_spec (kind : QuotKind) :
    GetSpec getQuotKind (u8Bytes kind.toBits) kind := by
  exact getDecodedU8_spec _ _ _ quotKind_decode kind

theorem getQuotKind_canonical :
    GetCanonical getQuotKind (fun kind => u8Bytes kind.toBits) := by
  exact getDecodedU8_canonical _ _ _ quotKind_inverse

def pairBytes (encodeLeft : α → ByteArray) (encodeRight : β → ByteArray)
    (value : α × β) : ByteArray :=
  encodeLeft value.1 ++ encodeRight value.2

def getPair (getLeft : GetM α) (getRight : GetM β) : GetM (α × β) := do
  getPairM getLeft getRight

theorem getPair_spec (getLeft : GetM α) (getRight : GetM β)
    (encodeLeft : α → ByteArray) (encodeRight : β → ByteArray)
    {left : α} {right : β}
    (hleft : GetSpec getLeft (encodeLeft left) left)
    (hright : GetSpec getRight (encodeRight right) right) :
    GetSpec (getPair getLeft getRight)
      (pairBytes encodeLeft encodeRight (left, right)) (left, right) := by
  let finish : β → GetM (α × β) := fun decodedRight =>
    pure (left, decodedRight)
  have hfinish : GetSpec (finish right) ByteArray.empty (left, right) :=
    GetSpec.pure _
  have hright' := GetSpec.bind (next := finish) hright hfinish
  simp only [ByteArray.append_empty] at hright'
  let afterLeft : α → GetM (α × β) := fun decodedLeft => do
    let decodedRight ← getRight
    return (decodedLeft, decodedRight)
  have hafter : GetSpec (afterLeft left) (encodeRight right) (left, right) := by
    simpa [afterLeft, finish] using hright'
  have htotal := GetSpec.bind (next := afterLeft) hleft hafter
  simpa [getPair, getPairM, pairBytes, afterLeft, finish] using htotal

theorem getPair_canonical (getLeft : GetM α) (getRight : GetM β)
    (encodeLeft : α → ByteArray) (encodeRight : β → ByteArray)
    (hleft : GetCanonical getLeft encodeLeft)
    (hright : GetCanonical getRight encodeRight) :
    GetCanonical (getPair getLeft getRight)
      (pairBytes encodeLeft encodeRight) := by
  intro pre rest value st' h
  let afterLeft : α → GetM (α × β) := fun left => do
    let right ← getRight
    return (left, right)
  change (getLeft >>= afterLeft).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨left, afterLeftBytes, hrestLeft, hafterLeft⟩ :=
    ExprLaws.GetCanonical.bind_inv hleft pre rest h
  let leftPre := pre ++ encodeLeft left
  let finish : β → GetM (α × β) := fun right => pure (left, right)
  have hafterLeft' :
      (getRight >>= finish).run
        ⟨leftPre ++ afterLeftBytes, leftPre.size⟩ = .ok (value, st') := by
    simpa [afterLeft, finish, leftPre] using hafterLeft
  obtain ⟨right, suffix, hrestRight, hfinish⟩ :=
    ExprLaws.GetCanonical.bind_inv hright leftPre afterLeftBytes hafterLeft'
  simp [finish] at hfinish
  cases hfinish
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestLeft, hrestRight]
    simp [pairBytes, ByteArray.append_assoc]
  · simp [pairBytes, leftPre, hrestLeft, hrestRight,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc]

theorem GetCanonical.map {get : GetM α} {encode : α → ByteArray}
    (hget : GetCanonical get encode) (f : α → β) (encodeResult : β → ByteArray)
    (hencode : ∀ value, encodeResult (f value) = encode value) :
    GetCanonical (f <$> get) encodeResult := by
  intro pre rest result st' h
  change (get >>= fun value => pure (f value)).run
    ⟨pre ++ rest, pre.size⟩ = .ok (result, st') at h
  obtain ⟨value, suffix, hrest, hfinish⟩ :=
    ExprLaws.GetCanonical.bind_inv hget pre rest h
  simp at hfinish
  cases hfinish
  rw [hencode value] at ⊢
  exact ⟨suffix, hrest, by simp [hrest, ByteArray.append_assoc]⟩

theorem address_ofBytes_inverse {bytes : ByteArray} {address : Address}
    (h : Address.ofBytes? bytes = some address) : bytes = address.hash := by
  unfold Address.ofBytes? at h
  split at h
  · simp at h
    cases h
    rfl
  · contradiction

theorem getAddress_canonical :
    GetCanonical (Serialize.get (self := inferInstance) : GetM Address)
      (fun address => address.hash) := by
  intro pre rest address st' h
  change (do
    let bytes ← getBytes 32
    match Address.ofBytes? bytes with
    | some decoded => return decoded
    | none => throw "internal: getBytes returned a non-32-byte address").run
      ⟨pre ++ rest, pre.size⟩ = .ok (address, st') at h
  obtain ⟨bytes, suffix, hrest, hfinish⟩ :=
    ExprLaws.GetCanonical.bind_inv (getBytes_canonical 32) pre rest h
  cases ha : Address.ofBytes? bytes with
  | none =>
    simp [ha] at hfinish
    change (Except.error _) = Except.ok (address, st') at hfinish
    contradiction
  | some decoded =>
    simp [ha] at hfinish
    cases hfinish
    have hbytes := address_ofBytes_inverse ha
    subst bytes
    exact ⟨suffix, hrest,
      by simp [hrest, ByteArray.append_assoc, address.hash_size]⟩

def DefinitionRaw :=
  (DefKind × DefinitionSafety) × (Tag0 × (Expr × Expr))

def getDefinitionRaw : GetM DefinitionRaw :=
  getPairM getDefinitionMode
    (getPairM getTag0 (getPairM getExpr getExpr))

def definitionRawBytes : DefinitionRaw → ByteArray :=
  pairBytes
    (fun mode => u8Bytes (definitionModeByte mode.1 mode.2))
    (pairBytes tag0Bytes (pairBytes exprBytes exprBytes))

def buildDefinition (raw : DefinitionRaw) : Definition :=
  ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1, raw.2.2.2⟩

theorem getDefinition_eq :
    getDefinition = buildDefinition <$> getDefinitionRaw := by
  rfl

theorem definitionRawBytes_build (raw : DefinitionRaw) :
    definitionBytes (buildDefinition raw) = definitionRawBytes raw := by
  rcases raw with ⟨⟨kind, safety⟩, ⟨lvls, typ, value⟩⟩
  simp [definitionBytes, definitionRawBytes, buildDefinition, pairBytes,
    ByteArray.append_assoc]

theorem getDefinition_spec (d : Definition) (hwf : d.wireWF) :
    GetSpec getDefinition (definitionBytes d) d := by
  rcases d with ⟨kind, safety, lvls, typ, value⟩
  rcases hwf with ⟨htyp, hvalue⟩
  let raw : DefinitionRaw := ((kind, safety), (⟨lvls⟩, (typ, value)))
  have hexprTyp := ExprLaws.getExpr_spec typ htyp
  have hexprValue := ExprLaws.getExpr_spec value hvalue
  have hraw : GetSpec getDefinitionRaw (definitionRawBytes raw) raw := by
    apply getPair_spec
    · exact getDefinitionMode_spec kind safety
    · apply getPair_spec
      · exact getTag0_encoded_spec ⟨lvls⟩
      · exact getPair_spec _ _ _ _ hexprTyp hexprValue
  rw [getDefinition_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildDefinition
  simpa [raw, definitionBytes, definitionRawBytes, buildDefinition,
    pairBytes, ByteArray.append_assoc] using hmapped

theorem getDefinition_canonical :
    GetCanonical getDefinition definitionBytes := by
  have hraw : GetCanonical getDefinitionRaw definitionRawBytes := by
    apply getPair_canonical
    · exact getDefinitionMode_canonical
    · apply getPair_canonical
      · exact getTag0_canonical
      · exact getPair_canonical _ _ _ _
          ExprLaws.getExpr_canonical ExprLaws.getExpr_canonical
  rw [getDefinition_eq]
  exact GetCanonical.map hraw buildDefinition definitionBytes
    definitionRawBytes_build

def RecursorRuleRaw := Tag0 × Expr

def getRecursorRuleRaw : GetM RecursorRuleRaw :=
  getPairM getTag0 getExpr

def recursorRuleRawBytes : RecursorRuleRaw → ByteArray :=
  pairBytes tag0Bytes exprBytes

def buildRecursorRule (raw : RecursorRuleRaw) : RecursorRule :=
  ⟨raw.1.size, raw.2⟩

theorem getRecursorRule_eq :
    getRecursorRule = buildRecursorRule <$> getRecursorRuleRaw := by
  rfl

theorem recursorRuleRawBytes_build (raw : RecursorRuleRaw) :
    recursorRuleBytes (buildRecursorRule raw) = recursorRuleRawBytes raw := by
  rcases raw with ⟨fields, rhs⟩
  rfl

theorem getRecursorRule_spec (r : RecursorRule) (hwf : r.wireWF) :
    GetSpec getRecursorRule (recursorRuleBytes r) r := by
  rcases r with ⟨fields, rhs⟩
  let raw : RecursorRuleRaw := (⟨fields⟩, rhs)
  have hraw : GetSpec getRecursorRuleRaw (recursorRuleRawBytes raw) raw :=
    getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨fields⟩)
      (ExprLaws.getExpr_spec rhs hwf)
  rw [getRecursorRule_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildRecursorRule
  simpa [getRecursorRuleRaw, raw, recursorRuleBytes,
    recursorRuleRawBytes, buildRecursorRule, pairBytes] using hmapped

theorem getRecursorRule_canonical :
    GetCanonical getRecursorRule recursorRuleBytes := by
  have hraw : GetCanonical getRecursorRuleRaw recursorRuleRawBytes :=
    getPair_canonical _ _ _ _ getTag0_canonical ExprLaws.getExpr_canonical
  rw [getRecursorRule_eq]
  exact GetCanonical.map hraw buildRecursorRule recursorRuleBytes
    recursorRuleRawBytes_build

def AxiomRaw := Bool × (Tag0 × Expr)

def getAxiomRaw : GetM AxiomRaw :=
  getPairM (getStrictBool "getAxiom") (getPairM getTag0 getExpr)

def axiomRawBytes : AxiomRaw → ByteArray :=
  pairBytes boolBytes (pairBytes tag0Bytes exprBytes)

def buildAxiom (raw : AxiomRaw) : Axiom :=
  ⟨raw.1, raw.2.1.size, raw.2.2⟩

theorem getAxiom_eq : getAxiom = buildAxiom <$> getAxiomRaw := by
  rfl

theorem axiomRawBytes_build (raw : AxiomRaw) :
    axiomBytes (buildAxiom raw) = axiomRawBytes raw := by
  rcases raw with ⟨isUnsafe, lvls, typ⟩
  simp [axiomBytes, axiomRawBytes, buildAxiom, pairBytes,
    ByteArray.append_assoc]

theorem getAxiom_spec (a : Axiom) (hwf : a.wireWF) :
    GetSpec getAxiom (axiomBytes a) a := by
  rcases a with ⟨isUnsafe, lvls, typ⟩
  let raw : AxiomRaw := (isUnsafe, (⟨lvls⟩, typ))
  have hraw : GetSpec getAxiomRaw (axiomRawBytes raw) raw := by
    apply getPair_spec
    · exact getStrictBool_spec "getAxiom" isUnsafe
    · exact getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨lvls⟩)
        (ExprLaws.getExpr_spec typ hwf)
  rw [getAxiom_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildAxiom
  simpa [getAxiomRaw, raw, axiomBytes, axiomRawBytes,
    buildAxiom, pairBytes, ByteArray.append_assoc] using hmapped

theorem getAxiom_canonical : GetCanonical getAxiom axiomBytes := by
  have hraw : GetCanonical getAxiomRaw axiomRawBytes := by
    apply getPair_canonical
    · exact getStrictBool_canonical "getAxiom"
    · exact getPair_canonical _ _ _ _ getTag0_canonical
        ExprLaws.getExpr_canonical
  rw [getAxiom_eq]
  exact GetCanonical.map hraw buildAxiom axiomBytes axiomRawBytes_build

def QuotientRaw := QuotKind × (Tag0 × Expr)

def getQuotientRaw : GetM QuotientRaw :=
  getPairM getQuotKind (getPairM getTag0 getExpr)

def quotientRawBytes : QuotientRaw → ByteArray :=
  pairBytes (fun kind => u8Bytes kind.toBits)
    (pairBytes tag0Bytes exprBytes)

def buildQuotient (raw : QuotientRaw) : Quotient :=
  ⟨raw.1, raw.2.1.size, raw.2.2⟩

theorem getQuotient_eq :
    getQuotient = buildQuotient <$> getQuotientRaw := by
  rfl

theorem quotientRawBytes_build (raw : QuotientRaw) :
    quotientBytes (buildQuotient raw) = quotientRawBytes raw := by
  rcases raw with ⟨kind, lvls, typ⟩
  simp [quotientBytes, quotientRawBytes, buildQuotient, pairBytes,
    ByteArray.append_assoc]

theorem getQuotient_spec (q : Quotient) (hwf : q.wireWF) :
    GetSpec getQuotient (quotientBytes q) q := by
  rcases q with ⟨kind, lvls, typ⟩
  let raw : QuotientRaw := (kind, (⟨lvls⟩, typ))
  have hraw : GetSpec getQuotientRaw (quotientRawBytes raw) raw := by
    apply getPair_spec
    · exact getQuotKind_spec kind
    · exact getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨lvls⟩)
        (ExprLaws.getExpr_spec typ hwf)
  rw [getQuotient_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildQuotient
  simpa [getQuotientRaw, raw, quotientBytes,
    quotientRawBytes, buildQuotient, pairBytes,
    ByteArray.append_assoc] using hmapped

theorem getQuotient_canonical : GetCanonical getQuotient quotientBytes := by
  have hraw : GetCanonical getQuotientRaw quotientRawBytes := by
    apply getPair_canonical
    · exact getQuotKind_canonical
    · exact getPair_canonical _ _ _ _ getTag0_canonical
        ExprLaws.getExpr_canonical
  rw [getQuotient_eq]
  exact GetCanonical.map hraw buildQuotient quotientBytes
    quotientRawBytes_build

def ConstructorRaw :=
  Bool × (Tag0 × (Tag0 × (Tag0 × (Tag0 × Expr))))

def getConstructorRaw : GetM ConstructorRaw :=
  getPairM (getStrictBool "getConstructor")
    (getPairM getTag0
      (getPairM getTag0 (getPairM getTag0 (getPairM getTag0 getExpr))))

def constructorRawBytes : ConstructorRaw → ByteArray :=
  pairBytes boolBytes
    (pairBytes tag0Bytes
      (pairBytes tag0Bytes
        (pairBytes tag0Bytes (pairBytes tag0Bytes exprBytes))))

def buildConstructor (raw : ConstructorRaw) : Constructor :=
  ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
    raw.2.2.2.2.1.size, raw.2.2.2.2.2⟩

theorem getConstructor_eq :
    getConstructor = buildConstructor <$> getConstructorRaw := by
  rfl

theorem constructorRawBytes_build (raw : ConstructorRaw) :
    constructorBytes (buildConstructor raw) = constructorRawBytes raw := by
  rcases raw with ⟨isUnsafe, lvls, cidx, params, fields, typ⟩
  simp [constructorBytes, constructorRawBytes, buildConstructor, pairBytes,
    ByteArray.append_assoc]

theorem getConstructor_spec (c : Constructor) (hwf : c.wireWF) :
    GetSpec getConstructor (constructorBytes c) c := by
  rcases c with ⟨isUnsafe, lvls, cidx, params, fields, typ⟩
  let raw : ConstructorRaw :=
    (isUnsafe, (⟨lvls⟩, (⟨cidx⟩, (⟨params⟩, (⟨fields⟩, typ)))))
  have hraw : GetSpec getConstructorRaw (constructorRawBytes raw) raw := by
    apply getPair_spec
    · exact getStrictBool_spec "getConstructor" isUnsafe
    · apply getPair_spec
      · exact getTag0_encoded_spec ⟨lvls⟩
      · apply getPair_spec
        · exact getTag0_encoded_spec ⟨cidx⟩
        · apply getPair_spec
          · exact getTag0_encoded_spec ⟨params⟩
          · exact getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨fields⟩)
              (ExprLaws.getExpr_spec typ hwf)
  rw [getConstructor_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildConstructor
  simpa [raw, constructorBytes, constructorRawBytes, buildConstructor,
    pairBytes, ByteArray.append_assoc] using hmapped

theorem getConstructor_canonical :
    GetCanonical getConstructor constructorBytes := by
  have hraw : GetCanonical getConstructorRaw constructorRawBytes := by
    apply getPair_canonical
    · exact getStrictBool_canonical "getConstructor"
    · apply getPair_canonical
      · exact getTag0_canonical
      · apply getPair_canonical
        · exact getTag0_canonical
        · apply getPair_canonical
          · exact getTag0_canonical
          · exact getPair_canonical _ _ _ _ getTag0_canonical
              ExprLaws.getExpr_canonical
  rw [getConstructor_eq]
  exact GetCanonical.map hraw buildConstructor constructorBytes
    constructorRawBytes_build

def OneProjRaw := Tag0 × Address

def getOneProjRaw : GetM OneProjRaw :=
  getPairM getTag0 Serialize.get

def oneProjRawBytes : OneProjRaw → ByteArray :=
  pairBytes tag0Bytes (fun address => address.hash)

theorem getOneProjRaw_spec (idx : UInt64) (block : Address) :
    GetSpec getOneProjRaw (oneProjRawBytes (⟨idx⟩, block)) (⟨idx⟩, block) :=
  getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨idx⟩) (Address.get_spec block)

theorem getOneProjRaw_canonical :
    GetCanonical getOneProjRaw oneProjRawBytes :=
  getPair_canonical _ _ _ _ getTag0_canonical getAddress_canonical

def buildInductiveProj (raw : OneProjRaw) : InductiveProj :=
  ⟨raw.1.size, raw.2⟩

def buildRecursorProj (raw : OneProjRaw) : RecursorProj :=
  ⟨raw.1.size, raw.2⟩

def buildDefinitionProj (raw : OneProjRaw) : DefinitionProj :=
  ⟨raw.1.size, raw.2⟩

theorem getInductiveProj_eq :
    getInductiveProj = buildInductiveProj <$> getOneProjRaw := by rfl

theorem getRecursorProj_eq :
    getRecursorProj = buildRecursorProj <$> getOneProjRaw := by rfl

theorem getDefinitionProj_eq :
    getDefinitionProj = buildDefinitionProj <$> getOneProjRaw := by rfl

theorem inductiveProjRawBytes_build (raw : OneProjRaw) :
    inductiveProjBytes (buildInductiveProj raw) = oneProjRawBytes raw := by
  rcases raw with ⟨idx, block⟩
  rfl

theorem recursorProjRawBytes_build (raw : OneProjRaw) :
    recursorProjBytes (buildRecursorProj raw) = oneProjRawBytes raw := by
  rcases raw with ⟨idx, block⟩
  rfl

theorem definitionProjRawBytes_build (raw : OneProjRaw) :
    definitionProjBytes (buildDefinitionProj raw) = oneProjRawBytes raw := by
  rcases raw with ⟨idx, block⟩
  rfl

theorem getInductiveProj_spec (p : InductiveProj) :
    GetSpec getInductiveProj (inductiveProjBytes p) p := by
  rcases p with ⟨idx, block⟩
  rw [getInductiveProj_eq]
  have hmapped := ExprLaws.GetSpec.map (getOneProjRaw_spec idx block)
    buildInductiveProj
  exact hmapped

theorem getRecursorProj_spec (p : RecursorProj) :
    GetSpec getRecursorProj (recursorProjBytes p) p := by
  rcases p with ⟨idx, block⟩
  rw [getRecursorProj_eq]
  exact ExprLaws.GetSpec.map (getOneProjRaw_spec idx block) buildRecursorProj

theorem getDefinitionProj_spec (p : DefinitionProj) :
    GetSpec getDefinitionProj (definitionProjBytes p) p := by
  rcases p with ⟨idx, block⟩
  rw [getDefinitionProj_eq]
  exact ExprLaws.GetSpec.map (getOneProjRaw_spec idx block)
    buildDefinitionProj

theorem getInductiveProj_canonical :
    GetCanonical getInductiveProj inductiveProjBytes := by
  rw [getInductiveProj_eq]
  exact GetCanonical.map getOneProjRaw_canonical buildInductiveProj
    inductiveProjBytes inductiveProjRawBytes_build

theorem getRecursorProj_canonical :
    GetCanonical getRecursorProj recursorProjBytes := by
  rw [getRecursorProj_eq]
  exact GetCanonical.map getOneProjRaw_canonical buildRecursorProj
    recursorProjBytes recursorProjRawBytes_build

theorem getDefinitionProj_canonical :
    GetCanonical getDefinitionProj definitionProjBytes := by
  rw [getDefinitionProj_eq]
  exact GetCanonical.map getOneProjRaw_canonical buildDefinitionProj
    definitionProjBytes definitionProjRawBytes_build

def ConstructorProjRaw := Tag0 × (Tag0 × Address)

def getConstructorProjRaw : GetM ConstructorProjRaw :=
  getPairM getTag0 (getPairM getTag0 Serialize.get)

def constructorProjRawBytes : ConstructorProjRaw → ByteArray :=
  pairBytes tag0Bytes
    (pairBytes tag0Bytes (fun address => address.hash))

def buildConstructorProj (raw : ConstructorProjRaw) : ConstructorProj :=
  ⟨raw.1.size, raw.2.1.size, raw.2.2⟩

theorem getConstructorProj_eq :
    getConstructorProj = buildConstructorProj <$> getConstructorProjRaw := by
  rfl

theorem constructorProjRawBytes_build (raw : ConstructorProjRaw) :
    constructorProjBytes (buildConstructorProj raw) =
      constructorProjRawBytes raw := by
  rcases raw with ⟨idx, cidx, block⟩
  simp [constructorProjBytes, constructorProjRawBytes, buildConstructorProj,
    pairBytes, ByteArray.append_assoc]

theorem getConstructorProj_spec (p : ConstructorProj) :
    GetSpec getConstructorProj (constructorProjBytes p) p := by
  rcases p with ⟨idx, cidx, block⟩
  let raw : ConstructorProjRaw := (⟨idx⟩, (⟨cidx⟩, block))
  have hraw : GetSpec getConstructorProjRaw
      (constructorProjRawBytes raw) raw := by
    exact getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨idx⟩)
      (getPair_spec _ _ _ _ (getTag0_encoded_spec ⟨cidx⟩)
        (Address.get_spec block))
  rw [getConstructorProj_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildConstructorProj
  simpa [raw, constructorProjBytes, constructorProjRawBytes,
    buildConstructorProj, pairBytes, ByteArray.append_assoc] using hmapped

theorem getConstructorProj_canonical :
    GetCanonical getConstructorProj constructorProjBytes := by
  have hraw : GetCanonical getConstructorProjRaw constructorProjRawBytes :=
    getPair_canonical _ _ _ _ getTag0_canonical
      (getPair_canonical _ _ _ _ getTag0_canonical getAddress_canonical)
  rw [getConstructorProj_eq]
  exact GetCanonical.map hraw buildConstructorProj constructorProjBytes
    constructorProjRawBytes_build

def RecursorRaw :=
  (Bool × Bool) ×
    (Tag0 × (Tag0 × (Tag0 × (Tag0 × (Tag0 × (Expr × Array RecursorRule))))))

def getRecursorRaw : GetM RecursorRaw :=
  getPairM getRecursorMode
    (getPairM getTag0
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getTag0
            (getPairM getTag0
              (getPairM getExpr (getCountedArray getRecursorRule)))))))

def recursorRawBytes : RecursorRaw → ByteArray :=
  pairBytes
    (fun mode => u8Bytes (recursorModeByte mode.1 mode.2))
    (pairBytes tag0Bytes
      (pairBytes tag0Bytes
        (pairBytes tag0Bytes
          (pairBytes tag0Bytes
            (pairBytes tag0Bytes
              (pairBytes exprBytes
                (countedArrayBytes recursorRuleBytes)))))))

def buildRecursor (raw : RecursorRaw) : Recursor :=
  ⟨raw.1.1, raw.1.2, raw.2.1.size, raw.2.2.1.size,
    raw.2.2.2.1.size, raw.2.2.2.2.1.size, raw.2.2.2.2.2.1.size,
    raw.2.2.2.2.2.2.1, raw.2.2.2.2.2.2.2⟩

theorem getRecursor_eq : getRecursor = buildRecursor <$> getRecursorRaw := by
  rfl

theorem recursorRawBytes_build (raw : RecursorRaw) :
    recursorBytes (buildRecursor raw) = recursorRawBytes raw := by
  rcases raw with ⟨⟨k, isUnsafe⟩, lvls, params, indices, motives, minors,
    typ, rules⟩
  simp [recursorBytes, recursorRawBytes, buildRecursor, pairBytes,
    ByteArray.append_assoc]

theorem getRecursor_spec (r : Recursor) (hwf : r.wireWF) :
    GetSpec getRecursor (recursorBytes r) r := by
  rcases r with
    ⟨k, isUnsafe, lvls, params, indices, motives, minors, typ, rules⟩
  rcases hwf with ⟨htyp, hrulesSize, hrules⟩
  have hrulesList : ∀ rule ∈ rules.toList, rule.wireWF := by
    intro rule hrule
    exact hrules rule (by simpa using hrule)
  let raw : RecursorRaw :=
    ((k, isUnsafe),
      (⟨lvls⟩, (⟨params⟩, (⟨indices⟩, (⟨motives⟩, (⟨minors⟩,
        (typ, rules)))))))
  have hrulesSpec : GetSpec (getCountedArray getRecursorRule)
      (countedArrayBytes recursorRuleBytes rules) rules :=
    getCountedArray_spec_of getRecursorRule recursorRuleBytes
      RecursorRule.wireWF getRecursorRule_spec rules hrulesSize hrulesList
  have hraw : GetSpec getRecursorRaw (recursorRawBytes raw) raw := by
    apply getPair_spec
    · exact getRecursorMode_spec k isUnsafe
    · apply getPair_spec
      · exact getTag0_encoded_spec ⟨lvls⟩
      · apply getPair_spec
        · exact getTag0_encoded_spec ⟨params⟩
        · apply getPair_spec
          · exact getTag0_encoded_spec ⟨indices⟩
          · apply getPair_spec
            · exact getTag0_encoded_spec ⟨motives⟩
            · apply getPair_spec
              · exact getTag0_encoded_spec ⟨minors⟩
              · exact getPair_spec _ _ _ _
                  (ExprLaws.getExpr_spec typ htyp) hrulesSpec
  rw [getRecursor_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildRecursor
  simpa [raw, recursorBytes, recursorRawBytes, buildRecursor, pairBytes,
    ByteArray.append_assoc] using hmapped

theorem getRecursor_canonical : GetCanonical getRecursor recursorBytes := by
  have hraw : GetCanonical getRecursorRaw recursorRawBytes := by
    apply getPair_canonical
    · exact getRecursorMode_canonical
    · apply getPair_canonical
      · exact getTag0_canonical
      · apply getPair_canonical
        · exact getTag0_canonical
        · apply getPair_canonical
          · exact getTag0_canonical
          · apply getPair_canonical
            · exact getTag0_canonical
            · apply getPair_canonical
              · exact getTag0_canonical
              · exact getPair_canonical _ _ _ _
                  ExprLaws.getExpr_canonical
                  (getCountedArray_canonical getRecursorRule
                    recursorRuleBytes getRecursorRule_canonical)
  rw [getRecursor_eq]
  exact GetCanonical.map hraw buildRecursor recursorBytes
    recursorRawBytes_build

def InductiveRaw :=
  Bool × (Tag0 × (Tag0 × (Tag0 × (Expr × Array Constructor))))

def getInductiveRaw : GetM InductiveRaw :=
  getPairM (getStrictBool "getInductive")
    (getPairM getTag0
      (getPairM getTag0
        (getPairM getTag0
          (getPairM getExpr (getCountedArray getConstructor)))))

def inductiveRawBytes : InductiveRaw → ByteArray :=
  pairBytes boolBytes
    (pairBytes tag0Bytes
      (pairBytes tag0Bytes
        (pairBytes tag0Bytes
          (pairBytes exprBytes (countedArrayBytes constructorBytes)))))

def buildInductive (raw : InductiveRaw) : Inductive :=
  ⟨raw.1, raw.2.1.size, raw.2.2.1.size, raw.2.2.2.1.size,
    raw.2.2.2.2.1, raw.2.2.2.2.2⟩

theorem getInductive_eq :
    getInductive = buildInductive <$> getInductiveRaw := by
  rfl

theorem inductiveRawBytes_build (raw : InductiveRaw) :
    inductiveBytes (buildInductive raw) = inductiveRawBytes raw := by
  rcases raw with ⟨isUnsafe, lvls, params, indices, typ, ctors⟩
  simp [inductiveBytes, inductiveRawBytes, buildInductive, pairBytes,
    ByteArray.append_assoc]

theorem getInductive_spec (i : Inductive) (hwf : i.wireWF) :
    GetSpec getInductive (inductiveBytes i) i := by
  rcases i with ⟨isUnsafe, lvls, params, indices, typ, ctors⟩
  rcases hwf with ⟨htyp, hctorsSize, hctors⟩
  have hctorsList : ∀ ctor ∈ ctors.toList, ctor.wireWF := by
    intro ctor hctor
    exact hctors ctor (by simpa using hctor)
  let raw : InductiveRaw :=
    (isUnsafe, (⟨lvls⟩, (⟨params⟩, (⟨indices⟩, (typ, ctors)))))
  have hctorsSpec : GetSpec (getCountedArray getConstructor)
      (countedArrayBytes constructorBytes ctors) ctors :=
    getCountedArray_spec_of getConstructor constructorBytes
      Constructor.wireWF getConstructor_spec ctors hctorsSize hctorsList
  have hraw : GetSpec getInductiveRaw (inductiveRawBytes raw) raw := by
    apply getPair_spec
    · exact getStrictBool_spec "getInductive" isUnsafe
    · apply getPair_spec
      · exact getTag0_encoded_spec ⟨lvls⟩
      · apply getPair_spec
        · exact getTag0_encoded_spec ⟨params⟩
        · apply getPair_spec
          · exact getTag0_encoded_spec ⟨indices⟩
          · exact getPair_spec _ _ _ _
              (ExprLaws.getExpr_spec typ htyp) hctorsSpec
  rw [getInductive_eq]
  have hmapped := ExprLaws.GetSpec.map hraw buildInductive
  simpa [raw, inductiveBytes, inductiveRawBytes, buildInductive, pairBytes,
    ByteArray.append_assoc] using hmapped

theorem getInductive_canonical : GetCanonical getInductive inductiveBytes := by
  have hraw : GetCanonical getInductiveRaw inductiveRawBytes := by
    apply getPair_canonical
    · exact getStrictBool_canonical "getInductive"
    · apply getPair_canonical
      · exact getTag0_canonical
      · apply getPair_canonical
        · exact getTag0_canonical
        · apply getPair_canonical
          · exact getTag0_canonical
          · exact getPair_canonical _ _ _ _
              ExprLaws.getExpr_canonical
              (getCountedArray_canonical getConstructor constructorBytes
                getConstructor_canonical)
  rw [getInductive_eq]
  exact GetCanonical.map hraw buildInductive inductiveBytes
    inductiveRawBytes_build

theorem getMutConstTag_spec (m : MutConst) (hwf : m.wireWF) :
    GetSpec (getMutConstTag (mutConstTag m)) (mutConstPayloadBytes m) m := by
  cases m with
  | defn d =>
    simpa [getMutConstTag, mutConstTag, mutConstPayloadBytes] using
      ExprLaws.GetSpec.map (getDefinition_spec d hwf) MutConst.defn
  | indc i =>
    simpa [getMutConstTag, mutConstTag, mutConstPayloadBytes] using
      ExprLaws.GetSpec.map (getInductive_spec i hwf) MutConst.indc
  | recr r =>
    simpa [getMutConstTag, mutConstTag, mutConstPayloadBytes] using
      ExprLaws.GetSpec.map (getRecursor_spec r hwf) MutConst.recr

theorem getMutConst_spec (m : MutConst) (hwf : m.wireWF) :
    GetSpec getMutConst (mutConstBytes m) m := by
  let afterTag : UInt8 → GetM MutConst := getMutConstTag
  have htotal := GetSpec.bind (next := afterTag)
    (getU8_spec (mutConstTag m)) (getMutConstTag_spec m hwf)
  simpa [getMutConst, mutConstBytes, afterTag] using htotal

theorem getMutConstTag_canonical (tag : UInt8) :
    GetCanonical (getMutConstTag tag) mutConstPayloadBytes := by
  by_cases h0 : tag = 0
  · subst tag
    simpa [getMutConstTag, mutConstPayloadBytes] using
      GetCanonical.map getDefinition_canonical MutConst.defn
        mutConstPayloadBytes (by intro d; rfl)
  by_cases h1 : tag = 1
  · subst tag
    simpa [getMutConstTag, mutConstPayloadBytes] using
      GetCanonical.map getInductive_canonical MutConst.indc
        mutConstPayloadBytes (by intro i; rfl)
  by_cases h2 : tag = 2
  · subst tag
    simpa [getMutConstTag, mutConstPayloadBytes] using
      GetCanonical.map getRecursor_canonical MutConst.recr
        mutConstPayloadBytes (by intro r; rfl)
  · intro pre rest value st' h
    simp [getMutConstTag] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getMutConstTag_success_tag (tag : UInt8) :
    ∀ (initial : GetState) {value : MutConst} {st' : GetState},
      (getMutConstTag tag).run initial = .ok (value, st') →
      tag = mutConstTag value := by
  intro initial value st' h
  by_cases h0 : tag = 0
  · subst tag
    simp [getMutConstTag] at h
    cases hd : getDefinition.run initial with
    | error err => rw [hd] at h; contradiction
    | ok result =>
      rcases result with ⟨d, after⟩
      rw [hd] at h
      cases h
      rfl
  by_cases h1 : tag = 1
  · subst tag
    simp [getMutConstTag] at h
    cases hi : getInductive.run initial with
    | error err => rw [hi] at h; contradiction
    | ok result =>
      rcases result with ⟨i, after⟩
      rw [hi] at h
      cases h
      rfl
  by_cases h2 : tag = 2
  · subst tag
    simp [getMutConstTag] at h
    cases hr : getRecursor.run initial with
    | error err => rw [hr] at h; contradiction
    | ok result =>
      rcases result with ⟨r, after⟩
      rw [hr] at h
      cases h
      rfl
  · simp [getMutConstTag] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getMutConst_canonical : GetCanonical getMutConst mutConstBytes := by
  intro pre rest value st' h
  change (getU8 >>= getMutConstTag).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨tag, afterTagBytes, hrestTag, hafterTag⟩ :=
    ExprLaws.GetCanonical.bind_inv getU8_canonical pre rest h
  let tagPre := pre ++ u8Bytes tag
  have hafterTag' :
      (getMutConstTag tag).run ⟨tagPre ++ afterTagBytes, tagPre.size⟩ =
        .ok (value, st') := by
    simpa [tagPre] using hafterTag
  obtain ⟨suffix, hrestPayload, hstate⟩ :=
    getMutConstTag_canonical tag tagPre afterTagBytes hafterTag'
  have htag := getMutConstTag_success_tag tag
    ⟨tagPre ++ afterTagBytes, tagPre.size⟩ hafterTag'
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestTag, hrestPayload, htag]
    simp [mutConstBytes, ByteArray.append_assoc]
  · simpa [tagPre, hrestTag, hrestPayload, htag, mutConstBytes,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc] using hstate

theorem getConstantInfoTag_spec (info : ConstantInfo) (hwf : info.wireWF) :
    GetSpec (getConstantInfoTag (constantInfoTag info))
      (constantInfoPayloadBytes info) info := by
  cases info with
  | defn d =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_DEFN] using
      ExprLaws.GetSpec.map (getDefinition_spec d hwf) ConstantInfo.defn
  | recr r =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_RECR] using
      ExprLaws.GetSpec.map (getRecursor_spec r hwf) ConstantInfo.recr
  | axio a =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_AXIO] using
      ExprLaws.GetSpec.map (getAxiom_spec a hwf) ConstantInfo.axio
  | quot q =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_QUOT] using
      ExprLaws.GetSpec.map (getQuotient_spec q hwf) ConstantInfo.quot
  | cPrj p =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_CPRJ] using
      ExprLaws.GetSpec.map (getConstructorProj_spec p) ConstantInfo.cPrj
  | rPrj p =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_RPRJ] using
      ExprLaws.GetSpec.map (getRecursorProj_spec p) ConstantInfo.rPrj
  | iPrj p =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_IPRJ] using
      ExprLaws.GetSpec.map (getInductiveProj_spec p) ConstantInfo.iPrj
  | dPrj p =>
    simpa [getConstantInfoTag, getConstantInfoVariant, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, ConstantInfo.CONST_DPRJ] using
      ExprLaws.GetSpec.map (getDefinitionProj_spec p) ConstantInfo.dPrj
  | muts members =>
    rcases hwf with ⟨hsize, hmembers⟩
    have hround : members.size.toUInt64.toNat = members.size :=
      UInt64.toNat_ofNat_of_lt hsize
    have hmembersList : ∀ member ∈ members.toList, member.wireWF := by
      intro member hmember
      exact hmembers member (by simpa using hmember)
    have harray := getArrayN_spec_of getMutConst mutConstBytes
      MutConst.wireWF getMutConst_spec members hmembersList
    have hmapped := ExprLaws.GetSpec.map harray ConstantInfo.muts
    simpa [getConstantInfoTag, constantInfoTag, constantInfoPayloadBytes,
      Constant.FLAG, Constant.FLAG_MUTS, hround] using hmapped

theorem getConstantInfo_spec (info : ConstantInfo) (hwf : info.wireWF) :
    GetSpec getConstantInfo (constantInfoBytes info) info := by
  let afterTag : Tag4 → GetM ConstantInfo := getConstantInfoTag
  have htotal := GetSpec.bind (next := afterTag)
    (getTag4_encoded_spec (constantInfoTag info) (by
      cases info <;> simp [constantInfoTag, Constant.FLAG, Constant.FLAG_MUTS]))
    (getConstantInfoTag_spec info hwf)
  simpa [getConstantInfo, constantInfoBytes, afterTag] using htotal

theorem getConstantInfoTag_canonical (tag : Tag4) :
    GetCanonical (getConstantInfoTag tag) constantInfoPayloadBytes := by
  rcases tag with ⟨flag, size⟩
  by_cases hm : flag = Constant.FLAG_MUTS
  · subst flag
    have harray := getArrayN_canonical getMutConst mutConstBytes
      getMutConst_canonical size.toNat
    simpa [getConstantInfoTag, Constant.FLAG_MUTS,
      constantInfoPayloadBytes] using
        GetCanonical.map harray ConstantInfo.muts
          constantInfoPayloadBytes (by intro members; rfl)
  by_cases hc : flag = Constant.FLAG
  · subst flag
    by_cases h0 : size = ConstantInfo.CONST_DEFN
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_DEFN, constantInfoPayloadBytes] using
          GetCanonical.map getDefinition_canonical ConstantInfo.defn
            constantInfoPayloadBytes (by intro d; rfl)
    by_cases h1 : size = ConstantInfo.CONST_RECR
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_RECR, constantInfoPayloadBytes] using
          GetCanonical.map getRecursor_canonical ConstantInfo.recr
            constantInfoPayloadBytes (by intro r; rfl)
    by_cases h2 : size = ConstantInfo.CONST_AXIO
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_AXIO, constantInfoPayloadBytes] using
          GetCanonical.map getAxiom_canonical ConstantInfo.axio
            constantInfoPayloadBytes (by intro a; rfl)
    by_cases h3 : size = ConstantInfo.CONST_QUOT
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_QUOT, constantInfoPayloadBytes] using
          GetCanonical.map getQuotient_canonical ConstantInfo.quot
            constantInfoPayloadBytes (by intro q; rfl)
    by_cases h4 : size = ConstantInfo.CONST_CPRJ
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_CPRJ, constantInfoPayloadBytes] using
          GetCanonical.map getConstructorProj_canonical ConstantInfo.cPrj
            constantInfoPayloadBytes (by intro p; rfl)
    by_cases h5 : size = ConstantInfo.CONST_RPRJ
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_RPRJ, constantInfoPayloadBytes] using
          GetCanonical.map getRecursorProj_canonical ConstantInfo.rPrj
            constantInfoPayloadBytes (by intro p; rfl)
    by_cases h6 : size = ConstantInfo.CONST_IPRJ
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_IPRJ, constantInfoPayloadBytes] using
          GetCanonical.map getInductiveProj_canonical ConstantInfo.iPrj
            constantInfoPayloadBytes (by intro p; rfl)
    by_cases h7 : size = ConstantInfo.CONST_DPRJ
    · subst size
      simpa [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_DPRJ, constantInfoPayloadBytes] using
          GetCanonical.map getDefinitionProj_canonical ConstantInfo.dPrj
            constantInfoPayloadBytes (by intro p; rfl)
    · intro pre rest value st' h
      have hn0 : size ≠ 0 := by simpa using h0
      have hn1 : size ≠ 1 := by simpa using h1
      have hn2 : size ≠ 2 := by simpa using h2
      have hn3 : size ≠ 3 := by simpa using h3
      have hn4 : size ≠ 4 := by simpa using h4
      have hn5 : size ≠ 5 := by simpa using h5
      have hn6 : size ≠ 6 := by simpa using h6
      have hn7 : size ≠ 7 := by simpa using h7
      simp [getConstantInfoTag, getConstantInfoVariant, Constant.FLAG, Constant.FLAG_MUTS,
        ConstantInfo.CONST_DEFN, ConstantInfo.CONST_RECR,
        ConstantInfo.CONST_AXIO, ConstantInfo.CONST_QUOT,
        ConstantInfo.CONST_CPRJ, ConstantInfo.CONST_RPRJ,
        ConstantInfo.CONST_IPRJ, ConstantInfo.CONST_DPRJ,
        hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7] at h
      change (Except.error _) = Except.ok (value, st') at h
      contradiction
  · intro pre rest value st' h
    have hnm : flag ≠ 12 := by simpa using hm
    have hnc : flag ≠ 13 := by simpa using hc
    simp [getConstantInfoTag,
      Constant.FLAG, Constant.FLAG_MUTS, hnm, hnc] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem map_success_inv (get : GetM α) (f : α → β)
    (initial : GetState) {value : β} {st' : GetState}
    (h : (f <$> get).run initial = .ok (value, st')) :
    ∃ source afterSource,
      get.run initial = .ok (source, afterSource) ∧
      value = f source ∧ st' = afterSource := by
  change (get >>= fun source => pure (f source)).run initial =
    .ok (value, st') at h
  simp only [StateT.run_bind] at h
  cases hg : get.run initial with
  | error err => rw [hg] at h; contradiction
  | ok sourceState =>
    rcases sourceState with ⟨source, afterSource⟩
    rw [hg] at h
    simp at h
    cases h
    exact ⟨source, afterSource, rfl, rfl, rfl⟩

theorem map_success_exists (get : GetM α) (f : α → β)
    (initial : GetState) {value : β} {st' : GetState}
    (h : (f <$> get).run initial = .ok (value, st')) :
    ∃ source, value = f source := by
  obtain ⟨source, afterSource, hsource, hvalue, hstate⟩ :=
    map_success_inv get f initial h
  exact ⟨source, hvalue⟩

theorem getConstantInfoVariant_success_tag (variant : UInt64) :
    ∀ (initial : GetState) {value : ConstantInfo} {st' : GetState},
      (getConstantInfoVariant variant).run initial = .ok (value, st') →
      ⟨Constant.FLAG, variant⟩ = constantInfoTag value := by
  intro initial value st' h
  by_cases h0 : variant = 0
  · subst variant
    have h' : (ConstantInfo.defn <$> getDefinition).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨d, rfl⟩ := map_success_exists getDefinition ConstantInfo.defn
      initial h'
    rfl
  by_cases h1 : variant = 1
  · subst variant
    have h' : (ConstantInfo.recr <$> getRecursor).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨r, rfl⟩ := map_success_exists getRecursor ConstantInfo.recr
      initial h'
    rfl
  by_cases h2 : variant = 2
  · subst variant
    have h' : (ConstantInfo.axio <$> getAxiom).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨a, rfl⟩ := map_success_exists getAxiom ConstantInfo.axio
      initial h'
    rfl
  by_cases h3 : variant = 3
  · subst variant
    have h' : (ConstantInfo.quot <$> getQuotient).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨q, rfl⟩ := map_success_exists getQuotient ConstantInfo.quot
      initial h'
    rfl
  by_cases h4 : variant = 4
  · subst variant
    have h' : (ConstantInfo.cPrj <$> getConstructorProj).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨p, rfl⟩ := map_success_exists getConstructorProj ConstantInfo.cPrj
      initial h'
    rfl
  by_cases h5 : variant = 5
  · subst variant
    have h' : (ConstantInfo.rPrj <$> getRecursorProj).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨p, rfl⟩ := map_success_exists getRecursorProj ConstantInfo.rPrj
      initial h'
    rfl
  by_cases h6 : variant = 6
  · subst variant
    have h' : (ConstantInfo.iPrj <$> getInductiveProj).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨p, rfl⟩ := map_success_exists getInductiveProj ConstantInfo.iPrj
      initial h'
    rfl
  by_cases h7 : variant = 7
  · subst variant
    have h' : (ConstantInfo.dPrj <$> getDefinitionProj).run initial =
        .ok (value, st') := by simpa [getConstantInfoVariant] using h
    obtain ⟨p, rfl⟩ := map_success_exists getDefinitionProj ConstantInfo.dPrj
      initial h'
    rfl
  · have hn0 : variant ≠ 0 := h0
    have hn1 : variant ≠ 1 := h1
    have hn2 : variant ≠ 2 := h2
    have hn3 : variant ≠ 3 := h3
    have hn4 : variant ≠ 4 := h4
    have hn5 : variant ≠ 5 := h5
    have hn6 : variant ≠ 6 := h6
    have hn7 : variant ≠ 7 := h7
    simp [getConstantInfoVariant, hn0, hn1, hn2, hn3,
      hn4, hn5, hn6, hn7] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getConstantInfoTag_success_tag (tag : Tag4) :
    ∀ (initial : GetState) {value : ConstantInfo} {st' : GetState},
      (getConstantInfoTag tag).run initial = .ok (value, st') →
      tag = constantInfoTag value := by
  rcases tag with ⟨flag, size⟩
  intro initial value st' h
  by_cases hm : flag = Constant.FLAG_MUTS
  · subst flag
    have h' : (ConstantInfo.muts <$> getArrayN getMutConst size.toNat).run
        initial = .ok (value, st') := by
      simpa [getConstantInfoTag] using h
    obtain ⟨members, afterMembers, ha, hvalue, hstate⟩ :=
      map_success_inv (getArrayN getMutConst size.toNat)
        ConstantInfo.muts initial h'
    subst value
    have hsize := getArrayN_success_size getMutConst size.toNat initial ha
    have hcount : members.size.toUInt64 = size := by
      rw [hsize]
      exact UInt64.ofNat_toNat
    simp [constantInfoTag, hcount]
  by_cases hc : flag = Constant.FLAG
  · subst flag
    have h' : (getConstantInfoVariant size).run initial =
        .ok (value, st') := by simpa [getConstantInfoTag] using h
    exact getConstantInfoVariant_success_tag size initial h'
  · have hnm : flag ≠ 12 := by simpa using hm
    have hnc : flag ≠ 13 := by simpa using hc
    simp [getConstantInfoTag, hnm, hnc] at h
    change (Except.error _) = Except.ok (value, st') at h
    contradiction

theorem getConstantInfo_canonical :
    GetCanonical getConstantInfo constantInfoBytes := by
  intro pre rest value st' h
  change (getTag4 >>= getConstantInfoTag).run ⟨pre ++ rest, pre.size⟩ =
    .ok (value, st') at h
  obtain ⟨tag, afterTagBytes, hrestTag, hafterTag⟩ :=
    ExprLaws.GetCanonical.bind_inv getTag4_canonical pre rest h
  let tagPre := pre ++ tag4Bytes tag
  have hafterTag' :
      (getConstantInfoTag tag).run
        ⟨tagPre ++ afterTagBytes, tagPre.size⟩ = .ok (value, st') := by
    simpa [tagPre] using hafterTag
  obtain ⟨suffix, hrestPayload, hstate⟩ :=
    getConstantInfoTag_canonical tag tagPre afterTagBytes hafterTag'
  have htag := getConstantInfoTag_success_tag tag
    ⟨tagPre ++ afterTagBytes, tagPre.size⟩ hafterTag'
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestTag, hrestPayload, htag]
    simp [constantInfoBytes, ByteArray.append_assoc]
  · simpa [tagPre, hrestTag, hrestPayload, htag, constantInfoBytes,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc] using hstate

theorem canonicalLaw_of_getCanonical [Serialize α]
    (encode : α → ByteArray)
    (hput : ∀ value, PutSpec (Serialize.put value) (encode value))
    (hget : GetCanonical (Serialize.get (self := inferInstance)) encode) :
    CanonicalLaw α := by
  intro input value h
  change runPut (Serialize.put value) = input
  rw [runPut_eq_of_spec (hput value)]
  simp only [de, runGet] at h
  cases hg : (Serialize.get (self := inferInstance) : GetM α).run
      ⟨input, 0⟩ with
  | error err => rw [hg] at h; contradiction
  | ok result =>
    rcases result with ⟨decoded, st⟩
    rw [hg] at h
    simp only [bind, Except.bind] at h
    obtain ⟨suffix, hinput, hst⟩ :=
      hget ByteArray.empty input hg
    by_cases hfull : st.idx = st.bytes.size
    · simp [hfull] at h
      cases h
      have hsize : (encode value).size = input.size := by
        have hidx := congrArg GetState.idx hst
        have hbytes := congrArg GetState.bytes hst
        simp at hidx hbytes
        rw [hfull, hbytes] at hidx
        exact hidx.symm
      have hsuffix : suffix = ByteArray.empty := by
        have hsizes := congrArg ByteArray.size hinput
        simpa [ByteArray.size_append, hsize] using hsizes
      simpa [hsuffix] using hinput.symm
    · simp [hfull] at h

theorem checkConstantSharing_spec (info : ConstantInfo)
    (sharing : Array Expr)
    (hwf : Sharing.layer1WF sharing info.exprs.toArray = true) :
    GetSpec (checkConstantSharing info sharing) ByteArray.empty () := by
  have hlayer := (Sharing.layer1WF_iff sharing info.exprs.toArray).mp hwf
  intro pre suffix
  simp only [checkConstantSharing]
  rw [hlayer.tableOk, hlayer.bodiesOk, hlayer.usedTwice]
  simp
  rfl

theorem checkConstantSharing_canonical (info : ConstantInfo)
    (sharing : Array Expr) :
    GetCanonical (checkConstantSharing info sharing)
      (fun _ => ByteArray.empty) := by
  intro pre rest value st' h
  simp only [checkConstantSharing] at h
  split at h
  · change (Except.error _) = Except.ok (value, st') at h
    contradiction
  · split at h
    · change (Except.error _) = Except.ok (value, st') at h
      contradiction
    · split at h
      · change (Except.error _) = Except.ok (value, st') at h
        contradiction
      · simp at h
        cases h
        exact ⟨rest, by simp, by simp⟩

def refsUnivsBytes (tables : Array Address × Array Univ) : ByteArray :=
  pairBytes (countedArrayBytes (fun address : Address => address.hash))
    (countedArrayBytes univBytes) tables

theorem getConstantRefsUnivs_spec (refs : Array Address) (univs : Array Univ)
    (hrefsSize : refs.size < UInt64.size)
    (hunivsSize : univs.size < UInt64.size) :
    GetSpec getConstantRefsUnivs (refsUnivsBytes (refs, univs))
      (refs, univs) := by
  exact getPair_spec _ _ _ _
    (getCountedArray_spec Serialize.get (fun address : Address => address.hash)
      Address.get_spec refs hrefsSize)
    (getCountedArray_spec getUniv univBytes UnivLaws.getUniv_spec
      univs hunivsSize)

theorem getConstantRefsUnivs_canonical :
    GetCanonical getConstantRefsUnivs refsUnivsBytes := by
  exact getPair_canonical _ _ _ _
    (getCountedArray_canonical Serialize.get
      (fun address : Address => address.hash) getAddress_canonical)
    (getCountedArray_canonical getUniv univBytes UnivLaws.getUniv_canonical)

def constantAfterInfoBytes
    (tail : Array Expr × (Array Address × Array Univ)) : ByteArray :=
  countedArrayBytes exprBytes tail.1 ++ refsUnivsBytes tail.2

def constantRawBytes (raw : ConstantRaw) : ByteArray :=
  constantInfoBytes raw.1 ++ constantAfterInfoBytes raw.2

theorem getConstantRaw_eq :
    getConstantRaw = getConstantInfo >>= fun info =>
      (fun tail => (info, tail)) <$> getConstantAfterInfo info := by
  rfl

theorem getConstantAfterSharing_spec (info : ConstantInfo)
    (sharing : Array Expr) (refs : Array Address) (univs : Array Univ)
    (hsharing : Sharing.layer1WF sharing info.exprs.toArray = true)
    (hrefsSize : refs.size < UInt64.size)
    (hunivsSize : univs.size < UInt64.size) :
    GetSpec (getConstantAfterSharing info sharing)
      (refsUnivsBytes (refs, univs)) (sharing, (refs, univs)) := by
  have hcheck := checkConstantSharing_spec info sharing hsharing
  have htables := getConstantRefsUnivs_spec refs univs hrefsSize hunivsSize
  let finish : Array Address × Array Univ →
      GetM (Array Expr × (Array Address × Array Univ)) := fun tables =>
    pure (sharing, tables)
  have hfinish : GetSpec (finish (refs, univs)) ByteArray.empty
      (sharing, (refs, univs)) := GetSpec.pure _
  have htables' := GetSpec.bind (next := finish) htables hfinish
  simp only [ByteArray.append_empty] at htables'
  let afterCheck : Unit → GetM (Array Expr × (Array Address × Array Univ)) :=
    fun _ => do
      let tables ← getConstantRefsUnivs
      return (sharing, tables)
  have hafter : GetSpec (afterCheck ()) (refsUnivsBytes (refs, univs))
      (sharing, (refs, univs)) := by
    simpa [afterCheck, finish] using htables'
  have htotal := GetSpec.bind (next := afterCheck) hcheck hafter
  simpa [getConstantAfterSharing, afterCheck] using htotal

theorem getConstantAfterInfo_spec (info : ConstantInfo)
    (sharing : Array Expr) (refs : Array Address) (univs : Array Univ)
    (hsharingSize : sharing.size < UInt64.size)
    (hsharingExprs : ∀ e ∈ sharing, e.wireWF)
    (hrefsSize : refs.size < UInt64.size)
    (hunivsSize : univs.size < UInt64.size)
    (hsharing : Sharing.layer1WF sharing info.exprs.toArray = true) :
    GetSpec (getConstantAfterInfo info)
      (constantAfterInfoBytes (sharing, (refs, univs)))
      (sharing, (refs, univs)) := by
  have hsharingList : ∀ e ∈ sharing.toList, e.wireWF := by
    intro e he
    exact hsharingExprs e (by simpa using he)
  have hsharingSpec : GetSpec (getCountedArray getExpr)
      (countedArrayBytes exprBytes sharing) sharing :=
    getCountedArray_spec_of getExpr exprBytes Expr.wireWF
      ExprLaws.getExpr_spec sharing hsharingSize hsharingList
  have hafter := getConstantAfterSharing_spec info sharing refs univs
    hsharing hrefsSize hunivsSize
  let afterSharing : Array Expr →
      GetM (Array Expr × (Array Address × Array Univ)) :=
    getConstantAfterSharing info
  have htotal := GetSpec.bind (next := afterSharing) hsharingSpec hafter
  simpa [getConstantAfterInfo, constantAfterInfoBytes, afterSharing,
    ByteArray.append_assoc] using htotal

theorem getConstantRaw_spec (c : Constant) (hwf : c.wireWF)
    (hsharing : c.sharingWF = true) :
    GetSpec getConstantRaw
      (constantRawBytes (c.info, (c.sharing, (c.refs, c.univs))))
      (c.info, (c.sharing, (c.refs, c.univs))) := by
  rcases c with ⟨info, sharing, refs, univs⟩
  rcases hwf with
    ⟨hinfo, hsharingSize, hsharingExprs, hrefsSize, hunivsSize⟩
  have htail := getConstantAfterInfo_spec info sharing refs univs
    hsharingSize hsharingExprs hrefsSize hunivsSize hsharing
  have hfinish : GetSpec
      ((fun tail => (info, tail)) <$> getConstantAfterInfo info)
      (constantAfterInfoBytes (sharing, (refs, univs)))
      (info, (sharing, (refs, univs))) := by
    simpa using ExprLaws.GetSpec.map htail (fun tail => (info, tail))
  have htotal := GetSpec.bind
    (next := fun decodedInfo =>
      (fun tail => (decodedInfo, tail)) <$> getConstantAfterInfo decodedInfo)
    (getConstantInfo_spec info hinfo) hfinish
  rw [getConstantRaw_eq]
  simpa [constantRawBytes] using htotal

theorem constantBytes_buildConstant (raw : ConstantRaw) :
    constantBytes (buildConstant raw) = constantRawBytes raw := by
  rcases raw with ⟨info, sharing, refs, univs⟩
  simp [constantBytes, constantTablesBytes, constantRawBytes,
    constantAfterInfoBytes, refsUnivsBytes, buildConstant, pairBytes,
    ByteArray.append_assoc]

theorem getConstant_spec (c : Constant) (hwf : c.wireWF)
    (hsharing : c.sharingWF = true) :
    GetSpec getConstant (constantBytes c) c := by
  let raw : ConstantRaw := (c.info, (c.sharing, (c.refs, c.univs)))
  have hraw := getConstantRaw_spec c hwf hsharing
  have hmapped := ExprLaws.GetSpec.map hraw buildConstant
  simpa [getConstant, raw, buildConstant, constantRawBytes,
    constantBytes, constantTablesBytes, constantAfterInfoBytes,
    refsUnivsBytes, pairBytes, ByteArray.append_assoc] using hmapped

theorem getConstantAfterSharing_canonical (info : ConstantInfo)
    (sharing : Array Expr) :
    GetCanonical (getConstantAfterSharing info sharing)
      (fun result => refsUnivsBytes result.2) := by
  have htables : GetCanonical
      ((fun tables => (sharing, tables)) <$> getConstantRefsUnivs)
      (fun result => refsUnivsBytes result.2) := by
    exact GetCanonical.map getConstantRefsUnivs_canonical
      (fun tables => (sharing, tables))
      (fun result => refsUnivsBytes result.2) (by intro tables; rfl)
  intro pre rest result st' h
  let afterCheck : Unit →
      GetM (Array Expr × (Array Address × Array Univ)) :=
    fun _ => (fun tables => (sharing, tables)) <$> getConstantRefsUnivs
  change (checkConstantSharing info sharing >>= afterCheck).run
    ⟨pre ++ rest, pre.size⟩ = .ok (result, st') at h
  obtain ⟨checked, afterCheckBytes, hrestCheck, hafterCheck⟩ :=
    ExprLaws.GetCanonical.bind_inv
      (checkConstantSharing_canonical info sharing) pre rest h
  have hchecked : checked = () := Subsingleton.elim _ _
  subst checked
  have hafterCheck' :
      ((fun tables => (sharing, tables)) <$> getConstantRefsUnivs).run
        ⟨(pre ++ ByteArray.empty) ++ afterCheckBytes,
          (pre ++ ByteArray.empty).size⟩ = .ok (result, st') := by
    simpa [afterCheck] using hafterCheck
  obtain ⟨suffix, hrestTables, hstate⟩ :=
    htables (pre ++ ByteArray.empty) afterCheckBytes hafterCheck'
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestCheck, hrestTables]
    simp
  · simpa [hrestCheck, hrestTables, ByteArray.append_assoc,
      ByteArray.size_append, Nat.add_assoc] using hstate

theorem getConstantAfterSharing_success_fst (info : ConstantInfo)
    (sharing : Array Expr) (initial : GetState)
    {result : Array Expr × (Array Address × Array Univ)} {st' : GetState}
    (h : (getConstantAfterSharing info sharing).run initial =
      .ok (result, st')) :
    result.1 = sharing := by
  simp only [getConstantAfterSharing, StateT.run_bind] at h
  cases hc : (checkConstantSharing info sharing).run initial with
  | error err => rw [hc] at h; contradiction
  | ok checkedState =>
    rcases checkedState with ⟨checked, afterCheck⟩
    rw [hc] at h
    simp only [bind, Except.bind] at h
    cases ht : getConstantRefsUnivs.run afterCheck with
    | error err => rw [ht] at h; contradiction
    | ok tablesState =>
      rcases tablesState with ⟨tables, afterTables⟩
      rw [ht] at h
      simp at h
      cases h
      rfl

theorem getConstantAfterInfo_canonical (info : ConstantInfo) :
    GetCanonical (getConstantAfterInfo info) constantAfterInfoBytes := by
  intro pre rest result st' h
  let afterSharing : Array Expr →
      GetM (Array Expr × (Array Address × Array Univ)) :=
    getConstantAfterSharing info
  change (getCountedArray getExpr >>= afterSharing).run
    ⟨pre ++ rest, pre.size⟩ = .ok (result, st') at h
  obtain ⟨sharing, afterSharingBytes, hrestSharing, hafterSharing⟩ :=
    ExprLaws.GetCanonical.bind_inv
      (getCountedArray_canonical getExpr exprBytes
        ExprLaws.getExpr_canonical) pre rest h
  let sharingPre := pre ++ countedArrayBytes exprBytes sharing
  have hafterSharing' :
      (getConstantAfterSharing info sharing).run
        ⟨sharingPre ++ afterSharingBytes, sharingPre.size⟩ =
          .ok (result, st') := by
    simpa [afterSharing, sharingPre] using hafterSharing
  obtain ⟨suffix, hrestTables, hstate⟩ :=
    getConstantAfterSharing_canonical info sharing
      sharingPre afterSharingBytes hafterSharing'
  have hshape := getConstantAfterSharing_success_fst info sharing
    ⟨sharingPre ++ afterSharingBytes, sharingPre.size⟩ hafterSharing'
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestSharing, hrestTables, ← hshape]
    simp [constantAfterInfoBytes, ByteArray.append_assoc]
  · simpa [sharingPre, hrestSharing, hrestTables, ← hshape,
      constantAfterInfoBytes, ByteArray.append_assoc,
      ByteArray.size_append, Nat.add_assoc] using hstate

theorem getConstantRaw_canonical :
    GetCanonical getConstantRaw constantRawBytes := by
  intro pre rest result st' h
  let afterInfo : ConstantInfo → GetM ConstantRaw := fun info =>
    (fun tail => (info, tail)) <$> getConstantAfterInfo info
  change (getConstantInfo >>= afterInfo).run
    ⟨pre ++ rest, pre.size⟩ = .ok (result, st') at h
  obtain ⟨info, afterInfoBytes, hrestInfo, hafterInfo⟩ :=
    ExprLaws.GetCanonical.bind_inv getConstantInfo_canonical pre rest h
  let infoPre := pre ++ constantInfoBytes info
  have hafterInfo' :
      ((fun tail => (info, tail)) <$> getConstantAfterInfo info).run
        ⟨infoPre ++ afterInfoBytes, infoPre.size⟩ = .ok (result, st') := by
    change ((fun tail => (info, tail)) <$> getConstantAfterInfo info).run
      ⟨(pre ++ constantInfoBytes info) ++ afterInfoBytes,
        (pre ++ constantInfoBytes info).size⟩ = .ok (result, st') at hafterInfo
    exact hafterInfo
  have hmapped : GetCanonical
      ((fun tail => (info, tail)) <$> getConstantAfterInfo info)
      (fun raw => constantAfterInfoBytes raw.2) :=
    GetCanonical.map (getConstantAfterInfo_canonical info)
      (fun tail => (info, tail))
      (fun raw => constantAfterInfoBytes raw.2) (by intro tail; rfl)
  obtain ⟨suffix, hrestTail, hstate⟩ :=
    hmapped infoPre afterInfoBytes hafterInfo'
  obtain ⟨tail, hresult⟩ :=
    map_success_exists (getConstantAfterInfo info)
      (fun decodedTail => (info, decodedTail))
      ⟨infoPre ++ afterInfoBytes, infoPre.size⟩ hafterInfo'
  subst result
  refine ⟨suffix, ?_, ?_⟩
  · rw [hrestInfo, hrestTail]
    simp [constantRawBytes, ByteArray.append_assoc]
  · simpa [infoPre, hrestInfo, hrestTail, constantRawBytes,
      ByteArray.append_assoc, ByteArray.size_append,
      Nat.add_assoc] using hstate

theorem getConstant_canonical :
    GetCanonical getConstant constantBytes := by
  change GetCanonical (buildConstant <$> getConstantRaw) constantBytes
  exact GetCanonical.map getConstantRaw_canonical buildConstant constantBytes
    constantBytes_buildConstant

end ConstLaws

namespace ConstantInfo

/-- Roundtrip on the exact recursively u64-count-representable domain. -/
def RoundtripLaw : Prop :=
  ∀ info : ConstantInfo, info.wireWF → de (ser info) = .ok info

theorem roundtripLaw : RoundtripLaw := by
  intro info hwf
  change runGet getConstantInfo (runPut (putConstantInfo info)) = .ok info
  rw [runPut_eq_of_spec (putConstantInfo_spec info)]
  exact runGet_eq_ok_of_spec (ConstLaws.getConstantInfo_spec info hwf)

/-- Every accepted constant-info payload has one canonical byte spelling. -/
theorem canonicalLaw : Ixon.CanonicalLaw ConstantInfo :=
  ConstLaws.canonicalLaw_of_getCanonical constantInfoBytes
    putConstantInfo_spec ConstLaws.getConstantInfo_canonical

end ConstantInfo

/-- Roundtrip is intentionally stated on the accepted and wire-representable
constant fragment. Raw `Constant` remains useful for constructing rejection
fixtures, and mathematical arrays may exceed their u64 wire counts. -/
def Constant.RoundtripLaw : Prop :=
  ∀ c : Constant, c.wireWF → c.sharingWF = true → de (ser c) = .ok c

namespace Constant

/-- Every accepted, count-representable constant survives strict decoding. -/
theorem roundtripLaw : RoundtripLaw := by
  intro c hwf hsharing
  change runGet getConstant (runPut (putConstant c)) = .ok c
  rw [runPut_eq_of_spec (putConstant_spec c)]
  exact runGet_eq_ok_of_spec (ConstLaws.getConstant_spec c hwf hsharing)

/-- Every byte string accepted as a constant is its canonical encoding. -/
theorem canonicalLaw : Ixon.CanonicalLaw Constant :=
  ConstLaws.canonicalLaw_of_getCanonical constantBytes
    putConstant_spec ConstLaws.getConstant_canonical

end Constant

/-! Elaboration-time roundtrip and canonicity checks. -/

private def constRoundtrips (c : Constant) : Bool :=
  match (de (ser c) : Except String Constant) with
  | .ok c' => c' == c
  | .error _ => false

private def addr (b : UInt8) : Address :=
  Address.replicate b

/-! A format-freezing v2 fixture. It deliberately covers all four
usage modes in both Π/λ telescopes, both result ownership modes, an
eight-element application and universe-instantiation spine, the
large form of Tag0/Tag2/Tag4, and every `Univ` constructor. Public
(not `private`): the compiled `Tests.lean` executable pins its raw bytes and
BLAKE3 digest through the real FFI hash path. Its deliberately synthetic local
indices make it a wire fixture, not a value admitted by the semantic
`address?` gate. -/

def goldenV2 : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 128
        typ :=
          .all .erased .unique (.sort 0)
            (.all .linear .shared (.sort 31)
              (.all .affine .unique (.sort 32)
                (.all .many .shared (.sort 128) (.sort 3))))
        value :=
          .lam .erased (.sort 0)
            (.lam .linear (.sort 31)
              (.lam .affine (.sort 32)
                (.lam .many (.sort 128)
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app (.ref 0 #[0, 1, 2, 3, 4, 0, 1, 2])
                                  (.var 3))
                                (.var 2))
                              (.var 1))
                            (.var 0))
                          (.share 0))
                        (.share 0))
                      (.str 0))
                    (.sort 256))))) }
    sharing := #[.app (.app (.recur 0 #[4]) (.prj 0 1 (.var 0))) (.var 0)]
    refs := #[addr 0xAB]
    univs := #[
      .zero,
      .succ .zero,
      .max (.var 0) (.succ (.var 1)),
      .imax (.var 2) (.max .zero (.var 3)),
      .var 256
    ] }

private def goldenV2Bytes : ByteArray := ByteArray.mk #[
  208, 1, 128, 128, 148, 0, 0, 5, 8, 31, 2, 8, 32, 7, 8, 128,
  3, 132, 0, 0, 1, 8, 31, 2, 8, 32, 3, 8, 128, 120, 8, 40,
  8, 0, 0, 1, 2, 3, 4, 0, 1, 2, 19, 18, 17, 16, 176, 176,
  80, 9, 0, 1, 1, 114, 49, 0, 4, 65, 0, 16, 16, 1, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 5, 0, 1, 0, 64, 192, 1, 193, 128, 194,
  64, 0, 195, 225, 0, 1
]

#guard ser goldenV2 == goldenV2Bytes
#guard constRoundtrips goldenV2

#guard constRoundtrips
  { info := .defn
      { kind := .thm, safety := .safe, lvls := 2
        typ := .all .many .shared (.sort 1) (.sort 1)
        value := .lam .linear (.var 0) (.app (.share 0) (.share 0)) }
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
    sharing := #[]
    refs := #[addr 0x02, addr 0x03]
    univs := #[.imax (.var 0) .zero] }

private def constRejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Constant) with
  | .ok _ => false
  | .error _ => true

private def sharingAxiom (typ : Expr) (sharing : Array Expr) : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ }
    sharing, refs := #[], univs := #[] }

private def invalidConstantRejected (c : Constant) : Bool :=
  match (de (ser c) : Except String Constant) with
  | .ok _ => false
  | .error _ => true

/-! Layer-1 sharing strictness. The positive fixture has a nested backward
reference: entry 0 is used twice by entry 1, then entry 1 twice by the body. -/

#guard constRoundtrips (sharingAxiom
  (.app (.share 1) (.share 1))
  #[.sort 0, .app (.share 0) (.share 0)])

-- body reference out of bounds
#guard invalidConstantRejected (sharingAxiom (.share 0) #[])
-- entry 0 self-reference (cycle)
#guard invalidConstantRejected (sharingAxiom
  (.app (.share 0) (.share 0))
  #[.app (.share 0) (.share 0)])
-- entry 0 forward-reference to entry 1
#guard invalidConstantRejected (sharingAxiom
  (.app (.share 1) (.share 1))
  #[.app (.share 1) (.share 1), .sort 0])
-- bare alias entry
#guard invalidConstantRejected (sharingAxiom
  (.app (.share 1) (.share 1))
  #[.sort 0, .share 0])
-- dead and singleton entries
#guard invalidConstantRejected (sharingAxiom (.sort 1) #[.sort 0])
#guard invalidConstantRejected (sharingAxiom (.share 0) #[.sort 0])

-- ConstantInfo variant 8 (out of range; large-form Tag4 size)
#guard constRejects #[0xD8, 0x08]
-- defn with invalid kind bits (0x0F: kind = 3)
#guard constRejects #[0xD0, 0x0F]
-- recursor with stray high bits in the packed-bool byte
#guard constRejects #[0xD1, 0x04]
-- axiom with non-canonical Bool byte 2
#guard constRejects #[0xD2, 0x02]
-- quotient with invalid quot-kind byte 4 (valid kinds are 0-3)
#guard constRejects #[0xD3, 0x04]
-- muts block whose first member carries invalid mut tag 3 (valid tags are 0-2)
#guard constRejects #[0xC1, 0x03]

end Ix.Compiler.Ixon
