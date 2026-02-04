import Ix.Ixon

namespace Ix

open Ixon

-- ============================================================================
-- Helpers
-- ============================================================================

private def computeMask (flags : List Bool) : UInt64 := Id.run do
  let mut mask : UInt64 := 0
  let mut i : UInt64 := 0
  for f in flags do
    if f then mask := mask ||| (1 <<< i)
    i := i + 1
  return mask

private def putBoolField (b : Bool) : PutM Unit := putU8 (if b then 1 else 0)

private def getBoolField : GetM Bool := do
  let v ← getU8
  if v == 0 then return false
  else if v == 1 then return true
  else throw s!"getBoolField: invalid {v}"

private def putDefKind (k : DefKind) : PutM Unit :=
  putU8 (match k with | .defn => 0 | .opaq => 1 | .thm => 2)

private def getDefKind : GetM DefKind := do
  match (← getU8) with
  | 0 => return .defn | 1 => return .opaq | 2 => return .thm
  | v => throw s!"getDefKind: invalid {v}"

private def putDefSafety (s : DefinitionSafety) : PutM Unit :=
  putU8 (match s with | .unsaf => 0 | .safe => 1 | .part => 2)

private def getDefSafety : GetM DefinitionSafety := do
  match (← getU8) with
  | 0 => return .unsaf | 1 => return .safe | 2 => return .part
  | v => throw s!"getDefSafety: invalid {v}"

private def putQuotKind (k : QuotKind) : PutM Unit :=
  putU8 (match k with | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3)

private def getQuotKind : GetM QuotKind := do
  match (← getU8) with
  | 0 => return .type | 1 => return .ctor | 2 => return .lift | 3 => return .ind
  | v => throw s!"getQuotKind: invalid {v}"

private def getTag0Size : GetM UInt64 := return (← getTag0).size

private def getOpt (mask : UInt64) (bit : UInt64) (read : GetM α) : GetM (Option α) :=
  if mask &&& bit != 0 then some <$> read else pure none

-- ============================================================================
-- Types
-- ============================================================================

/-- Revealed fields of a Constructor within an Inductive. -/
structure RevealConstructorInfo where
  isUnsafe : Option Bool := none
  lvls : Option UInt64 := none
  cidx : Option UInt64 := none
  params : Option UInt64 := none
  fields : Option UInt64 := none
  typ : Option Address := none
  deriving BEq, Repr, Inhabited

/-- Revealed fields of a RecursorRule. -/
structure RevealRecursorRule where
  ruleIdx : UInt64
  fields : UInt64
  rhs : Address
  deriving BEq, Repr, Inhabited

/-- Revealed fields of a MutConst component. -/
inductive RevealMutConstInfo where
  | defn (kind : Option DefKind) (safety : Option DefinitionSafety)
         (lvls : Option UInt64) (typ : Option Address) (value : Option Address)
  | indc (isRecr : Option Bool) (refl : Option Bool) (isUnsafe : Option Bool)
         (lvls : Option UInt64) (params : Option UInt64)
         (indices : Option UInt64) (nested : Option UInt64)
         (typ : Option Address) (ctors : Option (Array (UInt64 × RevealConstructorInfo)))
  | recr (k : Option Bool) (isUnsafe : Option Bool) (lvls : Option UInt64)
         (params : Option UInt64) (indices : Option UInt64)
         (motives : Option UInt64) (minors : Option UInt64)
         (typ : Option Address) (rules : Option (Array RevealRecursorRule))
  deriving BEq, Repr, Inhabited

/-- Revealed fields of a ConstantInfo behind a commitment. -/
inductive RevealConstantInfo where
  | defn (kind : Option DefKind) (safety : Option DefinitionSafety)
         (lvls : Option UInt64) (typ : Option Address) (value : Option Address)
  | recr (k : Option Bool) (isUnsafe : Option Bool) (lvls : Option UInt64)
         (params : Option UInt64) (indices : Option UInt64)
         (motives : Option UInt64) (minors : Option UInt64)
         (typ : Option Address) (rules : Option (Array RevealRecursorRule))
  | axio (isUnsafe : Option Bool) (lvls : Option UInt64) (typ : Option Address)
  | quot (kind : Option QuotKind) (lvls : Option UInt64) (typ : Option Address)
  | cPrj (idx : Option UInt64) (cidx : Option UInt64) (block : Option Address)
  | rPrj (idx : Option UInt64) (block : Option Address)
  | iPrj (idx : Option UInt64) (block : Option Address)
  | dPrj (idx : Option UInt64) (block : Option Address)
  | muts (components : Array (UInt64 × RevealMutConstInfo))
  deriving BEq, Repr, Inhabited

/-- A claim that can be proven. -/
inductive Claim where
  | eval (input : Address) (output : Address)
  | check (value : Address)
  | reveal (comm : Address) (info : RevealConstantInfo)
  deriving BEq, Repr, Inhabited

-- ============================================================================
-- RevealConstructorInfo serialization
-- ============================================================================

namespace RevealConstructorInfo

def put (info : RevealConstructorInfo) : PutM Unit := do
  let mask := computeMask [info.isUnsafe.isSome, info.lvls.isSome, info.cidx.isSome,
                           info.params.isSome, info.fields.isSome, info.typ.isSome]
  putTag0 ⟨mask⟩
  match info.isUnsafe with | some b => putBoolField b | none => pure ()
  match info.lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
  match info.cidx with | some n => putTag0 ⟨n⟩ | none => pure ()
  match info.params with | some n => putTag0 ⟨n⟩ | none => pure ()
  match info.fields with | some n => putTag0 ⟨n⟩ | none => pure ()
  match info.typ with | some a => Serialize.put a | none => pure ()

def get : GetM RevealConstructorInfo := do
  let mask := (← getTag0).size
  let isUnsafe ← getOpt mask 1 getBoolField
  let lvls ← getOpt mask 2 getTag0Size
  let cidx ← getOpt mask 4 getTag0Size
  let params ← getOpt mask 8 getTag0Size
  let fields ← getOpt mask 16 getTag0Size
  let typ ← getOpt mask 32 Serialize.get
  return ⟨isUnsafe, lvls, cidx, params, fields, typ⟩

end RevealConstructorInfo

-- ============================================================================
-- RevealRecursorRule serialization
-- ============================================================================

namespace RevealRecursorRule

def put (rule : RevealRecursorRule) : PutM Unit := do
  putTag0 ⟨rule.ruleIdx⟩
  putTag0 ⟨rule.fields⟩
  Serialize.put rule.rhs

def get : GetM RevealRecursorRule := do
  let ruleIdx ← getTag0Size
  let fields ← getTag0Size
  let rhs ← Serialize.get
  return ⟨ruleIdx, fields, rhs⟩

end RevealRecursorRule

-- ============================================================================
-- Array helpers
-- ============================================================================

private def putRules (rules : Array RevealRecursorRule) : PutM Unit := do
  putTag0 ⟨rules.size.toUInt64⟩
  for rule in rules do RevealRecursorRule.put rule

private def getRules : GetM (Array RevealRecursorRule) := do
  let count ← getTag0Size
  let mut rules := #[]
  for _ in [:count.toNat] do rules := rules.push (← RevealRecursorRule.get)
  return rules

private def putCtors (ctors : Array (UInt64 × RevealConstructorInfo)) : PutM Unit := do
  putTag0 ⟨ctors.size.toUInt64⟩
  for (idx, info) in ctors do
    putTag0 ⟨idx⟩
    RevealConstructorInfo.put info

private def getCtors : GetM (Array (UInt64 × RevealConstructorInfo)) := do
  let count ← getTag0Size
  let mut ctors := #[]
  for _ in [:count.toNat] do
    let idx ← getTag0Size
    let info ← RevealConstructorInfo.get
    ctors := ctors.push (idx, info)
  return ctors

-- ============================================================================
-- RevealMutConstInfo serialization
-- ============================================================================

namespace RevealMutConstInfo

def put : RevealMutConstInfo → PutM Unit
  | .defn kind safety lvls typ value => do
    putU8 0
    let mask := computeMask [kind.isSome, safety.isSome, lvls.isSome, typ.isSome, value.isSome]
    putTag0 ⟨mask⟩
    match kind with | some k => putDefKind k | none => pure ()
    match safety with | some s => putDefSafety s | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match value with | some a => Serialize.put a | none => pure ()
  | .indc isRecr refl isUnsafe lvls params indices nested typ ctors => do
    putU8 1
    let mask := computeMask [isRecr.isSome, refl.isSome, isUnsafe.isSome,
                             lvls.isSome, params.isSome, indices.isSome,
                             nested.isSome, typ.isSome, ctors.isSome]
    putTag0 ⟨mask⟩
    match isRecr with | some b => putBoolField b | none => pure ()
    match refl with | some b => putBoolField b | none => pure ()
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match params with | some n => putTag0 ⟨n⟩ | none => pure ()
    match indices with | some n => putTag0 ⟨n⟩ | none => pure ()
    match nested with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match ctors with | some c => putCtors c | none => pure ()
  | .recr k isUnsafe lvls params indices motives minors typ rules => do
    putU8 2
    let mask := computeMask [k.isSome, isUnsafe.isSome, lvls.isSome,
                             params.isSome, indices.isSome, motives.isSome,
                             minors.isSome, typ.isSome, rules.isSome]
    putTag0 ⟨mask⟩
    match k with | some b => putBoolField b | none => pure ()
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match params with | some n => putTag0 ⟨n⟩ | none => pure ()
    match indices with | some n => putTag0 ⟨n⟩ | none => pure ()
    match motives with | some n => putTag0 ⟨n⟩ | none => pure ()
    match minors with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match rules with | some r => putRules r | none => pure ()

def get : GetM RevealMutConstInfo := do
  let variant ← getU8
  let mask ← getTag0Size
  match variant with
  | 0 => do -- Defn
    let kind ← getOpt mask 1 getDefKind
    let safety ← getOpt mask 2 getDefSafety
    let lvls ← getOpt mask 4 getTag0Size
    let typ ← getOpt mask 8 Serialize.get
    let value ← getOpt mask 16 Serialize.get
    return .defn kind safety lvls typ value
  | 1 => do -- Indc
    let isRecr ← getOpt mask 1 getBoolField
    let refl ← getOpt mask 2 getBoolField
    let isUnsafe ← getOpt mask 4 getBoolField
    let lvls ← getOpt mask 8 getTag0Size
    let params ← getOpt mask 16 getTag0Size
    let indices ← getOpt mask 32 getTag0Size
    let nested ← getOpt mask 64 getTag0Size
    let typ ← getOpt mask 128 Serialize.get
    let ctors ← getOpt mask 256 getCtors
    return .indc isRecr refl isUnsafe lvls params indices nested typ ctors
  | 2 => do -- Recr
    let k ← getOpt mask 1 getBoolField
    let isUnsafe ← getOpt mask 2 getBoolField
    let lvls ← getOpt mask 4 getTag0Size
    let params ← getOpt mask 8 getTag0Size
    let indices ← getOpt mask 16 getTag0Size
    let motives ← getOpt mask 32 getTag0Size
    let minors ← getOpt mask 64 getTag0Size
    let typ ← getOpt mask 128 Serialize.get
    let rules ← getOpt mask 256 getRules
    return .recr k isUnsafe lvls params indices motives minors typ rules
  | v => throw s!"RevealMutConstInfo.get: invalid variant {v}"

end RevealMutConstInfo

-- ============================================================================
-- RevealConstantInfo serialization
-- ============================================================================

namespace RevealConstantInfo

def put : RevealConstantInfo → PutM Unit
  | .defn kind safety lvls typ value => do
    putU8 0
    let mask := computeMask [kind.isSome, safety.isSome, lvls.isSome, typ.isSome, value.isSome]
    putTag0 ⟨mask⟩
    match kind with | some k => putDefKind k | none => pure ()
    match safety with | some s => putDefSafety s | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match value with | some a => Serialize.put a | none => pure ()
  | .recr k isUnsafe lvls params indices motives minors typ rules => do
    putU8 1
    let mask := computeMask [k.isSome, isUnsafe.isSome, lvls.isSome,
                             params.isSome, indices.isSome, motives.isSome,
                             minors.isSome, typ.isSome, rules.isSome]
    putTag0 ⟨mask⟩
    match k with | some b => putBoolField b | none => pure ()
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match params with | some n => putTag0 ⟨n⟩ | none => pure ()
    match indices with | some n => putTag0 ⟨n⟩ | none => pure ()
    match motives with | some n => putTag0 ⟨n⟩ | none => pure ()
    match minors with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match rules with | some r => putRules r | none => pure ()
  | .axio isUnsafe lvls typ => do
    putU8 2
    let mask := computeMask [isUnsafe.isSome, lvls.isSome, typ.isSome]
    putTag0 ⟨mask⟩
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
  | .quot kind lvls typ => do
    putU8 3
    let mask := computeMask [kind.isSome, lvls.isSome, typ.isSome]
    putTag0 ⟨mask⟩
    match kind with | some k => putQuotKind k | none => pure ()
    match lvls with | some n => putTag0 ⟨n⟩ | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
  | .cPrj idx cidx block => do
    putU8 4
    let mask := computeMask [idx.isSome, cidx.isSome, block.isSome]
    putTag0 ⟨mask⟩
    match idx with | some n => putTag0 ⟨n⟩ | none => pure ()
    match cidx with | some n => putTag0 ⟨n⟩ | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .rPrj idx block => do
    putU8 5
    let mask := computeMask [idx.isSome, block.isSome]
    putTag0 ⟨mask⟩
    match idx with | some n => putTag0 ⟨n⟩ | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .iPrj idx block => do
    putU8 6
    let mask := computeMask [idx.isSome, block.isSome]
    putTag0 ⟨mask⟩
    match idx with | some n => putTag0 ⟨n⟩ | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .dPrj idx block => do
    putU8 7
    let mask := computeMask [idx.isSome, block.isSome]
    putTag0 ⟨mask⟩
    match idx with | some n => putTag0 ⟨n⟩ | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .muts components => do
    putU8 8
    let mask : UInt64 := if components.isEmpty then 0 else 1
    putTag0 ⟨mask⟩
    if !components.isEmpty then
      putTag0 ⟨components.size.toUInt64⟩
      for (idx, info) in components do
        putTag0 ⟨idx⟩
        RevealMutConstInfo.put info

def get : GetM RevealConstantInfo := do
  let variant ← getU8
  let mask ← getTag0Size
  match variant with
  | 0 => do -- Defn
    let kind ← getOpt mask 1 getDefKind
    let safety ← getOpt mask 2 getDefSafety
    let lvls ← getOpt mask 4 getTag0Size
    let typ ← getOpt mask 8 Serialize.get
    let value ← getOpt mask 16 Serialize.get
    return .defn kind safety lvls typ value
  | 1 => do -- Recr
    let k ← getOpt mask 1 getBoolField
    let isUnsafe ← getOpt mask 2 getBoolField
    let lvls ← getOpt mask 4 getTag0Size
    let params ← getOpt mask 8 getTag0Size
    let indices ← getOpt mask 16 getTag0Size
    let motives ← getOpt mask 32 getTag0Size
    let minors ← getOpt mask 64 getTag0Size
    let typ ← getOpt mask 128 Serialize.get
    let rules ← getOpt mask 256 getRules
    return .recr k isUnsafe lvls params indices motives minors typ rules
  | 2 => do -- Axio
    let isUnsafe ← getOpt mask 1 getBoolField
    let lvls ← getOpt mask 2 getTag0Size
    let typ ← getOpt mask 4 Serialize.get
    return .axio isUnsafe lvls typ
  | 3 => do -- Quot
    let kind ← getOpt mask 1 getQuotKind
    let lvls ← getOpt mask 2 getTag0Size
    let typ ← getOpt mask 4 Serialize.get
    return .quot kind lvls typ
  | 4 => do -- CPrj
    let idx ← getOpt mask 1 getTag0Size
    let cidx ← getOpt mask 2 getTag0Size
    let block ← getOpt mask 4 Serialize.get
    return .cPrj idx cidx block
  | 5 => do -- RPrj
    let idx ← getOpt mask 1 getTag0Size
    let block ← getOpt mask 2 Serialize.get
    return .rPrj idx block
  | 6 => do -- IPrj
    let idx ← getOpt mask 1 getTag0Size
    let block ← getOpt mask 2 Serialize.get
    return .iPrj idx block
  | 7 => do -- DPrj
    let idx ← getOpt mask 1 getTag0Size
    let block ← getOpt mask 2 Serialize.get
    return .dPrj idx block
  | 8 => do -- Muts
    let components ← if mask &&& 1 != 0 then do
      let count ← getTag0Size
      let mut comps : Array (UInt64 × RevealMutConstInfo) := #[]
      for _ in [:count.toNat] do
        let idx ← getTag0Size
        let info ← RevealMutConstInfo.get
        comps := comps.push (idx, info)
      pure comps
    else pure #[]
    return .muts components
  | v => throw s!"RevealConstantInfo.get: invalid variant {v}"

end RevealConstantInfo

-- ============================================================================
-- Claim serialization
-- ============================================================================

namespace Claim

def put : Claim → PutM Unit
  | .eval input output => do
    putTag4 ⟨0xE, 4⟩
    Serialize.put input
    Serialize.put output
  | .check value => do
    putTag4 ⟨0xE, 3⟩
    Serialize.put value
  | .reveal comm info => do
    putTag4 ⟨0xE, 6⟩
    Serialize.put comm
    RevealConstantInfo.put info

def get : GetM Claim := do
  let tag ← getTag4
  if tag.flag != 0xE then throw s!"Claim.get: expected flag 0xE, got {tag.flag}"
  match tag.size with
  | 4 => return .eval (← Serialize.get) (← Serialize.get)
  | 3 => return .check (← Serialize.get)
  | 6 => return .reveal (← Serialize.get) (← RevealConstantInfo.get)
  | n => throw s!"Claim.get: invalid variant {n}"

def ser (c : Claim) : ByteArray := runPut (put c)
def commit (c : Claim) : Address := Address.blake3 (ser c)

instance : ToString Claim where
  toString c := match c with
    | .eval i o => s!"EvalClaim({i}, {o})"
    | .check v => s!"CheckClaim({v})"
    | .reveal comm info => s!"RevealClaim({comm}, {repr info})"

end Claim

end Ix
