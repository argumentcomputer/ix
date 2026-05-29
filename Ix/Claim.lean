/-
  # Claim: ZK claim types and serialization

  Defines the claim types used in Ix's zero-knowledge proof system:
  - `EvalClaim`: asserts that a constant evaluates to a given output
  - `CheckClaim`: asserts that a constant is well-typed
  - `RevealClaim`: selectively reveals fields of a committed constant

  `RevealConstantInfo` and `RevealMutConstInfo` use bitmask-based serialization
  to encode which fields are present, enabling selective revelation without
  exposing the full constant.
-/

module
public import Ix.Ixon

public section

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

/--
A claim that can be proven.

Five variants in three families:

- **Typechecking claims** (`eval`, `check`, `checkEnv`): assert that a
  constant evaluates, a constant is well-typed, or every constant in an
  env is well-typed. Each carries `assumptions : Option Address`:
  - `none` → unconditional.
  - `some root` → conditional on every leaf in the merkle tree rooted
    at `root` being well-typed.
- **`reveal`**: selective field revelation of a committed constant.
  Carries no assumptions (orthogonal to typechecking).
- **`contains`**: structural membership claim — `const` is a leaf in
  the merkle tree rooted at `tree`. Used by aggregation to discharge
  leaves from a conditional claim's assumption set. Carries no
  assumptions.
-/
inductive Claim where
  | eval     (input output : Address) (assumptions : Option Address)
  | check    (const : Address) (assumptions : Option Address)
  | checkEnv (root : Address) (assumptions : Option Address)
  | reveal   (comm : Address) (info : RevealConstantInfo)
  | contains (tree : Address) (const : Address)
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

-- Tag4 size dispatch (mirrors src/ix/ixon/proof.rs).
-- Flag 0xE holds Env, Comm, AssumptionTree, and claims (single-byte tags).
-- Flag 0xF holds proofs (single-byte tags).

def FLAG_CLAIM : UInt8 := 0xE
def FLAG_PROOF : UInt8 := 0xF

def VARIANT_ENV              : UInt64 := 0
-- VARIANT 1 = Comm (handled in Ix.Ixon)
def VARIANT_ASSUMPTION_TREE  : UInt64 := 2
def VARIANT_EVAL_CLAIM       : UInt64 := 3
def VARIANT_CHECK_CLAIM      : UInt64 := 4
def VARIANT_CHECK_ENV_CLAIM  : UInt64 := 5
def VARIANT_REVEAL_CLAIM     : UInt64 := 6
def VARIANT_CONTAINS_CLAIM   : UInt64 := 7

def VARIANT_EVAL_PROOF       : UInt64 := 0
def VARIANT_CHECK_PROOF      : UInt64 := 1
def VARIANT_CHECK_ENV_PROOF  : UInt64 := 2
def VARIANT_REVEAL_PROOF     : UInt64 := 3
def VARIANT_CONTAINS_PROOF   : UInt64 := 4

/-- Encode an `Option Address` as `[0x00]` (none) or `[0x01][addr:32]`
    (some). Mirrors `put_opt_addr` in src/ix/ixon/proof.rs. -/
def putOptAddr : Option Address → PutM Unit
  | none => putU8 0x00
  | some a => do putU8 0x01; Serialize.put a

def getOptAddr : GetM (Option Address) := do
  let b ← getU8
  if b == 0x00 then return none
  else if b == 0x01 then return some (← Serialize.get)
  else throw s!"getOptAddr: invalid tag {b}"

def put : Claim → PutM Unit
  | .eval input output assumptions => do
    putTag4 ⟨FLAG_CLAIM, VARIANT_EVAL_CLAIM⟩
    Serialize.put input
    Serialize.put output
    putOptAddr assumptions
  | .check const assumptions => do
    putTag4 ⟨FLAG_CLAIM, VARIANT_CHECK_CLAIM⟩
    Serialize.put const
    putOptAddr assumptions
  | .checkEnv root assumptions => do
    putTag4 ⟨FLAG_CLAIM, VARIANT_CHECK_ENV_CLAIM⟩
    Serialize.put root
    putOptAddr assumptions
  | .reveal comm info => do
    putTag4 ⟨FLAG_CLAIM, VARIANT_REVEAL_CLAIM⟩
    Serialize.put comm
    RevealConstantInfo.put info
  | .contains tree const => do
    putTag4 ⟨FLAG_CLAIM, VARIANT_CONTAINS_CLAIM⟩
    Serialize.put tree
    Serialize.put const

def get : GetM Claim := do
  let tag ← getTag4
  if tag.flag != FLAG_CLAIM then
    throw s!"Claim.get: expected flag 0xE, got {tag.flag}"
  if tag.size == VARIANT_EVAL_CLAIM then
    let input ← Serialize.get
    let output ← Serialize.get
    let asm ← getOptAddr
    return .eval input output asm
  else if tag.size == VARIANT_CHECK_CLAIM then
    let const ← Serialize.get
    let asm ← getOptAddr
    return .check const asm
  else if tag.size == VARIANT_CHECK_ENV_CLAIM then
    let root ← Serialize.get
    let asm ← getOptAddr
    return .checkEnv root asm
  else if tag.size == VARIANT_REVEAL_CLAIM then
    return .reveal (← Serialize.get) (← RevealConstantInfo.get)
  else if tag.size == VARIANT_CONTAINS_CLAIM then
    return .contains (← Serialize.get) (← Serialize.get)
  else
    throw s!"Claim.get: invalid claim variant {tag.size}"

def ser (c : Claim) : ByteArray := runPut (put c)
def commit (c : Claim) : Address := Address.blake3 (ser c)

instance : ToString Claim where
  toString c := match c with
    | .eval i o asm => s!"Eval({i}, {o}, {asm})"
    | .check v asm => s!"Check({v}, {asm})"
    | .checkEnv r asm => s!"CheckEnv({r}, {asm})"
    | .reveal comm info => s!"Reveal({comm}, {repr info})"
    | .contains t c => s!"Contains({t}, {c})"

end Claim

end Ix

-- ============================================================================
-- Ixon.Proof — wraps a Claim with its opaque ZK proof bytes.
-- Mirrors `src/ix/ixon/proof.rs:173`. Lives under flag 0xF (vs claims
-- under 0xE) so the first serialized byte alone disambiguates kind.
-- ============================================================================

namespace Ixon

structure Proof where
  claim : Ix.Claim
  proof : ByteArray
  deriving Inhabited

namespace Proof

/-- The proof-variant size matching this claim, used as the Tag4 size
    field under `FLAG_PROOF = 0xF`. -/
def variantOf : Ix.Claim → UInt64
  | .eval _ _ _     => Ix.Claim.VARIANT_EVAL_PROOF
  | .check _ _      => Ix.Claim.VARIANT_CHECK_PROOF
  | .checkEnv _ _   => Ix.Claim.VARIANT_CHECK_ENV_PROOF
  | .reveal _ _     => Ix.Claim.VARIANT_REVEAL_PROOF
  | .contains _ _   => Ix.Claim.VARIANT_CONTAINS_PROOF

def put (p : Proof) : PutM Unit := do
  putTag4 ⟨Ix.Claim.FLAG_PROOF, variantOf p.claim⟩
  match p.claim with
  | .eval input output asm => do
    Serialize.put input
    Serialize.put output
    Ix.Claim.putOptAddr asm
  | .check addr asm => do
    Serialize.put addr
    Ix.Claim.putOptAddr asm
  | .checkEnv root asm => do
    Serialize.put root
    Ix.Claim.putOptAddr asm
  | .reveal comm info => do
    Serialize.put comm
    Ix.RevealConstantInfo.put info
  | .contains tree target => do
    Serialize.put tree
    Serialize.put target
  putTag0 ⟨p.proof.size.toUInt64⟩
  putBytes p.proof

def get : GetM Proof := do
  let tag ← getTag4
  if tag.flag != Ix.Claim.FLAG_PROOF then
    throw s!"Ixon.Proof.get: expected flag 0xF, got {tag.flag}"
  let claim : Ix.Claim ←
    if tag.size == Ix.Claim.VARIANT_EVAL_PROOF then do
      let input ← Serialize.get
      let output ← Serialize.get
      let asm ← Ix.Claim.getOptAddr
      pure (.eval input output asm)
    else if tag.size == Ix.Claim.VARIANT_CHECK_PROOF then do
      let addr ← Serialize.get
      let asm ← Ix.Claim.getOptAddr
      pure (.check addr asm)
    else if tag.size == Ix.Claim.VARIANT_CHECK_ENV_PROOF then do
      let root ← Serialize.get
      let asm ← Ix.Claim.getOptAddr
      pure (.checkEnv root asm)
    else if tag.size == Ix.Claim.VARIANT_REVEAL_PROOF then do
      let comm ← Serialize.get
      let info ← Ix.RevealConstantInfo.get
      pure (.reveal comm info)
    else if tag.size == Ix.Claim.VARIANT_CONTAINS_PROOF then do
      let tree ← Serialize.get
      let target ← Serialize.get
      pure (.contains tree target)
    else
      throw s!"Ixon.Proof.get: invalid proof variant {tag.size}"
  let lenTag ← getTag0
  let bytes ← getBytes lenTag.size.toNat
  pure { claim, proof := bytes }

def ser (p : Proof) : ByteArray := runPut (put p)
def de (bytes : ByteArray) : Except String Proof := runGet get bytes

end Proof

end Ixon

end
