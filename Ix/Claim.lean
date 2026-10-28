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

private def getTagN0Value : GetM UInt64 := return (← getTagN 0).value

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
  | indc (isUnsafe : Option Bool) (lvls : Option UInt64) (params : Option UInt64)
         (indices : Option UInt64) (typ : Option Address)
         (ctors : Option (Array (UInt64 × RevealConstructorInfo)))
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

/-- What a typing claim is relative to. The typing claims (`eval`, `check`,
`checkEnv`, `catalog`) state that constants are well-typed in Lean's theory
with its primitives read through a role binding, and these three fields say
which:

- `spec`: the specification digest (`Ix.SpecDigest.specDigest`), naming the
  specifications every bound role is validated against;
- `binding`: the binding hash, the BLAKE3 hash of the role table's section
  bytes (`Ixon.RoleBinding.address`), naming which constant plays each role;
- `axioms`: the axioms the claim depends on beyond the standard three
  (`propext`, `Classical.choice`, `Quot.sound`), as the canonical merkle root
  of their sorted addresses. `none` means the standard three only. No checker
  admits another axiom yet, so every claim made today carries `none`; the
  field is reserved so that admitting declared axioms later needs no second
  format change.

Typing assumptions (`assumptions` on the claims themselves) are a different
thing: constants assumed well-typed and discharged by other claims. An axiom
is never discharged by typing, so axioms are never listed there.

`bindingAssumed` says whether the claim validates the binding itself or
assumes it. A claim that validates it (validator `erased-lean-v2`) checks,
in its own proof, every role it uses against its specification. A `check`
or `checkEnv` claim may instead assume it (validator
`erased-lean-v2-assumed`). It then states its typing only *if* the role
table with hash `binding` meets the specifications `spec`, which a `binding`
claim states and aggregation discharges once. The flag is the claim's
validator byte, not a context field on the wire, and only `check` and
`checkEnv` carry it: the other typing claims always validate. -/
structure ClaimContext where
  spec : Address
  binding : Address
  axioms : Option Address
  bindingAssumed : Bool := false
  deriving BEq, Repr, Inhabited

/--
A claim that can be proven.

Eight variants in four families:

- **Typechecking claims** (`eval`, `check`, `checkEnv`, `catalog`):
  assert that a constant evaluates, a constant is well-typed, every
  constant in an env is well-typed, or every constant in a catalog is
  well-typed, relative to their `ClaimContext`. Each carries
  `assumptions : Option Address`:
  - `none` → unconditional.
  - `some root` → conditional on every leaf in the merkle tree rooted
    at `root` being well-typed.
- **`reveal`**: selective field revelation of a committed constant.
  Carries no assumptions (orthogonal to typechecking).
- **`contains`**: structural membership claim — `const` is a leaf in
  the merkle tree rooted at `tree`. Used by aggregation to discharge
  leaves from a conditional claim's assumption set. Carries no
  assumptions.
- **`resource`**: combined erased typing and resource admission, validated
  natively.
- **`binding`**: the role table with hash `binding` binds every role, and
  each bound constant meets its specification in `spec`. It discharges the
  condition of the typing claims that assume their binding
  (`ClaimContext.bindingAssumed`), once per aggregate.

`catalog` binds both `.ixc` roots. Two leaf vocabularies, never
mixed: `members` leaves are member ENV ROOTS; `content` (and
`assumptions`) leaves are CONSTANT ADDRESSES. Semantics: (1)
`tree(content)` is exactly the union of the member envs' const sets,
and (2) every constant in it typechecks modulo `assumptions`.
Verified by composition of per-piece `checkEnv` claims with set
discharge — there is deliberately no whole-catalog interpreter arm.
-/
inductive Claim where
  /-- Check the input declaration and normalize its body to the output's body.
  The output is a safe standalone definition with the same universe parameter
  count and structurally equal erased type. Assumptions concern input dependencies. -/
  | eval     (ctx : ClaimContext) (input output : Address) (assumptions : Option Address)
  | check    (ctx : ClaimContext) (const : Address) (assumptions : Option Address)
  | checkEnv (ctx : ClaimContext) (root : Address) (assumptions : Option Address)
  | reveal   (comm : Address) (info : RevealConstantInfo)
  | contains (tree : Address) (const : Address)
  | catalog  (ctx : ClaimContext) (members content : Address) (assumptions : Option Address)
  /-- Combined erased typing and resource admission of the complete addressed
  environment under the profile committed by `profile`. -/
  | resource (root profile : Address)
  /-- The role table with hash `binding` binds every role, and each bound
  constant meets its specification in the set with digest `spec`. -/
  | binding (spec binding : Address)
  deriving BEq, Repr, Inhabited

-- ============================================================================
-- RevealConstructorInfo serialization
-- ============================================================================

namespace RevealConstructorInfo

def put (info : RevealConstructorInfo) : PutM Unit := do
  let mask := computeMask [info.isUnsafe.isSome, info.lvls.isSome, info.cidx.isSome,
                           info.params.isSome, info.fields.isSome, info.typ.isSome]
  putTagN 0 0 mask
  match info.isUnsafe with | some b => putBoolField b | none => pure ()
  match info.lvls with | some n => putTagN 0 0 n | none => pure ()
  match info.cidx with | some n => putTagN 0 0 n | none => pure ()
  match info.params with | some n => putTagN 0 0 n | none => pure ()
  match info.fields with | some n => putTagN 0 0 n | none => pure ()
  match info.typ with | some a => Serialize.put a | none => pure ()

def get : GetM RevealConstructorInfo := do
  let mask := (← getTagN 0).value
  let isUnsafe ← getOpt mask 1 getBoolField
  let lvls ← getOpt mask 2 getTagN0Value
  let cidx ← getOpt mask 4 getTagN0Value
  let params ← getOpt mask 8 getTagN0Value
  let fields ← getOpt mask 16 getTagN0Value
  let typ ← getOpt mask 32 Serialize.get
  return ⟨isUnsafe, lvls, cidx, params, fields, typ⟩

end RevealConstructorInfo

-- ============================================================================
-- RevealRecursorRule serialization
-- ============================================================================

namespace RevealRecursorRule

def put (rule : RevealRecursorRule) : PutM Unit := do
  putTagN 0 0 rule.ruleIdx
  putTagN 0 0 rule.fields
  Serialize.put rule.rhs

def get : GetM RevealRecursorRule := do
  let ruleIdx ← getTagN0Value
  let fields ← getTagN0Value
  let rhs ← Serialize.get
  return ⟨ruleIdx, fields, rhs⟩

end RevealRecursorRule

-- ============================================================================
-- Array helpers
-- ============================================================================

private def putRules (rules : Array RevealRecursorRule) : PutM Unit := do
  putTagN 0 0 rules.size.toUInt64
  for rule in rules do RevealRecursorRule.put rule

private def getRules : GetM (Array RevealRecursorRule) := do
  let count ← getTagN0Value
  let mut rules := #[]
  for _ in [:count.toNat] do rules := rules.push (← RevealRecursorRule.get)
  return rules

private def putCtors (ctors : Array (UInt64 × RevealConstructorInfo)) : PutM Unit := do
  putTagN 0 0 ctors.size.toUInt64
  for (idx, info) in ctors do
    putTagN 0 0 idx
    RevealConstructorInfo.put info

private def getCtors : GetM (Array (UInt64 × RevealConstructorInfo)) := do
  let count ← getTagN0Value
  let mut ctors := #[]
  for _ in [:count.toNat] do
    let idx ← getTagN0Value
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
    putTagN 0 0 mask
    match kind with | some k => putDefKind k | none => pure ()
    match safety with | some s => putDefSafety s | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match value with | some a => Serialize.put a | none => pure ()
  | .indc isUnsafe lvls params indices typ ctors => do
    putU8 1
    let mask := computeMask [isUnsafe.isSome, lvls.isSome, params.isSome, 
      indices.isSome, typ.isSome, ctors.isSome]
    putTagN 0 0 mask
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match params with | some n => putTagN 0 0 n | none => pure ()
    match indices with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match ctors with | some c => putCtors c | none => pure ()
  | .recr k isUnsafe lvls params indices motives minors typ rules => do
    putU8 2
    let mask := computeMask [k.isSome, isUnsafe.isSome, lvls.isSome,
                             params.isSome, indices.isSome, motives.isSome,
                             minors.isSome, typ.isSome, rules.isSome]
    putTagN 0 0 mask
    match k with | some b => putBoolField b | none => pure ()
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match params with | some n => putTagN 0 0 n | none => pure ()
    match indices with | some n => putTagN 0 0 n | none => pure ()
    match motives with | some n => putTagN 0 0 n | none => pure ()
    match minors with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match rules with | some r => putRules r | none => pure ()

def get : GetM RevealMutConstInfo := do
  let variant ← getU8
  let mask ← getTagN0Value
  match variant with
  | 0 => do -- Defn
    let kind ← getOpt mask 1 getDefKind
    let safety ← getOpt mask 2 getDefSafety
    let lvls ← getOpt mask 4 getTagN0Value
    let typ ← getOpt mask 8 Serialize.get
    let value ← getOpt mask 16 Serialize.get
    return .defn kind safety lvls typ value
  | 1 => do -- Indc
    let isUnsafe ← getOpt mask 1 getBoolField
    let lvls ← getOpt mask 2 getTagN0Value
    let params ← getOpt mask 4 getTagN0Value
    let indices ← getOpt mask 8 getTagN0Value
    let typ ← getOpt mask 16 Serialize.get
    let ctors ← getOpt mask 32 getCtors
    return .indc isUnsafe lvls params indices typ ctors
  | 2 => do -- Recr
    let k ← getOpt mask 1 getBoolField
    let isUnsafe ← getOpt mask 2 getBoolField
    let lvls ← getOpt mask 4 getTagN0Value
    let params ← getOpt mask 8 getTagN0Value
    let indices ← getOpt mask 16 getTagN0Value
    let motives ← getOpt mask 32 getTagN0Value
    let minors ← getOpt mask 64 getTagN0Value
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
    putTagN 0 0 mask
    match kind with | some k => putDefKind k | none => pure ()
    match safety with | some s => putDefSafety s | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match value with | some a => Serialize.put a | none => pure ()
  | .recr k isUnsafe lvls params indices motives minors typ rules => do
    putU8 1
    let mask := computeMask [k.isSome, isUnsafe.isSome, lvls.isSome,
                             params.isSome, indices.isSome, motives.isSome,
                             minors.isSome, typ.isSome, rules.isSome]
    putTagN 0 0 mask
    match k with | some b => putBoolField b | none => pure ()
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match params with | some n => putTagN 0 0 n | none => pure ()
    match indices with | some n => putTagN 0 0 n | none => pure ()
    match motives with | some n => putTagN 0 0 n | none => pure ()
    match minors with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
    match rules with | some r => putRules r | none => pure ()
  | .axio isUnsafe lvls typ => do
    putU8 2
    let mask := computeMask [isUnsafe.isSome, lvls.isSome, typ.isSome]
    putTagN 0 0 mask
    match isUnsafe with | some b => putBoolField b | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
  | .quot kind lvls typ => do
    putU8 3
    let mask := computeMask [kind.isSome, lvls.isSome, typ.isSome]
    putTagN 0 0 mask
    match kind with | some k => putQuotKind k | none => pure ()
    match lvls with | some n => putTagN 0 0 n | none => pure ()
    match typ with | some a => Serialize.put a | none => pure ()
  | .cPrj idx cidx block => do
    putU8 4
    let mask := computeMask [idx.isSome, cidx.isSome, block.isSome]
    putTagN 0 0 mask
    match idx with | some n => putTagN 0 0 n | none => pure ()
    match cidx with | some n => putTagN 0 0 n | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .rPrj idx block => do
    putU8 5
    let mask := computeMask [idx.isSome, block.isSome]
    putTagN 0 0 mask
    match idx with | some n => putTagN 0 0 n | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .iPrj idx block => do
    putU8 6
    let mask := computeMask [idx.isSome, block.isSome]
    putTagN 0 0 mask
    match idx with | some n => putTagN 0 0 n | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .dPrj idx block => do
    putU8 7
    let mask := computeMask [idx.isSome, block.isSome]
    putTagN 0 0 mask
    match idx with | some n => putTagN 0 0 n | none => pure ()
    match block with | some a => Serialize.put a | none => pure ()
  | .muts components => do
    putU8 8
    let mask : UInt64 := if components.isEmpty then 0 else 1
    putTagN 0 0 mask
    if !components.isEmpty then
      putTagN 0 0 components.size.toUInt64
      for (idx, info) in components do
        putTagN 0 0 idx
        RevealMutConstInfo.put info

def get : GetM RevealConstantInfo := do
  let variant ← getU8
  let mask ← getTagN0Value
  match variant with
  | 0 => do -- Defn
    let kind ← getOpt mask 1 getDefKind
    let safety ← getOpt mask 2 getDefSafety
    let lvls ← getOpt mask 4 getTagN0Value
    let typ ← getOpt mask 8 Serialize.get
    let value ← getOpt mask 16 Serialize.get
    return .defn kind safety lvls typ value
  | 1 => do -- Recr
    let k ← getOpt mask 1 getBoolField
    let isUnsafe ← getOpt mask 2 getBoolField
    let lvls ← getOpt mask 4 getTagN0Value
    let params ← getOpt mask 8 getTagN0Value
    let indices ← getOpt mask 16 getTagN0Value
    let motives ← getOpt mask 32 getTagN0Value
    let minors ← getOpt mask 64 getTagN0Value
    let typ ← getOpt mask 128 Serialize.get
    let rules ← getOpt mask 256 getRules
    return .recr k isUnsafe lvls params indices motives minors typ rules
  | 2 => do -- Axio
    let isUnsafe ← getOpt mask 1 getBoolField
    let lvls ← getOpt mask 2 getTagN0Value
    let typ ← getOpt mask 4 Serialize.get
    return .axio isUnsafe lvls typ
  | 3 => do -- Quot
    let kind ← getOpt mask 1 getQuotKind
    let lvls ← getOpt mask 2 getTagN0Value
    let typ ← getOpt mask 4 Serialize.get
    return .quot kind lvls typ
  | 4 => do -- CPrj
    let idx ← getOpt mask 1 getTagN0Value
    let cidx ← getOpt mask 2 getTagN0Value
    let block ← getOpt mask 4 Serialize.get
    return .cPrj idx cidx block
  | 5 => do -- RPrj
    let idx ← getOpt mask 1 getTagN0Value
    let block ← getOpt mask 2 Serialize.get
    return .rPrj idx block
  | 6 => do -- IPrj
    let idx ← getOpt mask 1 getTagN0Value
    let block ← getOpt mask 2 Serialize.get
    return .iPrj idx block
  | 7 => do -- DPrj
    let idx ← getOpt mask 1 getTagN0Value
    let block ← getOpt mask 2 Serialize.get
    return .dPrj idx block
  | 8 => do -- Muts
    let components ← if mask &&& 1 != 0 then do
      let count ← getTagN0Value
      let mut comps : Array (UInt64 × RevealMutConstInfo) := #[]
      for _ in [:count.toNat] do
        let idx ← getTagN0Value
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

-- TagN (`f = 4`) value dispatch (mirrors crates/ixon/src/proof.rs).
-- Flag 0xE holds Comm, AssumptionTree, and claims. Variants 0–7 are in
-- rung 1, the single bytes 0xE0–0xE7; from 8 on the header is two bytes,
-- so catalog is `E8 00`, resource `E8 01` and binding `E8 02` on the
-- wire. The `.ixe` header also uses flag 0xE, with the format version as the value
-- (`0xE4` for version 4, the same byte as the check claim tag).
-- Flag 0xF holds proofs (single-byte tags 0xF0–0xF7).

def FLAG_CLAIM : UInt8 := 0xE
def FLAG_PROOF : UInt8 := 0xF

-- VARIANT 1 = Comm (handled in Ix.Ixon)
def VARIANT_ASSUMPTION_TREE  : UInt64 := 2
def VARIANT_EVAL_CLAIM       : UInt64 := 3
def VARIANT_CHECK_CLAIM      : UInt64 := 4
def VARIANT_CHECK_ENV_CLAIM  : UInt64 := 5
def VARIANT_REVEAL_CLAIM     : UInt64 := 6
def VARIANT_CONTAINS_CLAIM   : UInt64 := 7
def VARIANT_CATALOG_CLAIM    : UInt64 := 8
def VARIANT_RESOURCE_CLAIM   : UInt64 := 9
def VARIANT_BINDING_CLAIM    : UInt64 := 10

def VARIANT_EVAL_PROOF       : UInt64 := 0
def VARIANT_CHECK_PROOF      : UInt64 := 1
def VARIANT_CHECK_ENV_PROOF  : UInt64 := 2
def VARIANT_REVEAL_PROOF     : UInt64 := 3
def VARIANT_CONTAINS_PROOF   : UInt64 := 4
def VARIANT_CATALOG_PROOF    : UInt64 := 5
def VARIANT_RESOURCE_PROOF   : UInt64 := 6
def VARIANT_BINDING_PROOF    : UInt64 := 7

/-- Encode an `Option Address` as `[0x00]` (none) or `[0x01][addr:32]`
    (some). Mirrors `put_opt_addr` in crates/ixon/src/proof.rs. -/
def putOptAddr : Option Address → PutM Unit
  | none => putU8 0x00
  | some a => do putU8 0x01; Serialize.put a

def getOptAddr : GetM (Option Address) := do
  let b ← getU8
  if b == 0x00 then return none
  else if b == 0x01 then return some (← Serialize.get)
  else throw s!"getOptAddr: invalid tag {b}"

/-- The validator identities a claim's scope names, after the object format:

- `0`, structural-v1: `reveal` and `contains`, which read bytes only;
- `1`, erased-lean-v1: retired. It named typing claims whose primitives were
  recognized by fixed addresses and which admitted any axiom; new readers
  refuse it rather than read such a claim as a newer one;
- `2`, resource-v1: `resource`;
- `3`, erased-lean-v2: the typing claims, relative to their `ClaimContext`
  (Lean's theory over the standard axioms, primitives read through the
  committed role binding and validated against the committed
  specifications), and the `binding` claim;
- `4`, erased-lean-v2-assumed: a `check` or `checkEnv` claim that assumes
  its binding meets the specifications instead of validating it
  (`ClaimContext.bindingAssumed`); its typing holds if the `binding` claim
  for its context does. -/
def VALIDATOR_STRUCTURAL : UInt8 := 0
def VALIDATOR_ERASED_LEAN_RETIRED : UInt8 := 1
def VALIDATOR_RESOURCE : UInt8 := 2
def VALIDATOR_ERASED_LEAN : UInt8 := 3
def VALIDATOR_ERASED_LEAN_ASSUMED : UInt8 := 4

def validatorForVariant (variant : UInt64) : UInt8 :=
  if variant == VARIANT_REVEAL_CLAIM || variant == VARIANT_CONTAINS_CLAIM then
    VALIDATOR_STRUCTURAL
  else if variant == VARIANT_RESOURCE_CLAIM then VALIDATOR_RESOURCE
  else VALIDATOR_ERASED_LEAN

/-- Whether claims of variant `variant` may assume their binding: `check`
    and `checkEnv`. -/
def variantMayAssume (variant : UInt64) : Bool :=
  variant == VARIANT_CHECK_CLAIM || variant == VARIANT_CHECK_ENV_CLAIM

def variantOf : Claim → UInt64
  | .eval .. => VARIANT_EVAL_CLAIM
  | .check .. => VARIANT_CHECK_CLAIM
  | .checkEnv .. => VARIANT_CHECK_ENV_CLAIM
  | .reveal .. => VARIANT_REVEAL_CLAIM
  | .contains .. => VARIANT_CONTAINS_CLAIM
  | .catalog .. => VARIANT_CATALOG_CLAIM
  | .resource .. => VARIANT_RESOURCE_CLAIM
  | .binding .. => VARIANT_BINDING_CLAIM

/-- The validator a claim's scope names: its variant's, or
    erased-lean-v2-assumed for a `check` or `checkEnv` claim that assumes
    its binding. Only those two carry the flag on the wire; the other
    typing claims always validate. -/
def validatorOf : Claim → UInt8
  | .check ctx .. | .checkEnv ctx .. =>
    if ctx.bindingAssumed then VALIDATOR_ERASED_LEAN_ASSUMED else VALIDATOR_ERASED_LEAN
  | c => validatorForVariant (variantOf c)

def putScope (validator : UInt8) : PutM Unit := do
  putU8 Ixon.Env.OBJECT_FORMAT
  putU8 validator

/-- Read the scope of a claim of variant `variant` and return whether it
    assumes its binding. -/
def getScope (variant : UInt64) : GetM Bool := do
  let validator := validatorForVariant variant
  let format ← getU8
  unless format == Ixon.Env.OBJECT_FORMAT do
    throw s!"claim: unsupported object format {format}, expected \
      {Ixon.Env.OBJECT_FORMAT} — regenerate the claim"
  let found ← getU8
  if found == validator then return false
  if found == VALIDATOR_ERASED_LEAN_ASSUMED && variantMayAssume variant then return true
  if validator == VALIDATOR_ERASED_LEAN && found == VALIDATOR_ERASED_LEAN_RETIRED then
    throw "claim: validator erased-lean-v1 is retired — regenerate the claim"
  throw "claim: wrong validator identity"

def putContext (ctx : ClaimContext) : PutM Unit := do
  Serialize.put ctx.spec
  Serialize.put ctx.binding
  putOptAddr ctx.axioms

def getContext : GetM ClaimContext := do
  let spec ← Serialize.get
  let binding ← Serialize.get
  let axioms ← getOptAddr
  return { spec, binding, axioms }

/-- The bytes after the scope, shared by claims and proofs. -/
def putPayload : Claim → PutM Unit
  | .eval ctx input output assumptions => do
    putContext ctx
    Serialize.put input
    Serialize.put output
    putOptAddr assumptions
  | .check ctx const assumptions => do
    putContext ctx
    Serialize.put const
    putOptAddr assumptions
  | .checkEnv ctx root assumptions => do
    putContext ctx
    Serialize.put root
    putOptAddr assumptions
  | .reveal comm info => do
    Serialize.put comm
    RevealConstantInfo.put info
  | .contains tree const => do
    Serialize.put tree
    Serialize.put const
  | .catalog ctx members content assumptions => do
    -- A two-byte claim tag: `E8 00` on the wire.
    putContext ctx
    Serialize.put members
    Serialize.put content
    putOptAddr assumptions
  | .resource root profile => do
    Serialize.put root
    Serialize.put profile
  | .binding spec bound => do
    -- A two-byte claim tag: `E8 02` on the wire.
    Serialize.put spec
    Serialize.put bound

/-- Read the bytes after the scope of the claim variant `variant`; `assumed`
    is what the scope said (`getScope`). -/
def getPayload (variant : UInt64) (assumed : Bool := false) : GetM Claim := do
  if variant == VARIANT_EVAL_CLAIM then
    let ctx ← getContext
    let input ← Serialize.get
    let output ← Serialize.get
    let asm ← getOptAddr
    return .eval ctx input output asm
  else if variant == VARIANT_CHECK_CLAIM then
    let ctx ← getContext
    let const ← Serialize.get
    let asm ← getOptAddr
    return .check { ctx with bindingAssumed := assumed } const asm
  else if variant == VARIANT_CHECK_ENV_CLAIM then
    let ctx ← getContext
    let root ← Serialize.get
    let asm ← getOptAddr
    return .checkEnv { ctx with bindingAssumed := assumed } root asm
  else if variant == VARIANT_REVEAL_CLAIM then
    return .reveal (← Serialize.get) (← RevealConstantInfo.get)
  else if variant == VARIANT_CONTAINS_CLAIM then
    return .contains (← Serialize.get) (← Serialize.get)
  else if variant == VARIANT_CATALOG_CLAIM then
    let ctx ← getContext
    let members ← Serialize.get
    let content ← Serialize.get
    let asm ← getOptAddr
    return .catalog ctx members content asm
  else if variant == VARIANT_RESOURCE_CLAIM then
    return .resource (← Serialize.get) (← Serialize.get)
  else if variant == VARIANT_BINDING_CLAIM then
    return .binding (← Serialize.get) (← Serialize.get)
  else
    throw s!"Claim.get: invalid claim variant {variant}"

def put (claim : Claim) : PutM Unit := do
  putTagN 4 FLAG_CLAIM (variantOf claim)
  putScope (validatorOf claim)
  putPayload claim

def get : GetM Claim := do
  let tag ← getTagN 4
  if tag.flag != FLAG_CLAIM then
    throw s!"Claim.get: expected flag 0xE, got {tag.flag}"
  let assumed ← getScope tag.value
  getPayload tag.value assumed

def ser (c : Claim) : ByteArray := runPut (put c)
def de (bytes : ByteArray) : Except String Claim := runGetExact get bytes
def commit (c : Claim) : Address := Address.blake3 (ser c)

/-- The claim assuming its binding meets the specifications: `check` and
    `checkEnv` with validator 4; any other claim unchanged, since only those
    two may assume it. -/
def assumingBinding : Claim → Claim
  | .check ctx c asm => .check { ctx with bindingAssumed := true } c asm
  | .checkEnv ctx r asm => .checkEnv { ctx with bindingAssumed := true } r asm
  | c => c

/-- The claim's context, for the typing claims. -/
def context? : Claim → Option ClaimContext
  | .eval ctx .. | .check ctx .. | .checkEnv ctx .. | .catalog ctx .. => some ctx
  | _ => none

instance : ToString ClaimContext where
  toString ctx :=
    let base := s!"spec {ctx.spec}, binding {ctx.binding}, axioms {ctx.axioms}"
    if ctx.bindingAssumed then s!"{base}, assuming the binding meets the spec" else base

instance : ToString Claim where
  toString c := match c with
    | .eval ctx i o asm => s!"Eval({i}, {o}, {asm}; {ctx})"
    | .check ctx v asm => s!"Check({v}, {asm}; {ctx})"
    | .checkEnv ctx r asm => s!"CheckEnv({r}, {asm}; {ctx})"
    | .reveal comm info => s!"Reveal({comm}, {repr info})"
    | .contains t c => s!"Contains({t}, {c})"
    | .catalog ctx m c asm => s!"Catalog({m}, {c}, {asm}; {ctx})"
    | .resource root profile => s!"Resource({root}, {profile})"
    | .binding spec bound => s!"Binding({bound} meets spec {spec})"

end Claim

end Ix

-- ============================================================================
-- Ixon.Proof — wraps a Claim with its opaque ZK proof bytes.
-- Mirrors `Proof` in `crates/ixon/src/proof.rs`. Lives under flag 0xF (vs claims
-- under 0xE) so the first serialized byte alone disambiguates kind.
-- ============================================================================

namespace Ixon

structure Proof where
  claim : Ix.Claim
  proof : ByteArray
  deriving Inhabited

namespace Proof

/-- The proof variant matching this claim, used as the TagN (`f = 4`) value
    field under `FLAG_PROOF = 0xF`. -/
def variantOf : Ix.Claim → UInt64
  | .eval ..     => Ix.Claim.VARIANT_EVAL_PROOF
  | .check ..    => Ix.Claim.VARIANT_CHECK_PROOF
  | .checkEnv .. => Ix.Claim.VARIANT_CHECK_ENV_PROOF
  | .reveal ..   => Ix.Claim.VARIANT_REVEAL_PROOF
  | .contains .. => Ix.Claim.VARIANT_CONTAINS_PROOF
  | .catalog ..  => Ix.Claim.VARIANT_CATALOG_PROOF
  | .resource .. => Ix.Claim.VARIANT_RESOURCE_PROOF
  | .binding ..  => Ix.Claim.VARIANT_BINDING_PROOF

def put (p : Proof) : PutM Unit := do
  putTagN 4 Ix.Claim.FLAG_PROOF (variantOf p.claim)
  Ix.Claim.putScope (Ix.Claim.validatorOf p.claim)
  Ix.Claim.putPayload p.claim
  putTagN 0 0 p.proof.size.toUInt64
  putBytes p.proof

def get : GetM Proof := do
  let tag ← getTagN 4
  if tag.flag != Ix.Claim.FLAG_PROOF then
    throw s!"Ixon.Proof.get: expected flag 0xF, got {tag.flag}"
  if tag.value > Ix.Claim.VARIANT_BINDING_PROOF then
    throw s!"Ixon.Proof.get: invalid proof variant {tag.value}"
  let assumed ← Ix.Claim.getScope (tag.value + 3)
  let claim ← Ix.Claim.getPayload (tag.value + 3) assumed
  let lenTag ← getTagN 0
  let bytes ← getBytes lenTag.value.toNat
  pure { claim, proof := bytes }

def ser (p : Proof) : ByteArray := runPut (put p)
def de (bytes : ByteArray) : Except String Proof := runGetExact get bytes

end Proof

end Ixon

end
