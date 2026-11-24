module
public import Ix.DynamicLink.Spec
public import Ix.Ixon

/-! # Dynamic Circuit Linking Wire Codec (`Ix.DynamicLink.Codec`)

Canonical binary codecs for Workstream 5 using the unallocated `0xE`/`0xF` tag
and validator space documented in `Ix/Claim.lean:586-612`:

| Space | Value (bytes) | Allocation |
|---|---|---|
| `0xE` | 21 (`E8 0D`) | `DynamicLinkStatement` (Tier 1 Shape 17 output) |
| `0xE` | 22 (`E8 0E`) | `EvalAssumption` leaf preimage (Tier 2 Merkle leaf) |
| `0xE` | 23 (`E8 0F`) | `LinkedCircuitEntry` leaf preimage (Mode 3a Merkle leaf) |
| `0xF` | 9 (`F8 01`) | `DynamicLinkProof` envelope |
| validator | `10` | `erased-lean-v2-eval-assumed` (`Check`/`CheckEnv` + `evalAssumptions`) |
| validator | `11` | `erased-lean-v2-binding-eval-assumed` (`Check`/`CheckEnv` + assumed binding + `evalAssumptions`) |
| validator | `12` | `erased-lean-v2-linked` (`Check`/`CheckEnv` + optional `evalAssumptions` + `linkedCircuits`) |
| validator | `13` | `erased-lean-v2-binding-linked` (`Check`/`CheckEnv` + assumed binding + optional `evalAssumptions` + `linkedCircuits`) |

Every byte sequence produced by `serDynamicLink`, `serEvalAssumption`,
`serLinkedCircuitEntry`, `serEvalAssumedClaim`, or `serLinkedClaim` is strictly
rejected by `Ix.Claim.de`, preserving the exact domain of frozen
`IxVM.Consistency.InScopeTyping` and `CircuitComposed`.
-/

@[expose] public section

namespace Ix.DynamicLink

open Ixon

def VARIANT_DYNAMIC_LINK       : UInt64 := 21  -- wire header: 0xE8 0x0D
def VARIANT_EVAL_ASSUMPTION    : UInt64 := 22  -- wire header: 0xE8 0x0E
def VARIANT_LINKED_CIRCUIT     : UInt64 := 23  -- wire header: 0xE8 0x0F
def VARIANT_DYNAMIC_LINK_PROOF : UInt64 := 9   -- wire header: 0xF8 0x01

def VALIDATOR_EVAL_ASSUMED         : UInt8 := 10
def VALIDATOR_BINDING_EVAL_ASSUMED : UInt8 := 11
def VALIDATOR_LINKED               : UInt8 := 12
def VALIDATOR_BINDING_LINKED       : UInt8 := 13

def putU32LE (n : UInt32) : PutM Unit := do
  putU8 (UInt8.ofNat (n.toNat % 256))
  putU8 (UInt8.ofNat ((n.toNat >>> 8) % 256))
  putU8 (UInt8.ofNat ((n.toNat >>> 16) % 256))
  putU8 (UInt8.ofNat ((n.toNat >>> 24) % 256))

def getU32LE : GetM UInt32 := do
  let b0 ← getU8
  let b1 ← getU8
  let b2 ← getU8
  let b3 ← getU8
  pure (UInt32.ofNat (b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)))

def putU64LE (n : UInt64) : PutM Unit := do
  let lo := UInt32.ofNat (n.toNat % 4294967296)
  let hi := UInt32.ofNat (n.toNat >>> 32)
  putU32LE lo
  putU32LE hi

def getU64LE : GetM UInt64 := do
  let lo ← getU32LE
  let hi ← getU32LE
  pure (UInt64.ofNat (lo.toNat + (hi.toNat <<< 32)))

def putU64Array (xs : Array UInt64) : PutM Unit := do
  putU32LE (UInt32.ofNat xs.size)
  for x in xs do
    putU64LE x

def getU64Array : GetM (Array UInt64) := do
  let n ← getU32LE
  let st ← get
  if n.toNat * 8 > st.bytes.size - st.idx then
    throw "getU64Array: length exceeds remaining bytes"
  let mut out := Array.mkEmpty n.toNat
  for _ in [0:n.toNat] do
    out := out.push (← getU64LE)
  pure out

def putCircuitRef (c : CircuitRef) : PutM Unit := do
  Serialize.put c.vkDigest
  putU64LE c.entryIdx

def getCircuitRef : GetM CircuitRef := do
  let vkDigest ← Serialize.get
  let entryIdx ← getU64LE
  pure { vkDigest, entryIdx }

def putOptCircuitRef : Option CircuitRef → PutM Unit
  | none => putU8 0x00
  | some c => do putU8 0x01; putCircuitRef c

def getOptCircuitRef : GetM (Option CircuitRef) := do
  let tag ← getU8
  if tag == 0x00 then pure none
  else if tag == 0x01 then some <$> getCircuitRef
  else throw s!"getOptCircuitRef: invalid tag {tag}"

def putOptBridge : Option BridgeBinding → PutM Unit
  | none => putU8 0x00
  | some b => do
    putU8 0x01
    Serialize.put b.spec
    Serialize.put b.binding
    Serialize.put b.targetConst
    putU64LE b.codec.toUInt64
    Serialize.put b.certConst

def getOptBridge : GetM (Option BridgeBinding) := do
  let tag ← getU8
  if tag == 0x00 then pure none
  else if tag == 0x01 then do
    let spec ← Serialize.get
    let binding ← Serialize.get
    let targetConst ← Serialize.get
    let codec ← CodecTag.ofUInt64 <$> getU64LE
    let certConst ← Serialize.get
    pure (some { spec, binding, targetConst, codec, certConst })
  else throw s!"getOptBridge: invalid tag {tag}"

/-! ## Tier 1: `DynamicLinkStatement` (`0xE8 0x0D`) -/

def putDynamicLink (s : DynamicLinkStatement) : PutM Unit := do
  putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_DYNAMIC_LINK
  putCircuitRef s.circuit
  putU64Array s.pubInputs
  putU64Array s.pubOutputs
  putOptBridge s.bridge?

def getDynamicLink : GetM DynamicLinkStatement := do
  let tag ← getTagN 4
  unless tag.flag == Ix.Claim.FLAG_CLAIM && tag.value == VARIANT_DYNAMIC_LINK do
    throw s!"getDynamicLink: expected tag (0xE, 21), got ({tag.flag}, {tag.value})"
  let circuit ← getCircuitRef
  let pubInputs ← getU64Array
  let pubOutputs ← getU64Array
  let bridge? ← getOptBridge
  let st ← get
  unless st.idx == st.bytes.size do
    throw s!"getDynamicLink: trailing bytes ({st.bytes.size - st.idx})"
  pure { circuit, pubInputs, pubOutputs, bridge? }

def serDynamicLink (s : DynamicLinkStatement) : ByteArray :=
  runPut (putDynamicLink s)

def deDynamicLink (bytes : ByteArray) : Except String DynamicLinkStatement :=
  runGet getDynamicLink bytes

/-- Content address of a `DynamicLinkStatement` (BLAKE3 digest of its wire bytes). -/
def DynamicLinkStatement.address (s : DynamicLinkStatement) : Address :=
  Address.blake3Pure (serDynamicLink s)

/-! ## Tier 2: `EvalAssumption` leaf (`0xE8 0x0E`) -/

def putEvalAssumption (e : EvalAssumption) : PutM Unit := do
  putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_EVAL_ASSUMPTION
  Serialize.put e.lhs
  Serialize.put e.rhs
  Serialize.put e.typ
  putOptCircuitRef e.circuit?

def getEvalAssumption : GetM EvalAssumption := do
  let tag ← getTagN 4
  unless tag.flag == Ix.Claim.FLAG_CLAIM && tag.value == VARIANT_EVAL_ASSUMPTION do
    throw s!"getEvalAssumption: expected tag (0xE, 22), got ({tag.flag}, {tag.value})"
  let lhs ← Serialize.get
  let rhs ← Serialize.get
  let typ ← Serialize.get
  let circuit? ← getOptCircuitRef
  let st ← get
  unless st.idx == st.bytes.size do
    throw s!"getEvalAssumption: trailing bytes ({st.bytes.size - st.idx})"
  pure { lhs, rhs, typ, circuit? }

def serEvalAssumption (e : EvalAssumption) : ByteArray :=
  runPut (putEvalAssumption e)

def deEvalAssumption (bytes : ByteArray) : Except String EvalAssumption :=
  runGet getEvalAssumption bytes

/-- Content address of an `EvalAssumption` leaf in an `evalAssumptions` Merkle tree. -/
def EvalAssumption.address (e : EvalAssumption) : Address :=
  Address.blake3Pure (serEvalAssumption e)

/-! ## Tier 2: `EvalAssumedClaim` (validators `10` / `11`) -/

def EvalAssumedClaim.validator (c : EvalAssumedClaim) : UInt8 :=
  if c.ctx.bindingAssumed then VALIDATOR_BINDING_EVAL_ASSUMED else VALIDATOR_EVAL_ASSUMED

def putEvalAssumedClaim (c : EvalAssumedClaim) : PutM Unit := do
  let variant := match c.kind with
    | .check _ => Ix.Claim.VARIANT_CHECK_CLAIM
    | .checkEnv _ => Ix.Claim.VARIANT_CHECK_ENV_CLAIM
  putTagN 4 Ix.Claim.FLAG_CLAIM variant
  Ix.Claim.putScope c.validator
  Serialize.put c.ctx.spec
  Serialize.put c.ctx.binding
  Ix.Claim.putOptAddr c.ctx.axioms
  match c.kind with
  | .check const => Serialize.put const
  | .checkEnv root => Serialize.put root
  Ix.Claim.putOptAddr c.assumptions
  Serialize.put c.evalAssumptions

def getEvalAssumedClaim : GetM EvalAssumedClaim := do
  let tag ← getTagN 4
  unless tag.flag == Ix.Claim.FLAG_CLAIM &&
      (tag.value == Ix.Claim.VARIANT_CHECK_CLAIM || tag.value == Ix.Claim.VARIANT_CHECK_ENV_CLAIM) do
    throw s!"getEvalAssumedClaim: expected check/checkEnv tag, got ({tag.flag}, {tag.value})"
  let format ← getU8
  unless format == Ixon.Env.OBJECT_FORMAT do
    throw s!"getEvalAssumedClaim: unsupported object format {format}"
  let validator ← getU8
  let bindingAssumed ←
    if validator == VALIDATOR_EVAL_ASSUMED then pure false
    else if validator == VALIDATOR_BINDING_EVAL_ASSUMED then pure true
    else throw s!"getEvalAssumedClaim: expected validator 10 or 11, got {validator}"
  let spec ← Serialize.get
  let binding ← Serialize.get
  let axioms ← Ix.Claim.getOptAddr
  let kind ←
    if tag.value == Ix.Claim.VARIANT_CHECK_CLAIM then
      EvalAssumedKind.check <$> Serialize.get
    else
      EvalAssumedKind.checkEnv <$> Serialize.get
  let assumptions ← Ix.Claim.getOptAddr
  let evalAssumptions ← Serialize.get
  let st ← get
  unless st.idx == st.bytes.size do
    throw s!"getEvalAssumedClaim: trailing bytes ({st.bytes.size - st.idx})"
  let ctx : Ix.ClaimContext := { spec, binding, axioms, bindingAssumed }
  pure { ctx, kind, assumptions, evalAssumptions }

def serEvalAssumedClaim (c : EvalAssumedClaim) : ByteArray :=
  runPut (putEvalAssumedClaim c)

def deEvalAssumedClaim (bytes : ByteArray) : Except String EvalAssumedClaim :=
  runGet getEvalAssumedClaim bytes

/-- When all `evalAssumptions` have been discharged EXCLUSIVELY by Mode 2 (`@Eq` `Claim.check`,
zero external linked circuits), convert an `EvalAssumedClaim` (validator `10`/`11`) to its
unconditional standard `Ix.Claim` (validator `3`/`4`). -/
def EvalAssumedClaim.dischargeAll (c : EvalAssumedClaim) : Ix.Claim :=
  match c.kind with
  | .check const => .check c.ctx const c.assumptions
  | .checkEnv root => .checkEnv c.ctx root c.assumptions

/-- Transition an `EvalAssumedClaim` (validator `10`/`11`) into a `LinkedClaim`
(validator `12`/`13`) upon a Shape 18 Mode 3a discharge via an external `DynamicLinkStatement`. -/
def EvalAssumedClaim.withLinkedCircuit (c : EvalAssumedClaim)
    (evalAfter : Option Address) (linkedRoot : Address) : LinkedClaim :=
  { ctx := c.ctx
    kind := c.kind
    assumptions := c.assumptions
    evalAssumptions := evalAfter
    linkedCircuits := linkedRoot }

/-! ## Mode 3a: `LinkedCircuitEntry` leaf (`0xE8 0x0F`) -/

def putLinkedCircuitEntry (e : LinkedCircuitEntry) : PutM Unit := do
  putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_LINKED_CIRCUIT
  Serialize.put e.vkDigest
  putU64LE e.entryIdx
  putU64LE e.codec.toUInt64
  Serialize.put e.targetConst
  Serialize.put e.certConst
  Serialize.put e.evalType
  Serialize.put e.spec
  Serialize.put e.binding

def getLinkedCircuitEntry : GetM LinkedCircuitEntry := do
  let tag ← getTagN 4
  unless tag.flag == Ix.Claim.FLAG_CLAIM && tag.value == VARIANT_LINKED_CIRCUIT do
    throw s!"getLinkedCircuitEntry: expected tag (0xE, 23), got ({tag.flag}, {tag.value})"
  let vkDigest ← Serialize.get
  let entryIdx ← getU64LE
  let codec ← CodecTag.ofUInt64 <$> getU64LE
  let targetConst ← Serialize.get
  let certConst ← Serialize.get
  let evalType ← Serialize.get
  let spec ← Serialize.get
  let binding ← Serialize.get
  let st ← get
  unless st.idx == st.bytes.size do
    throw s!"getLinkedCircuitEntry: trailing bytes ({st.bytes.size - st.idx})"
  pure { vkDigest, entryIdx, codec, targetConst, certConst, evalType, spec, binding }

def serLinkedCircuitEntry (e : LinkedCircuitEntry) : ByteArray :=
  runPut (putLinkedCircuitEntry e)

def deLinkedCircuitEntry (bytes : ByteArray) : Except String LinkedCircuitEntry :=
  runGet getLinkedCircuitEntry bytes

/-- Content address of a `LinkedCircuitEntry` leaf in a `linkedCircuits` Merkle tree. -/
def LinkedCircuitEntry.address (e : LinkedCircuitEntry) : Address :=
  Address.blake3Pure (serLinkedCircuitEntry e)

/-! ## Mode 3a: `LinkedClaim` (validators `12` / `13`) -/

def LinkedClaim.validator (c : LinkedClaim) : UInt8 :=
  if c.ctx.bindingAssumed then VALIDATOR_BINDING_LINKED else VALIDATOR_LINKED

def putLinkedClaim (c : LinkedClaim) : PutM Unit := do
  let variant := match c.kind with
    | .check _ => Ix.Claim.VARIANT_CHECK_CLAIM
    | .checkEnv _ => Ix.Claim.VARIANT_CHECK_ENV_CLAIM
  putTagN 4 Ix.Claim.FLAG_CLAIM variant
  Ix.Claim.putScope c.validator
  Serialize.put c.ctx.spec
  Serialize.put c.ctx.binding
  Ix.Claim.putOptAddr c.ctx.axioms
  match c.kind with
  | .check const => Serialize.put const
  | .checkEnv root => Serialize.put root
  Ix.Claim.putOptAddr c.assumptions
  Ix.Claim.putOptAddr c.evalAssumptions
  Serialize.put c.linkedCircuits

def getLinkedClaim : GetM LinkedClaim := do
  let tag ← getTagN 4
  unless tag.flag == Ix.Claim.FLAG_CLAIM &&
      (tag.value == Ix.Claim.VARIANT_CHECK_CLAIM || tag.value == Ix.Claim.VARIANT_CHECK_ENV_CLAIM) do
    throw s!"getLinkedClaim: expected check/checkEnv tag, got ({tag.flag}, {tag.value})"
  let format ← getU8
  unless format == Ixon.Env.OBJECT_FORMAT do
    throw s!"getLinkedClaim: unsupported object format {format}"
  let validator ← getU8
  let bindingAssumed ←
    if validator == VALIDATOR_LINKED then pure false
    else if validator == VALIDATOR_BINDING_LINKED then pure true
    else throw s!"getLinkedClaim: expected validator 12 or 13, got {validator}"
  let spec ← Serialize.get
  let binding ← Serialize.get
  let axioms ← Ix.Claim.getOptAddr
  let kind ←
    if tag.value == Ix.Claim.VARIANT_CHECK_CLAIM then
      EvalAssumedKind.check <$> Serialize.get
    else
      EvalAssumedKind.checkEnv <$> Serialize.get
  let assumptions ← Ix.Claim.getOptAddr
  let evalAssumptions ← Ix.Claim.getOptAddr
  let linkedCircuits ← Serialize.get
  let st ← get
  unless st.idx == st.bytes.size do
    throw s!"getLinkedClaim: trailing bytes ({st.bytes.size - st.idx})"
  let ctx : Ix.ClaimContext := { spec, binding, axioms, bindingAssumed }
  pure { ctx, kind, assumptions, evalAssumptions, linkedCircuits }

def serLinkedClaim (c : LinkedClaim) : ByteArray :=
  runPut (putLinkedClaim c)

def deLinkedClaim (bytes : ByteArray) : Except String LinkedClaim :=
  runGet getLinkedClaim bytes

end Ix.DynamicLink
