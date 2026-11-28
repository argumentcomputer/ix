module
public import Ix.Claim

/-! # Dynamic Circuit Linking Specification (`Ix.DynamicLink`)

Defines the content-addressed interface for IxVM-bootstrapped dynamic circuit
linking (Workstream 5):

1. **Tier 1 (`ix_aggr` Shape 17 — `aggr_dynamic_link`, 0 IxVM VK change):**
   A `DynamicLinkStatement` binds an arbitrary Multi-STARK accelerator circuit
   `C` (identified by `vkDigest = blake3(vk_C)` and `entryIdx`) to its verified
   public inputs/outputs `(pubInputs, pubOutputs)` and an optional IxVM-verified
   soundness bridge theorem `T_C` (`BridgeBinding`).
2. **Tier 2 (`IxVM` `evalAssumptions` + `ix_aggr` Shape 18 — `aggr_discharge_eval`):**
   An `EvalAssumption` leaf asserts closed equality `lhs = rhs : typ` (optionally
   backed by a linked accelerator circuit `C`), carried in a canonical
   `AssumptionTree` under validators `10`/`11` (strictly disjoint from `Ix.Claim.de`'s
   validators `0, 3, 4, 5` so frozen `InScopeTyping` and `CircuitComposed` stay
   untouched and sound).
-/

@[expose] public section

namespace Ix.DynamicLink

/-- Cryptographic identity of an external Multi-STARK accelerator circuit `C`:
its verifying-key BLAKE3 digest `h_C = blake3(vk_C)` and callable entrypoint index. -/
structure CircuitRef where
  vkDigest : Address
  entryIdx : UInt64
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Canonical codec tag specifying how public field words encode Ixon/byte
inputs and outputs for a linked circuit. Custom tags are statically restricted
to `id ≥ 3` so `.custom` can never alias `.rawWords` (`0`), `.ixonAddrPair` (`1`),
or `.ixonAddrSingle` (`2`). -/
inductive CodecTag where
  /-- Raw Goldilocks `UInt64` words (pass-through). -/
  | rawWords
  /-- Two 32-byte Ixon addresses `(inAddr, outAddr)` packed as 8 + 8 `u32` words. -/
  | ixonAddrPair
  /-- Single 32-byte Ixon address `inAddr` packed as 8 `u32` words (predicate mode). -/
  | ixonAddrSingle
  /-- Custom application-defined codec tag (`≥ 3`). -/
  | custom (id : UInt64) (h : 3 ≤ id.toNat)
  deriving DecidableEq

instance : BEq CodecTag where
  beq a b := decide (a = b)

instance : Inhabited CodecTag := ⟨.rawWords⟩

instance : Repr CodecTag where
  reprPrec
    | .rawWords, _ => "Ix.DynamicLink.CodecTag.rawWords"
    | .ixonAddrPair, _ => "Ix.DynamicLink.CodecTag.ixonAddrPair"
    | .ixonAddrSingle, _ => "Ix.DynamicLink.CodecTag.ixonAddrSingle"
    | .custom id _, prec =>
      Repr.addAppParen (f!"Ix.DynamicLink.CodecTag.custom {repr id}") prec

def CodecTag.toUInt64 : CodecTag → UInt64
  | .rawWords => 0
  | .ixonAddrPair => 1
  | .ixonAddrSingle => 2
  | .custom id _ => id

def CodecTag.ofUInt64 (id : UInt64) : CodecTag :=
  if h0 : id.toNat = 0 then .rawWords
  else if h1 : id.toNat = 1 then .ixonAddrPair
  else if h2 : id.toNat = 2 then .ixonAddrSingle
  else .custom id (by omega)

theorem CodecTag.ofUInt64_toUInt64 (c : CodecTag) : CodecTag.ofUInt64 c.toUInt64 = c := by
  cases c with
  | rawWords => rfl
  | ixonAddrPair => rfl
  | ixonAddrSingle => rfl
  | custom id h =>
    have h0 : id.toNat ≠ 0 := by omega
    have h1 : id.toNat ≠ 1 := by omega
    have h2 : id.toNat ≠ 2 := by omega
    simp [CodecTag.toUInt64, CodecTag.ofUInt64, h0, h1, h2]

theorem CodecTag.toUInt64_ofUInt64 (id : UInt64) : (CodecTag.ofUInt64 id).toUInt64 = id := by
  unfold CodecTag.ofUInt64
  by_cases h0 : id.toNat = 0
  · simp [h0, CodecTag.toUInt64]
    exact UInt64.toNat_inj.mp h0.symm
  · by_cases h1 : id.toNat = 1
    · simp [h1, CodecTag.toUInt64]
      exact UInt64.toNat_inj.mp h1.symm
    · by_cases h2 : id.toNat = 2
      · simp [h2, CodecTag.toUInt64]
        exact UInt64.toNat_inj.mp h2.symm
      · simp [h0, h1, h2, CodecTag.toUInt64]

theorem CodecTag.toUInt64_injective {a b : CodecTag} (h : a.toUInt64 = b.toUInt64) : a = b := by
  have h' := congrArg CodecTag.ofUInt64 h
  rwa [ofUInt64_toUInt64, ofUInt64_toUInt64] at h'

/-- Optional binding to an IxVM-verified soundness theorem `T_C` authorizing
`circuit` for an Ixon constant `targetConst` under `(spec, binding, codec)`.
`spec` and `binding` are explicitly carried and checked by Shape 17
(`aggr_verify_bridge_cert`, validator `3` validated role table only) and Shape 18 Mode 3a
(`aggr_discharge_eval`) so the bridge certificate is cryptographically bound to the
target claim's specification digest and role binding. -/
structure BridgeBinding where
  /-- IxVM specification digest under which `certConst` was verified. -/
  spec : Address
  /-- Validated role binding (validator `3`) under which `certConst` was verified. -/
  binding : Address
  /-- Ixon address of the accelerated Lean constant `f` (or predicate `P`). -/
  targetConst : Address
  /-- Codec governing the mapping between `f`'s inputs/outputs and `pubInputs ++ pubOutputs`. -/
  codec : CodecTag
  /-- Packed claim digest / Ixon address of the unconditional IxVM/aggr proof of `T_C`. -/
  certConst : Address
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Canonical linked-circuit audit leaf (`0xE8 0x0F`), committed into the sorted
Merkle tree `linkedCircuits` of a validator `12`/`13` (`LinkedClaim`) output
whenever Shape 18 Mode 3a discharges an `EvalAssumption` via a Tier 1
`DynamicLinkStatement`. External circuits are never silently erased into
unconditional validator `3`/`4` claims, and `evalType` binds the discharged
`EvalAssumption`'s `typ` address (`leaf_typ`). -/
structure LinkedCircuitEntry where
  vkDigest : Address
  entryIdx : UInt64
  codec : CodecTag
  targetConst : Address
  certConst : Address
  evalType : Address
  spec : Address
  binding : Address
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Tier 1 dynamic-linking output statement (`0xE8 0x0D`), emitted by
`ix_aggr` Shape 17 (`aggr_dynamic_link`) and composable with `Catalog` /
proof compression / Tier 2 `aggr_discharge_eval` (Mode 3a). -/
structure DynamicLinkStatement where
  circuit : CircuitRef
  pubInputs : Array UInt64
  pubOutputs : Array UInt64
  bridge? : Option BridgeBinding := none
  deriving BEq, Repr, Inhabited

/-- Extract the canonical `LinkedCircuitEntry` recorded by Shape 18 Mode 3a
for a bridged `DynamicLinkStatement` discharging an `EvalAssumption` at type `evalType`.
Returns `none` when `bridge? = none`. -/
def DynamicLinkStatement.linkedEntry? (s : DynamicLinkStatement) (evalType : Address) :
    Option LinkedCircuitEntry :=
  s.bridge?.map fun b =>
    { vkDigest := s.circuit.vkDigest
      entryIdx := s.circuit.entryIdx
      codec := b.codec
      targetConst := b.targetConst
      certConst := b.certConst
      evalType
      spec := b.spec
      binding := b.binding }

/-- Tier 2 assumed-evaluation leaf (`0xE8 0x0E`), stored in a canonical
`AssumptionTree` (`evalAssumptions`) of a validator `10`/`11` claim.
Asserts closed equality `lhs = rhs : typ` (groundable via `Red.eqProof` /
`DefEq.eqProof` / `Red.defEqClosed`). -/
structure EvalAssumption where
  lhs : Address
  rhs : Address
  typ : Address
  circuit? : Option CircuitRef := none
  deriving BEq, Repr, Inhabited

/-- Kind of a Tier 2 eval-assumed or linked typing claim (mirrors `Claim.check` / `Claim.checkEnv`). -/
inductive EvalAssumedKind where
  | check (const : Address)
  | checkEnv (root : Address)
  deriving BEq, Repr, Inhabited

/-- Tier 2 typing claim carrying a non-empty `evalAssumptions` canonical Merkle root
and NO external linked circuits (`linkedCircuits = none`).
Encoded under validators `10` (`erased-lean-v2-eval-assumed`) and `11`
(`erased-lean-v2-binding-eval-assumed`) so `Ix.Claim.de` rejects it and frozen
`InScopeTyping` / `CircuitComposed` remain unaffected. -/
structure EvalAssumedClaim where
  ctx : Ix.ClaimContext
  kind : EvalAssumedKind
  assumptions : Option Address
  evalAssumptions : Address
  deriving BEq, Repr, Inhabited

/-- Typing claim carrying a non-empty `linkedCircuits` canonical Merkle root of
`LinkedCircuitEntry` leaves (`0xE8 0x0F`) and optionally remaining `evalAssumptions`.
Emitted by Shape 18 Mode 3a (`aggr_discharge_eval` on a `DynamicLinkStatement`)
under validators `12` (`erased-lean-v2-linked`) and `13` (`erased-lean-v2-binding-linked`),
strictly disjoint from `Ix.Claim.de`'s validators `0, 3, 4, 5` so an external linked
circuit can never masquerade as an unconditional validator `3`/`4` claim. -/
structure LinkedClaim where
  ctx : Ix.ClaimContext
  kind : EvalAssumedKind
  assumptions : Option Address
  evalAssumptions : Option Address
  linkedCircuits : Address
  deriving BEq, Repr, Inhabited

/-- Typing claim whose `evalAssumptions` were all discharged exclusively via Shape 18 Mode 2
(`@Eq` `Claim.check`, with `linkedCircuits = none`). Encoded under validators `14`
(`erased-lean-v2-eval-discharged`) and `15` (`erased-lean-v2-binding-eval-discharged`), strictly
disjoint from `Ix.Claim.de`'s validators `0, 3, 4, 5` so a Mode 2 equality-reflection root can
never be byte-identical to a direct `InScopeTyping` claim. -/
structure EvalDischargedClaim where
  ctx : Ix.ClaimContext
  kind : EvalAssumedKind
  assumptions : Option Address
  deriving BEq, Repr, Inhabited

/-- Canonical Multi-STARK public claim words `[1, entryIdx, pubInputs..., pubOutputs...]`
expected from an external accelerator circuit `C`. -/
def DynamicLinkStatement.expectedMultiStarkClaim (s : DynamicLinkStatement) : Array UInt64 :=
  #[1, s.circuit.entryIdx] ++ s.pubInputs ++ s.pubOutputs

/-- Abstract decidable-trace acceptance predicate parameterized over an external
Multi-STARK system digest `h_C`, entry index `entry_C`, and public claim words.
Instantiated concretely in `Ix.DynamicLink.Soundness` via `Ix.Cert.MultiStark`. -/
abbrev TraceRelation := Address → UInt64 → Array UInt64 → Prop

/-- Pinned specification interface for an evaluation accelerator circuit `C`:
every accepted trace of `C` at `(h_C, entry_C)` on codec-encoded `(x, y)`
satisfies the target relation `R x y` (typically `f x = y`). -/
def EvalSound (accepts : TraceRelation) (h_C : Address) (entry_C : UInt64)
    (encode : α → β → Array UInt64) (R : α → β → Prop) : Prop :=
  ∀ x y, accepts h_C entry_C (encode x y) → R x y

/-- Pinned specification interface for a predicate accelerator circuit `C`:
every accepted trace of `C` at `(h_C, entry_C)` on codec-encoded `x`
satisfies predicate `P x`. -/
def PropSound (accepts : TraceRelation) (h_C : Address) (entry_C : UInt64)
    (encode : α → Array UInt64) (P : α → Prop) : Prop :=
  ∀ x, accepts h_C entry_C (encode x) → P x

end Ix.DynamicLink
