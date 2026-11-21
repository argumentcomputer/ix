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
inputs and outputs for a linked circuit. -/
inductive CodecTag where
  /-- Raw Goldilocks `UInt64` words (pass-through). -/
  | rawWords
  /-- Two 32-byte Ixon addresses `(inAddr, outAddr)` packed as 8 + 8 `u32` words. -/
  | ixonAddrPair
  /-- Single 32-byte Ixon address `inAddr` packed as 8 `u32` words (predicate mode). -/
  | ixonAddrSingle
  /-- Custom application-defined codec tag (`≥ 3`). -/
  | custom (id : UInt64)
  deriving BEq, Repr, Inhabited, DecidableEq

def CodecTag.toUInt64 : CodecTag → UInt64
  | .rawWords => 0
  | .ixonAddrPair => 1
  | .ixonAddrSingle => 2
  | .custom id => id

def CodecTag.ofUInt64 : UInt64 → CodecTag
  | 0 => .rawWords
  | 1 => .ixonAddrPair
  | 2 => .ixonAddrSingle
  | id => .custom id

/-- Optional binding to an IxVM-verified soundness theorem `T_C` authorizing
`circuit` for an Ixon constant `targetConst` under `codec`. -/
structure BridgeBinding where
  /-- Ixon address of the accelerated Lean constant `f` (or predicate `P`). -/
  targetConst : Address
  /-- Codec governing the mapping between `f`'s inputs/outputs and `pubInputs ++ pubOutputs`. -/
  codec : CodecTag
  /-- Packed claim digest / Ixon address of the unconditional IxVM/aggr proof of `T_C`. -/
  certConst : Address
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Tier 1 dynamic-linking output statement (`0xE8 0x0D`), emitted by
`ix_aggr` Shape 17 (`aggr_dynamic_link`) and composable with `Catalog` /
proof compression / Tier 2 `aggr_discharge_eval`. -/
structure DynamicLinkStatement where
  circuit : CircuitRef
  pubInputs : Array UInt64
  pubOutputs : Array UInt64
  bridge? : Option BridgeBinding := none
  deriving BEq, Repr, Inhabited

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

/-- Kind of a Tier 2 eval-assumed typing claim (mirrors `Claim.check` / `Claim.checkEnv`). -/
inductive EvalAssumedKind where
  | check (const : Address)
  | checkEnv (root : Address)
  deriving BEq, Repr, Inhabited

/-- Tier 2 typing claim carrying a non-empty `evalAssumptions` canonical Merkle root.
Encoded under validators `10` (`erased-lean-v2-eval-assumed`) and `11`
(`erased-lean-v2-binding-eval-assumed`) so `Ix.Claim.de` rejects it and frozen
`InScopeTyping` / `CircuitComposed` remain unaffected. -/
structure EvalAssumedClaim where
  ctx : Ix.ClaimContext
  kind : EvalAssumedKind
  assumptions : Option Address
  evalAssumptions : Address
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
