import IxCCAiur.Compression.StarkWire
import IxCCAiur.Compression.CompressWrapPure
import IxCCAiur.Compression.CompressWrapSpec
import IxCCAiur.Compression.AggregatePure
import Ix.Cert.Aggr.Shapes
import Ix.Cert.Aggr.ConditionalShard
import Ix.Cert.Aggr.EndToEnd
import IxVMRefinement.Endpoint.ConditionalShards
import Aiur.MultiStarkBridge

/-! # Formal Aggregation Soundness, Concrete `Ix.Kernel.Model` Semantics, & End-to-End Composition (`AggregateSpec`)

Establishes the complete formal specification and soundness chain for
`IxCCAiur/Compression/AggregatePure.lean`, connecting the pure-Lean 19-shape
aggregation circuit directly to `Ix.Cert.Aggr.AcceptedAggrTree`, `Aggr.AggrDerivation19`,
concrete set-theoretic `Ix.Kernel.Model W` via `IxVMRefinement.Endpoint.ConditionalShards`
and `IxVM.Refinement.Endpoint.circuitComposed`, `Aiur.MultiStarkBridge`, and
`IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert`:

1. **Part 1 — Pure-Lean Aggregation Circuit Soundness (`AggregatePure` → `AcceptedAggrTree`):**
   - Exact big-endian 32-byte address order (`aggrAddressOrder_spec`), canonical `0xE2` tree
     verification (`aggrCheckCanonicalTree_sound`), sorted set union (`aggrAssertUnion_sound`),
     disjoint union (`aggrAssertDisjointUnion_sound`), disjointness (`aggrAssertDisjoint_sound`),
     flat cross-discharge (`joinRel_of_aggrPair_checks`), structural Merkle-path discharge
     (`aggrVerifyDischargeChoice_sound`, `aggrAssertStructuralDifference_sound`), and
     single-leaf removal (`aggrExtractRemovedLeaf_sound` → `Aggr.EvalRemoveRel`).
   - Exact 80-byte allowed-blob identity binding (`parseAllowedBlob_sound`) and recursive child
     Multi-STARK verification (`verifyChildBatch_sound`, `verifyChildDigest_sound`) producing
     full `CompressWrapSpec.CompressWrapAccepted` witnesses at every child proof.
   - Exact Shape `10` range-leaf (`verifyShapeRangeLeaf_sound`), Shape `11` range-join
     (`verifyShapeRangeJoin_sound`), and Shape `12` range-root (`verifyShapeRangeRoot_sound`)
     telescoping in `Ix.Cert.MultiStark.K = Fp[X]/(X^3 - X - 1)`.
   - Exact Shape `17` uniform security envelope equivalence (`aggrAssertSecurityEnvelope_iff`)
     connecting directly to `Ix.Cert.Aggr.SecurityEnvelopeOk` and `Aiur.meetsSecurityFloor`.
   - Strict Shape `18` validator isolation (`aggrParseEvalDischargeOut_isolation`,
     `verifyShapeDischargeEval_mode_isolation`, `verifyAggregateStep_shape18_never_standard_validator`):
     Mode 1 (`tag = 227`) is disabled; Mode 2 (`tag = 228`) lands strictly on validators `14`/`15`
     upon full unlinked discharge; Mode 3a (`tag = 232`) always lands on linked validators `12`/`13`;
     and NO Shape `18` execution can EVER produce standard validators `3`, `4`, or `5`.
   - Full step & recursive tree soundness (`verifyAggregateStep_sound`, `verifyAggregateRoot_sound`,
     `verifyAggregateRoot_to_pureAcceptedAggrTree`, `verifyAggregateRoot_to_acceptedAggrTree`).
2. **Part 2 — Concrete `AggrSemantics` Instantiation (`ConditionalShards` + `circuitComposed` + `MultiStarkBridge` → `Ix.Kernel.Model W`):**
   - Discharges `Ix.Cert.Aggr.AcceptedCircuitRun` directly from `Aiur.MultiStarkBridge.LoweredSystemSatisfied`
     for both unsegmented and segmented (`MEMSEG = 16`) Goldilocks traces
     (`acceptedCircuitRun_of_loweredSystem_unsegmented`, `acceptedCircuitRun_of_loweredSystem_segmented`).
   - Concretely instantiates `Aggr.AggrSemantics` (`ixvmShardedAggrSemantics`) using
     `IxVM.Refinement.Endpoint.circuitShardedComposed` (`ConditionalShards.lean`) and proves that
     an accepted unconditional `CheckEnv` aggregation tree (under standard validator `3`, validator `4`
     discharged via Shapes `13`/`14`, or literal-class validator `5`) yields an actual
     `Nonempty (Ix.Kernel.Model W (claimedEnv env))` (plus `SeedsNotFalse` and `SeedsInhabited`)
     in every `Ix.Kernel.SetTheory W` (`acceptedAggrTree_sharded_yields_kernel_model`), together with
     the single-run corollary via `IxVM.Refinement.Endpoint.circuitComposed`
     (`acceptedAggrTree_singleRun_yields_kernel_model`).
3. **Part 3 — End-to-End Composition with `CompressionIntrinsicsProof.CompressionCert` + `Aiur.MultiStarkBridge`:**
   - Connects an `IxCCAiur`-compiled `AggregatePure` verifier circuit directly to `CompressionCert`
     over arbitrary prime fields `[Field F] [DecidableEq F]`, concretely over Goldilocks (`GLF`),
     BN254 (`Fr`), and BLS12-381 (`Fr`), and to `Recheck.FrontFir` source evaluation
     (`compressionCert_aggregateStep_{accepted,goldilocks,bn254,bls12381,source_accepted}`).
   - Proves the unified end-to-end chain `loweredSystem_compressionCert_aggregate_to_kernel_model`:
     `LoweredSystemSatisfied` → `Plan.checkMemo` → `SrcEval` → `AggregateStepAccepted` &
     `AcceptedAggrTree` → `Ix.Kernel.Model W`.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`,
zero `partial`/`unsafe`; strictly `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

universe u

namespace AggregateSpec

open StarkWire CompressWrapPure CompressWrapSpec AggregatePure

/-! ## Section 1: Pure Address/Digest Conversions, Big-Endian Order, & `ExtGl` ↔ `K` Bridge -/

/-- Convert a 32-byte `DigestBytes` into an Ixon `Address`. -/
def digestBytesToAddress (d : DigestBytes) : _root_.Address :=
  ⟨ByteArray.mk (digestBytesToUInt8List d).toArray⟩

/-- Convert an `OptAddr` into `Option Address`. -/
def optAddrToOption : OptAddr → Option _root_.Address
  | .none => none
  | .some d => some (digestBytesToAddress d)

/-- Convert a `DigestBytesList` to a standard `List DigestBytes`. -/
def digestBytesListToList : DigestBytesList → List DigestBytes
  | .nil => []
  | .cons x rest => x :: digestBytesListToList rest

/-- Membership predicate on `DigestBytesList`. -/
def digestBytesListMem (x : DigestBytes) (xs : DigestBytesList) : Prop :=
  x ∈ digestBytesListToList xs

/-- Convert a `DigestBytesList` into a list of `Address`es. -/
def digestBytesListToAddresses (xs : DigestBytesList) : List _root_.Address :=
  (digestBytesListToList xs).map digestBytesToAddress

/-- Every element in a `DigestBytesList` has all 32 bytes `< 256`. -/
def ValidDigestList : DigestBytesList → Prop
  | .nil => True
  | .cons x rest => ValidDigestBytes x ∧ ValidDigestList rest

/-- Map `StarkWire.ExtGl` into the mathematical cubic extension `Ix.Cert.MultiStark.K = Fp[X]/(X^3 - X - 1)`. -/
def extGlToK (e : ExtGl) : Ix.Cert.MultiStark.K :=
  ⟨(e.c0 : Ix.Cert.MultiStark.Fp), (e.c1 : Ix.Cert.MultiStark.Fp), (e.c2 : Ix.Cert.MultiStark.Fp)⟩

/-- Convert `StarkWire.SysParams` into `Ix.Cert.MultiStark.StarkParams`. -/
def toStarkParams (p : SysParams) : Ix.Cert.MultiStark.StarkParams :=
  { logBlowup := p.logBlowup
    capHeight := p.capHeight
    logFinalPolyLen := p.logFinalPolyLen
    maxLogArity := p.maxLogArity
    numQueries := p.numQueries
    commitPowBits := p.commitPowBits
    queryPowBits := p.queryPowBits }

/-- Convert a validator code byte (`3, 4, 5, 10, 11, 12, 13, 14, 15`) and binding address into
an `Aggr.ValidatorMode Address`. -/
def validatorModeOf (val : Nat) (b : _root_.Address) : Option (_root_.Aggr.ValidatorMode _root_.Address) :=
  match val with
  | 3 => some (.validated b)
  | 4 => some (.assumedBinding b)
  | 5 => some (.literalClass b)
  | 10 => some (.evalAssumed b)
  | 11 => some (.bindingEvalAssumed b)
  | 12 => some (.linked b)
  | 13 => some (.bindingLinked b)
  | 14 => some (.evalDischarged b)
  | 15 => some (.bindingEvalDischarged b)
  | _ => none

/-- Extract the first `n` shard headers from a `ShardHeaderList`. -/
def shardHeaderListTake : Nat → ShardHeaderList → ShardHeaderList
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons h rest => .cons h (shardHeaderListTake n rest)

/-- Extract the `idx`-th `ShardProof`'s final accumulator from a `ShardProofList`. -/
def shardProofListGetAcc : Nat → ShardProofList → ExtGl
  | _, .nil => extZero
  | 0, .cons p _ => lastAcc p.intermediateAccs
  | k + 1, .cons _ rest => shardProofListGetAcc k rest

/-- Per-shard residual function for a Shape 10 range leaf starting at shard `base`. -/
def shardProofResidualAt (proofs : ShardProofList) (base s : Nat) : Ix.Cert.MultiStark.K :=
  if s < base then 0 else extGlToK (shardProofListGetAcc (s - base) proofs)

/-! ### Basic `Digest32Words`, `OptAddr`, `ExtGl → K`, & `Address` Lemmas -/

private theorem ite_nat_eq_one_right {c : Prop} [Decidable c] {a : Nat}
    (h : (if c then 0 else a) = 1) : ¬ c ∧ a = 1 := by
  by_cases hc : c
  · simp [hc] at h
  · simp [hc] at h; exact ⟨hc, h⟩

private theorem ite_zero_or_one {c : Prop} [Decidable c] {a : Nat}
    (ha : a = 0 ∨ a = 1) : (if c then 0 else a) = 0 ∨ (if c then 0 else a) = 1 := by
  by_cases hc : c <;> simp [hc, ha]

private theorem ite_both_zero_or_one {c : Prop} [Decidable c] {a b : Nat}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if c then a else b) = 0 ∨ (if c then a else b) = 1 := by
  by_cases hc : c <;> simp [hc, ha, hb]

private theorem ite_ok_zero_or_one {β : Type*} (okFn : β → Nat) {c : Prop} [Decidable c]
    {b a : β} (hb : okFn b = 0) (ha : okFn a = 0 ∨ okFn a = 1) :
    okFn (if c then b else a) = 0 ∨ okFn (if c then b else a) = 1 := by
  by_cases hc : c <;> simp [hc, hb, ha]

private theorem ite_elim_bad {β : Type*} {c : Prop} [Decidable c] {b a : β}
    {okFn : β → Nat} (hb : okFn b = 0)
    (h : okFn (if c then b else a) = 1) : ¬ c ∧ okFn a = 1 ∧ (if c then b else a) = a := by
  by_cases hc : c
  · simp [hc, hb] at h
  · have hite : (if c then b else a) = a := by simp [hc]
    rw [hite] at h ⊢
    exact ⟨hc, h, rfl⟩

theorem digest32WordsEq_eq_one_iff (a b : Digest32Words) :
    digest32WordsEq a b = 1 ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases b with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  unfold digest32WordsEq
  simp only [Digest32Words.mk.injEq]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    simp
  · rename_i h
    constructor
    · intro h0; cases h0
    · intro heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp at h

theorem digest32WordsEq_zero_or_one (a b : Digest32Words) :
    digest32WordsEq a b = 0 ∨ digest32WordsEq a b = 1 := by
  unfold digest32WordsEq; split <;> simp

theorem digestBytesEq_zero_or_one (a b : DigestBytes) :
    digestBytesEq a b = 0 ∨ digestBytesEq a b = 1 := by
  unfold digestBytesEq; split <;> simp

theorem optAddrEq_eq_one_iff (a b : OptAddr) :
    optAddrEq a b = 1 ↔ a = b := by
  cases a <;> cases b <;> simp [optAddrEq, digestBytesEq_eq_one_iff]

theorem optAddrEq_zero_or_one (a b : OptAddr) :
    optAddrEq a b = 0 ∨ optAddrEq a b = 1 := by
  cases a <;> cases b <;> simp [optAddrEq, digestBytesEq_zero_or_one]

theorem digestBytesToAddress_inj {a b : DigestBytes}
    (ha : ValidDigestBytes a) (hb : ValidDigestBytes b)
    (heq : digestBytesToAddress a = digestBytesToAddress b) : a = b := by
  unfold digestBytesToAddress at heq
  have hlist : digestBytesToUInt8List a = digestBytesToUInt8List b := by
    have h1 := congrArg (fun x : _root_.Address => x.hash.data.toList) heq
    simpa using h1
  have hva : ValidBytes (digestBytesOnto a .nil) := by
    unfold digestBytesOnto
    rw [validBytes_u64BytesOnto, validBytes_u64BytesOnto, validBytes_u64BytesOnto, validBytes_u64BytesOnto]
    exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, trivial⟩
  have hvb : ValidBytes (digestBytesOnto b .nil) := by
    unfold digestBytesOnto
    rw [validBytes_u64BytesOnto, validBytes_u64BytesOnto, validBytes_u64BytesOnto, validBytes_u64BytesOnto]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, trivial⟩
  have hbl := byteList_eq_of_toUInt8List_eq hva hvb hlist
  rcases a with ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11, a12, a13, a14, a15⟩,
    ⟨a16, a17, a18, a19, a20, a21, a22, a23⟩, ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩⟩
  rcases b with ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7⟩, ⟨b8, b9, b10, b11, b12, b13, b14, b15⟩,
    ⟨b16, b17, b18, b19, b20, b21, b22, b23⟩, ⟨b24, b25, b26, b27, b28, b29, b30, b31⟩⟩
  unfold digestBytesOnto u64BytesOnto at hbl
  injection hbl with h0 hbl; subst h0; injection hbl with h1 hbl; subst h1
  injection hbl with h2 hbl; subst h2; injection hbl with h3 hbl; subst h3
  injection hbl with h4 hbl; subst h4; injection hbl with h5 hbl; subst h5
  injection hbl with h6 hbl; subst h6; injection hbl with h7 hbl; subst h7
  injection hbl with h8 hbl; subst h8; injection hbl with h9 hbl; subst h9
  injection hbl with h10 hbl; subst h10; injection hbl with h11 hbl; subst h11
  injection hbl with h12 hbl; subst h12; injection hbl with h13 hbl; subst h13
  injection hbl with h14 hbl; subst h14; injection hbl with h15 hbl; subst h15
  injection hbl with h16 hbl; subst h16; injection hbl with h17 hbl; subst h17
  injection hbl with h18 hbl; subst h18; injection hbl with h19 hbl; subst h19
  injection hbl with h20 hbl; subst h20; injection hbl with h21 hbl; subst h21
  injection hbl with h22 hbl; subst h22; injection hbl with h23 hbl; subst h23
  injection hbl with h24 hbl; subst h24; injection hbl with h25 hbl; subst h25
  injection hbl with h26 hbl; subst h26; injection hbl with h27 hbl; subst h27
  injection hbl with h28 hbl; subst h28; injection hbl with h29 hbl; subst h29
  injection hbl with h30 hbl; subst h30; injection hbl with h31 _; subst h31
  rfl

theorem packAddress_digest32ToDigestBytes (h : Digest32) :
    packAddress (digest32ToDigestBytes h) = packDigest h := by
  rcases h with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
  have hpack : ∀ w : UInt32,
      packLe4 (w.toNat % 256) (w.toNat / 256 % 256) (w.toNat / 256 / 256 % 256)
        (w.toNat / 256 / 256 / 256) = w.toNat := by
    intro w
    have hlt : w.toNat < 2 ^ 32 := w.toNat_lt
    unfold packLe4; omega
  simp only [packAddress, digest32ToDigestBytes, u64OfTwoU32, packDigest, Digest32Words.mk.injEq]
  exact ⟨hpack w0, hpack w1, hpack w2, hpack w3, hpack w4, hpack w5, hpack w6, hpack w7⟩

theorem packDigest_eq_iff (a b : Digest32) :
    packDigest a = packDigest b ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases b with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  simp only [packDigest, Digest32Words.mk.injEq, Digest32.mk.injEq, UInt32.toNat_inj]

theorem validDigestBytes_bytesToAddr (bs : ByteList) :
    ValidDigestBytes (bytesToAddr bs) :=
  validDigestBytes_digest32ToDigestBytes (blake3HashBytes bs)

theorem validDigestBytes_dummy : ValidDigestBytes dummyDigestBytes :=
  ⟨validU64Bytes_u64Zero, validU64Bytes_u64Zero, validU64Bytes_u64Zero, validU64Bytes_u64Zero⟩

private theorem natCast_fp_eq_iff (a b : Nat) :
    ((a : Ix.Cert.MultiStark.Fp) = (b : Ix.Cert.MultiStark.Fp)) ↔ a % glPrime = b % glPrime := by
  change ((a : ZMod Aiur.Library.U32.Goldilocks.modulus) = (b : ZMod Aiur.Library.U32.Goldilocks.modulus)) ↔ _
  rw [ZMod.natCast_eq_natCast_iff']
  rfl

theorem extGlToK_zero : extGlToK extZero = (0 : Ix.Cert.MultiStark.K) := rfl

theorem extGlToK_add (a b : ExtGl) :
    extGlToK (extAdd a b) = extGlToK a + extGlToK b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  have hmod : ∀ x y : Nat,
      (((x + y) % glPrime : Nat) : Ix.Cert.MultiStark.Fp) =
        (x : Ix.Cert.MultiStark.Fp) + (y : Ix.Cert.MultiStark.Fp) := by
    intro x y
    rw [← Nat.cast_add, natCast_fp_eq_iff, Nat.mod_mod]
  change CertiFri.P3.Fp3Model.mk (((a0 + b0) % glPrime : Nat) : Ix.Cert.MultiStark.Fp)
    (((a1 + b1) % glPrime : Nat) : Ix.Cert.MultiStark.Fp)
    (((a2 + b2) % glPrime : Nat) : Ix.Cert.MultiStark.Fp) =
    CertiFri.P3.Fp3Model.mk ((a0 : Ix.Cert.MultiStark.Fp) + (b0 : Ix.Cert.MultiStark.Fp))
      ((a1 : Ix.Cert.MultiStark.Fp) + (b1 : Ix.Cert.MultiStark.Fp))
      ((a2 : Ix.Cert.MultiStark.Fp) + (b2 : Ix.Cert.MultiStark.Fp))
  congr 1
  · exact hmod a0 b0
  · exact hmod a1 b1
  · exact hmod a2 b2

theorem extGlToK_eq_iff (a b : ExtGl) :
    extEq a b = 1 ↔ extGlToK a = extGlToK b := by
  rw [extEq_eq_one_iff]
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  constructor
  · rintro ⟨h0, h1, h2⟩
    change CertiFri.P3.Fp3Model.mk _ _ _ = CertiFri.P3.Fp3Model.mk _ _ _
    congr 1
    · exact (natCast_fp_eq_iff a0 b0).mpr h0
    · exact (natCast_fp_eq_iff a1 b1).mpr h1
    · exact (natCast_fp_eq_iff a2 b2).mpr h2
  · intro h
    injection h with h0 h1 h2
    exact ⟨(natCast_fp_eq_iff a0 b0).mp h0, (natCast_fp_eq_iff a1 b1).mp h1,
      (natCast_fp_eq_iff a2 b2).mp h2⟩

theorem extGlToK_isZero_iff (a : ExtGl) :
    extIsZero a = 1 ↔ extGlToK a = (0 : Ix.Cert.MultiStark.K) := by
  rw [extIsZero_eq_one_iff]
  rcases a with ⟨a0, a1, a2⟩
  have h0 : ∀ x : Nat, ((x : Ix.Cert.MultiStark.Fp) = 0) ↔ x % glPrime = 0 := by
    intro x
    simpa [Nat.zero_mod] using natCast_fp_eq_iff x 0
  constructor
  · rintro ⟨ha0, ha1, ha2⟩
    change CertiFri.P3.Fp3Model.mk _ _ _ = CertiFri.P3.Fp3Model.mk 0 0 0
    congr 1
    · exact (h0 a0).mpr ha0
    · exact (h0 a1).mpr ha1
    · exact (h0 a2).mpr ha2
  · intro h
    injection h with ha0 ha1 ha2
    exact ⟨(h0 a0).mp ha0, (h0 a1).mp ha1, (h0 a2).mp ha2⟩

/-! ### Big-Endian 32-Byte Address Order (`aggrAddressOrder_spec`) -/

/-- Exact 8-word big-endian integer representation of a 32-byte `DigestBytes` (256-bit key). -/
def aggrAddressKey (a : DigestBytes) : Nat :=
  let c0 := packBe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3
  let c1 := packBe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7
  let c2 := packBe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3
  let c3 := packBe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7
  let c4 := packBe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3
  let c5 := packBe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7
  let c6 := packBe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3
  let c7 := packBe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7
  c0 * 2 ^ 224 + c1 * 2 ^ 192 + c2 * 2 ^ 160 + c3 * 2 ^ 128 +
  c4 * 2 ^ 96 + c5 * 2 ^ 64 + c6 * 2 ^ 32 + c7

private theorem packBe4_lt {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    packBe4 a b c d < 2 ^ 32 := by
  unfold packBe4; omega

private theorem packBe4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : Nat}
    (_ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (_hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (h : packBe4 a0 a1 a2 a3 = packBe4 b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  unfold packBe4 at h
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem lex_step {B a0 b0 a1 b1 : Nat} (ha1 : a1 < B) (hb1 : b1 < B) :
    (a0 * B + a1 < b0 * B + b1 ↔ a0 < b0 ∨ (a0 = b0 ∧ a1 < b1)) ∧
    (a0 * B + a1 = b0 * B + b1 ↔ a0 = b0 ∧ a1 = b1) := by
  constructor
  · constructor
    · intro h
      by_cases hlt : a0 < b0
      · exact Or.inl hlt
      · by_cases heq : a0 = b0
        · subst heq; exact Or.inr ⟨rfl, by omega⟩
        · have hge : b0 + 1 ≤ a0 := by omega
          have hmul : (b0 + 1) * B ≤ a0 * B := Nat.mul_le_mul_right B hge
          rw [Nat.add_mul, Nat.one_mul] at hmul
          omega
    · rintro (hlt | ⟨rfl, h1⟩)
      · have hle : a0 + 1 ≤ b0 := by omega
        have hmul : (a0 + 1) * B ≤ b0 * B := Nat.mul_le_mul_right B hle
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      · omega
  · constructor
    · intro h
      by_cases hlt : a0 < b0
      · have hle : a0 + 1 ≤ b0 := by omega
        have hmul : (a0 + 1) * B ≤ b0 * B := Nat.mul_le_mul_right B hle
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
      · by_cases hgt : b0 < a0
        · have hle : b0 + 1 ≤ a0 := by omega
          have hmul : (b0 + 1) * B ≤ a0 * B := Nat.mul_le_mul_right B hle
          rw [Nat.add_mul, Nat.one_mul] at hmul
          omega
        · have heq : a0 = b0 := by omega
          subst heq; exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl

private theorem cmpU32_spec (x y : Nat) :
    (cmpU32 x y = 0 ↔ x < y) ∧ (cmpU32 x y = 1 ↔ x = y) ∧ (cmpU32 x y = 2 ↔ y < x) := by
  unfold cmpU32
  by_cases hxy : x = y
  · subst hxy; simp
  · have hbeq : (x == y) = false := beq_false_of_ne hxy
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlt : x < y
    · simp [hlt]; omega
    · simp [hlt]; omega

private theorem aggrAddressKey_step_lt {c1 c2 c3 c4 c5 c6 c7 : Nat}
    (h1 : c1 < 2^32) (h2 : c2 < 2^32) (h3 : c3 < 2^32)
    (h4 : c4 < 2^32) (h5 : c5 < 2^32) (h6 : c6 < 2^32) (h7 : c7 < 2^32) :
    c1 * 2^192 + (c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))))) < 2^224 ∧
    c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)))) < 2^192 ∧
    c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))) < 2^160 ∧
    c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)) < 2^128 ∧
    c5 * 2^64 + (c6 * 2^32 + c7) < 2^96 ∧
    c6 * 2^32 + c7 < 2^64 := by
  have b6 : c6 * 2^32 + c7 < 2^64 := by
    have : c6 ≤ 2^32 - 1 := by omega
    calc c6 * 2^32 + c7 < (2^32 - 1) * 2^32 + 2^32 := by nlinarith
      _ = 2^64 := by norm_num
  have b5 : c5 * 2^64 + (c6 * 2^32 + c7) < 2^96 := by
    have : c5 ≤ 2^32 - 1 := by omega
    calc c5 * 2^64 + (c6 * 2^32 + c7) < (2^32 - 1) * 2^64 + 2^64 := by nlinarith
      _ = 2^96 := by norm_num
  have b4 : c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)) < 2^128 := by
    have : c4 ≤ 2^32 - 1 := by omega
    calc c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)) < (2^32 - 1) * 2^96 + 2^96 := by nlinarith
      _ = 2^128 := by norm_num
  have b3 : c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))) < 2^160 := by
    have : c3 ≤ 2^32 - 1 := by omega
    calc c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))) < (2^32 - 1) * 2^128 + 2^128 := by nlinarith
      _ = 2^160 := by norm_num
  have b2 : c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)))) < 2^192 := by
    have : c2 ≤ 2^32 - 1 := by omega
    calc c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))))
        < (2^32 - 1) * 2^160 + 2^160 := by nlinarith
      _ = 2^192 := by norm_num
  have b1 : c1 * 2^192 + (c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7))))) < 2^224 := by
    have : c1 ≤ 2^32 - 1 := by omega
    calc c1 * 2^192 + (c2 * 2^160 + (c3 * 2^128 + (c4 * 2^96 + (c5 * 2^64 + (c6 * 2^32 + c7)))))
        < (2^32 - 1) * 2^192 + 2^192 := by nlinarith
      _ = 2^224 := by norm_num
  exact ⟨b1, b2, b3, b4, b5, b6⟩

/-- Exact characterization of `aggrAddressOrder` on valid 32-byte addresses:
`0 ↔ key a < key b`, `1 ↔ a = b`, `2 ↔ key b < key a`. -/
theorem aggrAddressOrder_spec {a b : DigestBytes}
    (ha : ValidDigestBytes a) (hb : ValidDigestBytes b) :
    (aggrAddressOrder a b = 0 ↔ aggrAddressKey a < aggrAddressKey b) ∧
    (aggrAddressOrder a b = 1 ↔ a = b) ∧
    (aggrAddressOrder a b = 2 ↔ aggrAddressKey b < aggrAddressKey a) := by
  have ha1 := packBe4_lt ha.1.2.2.2.2.1 ha.1.2.2.2.2.2.1 ha.1.2.2.2.2.2.2.1 ha.1.2.2.2.2.2.2.2
  have ha2 := packBe4_lt ha.2.1.1 ha.2.1.2.1 ha.2.1.2.2.1 ha.2.1.2.2.2.1
  have ha3 := packBe4_lt ha.2.1.2.2.2.2.1 ha.2.1.2.2.2.2.2.1 ha.2.1.2.2.2.2.2.2.1 ha.2.1.2.2.2.2.2.2.2
  have ha4 := packBe4_lt ha.2.2.1.1 ha.2.2.1.2.1 ha.2.2.1.2.2.1 ha.2.2.1.2.2.2.1
  have ha5 := packBe4_lt ha.2.2.1.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.2.2
  have ha6 := packBe4_lt ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2.1
  have ha7 := packBe4_lt ha.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.2.2
  have hb1 := packBe4_lt hb.1.2.2.2.2.1 hb.1.2.2.2.2.2.1 hb.1.2.2.2.2.2.2.1 hb.1.2.2.2.2.2.2.2
  have hb2 := packBe4_lt hb.2.1.1 hb.2.1.2.1 hb.2.1.2.2.1 hb.2.1.2.2.2.1
  have hb3 := packBe4_lt hb.2.1.2.2.2.2.1 hb.2.1.2.2.2.2.2.1 hb.2.1.2.2.2.2.2.2.1 hb.2.1.2.2.2.2.2.2.2
  have hb4 := packBe4_lt hb.2.2.1.1 hb.2.2.1.2.1 hb.2.2.1.2.2.1 hb.2.2.1.2.2.2.1
  have hb5 := packBe4_lt hb.2.2.1.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.2.2
  have hb6 := packBe4_lt hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1
  have hb7 := packBe4_lt hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.2
  have hba := aggrAddressKey_step_lt ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hbb := aggrAddressKey_step_lt hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have heqChunks :
      (packBe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3 = packBe4 b.d0.b0 b.d0.b1 b.d0.b2 b.d0.b3 ∧
       packBe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7 = packBe4 b.d0.b4 b.d0.b5 b.d0.b6 b.d0.b7 ∧
       packBe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3 = packBe4 b.d1.b0 b.d1.b1 b.d1.b2 b.d1.b3 ∧
       packBe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7 = packBe4 b.d1.b4 b.d1.b5 b.d1.b6 b.d1.b7 ∧
       packBe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3 = packBe4 b.d2.b0 b.d2.b1 b.d2.b2 b.d2.b3 ∧
       packBe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7 = packBe4 b.d2.b4 b.d2.b5 b.d2.b6 b.d2.b7 ∧
       packBe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3 = packBe4 b.d3.b0 b.d3.b1 b.d3.b2 b.d3.b3 ∧
       packBe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7 = packBe4 b.d3.b4 b.d3.b5 b.d3.b6 b.d3.b7) ↔ a = b := by
    constructor
    · rintro ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩
      have q0 := packBe4_inj ha.1.1 ha.1.2.1 ha.1.2.2.1 ha.1.2.2.2.1 hb.1.1 hb.1.2.1 hb.1.2.2.1 hb.1.2.2.2.1 e0
      have q1 := packBe4_inj ha.1.2.2.2.2.1 ha.1.2.2.2.2.2.1 ha.1.2.2.2.2.2.2.1 ha.1.2.2.2.2.2.2.2
        hb.1.2.2.2.2.1 hb.1.2.2.2.2.2.1 hb.1.2.2.2.2.2.2.1 hb.1.2.2.2.2.2.2.2 e1
      have q2 := packBe4_inj ha.2.1.1 ha.2.1.2.1 ha.2.1.2.2.1 ha.2.1.2.2.2.1 hb.2.1.1 hb.2.1.2.1 hb.2.1.2.2.1 hb.2.1.2.2.2.1 e2
      have q3 := packBe4_inj ha.2.1.2.2.2.2.1 ha.2.1.2.2.2.2.2.1 ha.2.1.2.2.2.2.2.2.1 ha.2.1.2.2.2.2.2.2.2
        hb.2.1.2.2.2.2.1 hb.2.1.2.2.2.2.2.1 hb.2.1.2.2.2.2.2.2.1 hb.2.1.2.2.2.2.2.2.2 e3
      have q4 := packBe4_inj ha.2.2.1.1 ha.2.2.1.2.1 ha.2.2.1.2.2.1 ha.2.2.1.2.2.2.1
        hb.2.2.1.1 hb.2.2.1.2.1 hb.2.2.1.2.2.1 hb.2.2.1.2.2.2.1 e4
      have q5 := packBe4_inj ha.2.2.1.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.2.1 ha.2.2.1.2.2.2.2.2.2.2
        hb.2.2.1.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.2.1 hb.2.2.1.2.2.2.2.2.2.2 e5
      have q6 := packBe4_inj ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2.1
        hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 e6
      have q7 := packBe4_inj ha.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.2.1 ha.2.2.2.2.2.2.2.2.2.2
        hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.2 e7
      rcases a with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
      rcases b with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
      dsimp only at q0 q1 q2 q3 q4 q5 q6 q7
      rcases q0 with ⟨rfl, rfl, rfl, rfl⟩; rcases q1 with ⟨rfl, rfl, rfl, rfl⟩
      rcases q2 with ⟨rfl, rfl, rfl, rfl⟩; rcases q3 with ⟨rfl, rfl, rfl, rfl⟩
      rcases q4 with ⟨rfl, rfl, rfl, rfl⟩; rcases q5 with ⟨rfl, rfl, rfl, rfl⟩
      rcases q6 with ⟨rfl, rfl, rfl, rfl⟩; rcases q7 with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · rintro rfl; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hstep : ∀ (a0 b0 : Nat) {B a1 b1 r : Nat}, a1 < B → b1 < B →
      ((r = 0 ↔ a1 < b1) ∧ (r = 1 ↔ a1 = b1) ∧ (r = 2 ↔ b1 < a1)) →
      let out := if cmpU32 a0 b0 != 1 then cmpU32 a0 b0 else r
      (out = 0 ↔ a0 * B + a1 < b0 * B + b1) ∧
      (out = 1 ↔ a0 = b0 ∧ a1 = b1) ∧
      (out = 2 ↔ b0 * B + b1 < a0 * B + a1) := by
    intro a0 b0 B a1 b1 r h1 h2 hr
    dsimp only
    have hc := cmpU32_spec a0 b0
    have hl := lex_step (a0 := a0) (b0 := b0) h1 h2
    have hlr := lex_step (a0 := b0) (b0 := a0) h2 h1
    by_cases heq : a0 = b0
    · have h1c : cmpU32 a0 b0 = 1 := hc.2.1.mpr heq
      rw [h1c]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [hl.1, heq]; simp [hr.1]
      · simp [heq, hr.2.1]
      · rw [hlr.1, heq]; simp [hr.2.2]
    · have hne1 : cmpU32 a0 b0 ≠ 1 := fun h => heq (hc.2.1.mp h)
      have hbne : (cmpU32 a0 b0 != 1) = true := bne_iff_ne.mpr hne1
      simp only [hbne, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [hc.1, hl.1]; simp [heq]
      · simp [hne1, heq]
      · rw [hc.2.2, hlr.1]; simp [Ne.symm heq]
  have s7 := cmpU32_spec (packBe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7) (packBe4 b.d3.b4 b.d3.b5 b.d3.b6 b.d3.b7)
  have s6 := hstep (packBe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3) (packBe4 b.d3.b0 b.d3.b1 b.d3.b2 b.d3.b3) ha7 hb7 s7
  have s5 := hstep (packBe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7) (packBe4 b.d2.b4 b.d2.b5 b.d2.b6 b.d2.b7)
    hba.2.2.2.2.2 hbb.2.2.2.2.2 ⟨s6.1, by rw [s6.2.1, (lex_step ha7 hb7).2], s6.2.2⟩
  have s4 := hstep (packBe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3) (packBe4 b.d2.b0 b.d2.b1 b.d2.b2 b.d2.b3)
    hba.2.2.2.2.1 hbb.2.2.2.2.1 ⟨s5.1, by rw [s5.2.1, (lex_step hba.2.2.2.2.2 hbb.2.2.2.2.2).2], s5.2.2⟩
  have s3 := hstep (packBe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7) (packBe4 b.d1.b4 b.d1.b5 b.d1.b6 b.d1.b7)
    hba.2.2.2.1 hbb.2.2.2.1 ⟨s4.1, by rw [s4.2.1, (lex_step hba.2.2.2.2.1 hbb.2.2.2.2.1).2], s4.2.2⟩
  have s2 := hstep (packBe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3) (packBe4 b.d1.b0 b.d1.b1 b.d1.b2 b.d1.b3)
    hba.2.2.1 hbb.2.2.1 ⟨s3.1, by rw [s3.2.1, (lex_step hba.2.2.2.1 hbb.2.2.2.1).2], s3.2.2⟩
  have s1 := hstep (packBe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7) (packBe4 b.d0.b4 b.d0.b5 b.d0.b6 b.d0.b7)
    hba.2.1 hbb.2.1 ⟨s2.1, by rw [s2.2.1, (lex_step hba.2.2.1 hbb.2.2.1).2], s2.2.2⟩
  have s0 := hstep (packBe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3) (packBe4 b.d0.b0 b.d0.b1 b.d0.b2 b.d0.b3)
    hba.1 hbb.1 ⟨s1.1, by rw [s1.2.1, (lex_step hba.2.1 hbb.2.1).2], s1.2.2⟩
  have hkeyA : aggrAddressKey a =
      packBe4 a.d0.b0 a.d0.b1 a.d0.b2 a.d0.b3 * 2 ^ 224 +
      (packBe4 a.d0.b4 a.d0.b5 a.d0.b6 a.d0.b7 * 2 ^ 192 +
      (packBe4 a.d1.b0 a.d1.b1 a.d1.b2 a.d1.b3 * 2 ^ 160 +
      (packBe4 a.d1.b4 a.d1.b5 a.d1.b6 a.d1.b7 * 2 ^ 128 +
      (packBe4 a.d2.b0 a.d2.b1 a.d2.b2 a.d2.b3 * 2 ^ 96 +
      (packBe4 a.d2.b4 a.d2.b5 a.d2.b6 a.d2.b7 * 2 ^ 64 +
      (packBe4 a.d3.b0 a.d3.b1 a.d3.b2 a.d3.b3 * 2 ^ 32 +
       packBe4 a.d3.b4 a.d3.b5 a.d3.b6 a.d3.b7)))))) := by
    unfold aggrAddressKey; simp only [Nat.add_assoc]
  have hkeyB : aggrAddressKey b =
      packBe4 b.d0.b0 b.d0.b1 b.d0.b2 b.d0.b3 * 2 ^ 224 +
      (packBe4 b.d0.b4 b.d0.b5 b.d0.b6 b.d0.b7 * 2 ^ 192 +
      (packBe4 b.d1.b0 b.d1.b1 b.d1.b2 b.d1.b3 * 2 ^ 160 +
      (packBe4 b.d1.b4 b.d1.b5 b.d1.b6 b.d1.b7 * 2 ^ 128 +
      (packBe4 b.d2.b0 b.d2.b1 b.d2.b2 b.d2.b3 * 2 ^ 96 +
      (packBe4 b.d2.b4 b.d2.b5 b.d2.b6 b.d2.b7 * 2 ^ 64 +
      (packBe4 b.d3.b0 b.d3.b1 b.d3.b2 b.d3.b3 * 2 ^ 32 +
       packBe4 b.d3.b4 b.d3.b5 b.d3.b6 b.d3.b7)))))) := by
    unfold aggrAddressKey; simp only [Nat.add_assoc]
  have hkeyEq : aggrAddressKey a = aggrAddressKey b ↔ a = b := by
    rw [hkeyA, hkeyB]
    rw [(lex_step hba.1 hbb.1).2, (lex_step hba.2.1 hbb.2.1).2,
        (lex_step hba.2.2.1 hbb.2.2.1).2, (lex_step hba.2.2.2.1 hbb.2.2.2.1).2,
        (lex_step hba.2.2.2.2.1 hbb.2.2.2.2.1).2, (lex_step hba.2.2.2.2.2 hbb.2.2.2.2.2).2,
        (lex_step ha7 hb7).2]
    exact heqChunks
  have h1eq : aggrAddressOrder a b = 1 ↔ aggrAddressKey a = aggrAddressKey b := by
    rw [hkeyA, hkeyB, (lex_step hba.1 hbb.1).2]
    exact s0.2.1
  exact ⟨by rw [hkeyA, hkeyB]; exact s0.1, h1eq.trans hkeyEq, by rw [hkeyA, hkeyB]; exact s0.2.2⟩

theorem aggrAddressKey_inj {a b : DigestBytes}
    (ha : ValidDigestBytes a) (hb : ValidDigestBytes b)
    (h : aggrAddressKey a = aggrAddressKey b) : a = b := by
  have hs := aggrAddressOrder_spec ha hb
  have hne0 : aggrAddressOrder a b ≠ 0 := by
    intro h0; have hlt := hs.1.mp h0; rw [h] at hlt; exact Nat.lt_irrefl _ hlt
  have hne2 : aggrAddressOrder a b ≠ 2 := by
    intro h2; have hlt := hs.2.2.mp h2; rw [h] at hlt; exact Nat.lt_irrefl _ hlt
  have h012 : aggrAddressOrder a b = 0 ∨ aggrAddressOrder a b = 1 ∨ aggrAddressOrder a b = 2 := by
    have hc : ∀ x y, cmpU32 x y = 0 ∨ cmpU32 x y = 1 ∨ cmpU32 x y = 2 := fun x y => by
      unfold cmpU32; split <;> [exact Or.inr (Or.inl rfl); (split <;> simp)]
    unfold aggrAddressOrder
    extract_lets
    split; · exact hc _ _
    split; · exact hc _ _
    split; · exact hc _ _
    split; · exact hc _ _
    split; · exact hc _ _
    split; · exact hc _ _
    split; · exact hc _ _
    exact hc _ _
  rcases h012 with h0 | h1 | h2
  · exact absurd h0 hne0
  · exact hs.2.1.mp h1
  · exact absurd h2 hne2

/-! ## Section 2: Canonical Trees, Sorted Set Operations, Allowed Blob, & Shape Soundness -/

/-- Strictly ascending order on `DigestBytesList` under `aggrAddressKey`. -/
def StrictSorted : DigestBytesList → Prop
  | .nil => True
  | .cons a rest =>
    (∀ b, digestBytesListMem b rest → aggrAddressKey a < aggrAddressKey b) ∧ StrictSorted rest

theorem validDigestList_mem {xs : DigestBytesList} {x : DigestBytes}
    (hv : ValidDigestList xs) (hm : digestBytesListMem x xs) : ValidDigestBytes x := by
  induction xs with
  | nil => cases hm
  | cons a rest ih =>
    rcases List.mem_cons.mp hm with rfl | htl
    · exact hv.1
    · exact ih hv.2 htl

theorem validDigestList_append {xs ys : DigestBytesList}
    (hx : ValidDigestList xs) (hy : ValidDigestList ys) :
    ValidDigestList (digestBytesListAppend xs ys) := by
  induction xs with
  | nil => exact hy
  | cons a rest ih => exact ⟨hx.1, ih hx.2⟩

theorem aggrAssertStrictSorted_sound :
    ∀ (xs : DigestBytesList), ValidDigestList xs → aggrAssertStrictSorted xs = 1 → StrictSorted xs
  | .nil, _, _ => trivial
  | .cons a .nil, _, _ => ⟨(fun _ h => by cases h), trivial⟩
  | .cons a (.cons b rest), hv, hok => by
    unfold aggrAssertStrictSorted at hok
    by_cases hab : aggrAddressOrder a b = 0
    · simp only [hab, beq_self_eq_true, ↓reduceIte] at hok
      have hsr := aggrAssertStrictSorted_sound (.cons b rest) hv.2 hok
      have hlt : aggrAddressKey a < aggrAddressKey b := (aggrAddressOrder_spec hv.1 hv.2.1).1.mp hab
      refine ⟨fun c hc => ?_, hsr⟩
      rcases List.mem_cons.mp hc with rfl | htl
      · exact hlt
      · exact Nat.lt_trans hlt (hsr.1 c htl)
    · have hbf : (aggrAddressOrder a b == 0) = false := beq_false_of_ne hab
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

private theorem aggrParseTreeBodyFuel_ok_01 :
    ∀ k bs, (aggrParseTreeBodyFuel k bs).ok = 0 ∨ (aggrParseTreeBodyFuel k bs).ok = 1
  | 0, _ => Or.inl rfl
  | _ + 1, bs => by
    unfold aggrParseTreeBodyFuel; dsimp only
    split
    · exact Or.inl rfl
    · split
      · split <;> [exact Or.inl rfl; exact Or.inr rfl]
      · split
        · exact Or.inr rfl
        · split
          · split
            · exact Or.inl rfl
            · split <;> [exact Or.inl rfl; exact Or.inr rfl]
          · exact Or.inl rfl

theorem aggrParseTreeBodyFuel_valid :
    ∀ (fuel : Nat) (s : ByteList),
      (aggrParseTreeBodyFuel fuel s).ok = 1 →
      ValidDigestList (aggrParseTreeBodyFuel fuel s).val
  | 0, _, hok => by simp [aggrParseTreeBodyFuel] at hok
  | fuel + 1, s, hok => by
    unfold aggrParseTreeBodyFuel at hok ⊢; dsimp only at hok ⊢
    by_cases ht0 : (readU8 s).ok = 0
    · simp [ht0] at hok
    · have ht0f : ((readU8 s).ok == 0) = false := beq_false_of_ne ht0
      simp only [ht0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases hv0 : (readU8 s).val = 0
      · simp only [hv0, beq_self_eq_true, ↓reduceIte] at hok ⊢
        by_cases ha0 : (readDigest (readU8 s).rest).ok = 0
        · simp [ha0] at hok
        · have ha1 := (readDigest_ok_zero_or_one _).resolve_left ha0
          have ha0f : ((readDigest (readU8 s).rest).ok == 0) = false := beq_false_of_ne ha0
          simp only [ha0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          exact ⟨(readDigest_sound _ ha1).1, trivial⟩
      · have hv0f : ((readU8 s).val == 0) = false := beq_false_of_ne hv0
        simp only [hv0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases hv1 : (readU8 s).val = 1
        · simp only [hv1, beq_self_eq_true, ↓reduceIte] at hok ⊢; trivial
        · have hv1f : ((readU8 s).val == 1) = false := beq_false_of_ne hv1
          simp only [hv1f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          by_cases hv2 : (readU8 s).val = 2
          · simp only [hv2, beq_self_eq_true, ↓reduceIte] at hok ⊢
            by_cases hl0 : (aggrParseTreeBodyFuel fuel (readU8 s).rest).ok = 0
            · simp [hl0] at hok
            · have hl0f : ((aggrParseTreeBodyFuel fuel (readU8 s).rest).ok == 0) = false := beq_false_of_ne hl0
              simp only [hl0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
              by_cases hr0 : (aggrParseTreeBodyFuel fuel (aggrParseTreeBodyFuel fuel (readU8 s).rest).rest).ok = 0
              · simp [hr0] at hok
              · have hr0f : ((aggrParseTreeBodyFuel fuel (aggrParseTreeBodyFuel fuel (readU8 s).rest).rest).ok == 0) = false :=
                  beq_false_of_ne hr0
                simp only [hr0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                exact validDigestList_append
                  (aggrParseTreeBodyFuel_valid fuel _ ((aggrParseTreeBodyFuel_ok_01 _ _).resolve_left hl0))
                  (aggrParseTreeBodyFuel_valid fuel _ ((aggrParseTreeBodyFuel_ok_01 _ _).resolve_left hr0))
          · have hv2f : ((readU8 s).val == 2) = false := beq_false_of_ne hv2
            simp only [hv2f, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

/-- Soundness of `aggrCheckCanonicalTree`: returns a non-empty, valid, strictly sorted leaf list
whose canonical Merkle root equals `root`. -/
theorem aggrCheckCanonicalTree_sound (root : DigestBytes) (treeBytes : ByteList)
    (hok : (aggrCheckCanonicalTree root treeBytes).ok = 1) :
    let r := aggrCheckCanonicalTree root treeBytes
    r.val ≠ .nil ∧ ValidDigestList r.val ∧ StrictSorted r.val ∧
    aggrCanonicalRoot r.val = root := by
  unfold aggrCheckCanonicalTree at hok ⊢; dsimp only at hok ⊢
  split at hok
  · cases hok
  · rename_i ht; rw [ite_eq_right ht]
    split at hok
    · cases hok
    · rename_i hrb0; rw [ite_eq_right hrb0]
      have hrbOk := (aggrParseTreeBodyFuel_ok_01 _ _).resolve_left (by simpa [beq_iff_eq] using hrb0)
      have hvalid := aggrParseTreeBodyFuel_valid _ _ hrbOk
      cases hrest : (aggrParseTreeBodyFuel (byteListLen (readU8 treeBytes).rest + 1) (readU8 treeBytes).rest).rest with
      | cons _ _ => simp [hrest] at hok
      | nil =>
        simp only [hrest] at hok ⊢
        cases hval : (aggrParseTreeBodyFuel (byteListLen (readU8 treeBytes).rest + 1) (readU8 treeBytes).rest).val with
        | nil => simp [hval] at hok
        | cons hd tl =>
          simp only [hval] at hok hvalid ⊢
          split at hok
          · cases hok
          · rename_i hsort; rw [ite_eq_right hsort]
            split at hok
            · cases hok
            · rename_i hroot; rw [ite_eq_right hroot]
              have hsort01 : ∀ xs, aggrAssertStrictSorted xs = 0 ∨ aggrAssertStrictSorted xs = 1 := by
                intro xs; induction xs with
                | nil => exact Or.inr rfl
                | cons a r ih =>
                  cases r with
                  | nil => exact Or.inr rfl
                  | cons b r' =>
                    unfold aggrAssertStrictSorted; dsimp only
                    split
                    · exact ih
                    · exact Or.inl rfl
              have hsort1 := (hsort01 _).resolve_left (by simpa [beq_iff_eq] using hsort)
              have hroot1 := (digestBytesEq_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hroot)
              exact ⟨by simp, hvalid, aggrAssertStrictSorted_sound _ hvalid hsort1,
                (digestBytesEq_eq_one_iff _ _).mp hroot1⟩

theorem aggrCheckOptionalTree_sound (optRoot : OptAddr) (treeBytes : ByteList)
    (hok : (aggrCheckOptionalTree optRoot treeBytes).ok = 1) :
    let r := aggrCheckOptionalTree optRoot treeBytes
    ValidDigestList r.val ∧ StrictSorted r.val ∧
    (optRoot = .none → r.val = .nil) ∧
    (∀ root, optRoot = .some root → r.val ≠ .nil ∧ aggrCanonicalRoot r.val = root) := by
  cases optRoot with
  | none => exact ⟨trivial, trivial, (fun _ => rfl), (fun _ h => by cases h)⟩
  | some root =>
    obtain ⟨hne, hv, hs, hr⟩ := aggrCheckCanonicalTree_sound root treeBytes hok
    exact ⟨hv, hs, (fun h => by cases h), (fun _ h => by injection h with h; subst h; exact ⟨hne, hr⟩)⟩

theorem aggrAssertSameList_eq_one_iff (a b : DigestBytesList) :
    aggrAssertSameList a b = 1 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [aggrAssertSameList]
  | cons x ar ih =>
    cases b with
    | nil => simp [aggrAssertSameList]
    | cons y br =>
      unfold aggrAssertSameList
      by_cases hxy : digestBytesEq x y = 1
      · simp only [hxy, beq_self_eq_true, ↓reduceIte, ih, DigestBytesList.cons.injEq]
        rw [(digestBytesEq_eq_one_iff x y).mp hxy]; simp
      · have hbf : (digestBytesEq x y == 1) = false := beq_false_of_ne hxy
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, DigestBytesList.cons.injEq]
        exact ⟨(fun h => by cases h), fun ⟨heq, _⟩ => absurd ((digestBytesEq_eq_one_iff x y).mpr heq) hxy⟩

theorem aggrAssertUnionFuel_sound :
    ∀ (fuel : Nat) (left right output : DigestBytesList),
      ValidDigestList left → ValidDigestList right →
      aggrAssertUnionFuel fuel left right output = 1 →
      ∀ x, digestBytesListMem x output ↔ digestBytesListMem x left ∨ digestBytesListMem x right
  | 0, _, _, _, _, _, hok => by simp [aggrAssertUnionFuel] at hok
  | fuel + 1, .nil, right, output, _, _, hok => by
    unfold aggrAssertUnionFuel at hok
    have heq := (aggrAssertSameList_eq_one_iff right output).mp hok; subst heq
    intro x; simp [digestBytesListMem, digestBytesListToList]
  | fuel + 1, .cons a ar, .nil, output, _, _, hok => by
    unfold aggrAssertUnionFuel at hok
    have heq := (aggrAssertSameList_eq_one_iff (.cons a ar) output).mp hok; subst heq
    intro x; simp [digestBytesListMem, digestBytesListToList]
  | fuel + 1, .cons _ _, .cons _ _, .nil, _, _, hok => by simp [aggrAssertUnionFuel] at hok
  | fuel + 1, .cons a ar, .cons b br, .cons o or_, hvL, hvR, hok => by
    unfold aggrAssertUnionFuel at hok; dsimp only at hok
    by_cases h0 : aggrAddressOrder a b = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hok
      by_cases hao : digestBytesEq a o = 1
      · simp only [hao, beq_self_eq_true, ↓reduceIte] at hok
        have hEqAO := (digestBytesEq_eq_one_iff a o).mp hao; subst hEqAO
        have ih := aggrAssertUnionFuel_sound fuel ar (.cons b br) or_ hvL.2 hvR hok
        intro x; simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at ih ⊢
        rw [ih x]; tauto
      · have hf : (digestBytesEq a o == 1) = false := beq_false_of_ne hao
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
    · have h0f : (aggrAddressOrder a b == 0) = false := beq_false_of_ne h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte] at hok
      by_cases h1 : aggrAddressOrder a b = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte] at hok
        have hab := (aggrAddressOrder_spec hvL.1 hvR.1).2.1.mp h1; subst hab
        by_cases hao : digestBytesEq a o = 1
        · simp only [hao, beq_self_eq_true, ↓reduceIte] at hok
          have hEqAO := (digestBytesEq_eq_one_iff a o).mp hao; subst hEqAO
          have ih := aggrAssertUnionFuel_sound fuel ar br or_ hvL.2 hvR.2 hok
          intro x; simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at ih ⊢
          rw [ih x]; tauto
        · have hf : (digestBytesEq a o == 1) = false := beq_false_of_ne hao
          simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
      · have h1f : (aggrAddressOrder a b == 1) = false := beq_false_of_ne h1
        simp only [h1f, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hbo : digestBytesEq b o = 1
        · simp only [hbo, beq_self_eq_true, ↓reduceIte] at hok
          have hEqBO := (digestBytesEq_eq_one_iff b o).mp hbo; subst hEqBO
          have ih := aggrAssertUnionFuel_sound fuel (.cons a ar) br or_ hvL hvR.2 hok
          intro x; simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at ih ⊢
          rw [ih x]; tauto
        · have hf : (digestBytesEq b o == 1) = false := beq_false_of_ne hbo
          simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

theorem aggrAssertUnion_sound {left right output : DigestBytesList}
    (hvL : ValidDigestList left) (hvR : ValidDigestList right)
    (hok : aggrAssertUnion left right output = 1) :
    ∀ x, digestBytesListMem x output ↔ digestBytesListMem x left ∨ digestBytesListMem x right :=
  aggrAssertUnionFuel_sound _ left right output hvL hvR hok

theorem aggrAssertDisjointUnionFuel_sound :
    ∀ (fuel : Nat) (left right output : DigestBytesList),
      ValidDigestList left → ValidDigestList right →
      StrictSorted left → StrictSorted right →
      aggrAssertDisjointUnionFuel fuel left right output = 1 →
      (∀ x, digestBytesListMem x left → ¬ digestBytesListMem x right) ∧
      (∀ x, digestBytesListMem x output ↔ digestBytesListMem x left ∨ digestBytesListMem x right)
  | 0, _, _, _, _, _, _, _, hok => by simp [aggrAssertDisjointUnionFuel] at hok
  | fuel + 1, .nil, right, output, _, _, _, _, hok => by
    unfold aggrAssertDisjointUnionFuel at hok
    have heq := (aggrAssertSameList_eq_one_iff right output).mp hok; subst heq
    exact ⟨(fun _ h => by cases h), (fun x => by simp [digestBytesListMem, digestBytesListToList])⟩
  | fuel + 1, .cons a ar, .nil, output, _, _, _, _, hok => by
    unfold aggrAssertDisjointUnionFuel at hok
    have heq := (aggrAssertSameList_eq_one_iff (.cons a ar) output).mp hok; subst heq
    exact ⟨(fun _ _ h => by cases h), (fun x => by simp [digestBytesListMem, digestBytesListToList])⟩
  | fuel + 1, .cons _ _, .cons _ _, .nil, _, _, _, _, hok => by simp [aggrAssertDisjointUnionFuel] at hok
  | fuel + 1, .cons a ar, .cons b br, .cons o or_, hvL, hvR, hsL, hsR, hok => by
    unfold aggrAssertDisjointUnionFuel at hok; dsimp only at hok
    by_cases h0 : aggrAddressOrder a b = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hok
      have hlt := (aggrAddressOrder_spec hvL.1 hvR.1).1.mp h0
      by_cases hao : digestBytesEq a o = 1
      · simp only [hao, beq_self_eq_true, ↓reduceIte] at hok
        have hEqAO := (digestBytesEq_eq_one_iff a o).mp hao; subst hEqAO
        obtain ⟨hdisj, hunion⟩ := aggrAssertDisjointUnionFuel_sound fuel ar (.cons b br) or_
          hvL.2 hvR hsL.2 hsR hok
        refine ⟨fun x hxL hxR => ?_, fun x => ?_⟩
        · rcases List.mem_cons.mp hxL with rfl | htl
          · rcases List.mem_cons.mp hxR with rfl | htr
            · exact Nat.lt_irrefl _ hlt
            · exact Nat.lt_irrefl _ (Nat.lt_trans hlt (hsR.1 x htr))
          · exact hdisj x htl hxR
        · simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at hunion ⊢
          rw [hunion x]; tauto
      · have hf : (digestBytesEq a o == 1) = false := beq_false_of_ne hao
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
    · have h0f : (aggrAddressOrder a b == 0) = false := beq_false_of_ne h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte] at hok
      by_cases h1 : aggrAddressOrder a b = 1
      · simp [h1] at hok
      · have h1f : (aggrAddressOrder a b == 1) = false := beq_false_of_ne h1
        simp only [h1f, Bool.false_eq_true, ↓reduceIte] at hok
        have hgt : aggrAddressKey b < aggrAddressKey a := by
          have hs := aggrAddressOrder_spec hvL.1 hvR.1
          rcases Nat.lt_trichotomy (aggrAddressKey a) (aggrAddressKey b) with hlt | heq | hgt
          · exact absurd (hs.1.mpr hlt) h0
          · exact absurd (hs.2.1.mpr (aggrAddressKey_inj hvL.1 hvR.1 heq)) h1
          · exact hgt
        by_cases hbo : digestBytesEq b o = 1
        · simp only [hbo, beq_self_eq_true, ↓reduceIte] at hok
          have hEqBO := (digestBytesEq_eq_one_iff b o).mp hbo; subst hEqBO
          obtain ⟨hdisj, hunion⟩ := aggrAssertDisjointUnionFuel_sound fuel (.cons a ar) br or_
            hvL hvR.2 hsL hsR.2 hok
          refine ⟨fun x hxL hxR => ?_, fun x => ?_⟩
          · rcases List.mem_cons.mp hxR with rfl | htr
            · rcases List.mem_cons.mp hxL with rfl | htl
              · exact Nat.lt_irrefl _ hgt
              · exact Nat.lt_irrefl _ (Nat.lt_trans hgt (hsL.1 x htl))
            · exact hdisj x hxL htr
          · simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at hunion ⊢
            rw [hunion x]; tauto
        · have hf : (digestBytesEq b o == 1) = false := beq_false_of_ne hbo
          simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

theorem aggrAssertDisjointUnion_sound {left right output : DigestBytesList}
    (hvL : ValidDigestList left) (hvR : ValidDigestList right)
    (hsL : StrictSorted left) (hsR : StrictSorted right)
    (hok : aggrAssertDisjointUnion left right output = 1) :
    (∀ x, digestBytesListMem x left → ¬ digestBytesListMem x right) ∧
    (∀ x, digestBytesListMem x output ↔ digestBytesListMem x left ∨ digestBytesListMem x right) :=
  aggrAssertDisjointUnionFuel_sound _ left right output hvL hvR hsL hsR hok

theorem aggrAssertDisjointFuel_sound :
    ∀ (fuel : Nat) (left right : DigestBytesList),
      ValidDigestList left → ValidDigestList right →
      StrictSorted left → StrictSorted right →
      aggrAssertDisjointFuel fuel left right = 1 →
      ∀ x, digestBytesListMem x left → ¬ digestBytesListMem x right
  | 0, _, _, _, _, _, _, hok => by simp [aggrAssertDisjointFuel] at hok
  | _ + 1, .nil, _, _, _, _, _, _ => fun _ h => by cases h
  | _ + 1, .cons _ _, .nil, _, _, _, _, _ => fun _ _ h => by cases h
  | fuel + 1, .cons a ar, .cons b br, hvL, hvR, hsL, hsR, hok => by
    unfold aggrAssertDisjointFuel at hok; dsimp only at hok
    by_cases h0 : aggrAddressOrder a b = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hok
      have hlt := (aggrAddressOrder_spec hvL.1 hvR.1).1.mp h0
      have ih := aggrAssertDisjointFuel_sound fuel ar (.cons b br) hvL.2 hvR hsL.2 hsR hok
      intro x hxL hxR
      rcases List.mem_cons.mp hxL with rfl | htl
      · rcases List.mem_cons.mp hxR with rfl | htr
        · exact Nat.lt_irrefl _ hlt
        · exact Nat.lt_irrefl _ (Nat.lt_trans hlt (hsR.1 x htr))
      · exact ih x htl hxR
    · have h0f : (aggrAddressOrder a b == 0) = false := beq_false_of_ne h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte] at hok
      by_cases h1 : aggrAddressOrder a b = 1
      · simp [h1] at hok
      · have h1f : (aggrAddressOrder a b == 1) = false := beq_false_of_ne h1
        simp only [h1f, Bool.false_eq_true, ↓reduceIte] at hok
        have hgt : aggrAddressKey b < aggrAddressKey a := by
          have hs := aggrAddressOrder_spec hvL.1 hvR.1
          rcases Nat.lt_trichotomy (aggrAddressKey a) (aggrAddressKey b) with hlt | heq | hgt
          · exact absurd (hs.1.mpr hlt) h0
          · exact absurd (hs.2.1.mpr (aggrAddressKey_inj hvL.1 hvR.1 heq)) h1
          · exact hgt
        have ih := aggrAssertDisjointFuel_sound fuel (.cons a ar) br hvL hvR.2 hsL hsR.2 hok
        intro x hxL hxR
        rcases List.mem_cons.mp hxR with rfl | htr
        · rcases List.mem_cons.mp hxL with rfl | htl
          · exact Nat.lt_irrefl _ hgt
          · exact Nat.lt_irrefl _ (Nat.lt_trans hgt (hsL.1 x htl))
        · exact ih x hxL htr

theorem aggrAssertDisjoint_sound {left right : DigestBytesList}
    (hvL : ValidDigestList left) (hvR : ValidDigestList right)
    (hsL : StrictSorted left) (hsR : StrictSorted right)
    (hok : aggrAssertDisjoint left right = 1) :
    ∀ x, digestBytesListMem x left → ¬ digestBytesListMem x right :=
  aggrAssertDisjointFuel_sound _ left right hvL hvR hsL hsR hok

theorem aggrSeekSubject_sound (target : DigestBytes) (ht : ValidDigestBytes target) :
    ∀ (subjects : DigestBytesList), ValidDigestList subjects → StrictSorted subjects →
      let sk := aggrSeekSubject target subjects
      ValidDigestList sk.rest ∧ StrictSorted sk.rest ∧
      (sk.found = 1 → digestBytesListMem target subjects) ∧
      (∀ x, digestBytesListMem x sk.rest → digestBytesListMem x subjects)
  | .nil, _, _ => ⟨trivial, trivial, (fun h => by cases h), fun _ h => h⟩
  | .cons subj rest, hv, hs => by
    unfold aggrSeekSubject; dsimp only
    by_cases h0 : aggrAddressOrder subj target = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte]
      obtain ⟨hvr, hsr, hfd, hsub⟩ := aggrSeekSubject_sound target ht rest hv.2 hs.2
      exact ⟨hvr, hsr, fun h1 => List.mem_cons_of_mem _ (hfd h1),
        fun x hx => List.mem_cons_of_mem _ (hsub x hx)⟩
    · have h0f : (aggrAddressOrder subj target == 0) = false := beq_false_of_ne h0
      simp only [h0f, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : aggrAddressOrder subj target = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte]
        have heq := (aggrAddressOrder_spec hv.1 ht).2.1.mp h1; subst heq
        exact ⟨hv.2, hs.2, fun _ => List.mem_cons_self, fun x hx => List.mem_cons_of_mem _ hx⟩
      · have h1f : (aggrAddressOrder subj target == 1) = false := beq_false_of_ne h1
        simp only [h1f, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hv, hs, (fun h => by cases h), fun _ h => h⟩

theorem aggrNextAssumption_spec {left right : DigestBytesList}
    (hvL : ValidDigestList left) (hvR : ValidDigestList right)
    (hsL : StrictSorted left) (hsR : StrictSorted right) :
    match aggrNextAssumption left right with
    | .done => left = .nil ∧ right = .nil
    | .more cand src lr rr =>
      ValidDigestBytes cand ∧ ValidDigestList lr ∧ ValidDigestList rr ∧
      StrictSorted lr ∧ StrictSorted rr ∧
      (∀ x, digestBytesListMem x left ↔ (((src = 0 ∨ src = 1) ∧ x = cand) ∨ digestBytesListMem x lr)) ∧
      (∀ x, digestBytesListMem x right ↔ (((src = 1 ∨ src = 2) ∧ x = cand) ∨ digestBytesListMem x rr)) ∧
      (∀ x, (digestBytesListMem x left ∨ digestBytesListMem x right) ↔
        x = cand ∨ digestBytesListMem x lr ∨ digestBytesListMem x rr) := by
  cases left with
  | nil =>
    cases right with
    | nil => exact ⟨rfl, rfl⟩
    | cons b br =>
      refine ⟨hvR.1, trivial, hvR.2, trivial, hsR.2,
        fun x => by simp [digestBytesListMem, digestBytesListToList],
        fun x => by simp [digestBytesListMem, digestBytesListToList],
        fun x => by simp [digestBytesListMem, digestBytesListToList]⟩
  | cons a ar =>
    cases right with
    | nil =>
      refine ⟨hvL.1, hvL.2, trivial, hsL.2, trivial,
        fun x => by simp [digestBytesListMem, digestBytesListToList],
        fun x => by simp [digestBytesListMem, digestBytesListToList],
        fun x => by simp [digestBytesListMem, digestBytesListToList]⟩
    | cons b br =>
      unfold aggrNextAssumption; dsimp only
      by_cases h0 : aggrAddressOrder a b = 0
      · simp only [h0, beq_self_eq_true, ↓reduceIte]
        refine ⟨hvL.1, hvL.2, hvR, hsL.2, hsR,
          fun x => by simp [digestBytesListMem, digestBytesListToList],
          fun x => by simp [digestBytesListMem, digestBytesListToList],
          fun x => by simp only [digestBytesListMem, digestBytesListToList, List.mem_cons]; tauto⟩
      · have h0f : (aggrAddressOrder a b == 0) = false := beq_false_of_ne h0
        simp only [h0f, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : aggrAddressOrder a b = 1
        · simp only [h1, beq_self_eq_true, ↓reduceIte]
          have hab := (aggrAddressOrder_spec hvL.1 hvR.1).2.1.mp h1; subst hab
          refine ⟨hvL.1, hvL.2, hvR.2, hsL.2, hsR.2,
            fun x => by simp [digestBytesListMem, digestBytesListToList],
            fun x => by simp [digestBytesListMem, digestBytesListToList],
            fun x => by simp only [digestBytesListMem, digestBytesListToList, List.mem_cons]; tauto⟩
        · have h1f : (aggrAddressOrder a b == 1) = false := beq_false_of_ne h1
          simp only [h1f, Bool.false_eq_true, ↓reduceIte]
          refine ⟨hvR.1, hvL, hvR.2, hsL, hsR.2,
            fun x => by simp [digestBytesListMem, digestBytesListToList],
            fun x => by simp [digestBytesListMem, digestBytesListToList],
            fun x => by simp only [digestBytesListMem, digestBytesListToList, List.mem_cons]; tauto⟩

theorem aggrAssertDifferenceFuel_sound :
    ∀ (fuel : Nat) (left right subjects output : DigestBytesList),
      ValidDigestList left → ValidDigestList right → ValidDigestList subjects →
      StrictSorted left → StrictSorted right → StrictSorted subjects →
      aggrAssertDifferenceFuel fuel left right subjects output = 1 →
      (∀ x, (digestBytesListMem x left ∨ digestBytesListMem x right) →
        ¬ digestBytesListMem x output → digestBytesListMem x subjects) ∧
      (∀ x, digestBytesListMem x output →
        digestBytesListMem x left ∨ digestBytesListMem x right)
  | 0, _, _, _, _, _, _, _, _, _, _, hok => by simp [aggrAssertDifferenceFuel] at hok
  | fuel + 1, left, right, subjects, output, hvL, hvR, hvS, hsL, hsR, hsS, hok => by
    unfold aggrAssertDifferenceFuel at hok
    have hnext := aggrNextAssumption_spec hvL hvR hsL hsR
    cases hna : aggrNextAssumption left right with
    | done =>
      rw [hna] at hok hnext; obtain ⟨rfl, rfl⟩ := hnext
      cases output with
      | nil => exact ⟨(fun _ h => by rcases h with h | h <;> cases h), (fun _ h => by cases h)⟩
      | cons _ _ => simp at hok
    | more cand src lr rr =>
      rw [hna] at hok hnext
      obtain ⟨hvc, hvlr, hvrr, hslr, hsrr, _, _, hiff⟩ := hnext
      dsimp only at hok
      have hsk := aggrSeekSubject_sound cand hvc subjects hvS hsS
      by_cases hfd : (aggrSeekSubject cand subjects).found = 1
      · simp only [hfd, beq_self_eq_true, ↓reduceIte] at hok
        obtain ⟨hdisc, hsub⟩ := aggrAssertDifferenceFuel_sound fuel lr rr
          (aggrSeekSubject cand subjects).rest output hvlr hvrr hsk.1 hslr hsrr hsk.2.1 hok
        refine ⟨fun x hx hxOut => ?_, fun x hxOut => (hiff x).mpr (Or.inr (hsub x hxOut))⟩
        rcases (hiff x).mp hx with rfl | hxRest
        · exact hsk.2.2.1 hfd
        · exact hsk.2.2.2 x (hdisc x hxRest hxOut)
      · have hfdf : ((aggrSeekSubject cand subjects).found == 1) = false := beq_false_of_ne hfd
        simp only [hfdf, Bool.false_eq_true, ↓reduceIte] at hok
        cases output with
        | nil => cases hok
        | cons actual outRest =>
          by_cases heq : digestBytesEq cand actual = 1
          · simp only [heq, beq_self_eq_true, ↓reduceIte] at hok
            have hca := (digestBytesEq_eq_one_iff cand actual).mp heq; subst hca
            obtain ⟨hdisc, hsub⟩ := aggrAssertDifferenceFuel_sound fuel lr rr
              (aggrSeekSubject cand subjects).rest outRest hvlr hvrr hsk.1 hslr hsrr hsk.2.1 hok
            refine ⟨fun x hx hxOut => ?_, fun x hxOut => ?_⟩
            · rcases (hiff x).mp hx with rfl | hxRest
              · exact absurd List.mem_cons_self hxOut
              · exact hsk.2.2.2 x (hdisc x hxRest (fun hm => hxOut (List.mem_cons_of_mem _ hm)))
            · rcases List.mem_cons.mp hxOut with rfl | htl
              · exact (hiff x).mpr (Or.inl rfl)
              · exact (hiff x).mpr (Or.inr (hsub x htl))
          · have hf : (digestBytesEq cand actual == 1) = false := beq_false_of_ne heq
            simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

/-- **Flat Pair Cross-Discharge → `Aggr.JoinRel`:**
The four checks in `verifyShapePairFlat` establish `Aggr.JoinRel` directly. -/
theorem joinRel_of_aggrPair_checks
    {SL AL SR AR Sout Aout : DigestBytesList}
    (hvSL : ValidDigestList SL) (hvAL : ValidDigestList AL)
    (hvSR : ValidDigestList SR) (hvAR : ValidDigestList AR)
    (hvSout : ValidDigestList Sout)
    (hsSL : StrictSorted SL) (hsAL : StrictSorted AL)
    (hsSR : StrictSorted SR) (hsAR : StrictSorted AR)
    (hsSout : StrictSorted Sout)
    (hDisjL : aggrAssertDisjoint SL AL = 1)
    (hDisjR : aggrAssertDisjoint SR AR = 1)
    (hUnion : aggrAssertDisjointUnion SL SR Sout = 1)
    (hDiff : aggrAssertDifference AL AR Sout Aout = 1) :
    _root_.Aggr.JoinRel
      (fun x => digestBytesListMem x SL) (fun x => digestBytesListMem x AL)
      (fun x => digestBytesListMem x SR) (fun x => digestBytesListMem x AR)
      (fun x => digestBytesListMem x Sout) (fun x => digestBytesListMem x Aout) := by
  have hdl := aggrAssertDisjoint_sound hvSL hvAL hsSL hsAL hDisjL
  have hdr := aggrAssertDisjoint_sound hvSR hvAR hsSR hsAR hDisjR
  obtain ⟨_, hSubj⟩ := aggrAssertDisjointUnion_sound hvSL hvSR hsSL hsSR hUnion
  obtain ⟨hDisc, hSub⟩ := aggrAssertDifferenceFuel_sound _ AL AR Sout Aout hvAL hvAR hvSout hsAL hsAR hsSout hDiff
  exact
    { subjects_iff := hSubj
      discharge_left := fun x hxAL hxNotOut => by
        rcases (hSubj x).mp (hDisc x (Or.inl hxAL) hxNotOut) with hxSL | hxSR
        · exact absurd hxAL (hdl x hxSL)
        · exact hxSR
      discharge_right := fun x hxAR hxNotOut => by
        rcases (hSubj x).mp (hDisc x (Or.inr hxAR) hxNotOut) with hxSL | hxSR
        · exact hxSL
        · exact absurd hxAR (hdr x hxSR)
      assumptions_sub := hSub }

/-- Merkle inclusion path witness produced by `aggrFoldPath`. -/
inductive AggrMerklePathTo (root : DigestBytes) : DigestBytes → Prop where
  | refl : AggrMerklePathTo root root
  | stepLeft {h sib : DigestBytes} :
      ValidDigestBytes sib →
      AggrMerklePathTo root (aggrNodeHash sib h) →
      AggrMerklePathTo root h
  | stepRight {h sib : DigestBytes} :
      ValidDigestBytes sib →
      AggrMerklePathTo root (aggrNodeHash h sib) →
      AggrMerklePathTo root h

theorem aggrFoldPath_sound :
    ∀ (rem : Nat) (h : DigestBytes) (s : ByteList),
      (aggrFoldPath h rem s).ok = 1 →
      AggrMerklePathTo (aggrFoldPath h rem s).val h
  | 0, _, _, _ => .refl
  | rem + 1, h, s, hok => by
    unfold aggrFoldPath at hok ⊢; dsimp only at hok ⊢
    split at hok
    · cases hok
    · rename_i hside; rw [ite_eq_right hside]
      split at hok
      · cases hok
      · rename_i hsib; rw [ite_eq_right hsib]
        have hsib1 := (readDigest_ok_zero_or_one _).resolve_left (by simpa [beq_iff_eq] using hsib)
        have hvsib := (readDigest_sound _ hsib1).1
        have ih := aggrFoldPath_sound rem _ _ hok
        by_cases h0 : (readU8 s).val = 0
        · simp only [h0, beq_self_eq_true, ↓reduceIte] at ih ⊢
          exact .stepLeft hvsib ih
        · have h0f : ((readU8 s).val == 0) = false := beq_false_of_ne h0
          simp only [h0f, Bool.false_eq_true, ↓reduceIte] at ih ⊢
          exact .stepRight hvsib ih

/-- Soundness of `aggrVerifyDischargeChoice`: shared assumptions (`source = 1`) can never be
discharged; any discharge (`val = 1`) proves a valid `AggrMerklePathTo` into the opposite root. -/
theorem aggrVerifyDischargeChoice_sound (cand : DigestBytes) (source : Nat)
    (leftRoot rightRoot : DigestBytes) (choiceBytes : ByteList)
    (hok : (aggrVerifyDischargeChoice cand source leftRoot rightRoot choiceBytes).ok = 1) :
    let r := aggrVerifyDischargeChoice cand source leftRoot rightRoot choiceBytes
    (r.val = 0) ∨
    (r.val = 1 ∧
      ((source = 0 ∧ AggrMerklePathTo rightRoot (aggrLeafHash cand)) ∨
       (source = 2 ∧ AggrMerklePathTo leftRoot (aggrLeafHash cand)))) := by
  unfold aggrVerifyDischargeChoice at hok ⊢; dsimp only at hok ⊢
  split at hok
  · cases hok
  · rename_i hrc; rw [ite_eq_right hrc]
    split at hok
    · rename_i hc0; rw [ite_eq_left hc0]
      cases hr : (readU8 choiceBytes).rest with
      | cons _ _ => simp [hr] at hok
      | nil => exact Or.inl rfl
    · rename_i hc0; rw [ite_eq_right hc0]
      split at hok
      · cases hok
      · rename_i hcnt; rw [ite_eq_right hcnt]
        split at hok
        · cases hok
        · rename_i hfold; rw [ite_eq_right hfold]
          have hfold01 : ∀ n h bs, (aggrFoldPath h n bs).ok = 0 ∨ (aggrFoldPath h n bs).ok = 1 := by
            intro n; induction n with
            | zero => intro _ _; exact Or.inr rfl
            | succ n ih =>
              intro h bs; unfold aggrFoldPath; dsimp only
              split
              · exact Or.inl rfl
              · split
                · exact Or.inl rfl
                · exact ih _ _
          have hfold1 := (hfold01 _ _ _).resolve_left (by simpa [beq_iff_eq] using hfold)
          have hpath := aggrFoldPath_sound _ _ _ hfold1
          split at hok
          · cases hok
          · rename_i hls; rw [ite_eq_right hls]
            split at hok
            · cases hok
            · rename_i hlsib; rw [ite_eq_right hlsib]
              cases hrest : (readDigest (readU8 (aggrFoldPath (aggrLeafHash cand)
                  ((readU8 (readU8 choiceBytes).rest).val - 1)
                  (readU8 (readU8 choiceBytes).rest).rest).rest).rest).rest with
              | cons _ _ => simp [hrest] at hok
              | nil =>
                simp only [hrest] at hok ⊢
                split at hok
                · rename_i hs0; rw [ite_eq_left hs0]
                  split at hok
                  · rename_i hchk; rw [ite_eq_left hchk]
                    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
                    rw [(digestBytesEq_eq_one_iff _ _).mp hchk.2] at hpath
                    exact Or.inr ⟨rfl, Or.inl ⟨by simpa [beq_iff_eq] using hs0, hpath⟩⟩
                  · cases hok
                · rename_i hs0; rw [ite_eq_right hs0]
                  split at hok
                  · rename_i hs2; rw [ite_eq_left hs2]
                    split at hok
                    · rename_i hchk; rw [ite_eq_left hchk]
                      simp only [Bool.and_eq_true, beq_iff_eq] at hchk
                      rw [(digestBytesEq_eq_one_iff _ _).mp hchk.2] at hpath
                      exact Or.inr ⟨rfl, Or.inr ⟨by simpa [beq_iff_eq] using hs2, hpath⟩⟩
                    · cases hok
                  · cases hok

/-- Soundness of `aggrAssertStructuralDifferenceFuel`: every discharged left assumption carries
a Merkle path to `rightRoot`, every discharged right assumption carries a Merkle path to `leftRoot`,
and `output ⊆ left ∪ right`. -/
theorem aggrAssertStructuralDifferenceFuel_sound :
    ∀ (fuel : Nat) (left right : DigestBytesList) (leftRoot rightRoot : DigestBytes)
      (output : DigestBytesList) (paths : PathTable),
      ValidDigestList left → ValidDigestList right →
      StrictSorted left → StrictSorted right →
      aggrAssertStructuralDifferenceFuel fuel left right leftRoot rightRoot output paths = 1 →
      (∀ x, digestBytesListMem x left → ¬ digestBytesListMem x output →
        AggrMerklePathTo rightRoot (aggrLeafHash x)) ∧
      (∀ x, digestBytesListMem x right → ¬ digestBytesListMem x output →
        AggrMerklePathTo leftRoot (aggrLeafHash x)) ∧
      (∀ x, digestBytesListMem x output →
        digestBytesListMem x left ∨ digestBytesListMem x right)
  | 0, _, _, _, _, _, _, _, _, _, _, hok => by simp [aggrAssertStructuralDifferenceFuel] at hok
  | fuel + 1, left, right, leftRoot, rightRoot, output, paths, hvL, hvR, hsL, hsR, hok => by
    unfold aggrAssertStructuralDifferenceFuel at hok
    have hnext := aggrNextAssumption_spec hvL hvR hsL hsR
    cases hna : aggrNextAssumption left right with
    | done =>
      rw [hna] at hok hnext; obtain ⟨rfl, rfl⟩ := hnext
      cases output with
      | nil => exact ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩
      | cons _ _ => simp at hok
    | more cand src lr rr =>
      rw [hna] at hok hnext
      obtain ⟨_, hvlr, hvrr, hslr, hsrr, hleftIff, hrightIff, hiff⟩ := hnext
      dsimp only at hok
      have hdc01 : ∀ c sr l r bs, (aggrVerifyDischargeChoice c sr l r bs).ok = 0 ∨
          (aggrVerifyDischargeChoice c sr l r bs).ok = 1 := by
        intro c sr l r bs; unfold aggrVerifyDischargeChoice; dsimp only
        split; · exact Or.inl rfl
        split
        · split
          · exact Or.inr rfl
          · exact Or.inl rfl
        · split; · exact Or.inl rfl
          split; · exact Or.inl rfl
          split; · exact Or.inl rfl
          split; · exact Or.inl rfl
          split
          · exact Or.inl rfl
          · split
            · split
              · exact Or.inr rfl
              · exact Or.inl rfl
            · split
              · split
                · exact Or.inr rfl
                · exact Or.inl rfl
              · exact Or.inl rfl
      by_cases hdc0 : (aggrVerifyDischargeChoice cand src leftRoot rightRoot (pathTableLookup paths cand)).ok = 0
      · simp [hdc0] at hok
      · have hdc1 := (hdc01 _ _ _ _ _).resolve_left hdc0
        have hdcSpec := aggrVerifyDischargeChoice_sound cand src leftRoot rightRoot
          (pathTableLookup paths cand) hdc1
        have hdc0f : ((aggrVerifyDischargeChoice cand src leftRoot rightRoot
            (pathTableLookup paths cand)).ok == 0) = false := beq_false_of_ne hdc0
        simp only [hdc0f, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hval1 : (aggrVerifyDischargeChoice cand src leftRoot rightRoot (pathTableLookup paths cand)).val = 1
        · simp only [hval1, beq_self_eq_true, ↓reduceIte] at hok
          obtain ⟨hDL, hDR, hSub⟩ := aggrAssertStructuralDifferenceFuel_sound fuel lr rr leftRoot rightRoot
            output paths hvlr hvrr hslr hsrr hok
          rcases hdcSpec with hv0 | ⟨_, ⟨rfl, hpathR⟩ | ⟨rfl, hpathL⟩⟩
          · rw [hv0] at hval1; cases hval1
          · refine ⟨fun x hxL hxOut => ?_, fun x hxR hxOut => ?_, fun x hxOut => (hiff x).mpr (Or.inr (hSub x hxOut))⟩
            · rcases (hleftIff x).mp hxL with ⟨_, rfl⟩ | hxlr
              · exact hpathR
              · exact hDL x hxlr hxOut
            · rcases (hrightIff x).mp hxR with ⟨hbad, _⟩ | hxrr
              · rcases hbad with h | h <;> cases h
              · exact hDR x hxrr hxOut
          · refine ⟨fun x hxL hxOut => ?_, fun x hxR hxOut => ?_, fun x hxOut => (hiff x).mpr (Or.inr (hSub x hxOut))⟩
            · rcases (hleftIff x).mp hxL with ⟨hbad, _⟩ | hxlr
              · rcases hbad with h | h <;> cases h
              · exact hDL x hxlr hxOut
            · rcases (hrightIff x).mp hxR with ⟨_, rfl⟩ | hxrr
              · exact hpathL
              · exact hDR x hxrr hxOut
        · have hv1f : ((aggrVerifyDischargeChoice cand src leftRoot rightRoot
              (pathTableLookup paths cand)).val == 1) = false := beq_false_of_ne hval1
          simp only [hv1f, Bool.false_eq_true, ↓reduceIte] at hok
          cases output with
          | nil => cases hok
          | cons actual outRest =>
            by_cases heq : digestBytesEq cand actual = 1
            · simp only [heq, beq_self_eq_true, ↓reduceIte] at hok
              have hca := (digestBytesEq_eq_one_iff cand actual).mp heq; subst hca
              obtain ⟨hDL, hDR, hSub⟩ := aggrAssertStructuralDifferenceFuel_sound fuel lr rr leftRoot rightRoot
                outRest paths hvlr hvrr hslr hsrr hok
              refine ⟨fun x hxL hxOut => ?_, fun x hxR hxOut => ?_, fun x hxOut => ?_⟩
              · rcases (hleftIff x).mp hxL with ⟨_, rfl⟩ | hxlr
                · exact absurd List.mem_cons_self hxOut
                · exact hDL x hxlr (fun hm => hxOut (List.mem_cons_of_mem _ hm))
              · rcases (hrightIff x).mp hxR with ⟨_, rfl⟩ | hxrr
                · exact absurd List.mem_cons_self hxOut
                · exact hDR x hxrr (fun hm => hxOut (List.mem_cons_of_mem _ hm))
              · rcases List.mem_cons.mp hxOut with rfl | htl
                · exact (hiff x).mpr (Or.inl rfl)
                · exact (hiff x).mpr (Or.inr (hSub x htl))
            · have hf : (digestBytesEq cand actual == 1) = false := beq_false_of_ne heq
              simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

theorem aggrAssertStructuralDifference_sound {left right : DigestBytesList}
    {leftRoot rightRoot : DigestBytes} {output : DigestBytesList} {paths : PathTable}
    (hvL : ValidDigestList left) (hvR : ValidDigestList right)
    (hsL : StrictSorted left) (hsR : StrictSorted right)
    (hok : aggrAssertStructuralDifference left right leftRoot rightRoot output paths = 1) :
    (∀ x, digestBytesListMem x left → ¬ digestBytesListMem x output →
      AggrMerklePathTo rightRoot (aggrLeafHash x)) ∧
    (∀ x, digestBytesListMem x right → ¬ digestBytesListMem x output →
      AggrMerklePathTo leftRoot (aggrLeafHash x)) ∧
    (∀ x, digestBytesListMem x output →
      digestBytesListMem x left ∨ digestBytesListMem x right) :=
  aggrAssertStructuralDifferenceFuel_sound _ left right leftRoot rightRoot output paths hvL hvR hsL hsR hok

/-- **Single-Leaf Removal Soundness (`aggrExtractRemovedLeaf_sound` → `Aggr.EvalRemoveRel`):**
On strictly sorted lists `before`, `after`, `aggrExtractRemovedLeaf` returning `ok = 1`
establishes exact `Aggr.EvalRemoveRel`! -/
theorem aggrExtractRemovedLeaf_sound :
    ∀ (before after : DigestBytesList),
      StrictSorted before →
      (aggrExtractRemovedLeaf before after).ok = 1 →
      _root_.Aggr.EvalRemoveRel
        (fun x => digestBytesListMem x before)
        (fun x => digestBytesListMem x after)
        (aggrExtractRemovedLeaf before after).removed
  | .nil, _, _, hok => by simp [aggrExtractRemovedLeaf] at hok
  | .cons a ar, .nil, _, hok => by
    unfold aggrExtractRemovedLeaf at hok ⊢
    cases ar with
    | cons _ _ => simp at hok
    | nil =>
      exact
        { removed_mem := List.mem_cons_self
          removed_not_after := fun h => by cases h
          before_iff := fun x => by simp [digestBytesListMem, digestBytesListToList] }
  | .cons a ar, .cons b br, hsB, hok => by
    unfold aggrExtractRemovedLeaf at hok ⊢; dsimp only at hok ⊢
    by_cases hab : digestBytesEq a b = 1
    · simp only [hab, beq_self_eq_true, ↓reduceIte] at hok ⊢
      have hEqAB := (digestBytesEq_eq_one_iff a b).mp hab; subst hEqAB
      have ih := aggrExtractRemovedLeaf_sound ar br hsB.2 hok
      exact
        { removed_mem := List.mem_cons_of_mem _ ih.removed_mem
          removed_not_after := fun hm => by
            rcases List.mem_cons.mp hm with heq | htl
            · exact Nat.lt_irrefl _ (heq ▸ hsB.1 _ ih.removed_mem)
            · exact ih.removed_not_after htl
          before_iff := fun x => by
            have h := ih.before_iff x
            simp only [digestBytesListMem, digestBytesListToList, List.mem_cons] at h ⊢
            rw [h]; tauto }
    · have habf : (digestBytesEq a b == 1) = false := beq_false_of_ne hab
      simp only [habf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases hsame : aggrAssertSameList ar (.cons b br) = 1
      · simp only [hsame, beq_self_eq_true, ↓reduceIte] at hok ⊢
        have hEqAr := (aggrAssertSameList_eq_one_iff ar (.cons b br)).mp hsame
        exact
          { removed_mem := List.mem_cons_self
            removed_not_after := fun hm => by
              rw [← hEqAr] at hm
              exact Nat.lt_irrefl _ (hsB.1 a hm)
            before_iff := fun x => by
              simp [digestBytesListMem, digestBytesListToList, hEqAr] }
      · have hf : (aggrAssertSameList ar (.cons b br) == 1) = false := beq_false_of_ne hsame
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

/-! ### Allowed-Blob Identity Pin & Child Proof Verification Soundness -/

/-- Complete mathematical postcondition of `parseAllowedBlob`: exact 80-byte valid byte stream,
BLAKE3 digest match against `allowedDigest`, and canonical `(ixvmVkDigest, verifyIdx, selfVkDigest, aggrIdx)`. -/
structure AllowedBlobAccepted (allowedDigest : Digest32Words) (allowedBytes : ByteList)
    (ap : AllowedParams) : Prop where
  len_eq_80 : byteListLen allowedBytes = 80
  valid_bytes : ValidBytes allowedBytes
  digest_eq : packDigest (blake3HashBytes allowedBytes) = allowedDigest
  pure_blake3_eq : digest32ToBytes (blake3HashBytes allowedBytes) =
    Blake3.Pure.digest (byteListToUInt8List allowedBytes)
  fields : ∃ (ixvmAddr : DigestBytes) (verifyIdxLimb : U64Bytes)
      (selfAddr : DigestBytes) (aggrIdxLimb : U64Bytes),
    allowedBytes =
      digestBytesOnto ixvmAddr (u64BytesOnto verifyIdxLimb
        (digestBytesOnto selfAddr (u64BytesOnto aggrIdxLimb .nil))) ∧
    ValidDigestBytes ixvmAddr ∧
    ValidDigestBytes selfAddr ∧
    u64BytesToNat verifyIdxLimb < glPrime ∧
    u64BytesToNat aggrIdxLimb < glPrime ∧
    ap =
      { ixvmVkDigest := packAddress ixvmAddr
        verifyIdx := u64BytesToNat verifyIdxLimb
        selfVkDigest := packAddress selfAddr
        aggrIdx := u64BytesToNat aggrIdxLimb }

theorem parseAllowedBlob_sound {allowedDigest : Digest32Words} {allowedBytes : ByteList}
    (hok : (parseAllowedBlob allowedDigest allowedBytes).ok = 1) :
    AllowedBlobAccepted allowedDigest allowedBytes (parseAllowedBlob allowedDigest allowedBytes).val := by
  unfold parseAllowedBlob at hok ⊢; dsimp only at hok ⊢
  split at hok
  · cases hok
  · rename_i hlen; rw [ite_eq_right hlen]
    have hlen80 : byteListLen allowedBytes = 80 := by simpa [bne_iff_ne] using hlen
    split at hok
    · cases hok
    · rename_i hdig; rw [ite_eq_right hdig]
      have hdig1 := (digest32WordsEq_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hdig)
      have hdigEq := (digest32WordsEq_eq_one_iff _ _).mp hdig1
      split at hok
      · cases hok
      · rename_i hix0; rw [ite_eq_right hix0]
        have hix1 := (readDigest_ok_zero_or_one _).resolve_left (by simpa [beq_iff_eq] using hix0)
        obtain ⟨hvIx, hsIx, _⟩ := readDigest_sound allowedBytes hix1
        split at hok
        · cases hok
        · rename_i hvidx0; rw [ite_eq_right hvidx0]
          have hvidxCond : (readU64LE (readDigest allowedBytes).rest).ok ≠ 0 ∧
              glLtPBytes (readU64LE (readDigest allowedBytes).rest).val ≠ 0 := by
            simpa [Bool.or_eq_true, beq_iff_eq, not_or] using hvidx0
          have hvidx1 := (readU64LE_ok_zero_or_one _).resolve_left hvidxCond.1
          have hvidxLt1 := (glLtPBytes_zero_or_one _).resolve_left hvidxCond.2
          obtain ⟨hvV, hsV, _⟩ := readU64LE_sound _ hvidx1
          obtain ⟨hvalV, _⟩ := glValBytes_of_ltP hvV hvidxLt1
          split at hok
          · cases hok
          · rename_i hself0; rw [ite_eq_right hself0]
            have hself1 := (readDigest_ok_zero_or_one _).resolve_left (by simpa [beq_iff_eq] using hself0)
            obtain ⟨hvSelf, hsSelf, _⟩ := readDigest_sound _ hself1
            split at hok
            · cases hok
            · rename_i haidx0; rw [ite_eq_right haidx0]
              have haidxCond : (readU64LE (readDigest (readU64LE (readDigest allowedBytes).rest).rest).rest).ok ≠ 0 ∧
                  glLtPBytes (readU64LE (readDigest (readU64LE (readDigest allowedBytes).rest).rest).rest).val ≠ 0 := by
                simpa [Bool.or_eq_true, beq_iff_eq, not_or] using haidx0
              have haidx1 := (readU64LE_ok_zero_or_one _).resolve_left haidxCond.1
              have haidxLt1 := (glLtPBytes_zero_or_one _).resolve_left haidxCond.2
              obtain ⟨hvA, hsA, _⟩ := readU64LE_sound _ haidx1
              obtain ⟨hvalA, _⟩ := glValBytes_of_ltP hvA haidxLt1
              cases hrest : (readU64LE (readDigest (readU64LE (readDigest allowedBytes).rest).rest).rest).rest with
              | cons _ _ => simp [hrest] at hok
              | nil =>
                simp only [hrest] at hsA ⊢
                have hbytesEq : allowedBytes =
                    digestBytesOnto (readDigest allowedBytes).val
                      (u64BytesOnto (readU64LE (readDigest allowedBytes).rest).val
                        (digestBytesOnto (readDigest (readU64LE (readDigest allowedBytes).rest).rest).val
                          (u64BytesOnto (readU64LE (readDigest (readU64LE (readDigest allowedBytes).rest).rest).rest).val .nil))) :=
                  hsIx.trans (congrArg _ (hsV.trans (congrArg _ (hsSelf.trans (congrArg _ hsA)))))
                have hvalidBytes : ValidBytes allowedBytes := by
                  rw [hbytesEq]
                  unfold digestBytesOnto
                  repeat rw [validBytes_u64BytesOnto]
                  exact ⟨hvIx.1, hvIx.2.1, hvIx.2.2.1, hvIx.2.2.2, hvV,
                    hvSelf.1, hvSelf.2.1, hvSelf.2.2.1, hvSelf.2.2.2, hvA, trivial⟩
                exact
                  { len_eq_80 := hlen80
                    valid_bytes := hvalidBytes
                    digest_eq := hdigEq
                    pure_blake3_eq := blake3HashBytes_eq_pure hvalidBytes (by omega)
                    fields := ⟨(readDigest allowedBytes).val,
                      (readU64LE (readDigest allowedBytes).rest).val,
                      (readDigest (readU64LE (readDigest allowedBytes).rest).rest).val,
                      (readU64LE (readDigest (readU64LE (readDigest allowedBytes).rest).rest).rest).val,
                      hbytesEq, hvIx, hvSelf,
                      (glLtPBytes_eq_one_iff hvV).mp hvidxLt1,
                      (glLtPBytes_eq_one_iff hvA).mp haidxLt1,
                      by rw [hvalV, hvalA]⟩ }

private theorem assertSameClaims_zero_or_one (a b : U64ListList) :
    assertSameClaims a b = 0 ∨ assertSameClaims a b = 1 := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact Or.inr rfl
    | cons _ _ => exact Or.inl rfl
  | cons x ra ih =>
    cases b with
    | nil => exact Or.inl rfl
    | cons y rb =>
      unfold assertSameClaims; dsimp only
      split
      · exact ih rb
      · exact Or.inl rfl

private theorem verifyRootBytesWithFloor_zero_or_one (ef : Nat)
    (r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (keyBytes claimsBytes proofBytes : ByteList) :
    verifyRootBytesWithFloor ef r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 keyBytes claimsBytes proofBytes = 0 ∨
    verifyRootBytesWithFloor ef r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 keyBytes claimsBytes proofBytes = 1 := by
  unfold verifyRootBytesWithFloor
  extract_lets stmt pSys pClaims pBatch vb
  clear_value stmt pSys pClaims pBatch vb
  repeat apply ite_zero_or_one
  exact assertSameClaims_zero_or_one _ _

/-- Complete postcondition of a verified child Multi-STARK proof (`verifyChildBatchWithFloor 1`),
wrapping `CompressWrapSpec.CompressWrapAccepted` directly! -/
structure PureVerifiedChild (w : ChildProofWitness) : Prop where
  accepted :
    let stmt := computeStatementDigest w.vkBytes w.claimsBytes
    CompressWrapAccepted 0 0 0 0 0 0 0 0
      stmt.w0 stmt.w1 stmt.w2 stmt.w3 stmt.w4 stmt.w5 stmt.w6 stmt.w7
      w.vkBytes w.claimsBytes w.proofBytes

/-- **Child Batch Proof Soundness (`verifyChildBatch_sound`):**
Every child Multi-STARK batch verified inside `AggregatePure` produces a complete
`CompressWrapSpec.CompressWrapAccepted` proof! -/
theorem verifyChildBatch_sound {w : ChildProofWitness}
    (hok : (verifyChildBatchWithFloor 1 w).ok = 1) :
    PureVerifiedChild w ∧
    (verifyChildBatchWithFloor 1 w).val = (readClaims w.claimsBytes).val := by
  revert hok
  unfold verifyChildBatchWithFloor
  extract_lets stmt ok pClaims
  have hokDef : ok = verifyRootBytes 0 0 0 0 0 0 0 0
      stmt.w0 stmt.w1 stmt.w2 stmt.w3 stmt.w4 stmt.w5 stmt.w6 stmt.w7
      w.vkBytes w.claimsBytes w.proofBytes := rfl
  have hpClaimsDef : pClaims = readClaims w.claimsBytes := rfl
  clear_value ok pClaims
  intro hok
  by_cases h0 : ok = 0
  · simp [h0] at hok
  · have h0f : (ok == 0) = false := beq_false_of_ne h0
    have hvr01 : ok = 0 ∨ ok = 1 := by
      rw [hokDef]; exact verifyRootBytesWithFloor_zero_or_one 1 0 0 0 0 0 0 0 0
        stmt.w0 stmt.w1 stmt.w2 stmt.w3 stmt.w4 stmt.w5 stmt.w6 stmt.w7
        w.vkBytes w.claimsBytes w.proofBytes
    have hvr1 : verifyRootBytes 0 0 0 0 0 0 0 0
        stmt.w0 stmt.w1 stmt.w2 stmt.w3 stmt.w4 stmt.w5 stmt.w6 stmt.w7
        w.vkBytes w.claimsBytes w.proofBytes = 1 := hokDef ▸ hvr01.resolve_left h0
    refine ⟨⟨verifyRootBytes_sound hvr1⟩, ?_⟩
    simp only [h0f, Bool.false_eq_true, ↓reduceIte, hpClaimsDef]

/-- Complete postcondition of `verifyChildDigestWithFloor 1` for an IxVM (`kind = 0`) or
recursive `ix_aggr` (`kind = 1`) child proof. -/
structure ChildDigestAccepted (kind : Nat) (ap : AllowedParams)
    (allowedDigest : Digest32Words) (w : ChildProofWitness) (digest : Digest32Words) : Prop where
  child : PureVerifiedChild w
  vk_pin : packDigest (blake3HashBytes w.vkBytes) = if kind = 0 then ap.ixvmVkDigest else ap.selfVkDigest
  single_claim : ∃ c, (readClaims w.claimsBytes).val = .cons c .nil ∧
    aggrClaimField c 0 = 1 ∧
    (kind = 0 → u64ListLen c = 10 ∧ aggrClaimField c 1 = ap.verifyIdx ∧ digest = aggrClaimDigest c 2) ∧
    (kind ≠ 0 → u64ListLen c = 18 ∧ aggrClaimField c 1 = ap.aggrIdx ∧
      aggrClaimDigest c 2 = allowedDigest ∧ digest = aggrClaimDigest c 10)

private theorem verifyChildBatchWithFloor_ok_01 (ef : Nat) (w : ChildProofWitness) :
    (verifyChildBatchWithFloor ef w).ok = 0 ∨ (verifyChildBatchWithFloor ef w).ok = 1 := by
  unfold verifyChildBatchWithFloor
  extract_lets stmt ok pClaims
  have hpClaims : pClaims = readClaims w.claimsBytes := rfl
  clear_value stmt ok pClaims
  apply ite_ok_zero_or_one ParseU64ListList.ok rfl
  rw [hpClaims]
  exact readClaims_ok_zero_or_one w.claimsBytes

private def verifyChildDigestCore (kind : Nat) (ap : AllowedParams) (allowedDigest : Digest32Words)
    (vkDig expectedVk : Digest32Words) (vc : ParseU64ListList) : VerifyChildDigestOut :=
  let bad : VerifyChildDigestOut := { ok := 0, digest := zeroDigest32Words }
  if digest32WordsEq vkDig expectedVk == 0 then bad
  else if vc.ok == 0 then bad
  else
    let oc := aggrOnlyClaim vc.val
    if oc.ok == 0 then bad
    else if aggrClaimField oc.claim 0 != 1 then bad
    else if kind == 0 then
      if u64ListLen oc.claim != 10 then bad
      else if aggrClaimField oc.claim 1 != ap.verifyIdx then bad
      else { ok := 1, digest := aggrClaimDigest oc.claim 2 }
    else
      if u64ListLen oc.claim != 18 then bad
      else if aggrClaimField oc.claim 1 != ap.aggrIdx then bad
      else if digest32WordsEq (aggrClaimDigest oc.claim 2) allowedDigest == 0 then bad
      else { ok := 1, digest := aggrClaimDigest oc.claim 10 }

private theorem verifyChildDigest_eq_core (ef kind : Nat) (ap : AllowedParams)
    (allowedDigest : Digest32Words) (w : ChildProofWitness) :
    verifyChildDigestWithFloor ef kind ap allowedDigest w =
      verifyChildDigestCore kind ap allowedDigest
        (packDigest (blake3HashBytes w.vkBytes))
        (if kind == 0 then ap.ixvmVkDigest else ap.selfVkDigest)
        (verifyChildBatchWithFloor ef w) := rfl

private theorem verifyChildDigestCore_sound (kind : Nat) (ap : AllowedParams)
    (allowedDigest vkDig expectedVk : Digest32Words) (vc : ParseU64ListList)
    (hok : (verifyChildDigestCore kind ap allowedDigest vkDig expectedVk vc).ok = 1) :
    digest32WordsEq vkDig expectedVk = 1 ∧
    vc.ok ≠ 0 ∧
    ∃ c, vc.val = .cons c .nil ∧ aggrClaimField c 0 = 1 ∧
      (kind = 0 → u64ListLen c = 10 ∧ aggrClaimField c 1 = ap.verifyIdx ∧
        (verifyChildDigestCore kind ap allowedDigest vkDig expectedVk vc).digest = aggrClaimDigest c 2) ∧
      (kind ≠ 0 → u64ListLen c = 18 ∧ aggrClaimField c 1 = ap.aggrIdx ∧
        digest32WordsEq (aggrClaimDigest c 2) allowedDigest = 1 ∧
        (verifyChildDigestCore kind ap allowedDigest vkDig expectedVk vc).digest = aggrClaimDigest c 10) := by
  unfold verifyChildDigestCore at hok ⊢
  dsimp only at hok ⊢
  by_cases hvk : digest32WordsEq vkDig expectedVk = 0
  · simp [hvk] at hok
  · have hvk1 : digest32WordsEq vkDig expectedVk = 1 :=
      (digest32WordsEq_zero_or_one _ _).resolve_left hvk
    simp only [hvk1, show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    by_cases hvc0 : vc.ok = 0
    · simp [hvc0] at hok
    · have hvcf : (vc.ok == 0) = false := beq_false_of_ne hvc0
      simp only [hvcf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      cases hcl : vc.val with
      | nil => simp [hcl, aggrOnlyClaim] at hok
      | cons c rest =>
        cases rest with
        | cons _ _ => simp [hcl, aggrOnlyClaim] at hok
        | nil =>
          rw [hcl] at hok
          dsimp only [aggrOnlyClaim] at hok ⊢
          simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          by_cases hch : aggrClaimField c 0 = 1
          · simp only [hch, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hok ⊢
            refine ⟨trivial, hvc0, c, rfl, hch, ?_, ?_⟩
            · intro hk0
              simp only [hk0, beq_self_eq_true, ↓reduceIte] at hok ⊢
              by_cases h10 : u64ListLen c = 10
              · simp only [h10, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                by_cases hvi : aggrClaimField c 1 = ap.verifyIdx
                · simp only [hvi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                  exact ⟨trivial, trivial, trivial⟩
                · simp [hvi] at hok
              · simp [h10] at hok
            · intro hkne
              have hk0f : (kind == 0) = false := beq_false_of_ne hkne
              simp only [hk0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
              by_cases h18 : u64ListLen c = 18
              · simp only [h18, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                by_cases hai : aggrClaimField c 1 = ap.aggrIdx
                · simp only [hai, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                  by_cases hal : digest32WordsEq (aggrClaimDigest c 2) allowedDigest = 0
                  · simp [hal] at hok
                  · have hal1 : digest32WordsEq (aggrClaimDigest c 2) allowedDigest = 1 :=
                      (digest32WordsEq_zero_or_one _ _).resolve_left hal
                    simp only [hal1, show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨trivial, trivial, trivial, trivial⟩
                · simp [hai] at hok
              · simp [h18] at hok
          · simp [hch] at hok

theorem verifyChildDigest_sound {kind : Nat} {ap : AllowedParams}
    {allowedDigest : Digest32Words} {w : ChildProofWitness}
    (hok : (verifyChildDigestWithFloor 1 kind ap allowedDigest w).ok = 1) :
    ChildDigestAccepted kind ap allowedDigest w
      (verifyChildDigestWithFloor 1 kind ap allowedDigest w).digest := by
  rw [verifyChildDigest_eq_core] at hok ⊢
  obtain ⟨hvk1, hvc0, c, hcl, hch1, hk0, hkne⟩ :=
    verifyChildDigestCore_sound kind ap allowedDigest _ _ _ hok
  have hvkEq := (digest32WordsEq_eq_one_iff _ _).mp hvk1
  have hvkPin : packDigest (blake3HashBytes w.vkBytes) =
      if kind = 0 then ap.ixvmVkDigest else ap.selfVkDigest := by
    by_cases hk : kind = 0
    · simpa [hk] using hvkEq
    · have hbf : (kind == 0) = false := beq_false_of_ne hk
      simpa [hk, hbf] using hvkEq
  have hvc1 : (verifyChildBatchWithFloor 1 w).ok = 1 :=
    (verifyChildBatchWithFloor_ok_01 1 w).resolve_left hvc0
  obtain ⟨hchild, hvalEq⟩ := verifyChildBatch_sound hvc1
  have hrcVal : (readClaims w.claimsBytes).val = .cons c .nil := by
    rw [← hvalEq, hcl]
  exact ⟨hchild, hvkPin, c, hrcVal, hch1, hk0, fun hne =>
    let ⟨h18, hai, hal1, hdig⟩ := hkne hne
    ⟨h18, hai, (digest32WordsEq_eq_one_iff _ _).mp hal1, hdig⟩⟩

/-- Extracted recursive child claim digest equals `digest` whenever `verifyChildDigestWithFloor 1 1` succeeds. -/
theorem extractRecursiveChildDigest_eq {ap : AllowedParams} {allowedDigest : Digest32Words}
    {w : ChildProofWitness}
    (hok : (verifyChildDigestWithFloor 1 1 ap allowedDigest w).ok = 1) :
    extractRecursiveChildDigest w.claimsBytes =
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w).digest := by
  have hacc := verifyChildDigest_sound hok
  obtain ⟨c, hcl, _, _, h1⟩ := hacc.single_claim
  obtain ⟨_, _, _, hdig⟩ := h1 (by decide)
  unfold extractRecursiveChildDigest
  have hrcOk : (readClaims w.claimsBytes).ok = 1 := hacc.child.accepted.claims_ok
  simp only [hrcOk, show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte, hcl,
    aggrOnlyClaim, hdig]

/-! ### Shape 10 Range Leaf & Shapes 11–12 Telescoping Soundness in `K` -/

private theorem rangeSumAux_congr_local {f g : Nat → Ix.Cert.MultiStark.K} {lo n : Nat}
    (h : ∀ k, lo ≤ k → k < lo + n → f k = g k) :
    _root_.Aggr.rangeSumAux Ix.Cert.Aggr.kResidualMonoid f lo n =
      _root_.Aggr.rangeSumAux Ix.Cert.Aggr.kResidualMonoid g lo n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    simp only [_root_.Aggr.rangeSumAux]
    rw [h lo (Nat.le_refl _) (by omega),
        ih (fun k h1 h2 => h k (by omega) (by omega))]

/-- **Shape 10 Range Loop Soundness (`aggrVerifyRange_sound`):**
Every shard `s ∈ [shard, shard + n)` satisfies `CompressWrapSpec.ShardAccepted` AND the
accumulated residual equals `extGlToK acc + rangeSum kResidualMonoid (shardProofResidualAt proofs shard) shard (shard + n)`. -/
theorem aggrVerifyRange_sound (sys : SysKey) :
    ∀ (n : Nat) (headers : ShardHeaderList) (proofs : ShardProofList) (shard : Nat)
      (input : ByteList) (lch fch acc : ExtGl),
      (aggrVerifyRangeWithFloor 1 sys headers proofs shard n input lch fch acc).ok = 1 →
      shardProofListLen proofs = n ∧
      ShardsAllAccepted sys (shardHeaderListTake n headers) proofs shard input lch fch ∧
      extGlToK (aggrVerifyRangeWithFloor 1 sys headers proofs shard n input lch fch acc).residual =
        extGlToK acc +
          _root_.Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid
            (shardProofResidualAt proofs shard) shard (shard + n)
  | 0, _, proofs, shard, _, _, _, acc, hok => by
    cases proofs with
    | cons _ _ => simp [aggrVerifyRangeWithFloor] at hok
    | nil =>
      refine ⟨rfl, trivial, ?_⟩
      change extGlToK acc = extGlToK acc + _root_.Aggr.rangeSumAux Ix.Cert.Aggr.kResidualMonoid _ shard (shard + 0 - shard)
      have h0 : shard + 0 - shard = 0 := by omega
      rw [h0]; simp [_root_.Aggr.rangeSumAux, Ix.Cert.Aggr.kResidualMonoid]
  | n + 1, headers, proofs, shard, input, lch, fch, acc, hok => by
    cases headers with
    | nil => simp [aggrVerifyRangeWithFloor] at hok
    | cons h hrest =>
      cases proofs with
      | nil => simp [aggrVerifyRangeWithFloor] at hok
      | cons p prest =>
        unfold aggrVerifyRangeWithFloor at hok ⊢; dsimp only at hok ⊢
        by_cases hr0 : (verifyShardWithFloor 1 sys h shard p input lch fch).ok = 0
        · simp [hr0] at hok
        · have hr1 : (verifyShard sys h shard p input lch fch).ok = 1 :=
            (verifyShardWithFloor_ok_zero_or_one 1 sys h shard p input lch fch).resolve_left hr0
          have hr0f : ((verifyShardWithFloor 1 sys h shard p input lch fch).ok == 0) = false := beq_false_of_ne hr0
          simp only [hr0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          have hsa := verifyShard_sound hr1
          obtain ⟨hlen, hrestAcc, hsum⟩ :=
            aggrVerifyRange_sound sys n hrest prest (shard + 1) input lch fch
              (extAdd acc (verifyShardWithFloor 1 sys h shard p input lch fch).lastAcc) hok
          refine ⟨by simp [shardProofListLen, hlen]; omega, ⟨hsa, hrestAcc⟩, ?_⟩
          rw [hsum, extGlToK_add]
          have hlast : (verifyShardWithFloor 1 sys h shard p input lch fch).lastAcc = lastAcc p.intermediateAccs :=
            hsa.lastAcc_eq
          rw [hlast]
          unfold _root_.Aggr.rangeSum
          have hd1 : shard + (n + 1) - shard = n + 1 := by omega
          have hd2 : shard + 1 + n - (shard + 1) = n := by omega
          rw [hd1, hd2]
          simp only [_root_.Aggr.rangeSumAux]
          have h0 : shardProofResidualAt (.cons p prest) shard shard = extGlToK (lastAcc p.intermediateAccs) := by
            unfold shardProofResidualAt
            simp [shardProofListGetAcc]
          have hcongr :
              _root_.Aggr.rangeSumAux Ix.Cert.Aggr.kResidualMonoid (shardProofResidualAt prest (shard + 1)) (shard + 1) n =
              _root_.Aggr.rangeSumAux Ix.Cert.Aggr.kResidualMonoid (shardProofResidualAt (.cons p prest) shard) (shard + 1) n := by
            apply rangeSumAux_congr_local
            intro k hk1 _
            unfold shardProofResidualAt
            have hn1 : ¬ k < shard + 1 := by omega
            have hn2 : ¬ k < shard := by omega
            have hsub : k - shard = (k - (shard + 1)) + 1 := by omega
            simp [hn1, hn2, hsub, shardProofListGetAcc]
          rw [h0, hcongr]
          change extGlToK acc + extGlToK (lastAcc p.intermediateAccs) + _ =
            extGlToK acc + (extGlToK (lastAcc p.intermediateAccs) + _)
          rw [add_assoc]

/-- Additive shift law for `messagesAcc` in `Ix.Cert.MultiStark.K`. -/
theorem messagesAcc_add_spec (acc : ExtGl) (ms : BatchMessageList) (lch fch : ExtGl) :
    (messagesAcc acc ms lch fch).ok = (messagesAcc extZero ms lch fch).ok ∧
    ((messagesAcc acc ms lch fch).ok = 1 →
      extGlToK (messagesAcc acc ms lch fch).lastAcc =
        extGlToK (messagesAcc extZero ms lch fch).lastAcc + extGlToK acc) := by
  induction ms generalizing acc with
  | nil =>
    exact ⟨rfl, fun _ => by simp [messagesAcc, extGlToK_zero]⟩
  | cons m rest ih =>
    unfold messagesAcc; dsimp only
    by_cases hz : extIsZero (extAdd lch (fingerprintVals fch m.args)) = 1
    · simp [hz]
    · have hzf : (extIsZero (extAdd lch (fingerprintVals fch m.args)) == 1) = false := beq_false_of_ne hz
      simp only [hzf, Bool.false_eq_true, ↓reduceIte]
      set term := extScale (extInvDirect (extAdd lch (fingerprintVals fch m.args))) (glValBytes m.multiplicity)
      have h1 := ih (extAdd acc term)
      have h2 := ih (extAdd extZero term)
      refine ⟨h1.1.trans h2.1.symm, fun hok => ?_⟩
      have hok2 : (messagesAcc (extAdd extZero term) rest lch fch).ok = 1 := by
        rw [h2.1, ← h1.1]; exact hok
      rw [h1.2 hok, h2.2 hok2, extGlToK_add, extGlToK_add, extGlToK_zero, zero_add]
      ring

/-! ### Shape 17 Uniform Security Envelope & Shape 18 Validator Isolation -/

/-- **Shape 17 Uniform Security Envelope Equivalence (`aggrAssertSecurityEnvelope_iff`):**
`aggrAssertSecurityEnvelope p = 1` holds iff `Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams p)` holds
(which by `Ix.Cert.Aggr.securityEnvelopeOk_iff` implies BOTH `Ix.Cert.MultiStark.checkParams = true`
AND `Aiur.meetsSecurityFloor = true`!). -/
theorem aggrAssertSecurityEnvelope_iff (p : SysParams) :
    aggrAssertSecurityEnvelope p = 1 ↔ Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams p) := by
  constructor
  · intro hok
    unfold aggrAssertSecurityEnvelope at hok
    obtain ⟨hcap, hok⟩ := ite_nat_eq_one_right hok
    obtain ⟨hfin, hok⟩ := ite_nat_eq_one_right hok
    obtain ⟨har, hok⟩ := ite_nat_eq_one_right hok
    have hs := checkSecurityFloor_sound hok
    have hcap0 : p.capHeight = 0 := by simpa [bne_iff_ne] using hcap
    have hfin0 : p.logFinalPolyLen = 0 := by simpa [bne_iff_ne] using hfin
    have har1 : p.maxLogArity = 1 := by simpa [bne_iff_ne] using har
    have hudEq : Ix.Cert.Aggr.udMillibitsPerQuery p.logBlowup = udMillibitsOf p.logBlowup := by
      have hlb : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by
        have := hs.logBlowup_ge; have := hs.logBlowup_le; omega
      rcases hlb with h | h | h | h <;> rw [h] <;> rfl
    exact ⟨hcap0, hfin0, har1, hs.logBlowup_ge, hs.logBlowup_le, hs.numQueries_pos,
      hs.commitPow_le, hs.queryPow_le, hs.conjectured_ge_220,
      by simpa [Ix.Cert.Aggr.minProvableUdMillibits, Ix.Cert.Aggr.udQueryMillibits, toStarkParams, hudEq] using hs.ud_ge_80000,
      by simpa [Ix.Cert.Aggr.minJohnson128Millibits, Ix.Cert.Aggr.johnsonQueryMillibits, toStarkParams] using hs.johnson_ge_128000⟩
  · rintro ⟨hcap, hfin, har, hlb1, hlb4, hnq, hcp, hqp, hconj, hud, hj⟩
    unfold aggrAssertSecurityEnvelope checkSecurityFloor
    simp only [toStarkParams, Ix.Cert.Aggr.minProvableUdMillibits, Ix.Cert.Aggr.udQueryMillibits,
      Ix.Cert.Aggr.minJohnson128Millibits, Ix.Cert.Aggr.johnsonQueryMillibits,
      Aiur.maxProofOfWorkBits, Aiur.minConjecturedSecurityBits] at *
    have hcapB : (p.capHeight != 0) = false := by simp [hcap]
    have hfinB : (p.logFinalPolyLen != 0) = false := by simp [hfin]
    have harB : (p.maxLogArity != 1) = false := by simp [har]
    simp only [hcapB, hfinB, harB, Bool.false_eq_true, ↓reduceIte]
    have h1 : (decide (p.logBlowup < 1) || decide (p.logBlowup > 4)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have h2 : ¬ p.numQueries < 1 := by omega
    have h3 : (decide (p.commitPowBits > 32) || decide (p.queryPowBits > 32)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have h4 : ¬ p.logBlowup * p.numQueries + p.queryPowBits < 220 := by omega
    simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
    have hlbCases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by omega
    rcases hlbCases with hlb | hlb | hlb | hlb <;>
    · rw [hlb] at hud hj ⊢
      simp only [Ix.Cert.Aggr.udMillibitsPerQuery] at hud
      simp only [show (1 == 1) = true from rfl, show (2 == 1) = false from rfl,
        show (2 == 2) = true from rfl, show (3 == 1) = false from rfl,
        show (3 == 2) = false from rfl, show (3 == 3) = true from rfl,
        show (4 == 1) = false from rfl, show (4 == 2) = false from rfl,
        show (4 == 3) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      split; · omega
      split; · omega
      rfl

/-- Exact validator characterization of `aggrParseEvalAssumed` (Shape 18 child 0):
admits ONLY validators `∈ {10, 11, 12, 13}` (never `3`/`4`/`5`/`14`/`15`), and
`linked = .none ↔ validator ∈ {10, 11}`. -/
theorem aggrParseEvalAssumed_valid {bs : ByteList}
    (hok : (aggrParseEvalAssumed bs).ok = 1) :
    let p := aggrParseEvalAssumed bs
    (p.tag = 228 ∨ p.tag = 229) ∧
    ((p.ctx.validator = 10 ∨ p.ctx.validator = 11) ∧ p.linked = .none ∨
     (p.ctx.validator = 12 ∨ p.ctx.validator = 13) ∧ ∃ r, p.linked = .some r) := by
  dsimp only
  revert hok
  unfold aggrParseEvalAssumed
  extract_lets bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm ctx rEval rEvalOpt rLnk
  have hbad : bad.ok = 0 := rfl
  have hctx : ctx = { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := rVal.val } := rfl
  clear_value bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm ctx rEval rEvalOpt rLnk
  intro hok
  obtain ⟨htag, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  have htagOk : rTag.val = 228 ∨ rTag.val = 229 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, not_or, not_and] at htag
    by_cases h228 : rTag.val = 228
    · exact Or.inl h228
    · exact Or.inr (by_contra fun h229 => htag.2 h228 h229)
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
  by_cases h1011 : (rVal.val == 10 || rVal.val == 11) = true
  · rw [ite_eq_left h1011] at hok ⊢
    obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
    cases hr : rEval.rest with
    | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
    | nil =>
      dsimp only
      simp only [Bool.or_eq_true, beq_iff_eq] at h1011
      rw [hctx]
      exact ⟨htagOk, Or.inl ⟨h1011, rfl⟩⟩
  · rw [ite_eq_right h1011] at hok ⊢
    by_cases h1213 : (rVal.val == 12 || rVal.val == 13) = true
    · rw [ite_eq_left h1213] at hok ⊢
      obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
      cases hv : rEvalOpt.val with
      | none => rw [hv] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
      | some evalRoot =>
        rw [hv] at hok; dsimp only at hok ⊢
        obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalAssumedOut.ok) hbad hok; rw [heq]
        cases hr : rLnk.rest with
        | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
        | nil =>
          dsimp only
          simp only [Bool.or_eq_true, beq_iff_eq] at h1213
          rw [hctx]
          exact ⟨htagOk, Or.inr ⟨h1213, _, rfl⟩⟩
    · rw [ite_eq_right h1213] at hok; rw [hbad] at hok; cases hok

/-- **Strict Shape 18 Validator Isolation (`aggrParseEvalDischargeOut_isolation`):**
Any output accepted by `aggrParseEvalDischargeOut` satisfies ALL four isolation invariants:
1. `outVal ∈ {10, 11, 12, 13, 14, 15}` — **NEVER standard validator `3`, `4`, or `5`!**
2. If `c0Val ∈ {12, 13}`, then `outVal = c0Val` and `linkedOpt = .some _` (linked claims can NEVER drop links).
3. If `linkedOpt = .some _`, then `(c0Val ∈ {10, 12} ∧ outVal = 12) ∨ (c0Val ∈ {11, 13} ∧ outVal = 13)`.
4. If `evalOpt = .none ∧ linkedOpt = .none`, then `(c0Val = 10 ∧ outVal = 14) ∨ (c0Val = 11 ∧ outVal = 15)`! -/
theorem aggrParseEvalDischargeOut_isolation {bs : ByteList} {expectedTag c0Val : Nat}
    (hok : (aggrParseEvalDischargeOut bs expectedTag c0Val).ok = 1) :
    let p := aggrParseEvalDischargeOut bs expectedTag c0Val
    (p.ctx.validator ≠ 3 ∧ p.ctx.validator ≠ 4 ∧ p.ctx.validator ≠ 5) ∧
    (p.ctx.validator = 10 ∨ p.ctx.validator = 11 ∨ p.ctx.validator = 12 ∨
     p.ctx.validator = 13 ∨ p.ctx.validator = 14 ∨ p.ctx.validator = 15) ∧
    ((c0Val = 12 ∨ c0Val = 13) → p.ctx.validator = c0Val ∧ ∃ r, p.linkedOpt = .some r) ∧
    ((∃ r, p.linkedOpt = .some r) →
      ((c0Val = 10 ∨ c0Val = 12) ∧ p.ctx.validator = 12) ∨
      ((c0Val = 11 ∨ c0Val = 13) ∧ p.ctx.validator = 13)) ∧
    (p.evalOpt = .none ∧ p.linkedOpt = .none →
      (c0Val = 10 ∧ p.ctx.validator = 14) ∨ (c0Val = 11 ∧ p.ctx.validator = 15)) ∧
    ((∃ r, p.evalOpt = .some r) ∧ p.linkedOpt = .none →
      (c0Val = 10 ∨ c0Val = 11) ∧ p.ctx.validator = c0Val) := by
  dsimp only
  revert hok
  unfold aggrParseEvalDischargeOut
  extract_lets bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  have hbad : bad.ok = 0 := rfl
  have hctx : ctx = { spec := rSpec.val, binding := rBind.val, axioms := rAx.val, validator := outVal } := rfl
  have hlvDef : linkedVal = if (c0Val == 10 || c0Val == 12) = true then 12 else 13 := rfl
  clear_value bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  intro hok
  obtain ⟨hc0, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  have hc0Cases : c0Val = 10 ∨ c0Val = 11 ∨ c0Val = 12 ∨ c0Val = 13 := by
    simp only [Bool.and_eq_true, bne_iff_ne] at hc0
    by_cases h10 : c0Val = 10; · exact Or.inl h10
    by_cases h11 : c0Val = 11; · exact Or.inr (Or.inl h11)
    by_cases h12 : c0Val = 12; · exact Or.inr (Or.inr (Or.inl h12))
    by_cases h13 : c0Val = 13; · exact Or.inr (Or.inr (Or.inr h13))
    exact absurd ⟨⟨⟨h10, h11⟩, h12⟩, h13⟩ hc0
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  by_cases hlv : (outVal == linkedVal) = true
  · rw [ite_eq_left hlv] at hok ⊢
    obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
    obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
    cases hr : rLnk.rest with
    | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
    | nil =>
      rw [hctx]; dsimp only
      have hlvEq : outVal = if (c0Val == 10 || c0Val == 12) = true then 12 else 13 := by
        rw [← hlvDef]; simpa [beq_iff_eq] using hlv
      rcases hc0Cases with rfl | rfl | rfl | rfl <;>
      · simp at hlvEq
        refine ⟨by omega, by omega, ?_, ?_, (fun ⟨_, hn⟩ => by cases hn), (fun ⟨_, hn⟩ => by cases hn)⟩
        · intro h1213; rcases h1213 with h | h <;> first | omega | exact ⟨hlvEq, _, rfl⟩
        · intro _; first | exact Or.inl ⟨by omega, hlvEq⟩ | exact Or.inr ⟨by omega, hlvEq⟩
  · rw [ite_eq_right hlv] at hok ⊢
    by_cases h1011 : (c0Val == 10 || c0Val == 11) = true
    · rw [ite_eq_left h1011] at hok ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at h1011
      by_cases hsame : (outVal == c0Val) = true
      · rw [ite_eq_left hsame] at hok ⊢
        obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
        cases hr : rEval.rest with
        | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
        | nil =>
          rw [hctx]; dsimp only
          have hvalEq : outVal = c0Val := by simpa [beq_iff_eq] using hsame
          rcases h1011 with rfl | rfl <;>
          exact ⟨by omega, by omega, (fun h => by omega), (fun ⟨_, hn⟩ => by cases hn),
            (fun ⟨hn, _⟩ => by cases hn), fun _ => ⟨by omega, hvalEq⟩⟩
      · rw [ite_eq_right hsame] at hok ⊢
        by_cases hplus4 : (outVal == c0Val + 4) = true
        · rw [ite_eq_left hplus4] at hok ⊢
          cases hr : rAsm.rest with
          | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
          | nil =>
            rw [hctx]; dsimp only
            have hvalEq : outVal = c0Val + 4 := by simpa [beq_iff_eq] using hplus4
            rcases h1011 with rfl | rfl <;>
            exact ⟨by omega, by omega, (fun h => by omega), (fun ⟨_, hn⟩ => by cases hn),
              (fun _ => by omega), fun ⟨⟨_, hn⟩, _⟩ => by cases hn⟩
        · rw [ite_eq_right hplus4] at hok; rw [hbad] at hok; cases hok
    · rw [ite_eq_right h1011] at hok; rw [hbad] at hok; cases hok

private theorem verifyChildDigest_ok_01 (k : Nat) (ap : AllowedParams) (ad : Digest32Words)
    (w : ChildProofWitness) :
    (verifyChildDigestWithFloor 1 k ap ad w).ok = 0 ∨
    (verifyChildDigestWithFloor 1 k ap ad w).ok = 1 := by
  unfold verifyChildDigestWithFloor
  extract_lets bad vkDig expectedVk vc oc
  have hb0 : bad.ok = 0 := rfl
  clear_value bad vkDig expectedVk vc oc
  repeat apply ite_ok_zero_or_one VerifyChildDigestOut.ok hb0
  split
  · repeat apply ite_ok_zero_or_one VerifyChildDigestOut.ok hb0
    exact Or.inr rfl
  · repeat apply ite_ok_zero_or_one VerifyChildDigestOut.ok hb0
    exact Or.inr rfl

private theorem parseAllowedBlob_ok_01 (ad : Digest32Words) (bs : ByteList) :
    (parseAllowedBlob ad bs).ok = 0 ∨ (parseAllowedBlob ad bs).ok = 1 := by
  unfold parseAllowedBlob
  extract_lets bad rIxvm rVidx rSelf rAidx
  have hb0 : bad.ok = 0 := rfl
  clear_value bad rIxvm rVidx rSelf rAidx
  repeat apply ite_ok_zero_or_one ParseAllowedOut.ok hb0
  split
  · exact Or.inl hb0
  · exact Or.inr rfl

private theorem aggrParseEvalAssumed_ok_01 (bs : ByteList) :
    (aggrParseEvalAssumed bs).ok = 0 ∨ (aggrParseEvalAssumed bs).ok = 1 := by
  unfold aggrParseEvalAssumed
  extract_lets bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm ctx rEval rEvalOpt rLnk
  have hb0 : bad.ok = 0 := rfl
  clear_value bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm ctx rEval rEvalOpt rLnk
  repeat apply ite_ok_zero_or_one ParseEvalAssumedOut.ok hb0
  split
  · apply ite_ok_zero_or_one ParseEvalAssumedOut.ok hb0
    split
    · exact Or.inl hb0
    · exact Or.inr rfl
  · split
    · apply ite_ok_zero_or_one ParseEvalAssumedOut.ok hb0
      split
      · exact Or.inl hb0
      · apply ite_ok_zero_or_one ParseEvalAssumedOut.ok hb0
        split
        · exact Or.inl hb0
        · exact Or.inr rfl
    · exact Or.inl hb0

private theorem aggrParseEvalDischargeOut_ok_01 (bs : ByteList) (t c0 : Nat) :
    (aggrParseEvalDischargeOut bs t c0).ok = 0 ∨ (aggrParseEvalDischargeOut bs t c0).ok = 1 := by
  unfold aggrParseEvalDischargeOut
  extract_lets bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  have hb0 : bad.ok = 0 := rfl
  clear_value bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  repeat apply ite_ok_zero_or_one ParseEvalDischargeOut.ok hb0
  split
  · repeat apply ite_ok_zero_or_one ParseEvalDischargeOut.ok hb0
    split
    · exact Or.inl hb0
    · exact Or.inr rfl
  · split
    · split
      · apply ite_ok_zero_or_one ParseEvalDischargeOut.ok hb0
        split
        · exact Or.inl hb0
        · exact Or.inr rfl
      · split
        · split
          · exact Or.inl hb0
          · exact Or.inr rfl
        · exact Or.inl hb0
    · exact Or.inl hb0

private theorem aggrParseEvalDischargeOut_validator_eq {bs : ByteList} {t c0 : Nat}
    (hok : (aggrParseEvalDischargeOut bs t c0).ok = 1) :
    (readU8 (readU8 (readU8 bs).rest).rest).val =
      (aggrParseEvalDischargeOut bs t c0).ctx.validator := by
  revert hok
  unfold aggrParseEvalDischargeOut
  extract_lets bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  have hbad : bad.ok = 0 := rfl
  have hEq : (readU8 (readU8 (readU8 bs).rest).rest).val = ctx.validator := rfl
  clear_value bad rTag rFmt rVal rSpec rBind rAx rTgt rAsm outVal ctx linkedVal rEvalOpt rLnk rEval
  intro hok
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
  by_cases hlv : (outVal == linkedVal) = true
  · rw [ite_eq_left hlv] at hok ⊢
    obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
    obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
    cases hr : rLnk.rest with
    | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
    | nil => exact hEq
  · rw [ite_eq_right hlv] at hok ⊢
    by_cases h1011 : (c0 == 10 || c0 == 11) = true
    · rw [ite_eq_left h1011] at hok ⊢
      by_cases hsame : (outVal == c0) = true
      · rw [ite_eq_left hsame] at hok ⊢
        obtain ⟨_, hok, heq⟩ := ite_elim_bad (okFn := ParseEvalDischargeOut.ok) hbad hok; rw [heq]
        cases hr : rEval.rest with
        | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
        | nil => exact hEq
      · rw [ite_eq_right hsame] at hok ⊢
        by_cases hplus4 : (outVal == c0 + 4) = true
        · rw [ite_eq_left hplus4] at hok ⊢
          cases hr : rAsm.rest with
          | cons _ _ => rw [hr] at hok; dsimp only at hok; rw [hbad] at hok; cases hok
          | nil => exact hEq
        · rw [ite_eq_right hplus4] at hok; rw [hbad] at hok; cases hok
    · rw [ite_eq_right h1011] at hok; rw [hbad] at hok; cases hok

/-- **Headline Shape 18 Mode Isolation Theorem (`verifyShapeDischargeEval_mode_isolation`):**
In ANY accepted Shape 18 step:
1. Both child 0 and child 1 satisfy `ChildDigestAccepted` (with `CompressWrapAccepted`),
2. Output validator is strictly in `{10, 11, 12, 13, 14, 15}` — **NEVER `3`, `4`, or `5`**,
3. Mode 1 (`tag = 227`) is impossible; child 1 tag is strictly `228` (Mode 2) or `232` (Mode 3a),
4. In Mode 2 (`tag = 228`), full unlinked discharge lands strictly on validator `14`/`15`
   (`ValidatorMode.dischargeAllEvals`) with `linkedOpt = .none`,
5. In Mode 3a (`tag = 232`), output ALWAYS commits a non-empty `linkedOpt = .some _` under
   linked validator `12`/`13` (`ValidatorMode.toLinkedMode`)! -/
theorem verifyShapeDischargeEval_mode_isolation
    {ap : AllowedParams} {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hok : verifyShapeDischargeEval 1 ap allowedDigest outClaimDigest w = 1) :
    let p0 := aggrParseEvalAssumed w.child0Preimage
    let pOut := aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator
    (w.auxKind0 = 0 ∨ w.auxKind0 = 1) ∧
    (w.auxKind1 = 0 ∨ w.auxKind1 = 1) ∧
    ChildDigestAccepted w.auxKind0 ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 w.auxKind0 ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted w.auxKind1 ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 w.auxKind1 ap allowedDigest w.child1).digest ∧
    p0.ok = 1 ∧ pOut.ok = 1 ∧
    (pOut.ctx.validator ≠ 3 ∧ pOut.ctx.validator ≠ 4 ∧ pOut.ctx.validator ≠ 5) ∧
    ((readU8 w.child1Preimage).val = 228 ∨
     ((readU8 w.child1Preimage).val = 232 ∧ w.auxKind1 = 1 ∧
       (pOut.ctx.validator = 12 ∨ pOut.ctx.validator = 13) ∧ ∃ r, pOut.linkedOpt = .some r)) := by
  dsimp only
  unfold verifyShapeDischargeEval at hok
  obtain ⟨hk, hok⟩ := ite_nat_eq_one_right hok
  have hk0 : w.auxKind0 = 0 ∨ w.auxKind0 = 1 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, not_or, not_and] at hk
    by_cases h0 : w.auxKind0 = 0; · exact Or.inl h0
    · exact Or.inr (by_contra fun h1 => hk.1 h0 h1)
  have hk1 : w.auxKind1 = 0 ∨ w.auxKind1 = 1 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, not_or, not_and] at hk
    by_cases h0 : w.auxKind1 = 0; · exact Or.inl h0
    · exact Or.inr (by_contra fun h1 => hk.2 h0 h1)
  generalize hc0Def : verifyChildDigestWithFloor 1 w.auxKind0 ap allowedDigest w.child0 = c0 at hok
  obtain ⟨hc0_0, hok⟩ := ite_nat_eq_one_right hok
  generalize hc1Def : verifyChildDigestWithFloor 1 w.auxKind1 ap allowedDigest w.child1 = c1 at hok
  obtain ⟨hc1_0, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hp0Def : aggrParseEvalAssumed w.child0Preimage = p0 at hok
  obtain ⟨hp0_0, hok⟩ := ite_nat_eq_one_right hok
  generalize hpOutDef : aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator = pOut at hok
  obtain ⟨hpOut_0, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize ht0 : aggrCheckCanonicalTree p0.evalRoot w.leftSubjTreeBytes = tEval0 at hok
  generalize ht1 : aggrCheckOptionalTree pOut.evalOpt w.rightSubjTreeBytes = tEvalOut at hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hrem : aggrExtractRemovedLeaf tEval0.val tEvalOut.val = rem at hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hpLeaf : aggrParseEvalAssumption w.extraPreimage0 = pLeaf at hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hrC1Def : readU8 w.child1Preimage = rC1Tag at hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  have hc0_1 : (verifyChildDigestWithFloor 1 w.auxKind0 ap allowedDigest w.child0).ok = 1 :=
    (verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hc0Def]; simpa [beq_iff_eq] using hc0_0)
  have hc1_1 : (verifyChildDigestWithFloor 1 w.auxKind1 ap allowedDigest w.child1).ok = 1 :=
    (verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hc1Def]; simpa [beq_iff_eq] using hc1_0)
  have hp0_1 : (aggrParseEvalAssumed w.child0Preimage).ok = 1 :=
    (aggrParseEvalAssumed_ok_01 _).resolve_left (by rw [hp0Def]; simpa [beq_iff_eq] using hp0_0)
  have hpOut_1 : (aggrParseEvalDischargeOut w.outputBytes
      (aggrParseEvalAssumed w.child0Preimage).tag
      (aggrParseEvalAssumed w.child0Preimage).ctx.validator).ok = 1 :=
    (aggrParseEvalDischargeOut_ok_01 _ _ _).resolve_left
      (by rw [hp0Def, hpOutDef]; simpa [beq_iff_eq] using hpOut_0)
  have hiso := aggrParseEvalDischargeOut_isolation hpOut_1
  refine ⟨hk0, hk1,
    by rw [← hc0Def]; exact verifyChildDigest_sound hc0_1,
    by rw [← hc1Def]; exact verifyChildDigest_sound hc1_1,
    by rw [← hp0Def]; exact hp0_1,
    by rw [← hpOutDef, ← hp0Def]; exact hpOut_1,
    by rw [← hpOutDef, ← hp0Def]; exact hiso.1, ?_⟩
  by_cases h228 : rC1Tag.val = 228
  · exact Or.inl h228
  · have h228f : ¬ ((rC1Tag.val == 228) = true) := by simpa [beq_iff_eq] using h228
    rw [ite_eq_right h228f] at hok
    by_cases h232 : rC1Tag.val = 232
    · have h232t : (rC1Tag.val == 232) = true := by simp [h232]
      rw [ite_eq_left h232t] at hok
      obtain ⟨hk1ne, hok⟩ := ite_nat_eq_one_right hok
      have hk1eq : w.auxKind1 = 1 := by simpa [bne_iff_ne] using hk1ne
      generalize hpDL : aggrParseDynamicLink w.child1Preimage = pDL at hok
      obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
      cases hcirc : pLeaf.circuit with
      | noCircuitRef => rw [hcirc] at hok; cases hok
      | someCircuitRef _ _ =>
        rw [hcirc] at hok
        cases hbr : pDL.bridge with
        | noBridge => rw [hbr] at hok; cases hok
        | someBridge dlSpec dlBind tgtConst codec certConst =>
          rw [hbr] at hok; dsimp only at hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
          generalize hentry : aggrLinkedEntryAddr pDL.vkDigest pDL.entryIdx codec tgtConst certConst
            pLeaf.typ dlSpec dlBind = entryAddr at hok
          obtain ⟨hlnk, _⟩ := ite_nat_eq_one_right hok
          have hsomeLnk : ∃ r, (aggrParseEvalDischargeOut w.outputBytes
              (aggrParseEvalAssumed w.child0Preimage).tag
              (aggrParseEvalAssumed w.child0Preimage).ctx.validator).linkedOpt = .some r := by
            rw [hp0Def, hpOutDef]
            cases hlo : pOut.linkedOpt with
            | none => simp [hlo, aggrAssertLinkedMerge] at hlnk
            | some r => exact ⟨r, rfl⟩
          have h1213 : (aggrParseEvalDischargeOut w.outputBytes
              (aggrParseEvalAssumed w.child0Preimage).tag
              (aggrParseEvalAssumed w.child0Preimage).ctx.validator).ctx.validator = 12 ∨
            (aggrParseEvalDischargeOut w.outputBytes
              (aggrParseEvalAssumed w.child0Preimage).tag
              (aggrParseEvalAssumed w.child0Preimage).ctx.validator).ctx.validator = 13 := by
            rcases hiso.2.2.2.1 hsomeLnk with ⟨_, h12⟩ | ⟨_, h13⟩
            · exact Or.inl h12
            · exact Or.inr h13
          exact Or.inr ⟨h232, hk1eq,
            by rw [← hpOutDef, ← hp0Def]; exact h1213,
            by rw [← hpOutDef, ← hp0Def]; exact hsomeLnk⟩
    · have h232f : ¬ ((rC1Tag.val == 232) = true) := by simpa [beq_iff_eq] using h232
      rw [ite_eq_right h232f] at hok; cases hok

/-- **Headline Standard-Validator Non-Aliasing (`verifyAggregateStep_shape18_never_standard_validator`):**
No accepted Shape 18 (`w.shape = 18`) aggregation step can EVER emit an output claim with
standard validator `3`, `4`, or `5` — Mode 2 equality-reflection roots are strictly segregated
onto validators `14`/`15`, and Mode 3a linked roots onto `12`/`13`! -/
theorem verifyAggregateStep_shape18_never_standard_validator
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hshape : w.shape = 18)
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1) :
    let p0 := aggrParseEvalAssumed w.child0Preimage
    let pOut := aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator
    pOut.ok = 1 ∧
    pOut.ctx.validator ≠ 3 ∧ pOut.ctx.validator ≠ 4 ∧ pOut.ctx.validator ≠ 5 ∧
    (aggrParseCheckEnv w.outputBytes).ok = 0 ∧
    (aggrParseCheck w.outputBytes).ok = 0 := by
  dsimp only
  unfold verifyAggregateStep verifyAggregateStepWithFloor at hok
  generalize hpa : parseAllowedBlob allowedDigest w.allowedBytes = pa at hok
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  simp only [hshape, show (18 == 0) = false from rfl, show (18 == 1) = false from rfl,
    show (18 == 2) = false from rfl, show (18 == 3) = false from rfl, show (18 == 4) = false from rfl,
    show (18 == 5) = false from rfl, show (18 == 6) = false from rfl, show (18 == 7) = false from rfl,
    show (18 == 8) = false from rfl, show (18 == 9) = false from rfl, show (18 == 10) = false from rfl,
    show (18 == 11) = false from rfl, show (18 == 12) = false from rfl, show (18 == 13) = false from rfl,
    show (18 == 14) = false from rfl, show (18 == 15) = false from rfl, show (18 == 16) = false from rfl,
    show (18 == 17) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
  have hm := verifyShapeDischargeEval_mode_isolation hok
  obtain ⟨_, _, _, _, _, hpOut, ⟨hn3, hn4, hn5⟩, _⟩ := hm
  have hvalEq := aggrParseEvalDischargeOut_validator_eq hpOut
  have hce0 : (aggrParseCheckEnv w.outputBytes).ok = 0 := by
    unfold aggrParseCheckEnv
    generalize hrTag : readU8 w.outputBytes = rTag
    by_cases h1 : (rTag.ok == 0 || rTag.val != 229) = true
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1]
      generalize hrFmt : readU8 rTag.rest = rFmt
      by_cases h2 : (rFmt.ok == 0 || rFmt.val != 4) = true
      · rw [ite_eq_left h2]
      · rw [ite_eq_right h2]
        generalize hrVal : readU8 rFmt.rest = rVal
        have h3 : (rVal.ok == 0 || (rVal.val != 3 && rVal.val != 4 && rVal.val != 5)) = true := by
          rw [← hrVal, ← hrFmt, ← hrTag, hvalEq]; simp [hn3, hn4, hn5]
        rw [ite_eq_left h3]
  have hc0 : (aggrParseCheck w.outputBytes).ok = 0 := by
    unfold aggrParseCheck
    generalize hrTag : readU8 w.outputBytes = rTag
    by_cases h1 : (rTag.ok == 0 || rTag.val != 228) = true
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1]
      generalize hrFmt : readU8 rTag.rest = rFmt
      by_cases h2 : (rFmt.ok == 0 || rFmt.val != 4) = true
      · rw [ite_eq_left h2]
      · rw [ite_eq_right h2]
        generalize hrVal : readU8 rFmt.rest = rVal
        have h3 : (rVal.ok == 0 || (rVal.val != 3 && rVal.val != 4)) = true := by
          rw [← hrVal, ← hrFmt, ← hrTag, hvalEq]; simp [hn3, hn4]
        rw [ite_eq_left h3]
  exact ⟨hpOut, hn3, hn4, hn5, hce0, hc0⟩

/-! ## Section 3: Part 1 Headline — `AggregatePure` → `PureAcceptedAggrTree` & `Ix.Cert.Aggr.AcceptedAggrTree` -/

/-- Complete shape-by-shape mathematical postcondition of `verifyAggregateStep allowedDigest outClaimDigest w = 1`
across ALL 19 aggregation shapes (`0..18`). -/
structure AggregateStepAccepted (allowedDigest outClaimDigest : Digest32Words)
    (w : AggrStepWitness) : Prop where
  allowed_ok : AllowedBlobAccepted allowedDigest w.allowedBytes
    (parseAllowedBlob allowedDigest w.allowedBytes).val
  shape_lt_19 : w.shape < 19
  shape_post :
    let ap := (parseAllowedBlob allowedDigest w.allowedBytes).val
    match w.shape with
    | 0 => ChildDigestAccepted 0 ap allowedDigest w.child0 outClaimDigest
    | 1 => ChildDigestAccepted 1 ap allowedDigest w.child0 outClaimDigest
    | 2 => verifyShapePairFlat 1 0 0 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 0 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest
    | 3 => verifyShapePairFlat 1 0 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 0 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest
    | 4 => verifyShapePairFlat 1 1 0 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest
    | 5 => verifyShapePairFlat 1 1 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest
    | 6 => verifyShapePairStructural 1 0 0 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 0 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest
    | 7 => verifyShapePairStructural 1 0 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 0 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest
    | 8 => verifyShapePairStructural 1 1 0 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest
    | 9 => verifyShapePairStructural 1 1 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest
    | 10 => verifyShapeRangeLeaf 1 ap outClaimDigest w = 1 ∧
        packDigest (blake3HashBytes w.rangeVkBytes) = ap.ixvmVkDigest ∧
        (readSystem w.rangeVkBytes).ok = 1 ∧
        let pRng := aggrParseRange w.outputBytes
        let lo := glValBytes pRng.lo
        let hi := glValBytes pRng.hi
        lo ≤ hi ∧
        let rCnt := readCount w.rangeShardProofsBytes
        let rPrfs := readShardProofVecN rCnt.rest (hi - lo)
        shardProofListLen rPrfs.val = hi - lo ∧
        extGlToK pRng.residual =
          _root_.Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid (shardProofResidualAt rPrfs.val lo) lo hi
    | 11 => verifyShapeRangeJoin 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest ∧
        extGlToK (aggrParseRange w.child0Preimage).residual +
          extGlToK (aggrParseRange w.child1Preimage).residual =
          extGlToK (aggrParseRange w.outputBytes).residual
    | 12 => verifyShapeRangeRoot 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        packDigest (blake3HashBytes w.rangeVkBytes) = ap.ixvmVkDigest ∧
        (readSystem w.rangeVkBytes).ok = 1
    | 13 => verifyShapeDischargeBinding 1 0 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 0 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest ∧
        (aggrParseCheckEnv w.child0Preimage).ctx.validator = 4 ∧
        (aggrParseCheckEnv w.outputBytes).ctx.validator = 3
    | 14 => verifyShapeDischargeBinding 1 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 0 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest ∧
        (aggrParseCheckEnv w.child0Preimage).ctx.validator = 4 ∧
        (aggrParseCheckEnv w.outputBytes).ctx.validator = 3
    | 15 => verifyShapeCrossBinding 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest ∧
        (aggrParseCheckEnv w.outputBytes).ctx.validator = 5
    | 16 => verifyShapeCatalogJoin 1 ap allowedDigest outClaimDigest w = 1 ∧
        ChildDigestAccepted 1 ap allowedDigest w.child0
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
        ChildDigestAccepted 1 ap allowedDigest w.child1
          (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest
    | 17 => verifyShapeDynamicLink 1 ap allowedDigest outClaimDigest w = 1 ∧
        PureVerifiedChild w.child0 ∧
        Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams (readSystem w.child0.vkBytes).val.params)
    | 18 => verifyShapeDischargeEval 1 ap allowedDigest outClaimDigest w = 1 ∧
        let p0 := aggrParseEvalAssumed w.child0Preimage
        let pOut := aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator
        pOut.ok = 1 ∧
        pOut.ctx.validator ≠ 3 ∧ pOut.ctx.validator ≠ 4 ∧ pOut.ctx.validator ≠ 5
    | _ => False

private theorem aggrAssertSameContext_validator_eq {a b : CheckEnvCtx}
    (h : ¬ (aggrAssertSameContext a b == 0) = true) : a.validator = b.validator := by
  have hne : aggrAssertSameContext a b ≠ 0 := by simpa [beq_iff_eq] using h
  unfold aggrAssertSameContext aggrAssertSameContextBase at hne
  split at hne
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.2
  · exact absurd rfl hne

private theorem aggrParseRange_valid {bs : ByteList}
    (hok : ¬ ((aggrParseRange bs).ok == 0) = true) :
    ValidU64Bytes (aggrParseRange bs).lo ∧
    ValidU64Bytes (aggrParseRange bs).hi ∧
    glLtPBytes (aggrParseRange bs).lo = 1 ∧
    glLtPBytes (aggrParseRange bs).hi = 1 := by
  revert hok
  unfold aggrParseRange
  extract_lets bad rTag rd rLo rHi r0 r1 r2
  have hbad : bad.ok = 0 := rfl
  have hrLo : rLo = readU64LE rd.rest := rfl
  have hrHi : rHi = readU64LE rLo.rest := rfl
  clear_value bad rTag rd rLo rHi r0 r1 r2
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  rename_i h3
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  rename_i h4
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  split; · intro h; rw [hbad] at h; exact absurd rfl h
  cases r2.rest with
  | cons _ _ => intro h; rw [hbad] at h; exact absurd rfl h
  | nil =>
    intro _
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h3 h4
    have hloOk : (readU64LE rd.rest).ok = 1 :=
      (readU64LE_ok_zero_or_one rd.rest).resolve_left (by rw [← hrLo]; exact h3.1)
    have hhiOk : (readU64LE rLo.rest).ok = 1 :=
      (readU64LE_ok_zero_or_one rLo.rest).resolve_left (by rw [← hrHi]; exact h4.1)
    have hvLo : ValidU64Bytes rLo.val := by rw [hrLo]; exact (readU64LE_sound rd.rest hloOk).1
    have hvHi : ValidU64Bytes rHi.val := by rw [hrHi]; exact (readU64LE_sound rLo.rest hhiOk).1
    exact ⟨hvLo, hvHi,
      (glLtPBytes_zero_or_one _).resolve_left h3.2,
      (glLtPBytes_zero_or_one _).resolve_left h4.2⟩

private theorem u64BytesLe_zero_or_one (x y : U64Bytes) :
    u64BytesLe x y = 0 ∨ u64BytesLe x y = 1 := by
  unfold u64BytesLe
  split; · (split <;> simp)
  split; · (split <;> simp)
  split; · (split <;> simp)
  split; · (split <;> simp)
  split; · (split <;> simp)
  split; · (split <;> simp)
  split; · (split <;> simp)
  split <;> simp

private theorem aggrVerifyRangeWithFloor_ok_01 (sys : SysKey) :
    ∀ (n : Nat) (hs : ShardHeaderList) (ps : ShardProofList) (s : Nat)
      (inp : ByteList) (l f a : ExtGl),
      (aggrVerifyRangeWithFloor 1 sys hs ps s n inp l f a).ok = 0 ∨
      (aggrVerifyRangeWithFloor 1 sys hs ps s n inp l f a).ok = 1
  | 0, _, ps, _, _, _, _, _ => by
    cases ps with
    | nil => exact Or.inr rfl
    | cons _ _ => exact Or.inl rfl
  | n + 1, hs, ps, s, inp, l, f, a => by
    cases hs with
    | nil => exact Or.inl rfl
    | cons h hrest =>
      cases ps with
      | nil => exact Or.inl rfl
      | cons p prest =>
        unfold aggrVerifyRangeWithFloor; dsimp only
        split
        · exact Or.inl rfl
        · exact aggrVerifyRangeWithFloor_ok_01 sys n hrest prest (s + 1) inp l f _

private theorem verifyShapeRangeLeaf_sound {ap : AllowedParams}
    {outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hok : verifyShapeRangeLeaf 1 ap outClaimDigest w = 1) :
    packDigest (blake3HashBytes w.rangeVkBytes) = ap.ixvmVkDigest ∧
    (readSystem w.rangeVkBytes).ok = 1 ∧
    let sys := (readSystem w.rangeVkBytes).val
    let pRng := aggrParseRange w.outputBytes
    let pPre := aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes
    let bfs := batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit) pPre.headers pPre.messages
    let lo := glValBytes pRng.lo
    let hi := glValBytes pRng.hi
    lo ≤ hi ∧
    let rCnt := readCount w.rangeShardProofsBytes
    let rPrfs := readShardProofVecN rCnt.rest (hi - lo)
    shardProofListLen rPrfs.val = hi - lo ∧
    ShardsAllAccepted sys (shardHeaderListTake (hi - lo) (shardHeaderListDrop lo pPre.headers))
      rPrfs.val lo bfs.input bfs.lch bfs.fch ∧
    extGlToK pRng.residual =
      _root_.Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid (shardProofResidualAt rPrfs.val lo) lo hi := by
  dsimp only
  unfold verifyShapeRangeLeaf at hok
  obtain ⟨hvk, hok⟩ := ite_nat_eq_one_right hok
  have hvkEq := (digest32WordsEq_eq_one_iff _ _).mp
    ((digest32WordsEq_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hvk))
  generalize hpSys : readSystem w.rangeVkBytes = pSys at hok ⊢
  obtain ⟨hsys, hok⟩ := ite_nat_eq_one_right hok
  have hsys1 : pSys.ok = 1 := by
    rw [← hpSys]; exact (readSystem_ok_zero_or_one w.rangeVkBytes).resolve_left (by rw [hpSys]; simpa [beq_iff_eq] using hsys)
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hpRng : aggrParseRange w.outputBytes = pRng at hok ⊢
  obtain ⟨hrng, hok⟩ := ite_nat_eq_one_right hok
  have hrngValid : ValidU64Bytes pRng.lo ∧ ValidU64Bytes pRng.hi ∧
      glLtPBytes pRng.lo = 1 ∧ glLtPBytes pRng.hi = 1 := by
    rw [← hpRng]; exact aggrParseRange_valid (by rw [hpRng]; exact hrng)
  generalize hpPre : aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes = pPre at hok ⊢
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hbfs : batchFiatShamir pSys.val.transcriptLimbs (optCommitCap pSys.val.prepCommit) pPre.headers pPre.messages = bfs at hok ⊢
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  obtain ⟨hle0, hok⟩ := ite_nat_eq_one_right hok
  have hle1 : u64BytesLe pRng.lo pRng.hi = 1 :=
    (u64BytesLe_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hle0)
  have hloLeHi : glValBytes pRng.lo ≤ glValBytes pRng.hi := by
    rw [(glValBytes_of_ltP hrngValid.1 hrngValid.2.2.1).1,
        (glValBytes_of_ltP hrngValid.2.1 hrngValid.2.2.2).1]
    exact (u64BytesLe_eq_one_iff hrngValid.1 hrngValid.2.1).mp hle1
  generalize hlo : glValBytes pRng.lo = lo at hok hloLeHi ⊢
  generalize hhi : glValBytes pRng.hi = hi at hok hloLeHi ⊢
  generalize hrCnt : readCount w.rangeShardProofsBytes = rCnt at hok ⊢
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  generalize hrPrfs : readShardProofVecN rCnt.rest (hi - lo) = rPrfs at hok ⊢
  obtain ⟨_, hok⟩ := ite_nat_eq_one_right hok
  cases hrest : rPrfs.rest with
  | cons _ _ => rw [hrest] at hok; cases hok
  | nil =>
    rw [hrest] at hok
    generalize hvr : aggrVerifyRangeWithFloor 1 pSys.val
      (shardHeaderListDrop lo pPre.headers) rPrfs.val lo (hi - lo) bfs.input bfs.lch bfs.fch extZero = vr at hok
    dsimp only at hok
    obtain ⟨hvr0, hEqRes⟩ := ite_nat_eq_one_right hok
    have hvr1 : (aggrVerifyRangeWithFloor 1 pSys.val
        (shardHeaderListDrop lo pPre.headers) rPrfs.val lo (hi - lo) bfs.input bfs.lch bfs.fch extZero).ok = 1 :=
      (aggrVerifyRangeWithFloor_ok_01 _ _ _ _ _ _ _ _ _).resolve_left
        (by rw [hvr]; simpa [beq_iff_eq] using hvr0)
    obtain ⟨hplen, hShards, hsum⟩ := aggrVerifyRange_sound _ _ _ _ _ _ _ _ _ hvr1
    have hResEq := (extGlToK_eq_iff _ _).mp hEqRes
    have hhiEq : lo + (hi - lo) = hi := by omega
    rw [hvr, extGlToK_zero, zero_add, hhiEq] at hsum
    have hfinal : extGlToK pRng.residual =
        _root_.Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid (shardProofResidualAt rPrfs.val lo) lo hi :=
      hResEq.symm.trans hsum
    exact ⟨hvkEq, hsys1, hloLeHi, hplen, hShards, hfinal⟩

private theorem verifyShapeWrap_sound {k : Nat} {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeWrap 1 k ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted k ap allowedDigest w.child0 outClaimDigest := by
  unfold verifyShapeWrap at hp
  generalize hcDef : verifyChildDigestWithFloor 1 k ap allowedDigest w.child0 = c at hp
  obtain ⟨h0, hEq⟩ := ite_nat_eq_one_right hp
  have hc := verifyChildDigest_sound
    ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcDef]; simpa [beq_iff_eq] using h0))
  have hdig : c.digest = outClaimDigest := (digest32WordsEq_eq_one_iff _ _).mp hEq
  rw [hcDef, hdig] at hc
  exact hc

private theorem verifyShapePairFlat_sound {lk rk : Nat} {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapePairFlat 1 lk rk ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted lk ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 lk ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted rk ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 rk ap allowedDigest w.child1).digest := by
  unfold verifyShapePairFlat at hp
  generalize hcL : verifyChildDigestWithFloor 1 lk ap allowedDigest w.child0 = cL at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcR : verifyChildDigestWithFloor 1 rk ap allowedDigest w.child1 = cR at hp
  obtain ⟨h1, _⟩ := ite_nat_eq_one_right hp
  exact ⟨by rw [← hcL]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcL]; simpa [beq_iff_eq] using h0)),
         by rw [← hcR]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcR]; simpa [beq_iff_eq] using h1))⟩

private theorem verifyShapePairStructural_sound {lk rk : Nat} {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapePairStructural 1 lk rk ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted lk ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 lk ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted rk ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 rk ap allowedDigest w.child1).digest := by
  unfold verifyShapePairStructural at hp
  generalize hcL : verifyChildDigestWithFloor 1 lk ap allowedDigest w.child0 = cL at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcR : verifyChildDigestWithFloor 1 rk ap allowedDigest w.child1 = cR at hp
  obtain ⟨h1, _⟩ := ite_nat_eq_one_right hp
  exact ⟨by rw [← hcL]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcL]; simpa [beq_iff_eq] using h0)),
         by rw [← hcR]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcR]; simpa [beq_iff_eq] using h1))⟩

private theorem verifyShapeRangeJoin_sound {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeRangeJoin 1 ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted 1 ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted 1 ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest ∧
    extGlToK (aggrParseRange w.child0Preimage).residual +
      extGlToK (aggrParseRange w.child1Preimage).residual =
      extGlToK (aggrParseRange w.outputBytes).residual := by
  unfold verifyShapeRangeJoin at hp
  generalize hcL : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0 = cL at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcR : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1 = cR at hp
  obtain ⟨h1, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hpL : aggrParseRange w.child0Preimage = pL at hp
  generalize hpR : aggrParseRange w.child1Preimage = pR at hp
  generalize hpO : aggrParseRange w.outputBytes = pO at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hEq⟩ := ite_nat_eq_one_right hp
  have hsum : extGlToK pL.residual + extGlToK pR.residual = extGlToK pO.residual := by
    rw [← extGlToK_add]; exact (extGlToK_eq_iff _ _).mp hEq
  exact ⟨by rw [← hcL]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcL]; simpa [beq_iff_eq] using h0)),
         by rw [← hcR]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcR]; simpa [beq_iff_eq] using h1)),
         hsum⟩

private theorem verifyShapeRangeRoot_sound {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeRangeRoot 1 ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted 1 ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
    packDigest (blake3HashBytes w.rangeVkBytes) = ap.ixvmVkDigest ∧
    (readSystem w.rangeVkBytes).ok = 1 := by
  unfold verifyShapeRangeRoot at hp
  generalize hc0 : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0 = c0 at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hpRng : aggrParseRange w.child0Preimage = pRng at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨hvk, hp⟩ := ite_nat_eq_one_right hp
  generalize hpSys : readSystem w.rangeVkBytes = pSys at hp
  obtain ⟨hsys, _⟩ := ite_nat_eq_one_right hp
  have hvkEq := (digest32WordsEq_eq_one_iff _ _).mp
    ((digest32WordsEq_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hvk))
  have hsys1 : pSys.ok = 1 := by
    rw [← hpSys]; exact (readSystem_ok_zero_or_one w.rangeVkBytes).resolve_left
      (by rw [hpSys]; simpa [beq_iff_eq] using hsys)
  exact ⟨by rw [← hc0]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hc0]; simpa [beq_iff_eq] using h0)),
         hvkEq, hsys1⟩

private theorem verifyShapeDischargeBinding_sound {k : Nat} {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeDischargeBinding 1 k ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted k ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 k ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted 0 ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1).digest ∧
    (aggrParseCheckEnv w.child0Preimage).ctx.validator = 4 ∧
    (aggrParseCheckEnv w.outputBytes).ctx.validator = 3 := by
  unfold verifyShapeDischargeBinding at hp
  generalize hc0 : verifyChildDigestWithFloor 1 k ap allowedDigest w.child0 = c0 at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcB : verifyChildDigestWithFloor 1 0 ap allowedDigest w.child1 = cB at hp
  obtain ⟨h1, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hpC : aggrParseCheckEnv w.child0Preimage = pC at hp
  obtain ⟨hpc, hp⟩ := ite_nat_eq_one_right hp
  generalize hpB : aggrParseBinding w.child1Preimage = pB at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hpO : aggrParseCheckEnv w.outputBytes = pO at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨hsame, _⟩ := ite_nat_eq_one_right hp
  have hv4 : pC.ctx.validator = 4 := by
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, not_or, not_not] at hpc
    exact hpc.2
  have hctx3 : pO.ctx.validator = 3 :=
    (aggrAssertSameContext_validator_eq hsame).symm
  exact ⟨by rw [← hc0]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hc0]; simpa [beq_iff_eq] using h0)),
         by rw [← hcB]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcB]; simpa [beq_iff_eq] using h1)),
         hv4, hctx3⟩

private theorem verifyShapeCrossBinding_sound {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeCrossBinding 1 ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted 1 ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted 1 ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest ∧
    (aggrParseCheckEnv w.outputBytes).ctx.validator = 5 := by
  unfold verifyShapeCrossBinding at hp
  generalize hcL : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0 = cL at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcR : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1 = cR at hp
  obtain ⟨h1, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hpL : aggrParseCheckEnv w.child0Preimage = pL at hp
  generalize hpR : aggrParseCheckEnv w.child1Preimage = pR at hp
  generalize hpO : aggrParseCheckEnv w.outputBytes = pO at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  generalize hclsL : aggrContextClass pL.ctx w.extraPreimage0 = clsL at hp
  generalize hclsR : aggrContextClass pR.ctx w.extraPreimage1 = clsR at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨hsame, _⟩ := ite_nat_eq_one_right hp
  have hv5 : pO.ctx.validator = 5 := by
    unfold aggrAssertSameContextBase at hsame
    split at hsame
    · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.2.symm
    · exact absurd rfl hsame
  exact ⟨by rw [← hcL]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcL]; simpa [beq_iff_eq] using h0)),
         by rw [← hcR]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcR]; simpa [beq_iff_eq] using h1)),
         hv5⟩

private theorem verifyShapeCatalogJoin_sound {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeCatalogJoin 1 ap allowedDigest outClaimDigest w = 1) :
    ChildDigestAccepted 1 ap allowedDigest w.child0
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0).digest ∧
    ChildDigestAccepted 1 ap allowedDigest w.child1
      (verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1).digest := by
  unfold verifyShapeCatalogJoin at hp
  generalize hcL : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child0 = cL at hp
  obtain ⟨h0, hp⟩ := ite_nat_eq_one_right hp
  generalize hcR : verifyChildDigestWithFloor 1 1 ap allowedDigest w.child1 = cR at hp
  obtain ⟨h1, _⟩ := ite_nat_eq_one_right hp
  exact ⟨by rw [← hcL]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcL]; simpa [beq_iff_eq] using h0)),
         by rw [← hcR]; exact verifyChildDigest_sound ((verifyChildDigest_ok_01 _ _ _ _).resolve_left (by rw [hcR]; simpa [beq_iff_eq] using h1))⟩

private theorem verifyShapeDynamicLink_sound {ap : AllowedParams}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hp : verifyShapeDynamicLink 1 ap allowedDigest outClaimDigest w = 1) :
    PureVerifiedChild w.child0 ∧
    Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams (readSystem w.child0.vkBytes).val.params) := by
  unfold verifyShapeDynamicLink at hp
  generalize hext : bytesToAddr w.child0.vkBytes = extVkAddr at hp
  generalize hpSys : readSystem w.child0.vkBytes = pSys at hp
  obtain ⟨_, hp⟩ := ite_nat_eq_one_right hp
  obtain ⟨henv, hp⟩ := ite_nat_eq_one_right hp
  generalize hvc : verifyChildBatchWithFloor 1 w.child0 = vc at hp
  obtain ⟨hvc0, _⟩ := ite_nat_eq_one_right hp
  have henv01 : ∀ p, aggrAssertSecurityEnvelope p = 0 ∨ aggrAssertSecurityEnvelope p = 1 := fun p => by
    unfold aggrAssertSecurityEnvelope
    split; · exact Or.inl rfl
    split; · exact Or.inl rfl
    split; · exact Or.inl rfl
    exact checkSecurityFloor_zero_or_one p
  have henv1 : aggrAssertSecurityEnvelope pSys.val.params = 1 := by
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, not_and] at henv
    exact (henv01 _).resolve_left (henv (by decide))
  have hvc1 := (verifyChildBatchWithFloor_ok_01 1 w.child0).resolve_left
    (by rw [hvc]; simpa [beq_iff_eq] using hvc0)
  exact ⟨(verifyChildBatch_sound hvc1).1, (aggrAssertSecurityEnvelope_iff _).mp henv1⟩

/-- **Headline Single-Step Soundness (`verifyAggregateStep_sound`):**
Any input accepted by `AggregatePure.verifyAggregateStep` satisfies the complete 19-shape
mathematical postcondition `AggregateStepAccepted` (including exact 80-byte allowed-blob pin,
`CompressWrapAccepted` on every child proof, Shape 10 range-leaf `ShardAccepted` & `K` sum,
Shape 17 `SecurityEnvelopeOk`, and Shape 18 validator `14`/`15` & `12`/`13` isolation)! -/
theorem verifyAggregateStep_sound
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1) :
    AggregateStepAccepted allowedDigest outClaimDigest w := by
  unfold verifyAggregateStep verifyAggregateStepWithFloor at hok
  generalize hpa : parseAllowedBlob allowedDigest w.allowedBytes = pa at hok
  obtain ⟨hpa0, hok⟩ := ite_nat_eq_one_right hok
  have hpa1 := (parseAllowedBlob_ok_01 allowedDigest w.allowedBytes).resolve_left
    (by rw [hpa]; simpa [beq_iff_eq] using hpa0)
  have hAllow := parseAllowedBlob_sound hpa1
  rw [← hpa] at hok
  -- Case split on `w.shape` across all 19 shapes `0..18`
  rcases hsh : w.shape with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n'
  · -- Shape 0: wrap IxVM
    simp only [hsh, beq_self_eq_true, ↓reduceIte] at hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact verifyShapeWrap_sound hok⟩
  · -- Shape 1: wrap Aggr
    simp only [hsh, show (1 == 0) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact verifyShapeWrap_sound hok⟩
  · -- Shape 2: pairFlat 0 0
    simp only [hsh, show (2 == 0) = false from rfl, show (2 == 1) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairFlat_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 3: pairFlat 0 1
    simp only [hsh, show (3 == 0) = false from rfl, show (3 == 1) = false from rfl, show (3 == 2) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairFlat_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 4: pairFlat 1 0
    simp only [hsh, show (4 == 0) = false from rfl, show (4 == 1) = false from rfl, show (4 == 2) = false from rfl, show (4 == 3) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairFlat_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 5: pairFlat 1 1
    simp only [hsh, show (5 == 0) = false from rfl, show (5 == 1) = false from rfl, show (5 == 2) = false from rfl, show (5 == 3) = false from rfl, show (5 == 4) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairFlat_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 6: pairStructural 0 0
    simp only [hsh, show (6 == 0) = false from rfl, show (6 == 1) = false from rfl, show (6 == 2) = false from rfl, show (6 == 3) = false from rfl, show (6 == 4) = false from rfl, show (6 == 5) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairStructural_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 7: pairStructural 0 1
    simp only [hsh, show (7 == 0) = false from rfl, show (7 == 1) = false from rfl, show (7 == 2) = false from rfl, show (7 == 3) = false from rfl, show (7 == 4) = false from rfl, show (7 == 5) = false from rfl, show (7 == 6) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairStructural_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 8: pairStructural 1 0
    simp only [hsh, show (8 == 0) = false from rfl, show (8 == 1) = false from rfl, show (8 == 2) = false from rfl, show (8 == 3) = false from rfl, show (8 == 4) = false from rfl, show (8 == 5) = false from rfl, show (8 == 6) = false from rfl, show (8 == 7) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairStructural_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 9: pairStructural 1 1
    simp only [hsh, show (9 == 0) = false from rfl, show (9 == 1) = false from rfl, show (9 == 2) = false from rfl, show (9 == 3) = false from rfl, show (9 == 4) = false from rfl, show (9 == 5) = false from rfl, show (9 == 6) = false from rfl, show (9 == 7) = false from rfl, show (9 == 8) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hp := verifyShapePairStructural_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hp.1, hp.2⟩⟩
  · -- Shape 10: rangeLeaf
    simp only [hsh, show (10 == 0) = false from rfl, show (10 == 1) = false from rfl, show (10 == 2) = false from rfl, show (10 == 3) = false from rfl, show (10 == 4) = false from rfl, show (10 == 5) = false from rfl, show (10 == 6) = false from rfl, show (10 == 7) = false from rfl, show (10 == 8) = false from rfl, show (10 == 9) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨hvkEq, hsys1, hloLeHi, hplen, _, hsum⟩ := verifyShapeRangeLeaf_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hvkEq, hsys1, hloLeHi, hplen, hsum⟩⟩
  · -- Shape 11: rangeJoin
    simp only [hsh, show (11 == 0) = false from rfl, show (11 == 1) = false from rfl, show (11 == 2) = false from rfl, show (11 == 3) = false from rfl, show (11 == 4) = false from rfl, show (11 == 5) = false from rfl, show (11 == 6) = false from rfl, show (11 == 7) = false from rfl, show (11 == 8) = false from rfl, show (11 == 9) = false from rfl, show (11 == 10) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, h1, hsum⟩ := verifyShapeRangeJoin_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, h1, hsum⟩⟩
  · -- Shape 12: rangeRoot
    simp only [hsh, show (12 == 0) = false from rfl, show (12 == 1) = false from rfl, show (12 == 2) = false from rfl, show (12 == 3) = false from rfl, show (12 == 4) = false from rfl, show (12 == 5) = false from rfl, show (12 == 6) = false from rfl, show (12 == 7) = false from rfl, show (12 == 8) = false from rfl, show (12 == 9) = false from rfl, show (12 == 10) = false from rfl, show (12 == 11) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, hvkEq, hsys1⟩ := verifyShapeRangeRoot_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, hvkEq, hsys1⟩⟩
  · -- Shape 13: dischargeBinding 0
    simp only [hsh, show (13 == 0) = false from rfl, show (13 == 1) = false from rfl, show (13 == 2) = false from rfl, show (13 == 3) = false from rfl, show (13 == 4) = false from rfl, show (13 == 5) = false from rfl, show (13 == 6) = false from rfl, show (13 == 7) = false from rfl, show (13 == 8) = false from rfl, show (13 == 9) = false from rfl, show (13 == 10) = false from rfl, show (13 == 11) = false from rfl, show (13 == 12) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, h1, hv4, hv3⟩ := verifyShapeDischargeBinding_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, h1, hv4, hv3⟩⟩
  · -- Shape 14: dischargeBinding 1
    simp only [hsh, show (14 == 0) = false from rfl, show (14 == 1) = false from rfl, show (14 == 2) = false from rfl, show (14 == 3) = false from rfl, show (14 == 4) = false from rfl, show (14 == 5) = false from rfl, show (14 == 6) = false from rfl, show (14 == 7) = false from rfl, show (14 == 8) = false from rfl, show (14 == 9) = false from rfl, show (14 == 10) = false from rfl, show (14 == 11) = false from rfl, show (14 == 12) = false from rfl, show (14 == 13) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, h1, hv4, hv3⟩ := verifyShapeDischargeBinding_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, h1, hv4, hv3⟩⟩
  · -- Shape 15: crossBinding
    simp only [hsh, show (15 == 0) = false from rfl, show (15 == 1) = false from rfl, show (15 == 2) = false from rfl, show (15 == 3) = false from rfl, show (15 == 4) = false from rfl, show (15 == 5) = false from rfl, show (15 == 6) = false from rfl, show (15 == 7) = false from rfl, show (15 == 8) = false from rfl, show (15 == 9) = false from rfl, show (15 == 10) = false from rfl, show (15 == 11) = false from rfl, show (15 == 12) = false from rfl, show (15 == 13) = false from rfl, show (15 == 14) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, h1, hv5⟩ := verifyShapeCrossBinding_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, h1, hv5⟩⟩
  · -- Shape 16: catalogJoin
    simp only [hsh, show (16 == 0) = false from rfl, show (16 == 1) = false from rfl, show (16 == 2) = false from rfl, show (16 == 3) = false from rfl, show (16 == 4) = false from rfl, show (16 == 5) = false from rfl, show (16 == 6) = false from rfl, show (16 == 7) = false from rfl, show (16 == 8) = false from rfl, show (16 == 9) = false from rfl, show (16 == 10) = false from rfl, show (16 == 11) = false from rfl, show (16 == 12) = false from rfl, show (16 == 13) = false from rfl, show (16 == 14) = false from rfl, show (16 == 15) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨h0, h1⟩ := verifyShapeCatalogJoin_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, h0, h1⟩⟩
  · -- Shape 17: dynamicLink
    simp only [hsh, show (17 == 0) = false from rfl, show (17 == 1) = false from rfl, show (17 == 2) = false from rfl, show (17 == 3) = false from rfl, show (17 == 4) = false from rfl, show (17 == 5) = false from rfl, show (17 == 6) = false from rfl, show (17 == 7) = false from rfl, show (17 == 8) = false from rfl, show (17 == 9) = false from rfl, show (17 == 10) = false from rfl, show (17 == 11) = false from rfl, show (17 == 12) = false from rfl, show (17 == 13) = false from rfl, show (17 == 14) = false from rfl, show (17 == 15) = false from rfl, show (17 == 16) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨hvc, henv⟩ := verifyShapeDynamicLink_sound hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hvc, henv⟩⟩
  · -- Shape 18: dischargeEval
    simp only [hsh, show (18 == 0) = false from rfl, show (18 == 1) = false from rfl, show (18 == 2) = false from rfl, show (18 == 3) = false from rfl, show (18 == 4) = false from rfl, show (18 == 5) = false from rfl, show (18 == 6) = false from rfl, show (18 == 7) = false from rfl, show (18 == 8) = false from rfl, show (18 == 9) = false from rfl, show (18 == 10) = false from rfl, show (18 == 11) = false from rfl, show (18 == 12) = false from rfl, show (18 == 13) = false from rfl, show (18 == 14) = false from rfl, show (18 == 15) = false from rfl, show (18 == 16) = false from rfl, show (18 == 17) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at hok
    have hm := verifyShapeDischargeEval_mode_isolation hok
    exact ⟨hAllow, by omega, by simp [hsh]; exact ⟨hok, hm.2.2.2.2.2.1, hm.2.2.2.2.2.2.1⟩⟩
  · -- Shape ≥ 19: rejected!
    simp only [hsh] at hok
    have hne : ∀ k < 19, (n' + 19 == k) = false := fun k hk => beq_false_of_ne (by omega)
    simp only [hne 0 (by omega), hne 1 (by omega), hne 2 (by omega), hne 3 (by omega),
      hne 4 (by omega), hne 5 (by omega), hne 6 (by omega), hne 7 (by omega),
      hne 8 (by omega), hne 9 (by omega), hne 10 (by omega), hne 11 (by omega),
      hne 12 (by omega), hne 13 (by omega), hne 14 (by omega), hne 15 (by omega),
      hne 16 (by omega), hne 17 (by omega), hne 18 (by omega),
      Bool.false_eq_true, ↓reduceIte] at hok
    cases hok

/-- Inductive recursive soundness postcondition for a full `AggrTreeWitness`:
every node passes `AggregateStepAccepted` at the EXACT same pinned `allowedDigest`, and every
recursive child subtree is verified at the EXACT claim digest extracted from its parent! -/
inductive AggregateRootAccepted (allowedDigest : Digest32Words) :
    Digest32Words → AggrTreeWitness → Prop where
  | step0 {outDig s} :
      stepHasRecChild0 s = 0 → stepHasRecChild1 s = 0 →
      AggregateStepAccepted allowedDigest outDig s →
      AggregateRootAccepted allowedDigest outDig (.step0 s)
  | step1Left {outDig s sub} :
      stepHasRecChild0 s = 1 → stepHasRecChild1 s = 0 →
      AggregateStepAccepted allowedDigest outDig s →
      AggregateRootAccepted allowedDigest (extractRecursiveChildDigest s.child0.claimsBytes) sub →
      AggregateRootAccepted allowedDigest outDig (.step1 s sub)
  | step1Right {outDig s sub} :
      stepHasRecChild0 s = 0 → stepHasRecChild1 s = 1 →
      AggregateStepAccepted allowedDigest outDig s →
      AggregateRootAccepted allowedDigest (extractRecursiveChildDigest s.child1.claimsBytes) sub →
      AggregateRootAccepted allowedDigest outDig (.step1 s sub)
  | step2 {outDig s sub0 sub1} :
      stepHasRecChild0 s = 1 → stepHasRecChild1 s = 1 →
      AggregateStepAccepted allowedDigest outDig s →
      AggregateRootAccepted allowedDigest (extractRecursiveChildDigest s.child0.claimsBytes) sub0 →
      AggregateRootAccepted allowedDigest (extractRecursiveChildDigest s.child1.claimsBytes) sub1 →
      AggregateRootAccepted allowedDigest outDig (.step2 s sub0 sub1)

private theorem aggrAssertSameList_ok_01 (a b : DigestBytesList) :
    aggrAssertSameList a b = 0 ∨ aggrAssertSameList a b = 1 := by
  induction a generalizing b with
  | nil => cases b <;> simp [aggrAssertSameList]
  | cons _ _ ih =>
    cases b with
    | nil => exact Or.inl rfl
    | cons _ _ =>
      unfold aggrAssertSameList; dsimp only
      split
      · exact ih _
      · exact Or.inl rfl

private theorem aggrAssertUnionFuel_ok_01 :
    ∀ f l r o, aggrAssertUnionFuel f l r o = 0 ∨ aggrAssertUnionFuel f l r o = 1
  | 0, _, _, _ => Or.inl rfl
  | f + 1, .nil, r, o => aggrAssertSameList_ok_01 r o
  | f + 1, .cons a ar, .nil, o => aggrAssertSameList_ok_01 (.cons a ar) o
  | f + 1, .cons _ _, .cons _ _, .nil => Or.inl rfl
  | f + 1, .cons a ar, .cons b br, .cons o or_ => by
    unfold aggrAssertUnionFuel; dsimp only
    split
    · split
      · exact aggrAssertUnionFuel_ok_01 f ar (.cons b br) or_
      · exact Or.inl rfl
    · split
      · split
        · exact aggrAssertUnionFuel_ok_01 f ar br or_
        · exact Or.inl rfl
      · split
        · exact aggrAssertUnionFuel_ok_01 f (.cons a ar) br or_
        · exact Or.inl rfl

private theorem aggrAssertDifferenceFuel_ok_01 :
    ∀ f l r s o, aggrAssertDifferenceFuel f l r s o = 0 ∨ aggrAssertDifferenceFuel f l r s o = 1
  | 0, _, _, _, _ => Or.inl rfl
  | f + 1, l, r, s, o => by
    unfold aggrAssertDifferenceFuel
    cases aggrNextAssumption l r with
    | done => cases o <;> simp
    | more _ _ _ _ =>
      dsimp only; split
      · exact aggrAssertDifferenceFuel_ok_01 f _ _ _ _
      · cases o with
        | nil => exact Or.inl rfl
        | cons _ _ =>
          dsimp only; split
          · exact aggrAssertDifferenceFuel_ok_01 f _ _ _ _
          · exact Or.inl rfl

private theorem aggrAssertStructuralDifferenceFuel_ok_01 :
    ∀ f l r lr rr o p,
      aggrAssertStructuralDifferenceFuel f l r lr rr o p = 0 ∨
      aggrAssertStructuralDifferenceFuel f l r lr rr o p = 1
  | 0, _, _, _, _, _, _ => Or.inl rfl
  | f + 1, l, r, lr, rr, o, p => by
    unfold aggrAssertStructuralDifferenceFuel
    cases aggrNextAssumption l r with
    | done => cases o <;> simp
    | more _ _ _ _ =>
      dsimp only
      apply ite_zero_or_one
      split
      · exact aggrAssertStructuralDifferenceFuel_ok_01 f _ _ _ _ _ _
      · cases o with
        | nil => exact Or.inl rfl
        | cons _ _ =>
          dsimp only; split
          · exact aggrAssertStructuralDifferenceFuel_ok_01 f _ _ _ _ _ _
          · exact Or.inl rfl

private theorem aggrAssertAxiomsMerge_ok_01 (l r o : OptAddr) (a b c : ByteList) :
    aggrAssertAxiomsMerge l r o a b c = 0 ∨ aggrAssertAxiomsMerge l r o a b c = 1 := by
  unfold aggrAssertAxiomsMerge
  cases l with
  | none => exact optAddrEq_zero_or_one r o
  | some _ =>
    cases r with
    | none => exact optAddrEq_zero_or_one _ o
    | some _ =>
      dsimp only
      split
      · exact optAddrEq_zero_or_one _ o
      · cases o with
        | none => exact Or.inl rfl
        | some _ =>
          dsimp only
          split
          · exact aggrAssertUnionFuel_ok_01 _ _ _ _
          · exact Or.inl rfl

private theorem extEq_ok_01 (a b : ExtGl) : extEq a b = 0 ∨ extEq a b = 1 := by
  have hgl : ∀ x y, glEq x y = 0 ∨ glEq x y = 1 := fun x y => by unfold glEq; split <;> simp
  unfold extEq
  split
  · split
    · exact hgl _ _
    · exact Or.inl rfl
  · exact Or.inl rfl

private theorem aggrVerifyBridgeCert_ok_01 (ef : Nat) (bSpec bBind certConst : DigestBytes)
    (ap : AllowedParams) (ad : Digest32Words) (w : AggrStepWitness) :
    aggrVerifyBridgeCert ef bSpec bBind certConst ap ad w = 0 ∨
    aggrVerifyBridgeCert ef bSpec bBind certConst ap ad w = 1 := by
  unfold aggrVerifyBridgeCert
  extract_lets cCert certClaimAddr rTag pC1 pC2
  clear_value cCert certClaimAddr rTag pC1 pC2
  repeat apply ite_zero_or_one
  apply ite_both_zero_or_one
  · repeat apply ite_zero_or_one
    apply ite_both_zero_or_one (Or.inr rfl) (Or.inl rfl)
  · apply ite_both_zero_or_one
    · repeat apply ite_zero_or_one
      exact digestBytesEq_zero_or_one _ _
    · exact Or.inl rfl

private theorem verifyShapeDynamicLink_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeDynamicLink ef ap ad od w = 0 ∨ verifyShapeDynamicLink ef ap ad od w = 1 := by
  unfold verifyShapeDynamicLink
  extract_lets extVkAddr pSys vc oc pDL expectedClaim
  clear_value extVkAddr pSys vc oc pDL expectedClaim
  repeat apply ite_zero_or_one
  cases pDL.bridge with
  | noBridge => exact Or.inr rfl
  | someBridge _ _ _ _ _ =>
    apply ite_zero_or_one
    exact aggrVerifyBridgeCert_ok_01 _ _ _ _ _ _ _

private theorem verifyShapeDischargeEval_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeDischargeEval ef ap ad od w = 0 ∨ verifyShapeDischargeEval ef ap ad od w = 1 := by
  unfold verifyShapeDischargeEval
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef w.auxKind0 ap ad w.child0 = c0
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef w.auxKind1 ap ad w.child1 = c1
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseEvalAssumed w.child0Preimage = p0
  apply ite_zero_or_one
  generalize aggrParseEvalDischargeOut w.outputBytes p0.tag p0.ctx.validator = pOut
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrCheckCanonicalTree p0.evalRoot w.leftSubjTreeBytes = tEval0
  generalize aggrCheckOptionalTree pOut.evalOpt w.rightSubjTreeBytes = tEvalOut
  apply ite_zero_or_one
  generalize aggrExtractRemovedLeaf tEval0.val tEvalOut.val = rem
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseEvalAssumption w.extraPreimage0 = pLeaf
  apply ite_zero_or_one
  generalize readU8 w.child1Preimage = rC1Tag
  apply ite_zero_or_one
  apply ite_both_zero_or_one
  · generalize aggrParseCheck w.child1Preimage = pC1
    repeat apply ite_zero_or_one
    exact aggrAssertAxiomsMerge_ok_01 _ _ _ _ _ _
  · apply ite_both_zero_or_one
    · apply ite_zero_or_one
      generalize aggrParseDynamicLink w.child1Preimage = pDL
      apply ite_zero_or_one
      cases pLeaf.circuit with
      | noCircuitRef => exact Or.inl rfl
      | someCircuitRef _ _ =>
        cases pDL.bridge with
        | noBridge => exact Or.inl rfl
        | someBridge dlSpec dlBind tgtConst codec certConst =>
          dsimp (config := { zeta := false }) only
          apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
          apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
          generalize aggrLinkedEntryAddr pDL.vkDigest pDL.entryIdx codec tgtConst certConst
            pLeaf.typ dlSpec dlBind = entryAddr
          apply ite_zero_or_one
          exact aggrAssertAxiomsMerge_ok_01 _ _ _ _ _ _
    · exact Or.inl rfl

private theorem verifyShapeWrap_ok_01 (ef k : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeWrap ef k ap ad od w = 0 ∨ verifyShapeWrap ef k ap ad od w = 1 := by
  unfold verifyShapeWrap
  generalize verifyChildDigestWithFloor ef k ap ad w.child0 = c
  apply ite_zero_or_one
  exact digest32WordsEq_zero_or_one _ _

private theorem verifyShapePairFlat_ok_01 (ef lk rk : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapePairFlat ef lk rk ap ad od w = 0 ∨ verifyShapePairFlat ef lk rk ap ad od w = 1 := by
  unfold verifyShapePairFlat
  generalize verifyChildDigestWithFloor ef lk ap ad w.child0 = cL
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef rk ap ad w.child1 = cR
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCheckEnv w.child0Preimage = pL
  generalize aggrParseCheckEnv w.child1Preimage = pR
  generalize aggrParseCheckEnv w.outputBytes = pO
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrCheckCanonicalTree pL.root w.leftSubjTreeBytes = tLS
  generalize aggrCheckCanonicalTree pR.root w.rightSubjTreeBytes = tRS
  generalize aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes = tLA
  generalize aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes = tRA
  generalize aggrCheckCanonicalTree pO.root w.outSubjTreeBytes = tOS
  generalize aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes = tOA
  repeat apply ite_zero_or_one
  exact aggrAssertDifferenceFuel_ok_01 _ _ _ _ _

private theorem verifyShapePairStructural_ok_01 (ef lk rk : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapePairStructural ef lk rk ap ad od w = 0 ∨ verifyShapePairStructural ef lk rk ap ad od w = 1 := by
  unfold verifyShapePairStructural
  generalize verifyChildDigestWithFloor ef lk ap ad w.child0 = cL
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef rk ap ad w.child1 = cR
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCheckEnv w.child0Preimage = pL
  generalize aggrParseCheckEnv w.child1Preimage = pR
  generalize aggrParseCheckEnv w.outputBytes = pO
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes = tLA
  generalize aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes = tRA
  generalize aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes = tOA
  apply ite_zero_or_one
  exact aggrAssertStructuralDifferenceFuel_ok_01 _ _ _ _ _ _ _

private theorem verifyShapeRangeLeaf_ok_01 (ef : Nat) (ap : AllowedParams)
    (od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeRangeLeaf ef ap od w = 0 ∨ verifyShapeRangeLeaf ef ap od w = 1 := by
  unfold verifyShapeRangeLeaf
  apply ite_zero_or_one
  generalize readSystem w.rangeVkBytes = pSys
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseRange w.outputBytes = pRng
  apply ite_zero_or_one
  generalize aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes = pPre
  apply ite_zero_or_one
  generalize batchFiatShamir pSys.val.transcriptLimbs (optCommitCap pSys.val.prepCommit) pPre.headers pPre.messages = bfs
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize glValBytes pRng.lo = lo
  generalize glValBytes pRng.hi = hi
  generalize readCount w.rangeShardProofsBytes = rCnt
  apply ite_zero_or_one
  generalize readShardProofVecN rCnt.rest (hi - lo) = rPrfs
  apply ite_zero_or_one
  cases rPrfs.rest with
  | cons _ _ => exact Or.inl rfl
  | nil =>
    generalize aggrVerifyRangeWithFloor ef pSys.val
      (shardHeaderListDrop lo pPre.headers) rPrfs.val lo (hi - lo) bfs.input bfs.lch bfs.fch extZero = vr
    dsimp only
    apply ite_zero_or_one
    exact extEq_ok_01 _ _

private theorem verifyShapeRangeJoin_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeRangeJoin ef ap ad od w = 0 ∨ verifyShapeRangeJoin ef ap ad od w = 1 := by
  unfold verifyShapeRangeJoin
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child0 = cL
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child1 = cR
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseRange w.child0Preimage = pL
  generalize aggrParseRange w.child1Preimage = pR
  generalize aggrParseRange w.outputBytes = pO
  repeat apply ite_zero_or_one
  exact extEq_ok_01 _ _

private theorem verifyShapeRangeRoot_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeRangeRoot ef ap ad od w = 0 ∨ verifyShapeRangeRoot ef ap ad od w = 1 := by
  unfold verifyShapeRangeRoot
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child0 = c0
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseRange w.child0Preimage = pRng
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize readSystem w.rangeVkBytes = pSys
  apply ite_zero_or_one
  generalize aggrCheckPreamble pRng.batchDigest w.rangePreambleBytes = pPre
  apply ite_zero_or_one
  generalize shardHeaderListLen pPre.headers = k
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize systemRomWidths pSys.val.circuits = romWidths
  generalize assertClosureWidthsLoop pPre.messages romWidths 0 = cw
  apply ite_zero_or_one
  generalize batchFiatShamir pSys.val.transcriptLimbs (optCommitCap pSys.val.prepCommit) pPre.headers pPre.messages = bfs
  apply ite_zero_or_one
  generalize messagesAcc pRng.residual pPre.messages bfs.lch bfs.fch = total
  apply ite_zero_or_one
  generalize aggrOnlyClaim (batchClaims pPre.headers) = oc
  repeat apply ite_zero_or_one
  exact digest32WordsEq_zero_or_one _ _

private theorem verifyShapeDischargeBinding_ok_01 (ef k : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeDischargeBinding ef k ap ad od w = 0 ∨ verifyShapeDischargeBinding ef k ap ad od w = 1 := by
  unfold verifyShapeDischargeBinding
  generalize verifyChildDigestWithFloor ef k ap ad w.child0 = c0
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef 0 ap ad w.child1 = cB
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCheckEnv w.child0Preimage = pC
  apply ite_zero_or_one
  generalize aggrParseBinding w.child1Preimage = pB
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCheckEnv w.outputBytes = pO
  repeat apply ite_zero_or_one
  exact optAddrEq_zero_or_one _ _

private theorem verifyShapeCrossBinding_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeCrossBinding ef ap ad od w = 0 ∨ verifyShapeCrossBinding ef ap ad od w = 1 := by
  unfold verifyShapeCrossBinding
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child0 = cL
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child1 = cR
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCheckEnv w.child0Preimage = pL
  generalize aggrParseCheckEnv w.child1Preimage = pR
  generalize aggrParseCheckEnv w.outputBytes = pO
  apply ite_zero_or_one
  generalize aggrContextClass pL.ctx w.extraPreimage0 = clsL
  generalize aggrContextClass pR.ctx w.extraPreimage1 = clsR
  apply ite_zero_or_one; apply ite_zero_or_one
  apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrCheckOptionalTree pL.assumptions w.leftAsmTreeBytes = tLA
  generalize aggrCheckOptionalTree pR.assumptions w.rightAsmTreeBytes = tRA
  generalize aggrCheckOptionalTree pO.assumptions w.outAsmTreeBytes = tOA
  apply ite_zero_or_one
  exact aggrAssertStructuralDifferenceFuel_ok_01 _ _ _ _ _ _ _

private theorem verifyShapeCatalogJoin_ok_01 (ef : Nat) (ap : AllowedParams)
    (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyShapeCatalogJoin ef ap ad od w = 0 ∨ verifyShapeCatalogJoin ef ap ad od w = 1 := by
  unfold verifyShapeCatalogJoin
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child0 = cL
  apply ite_zero_or_one
  generalize verifyChildDigestWithFloor ef 1 ap ad w.child1 = cR
  apply ite_zero_or_one
  generalize aggrCatalogPart cL.digest w.child0Preimage w.leftSubjTreeBytes = left
  generalize aggrCatalogPart cR.digest w.child1Preimage w.rightSubjTreeBytes = right
  apply ite_zero_or_one; apply ite_zero_or_one
  generalize aggrParseCatalog w.outputBytes = pOut
  apply ite_zero_or_one
  generalize aggrCheckCanonicalTree pOut.members w.outSubjTreeBytes = outTree
  apply ite_zero_or_one
  exact aggrAssertUnionFuel_ok_01 _ _ _ _

private theorem verifyAggregateStepWithFloor_ok_01 (ef : Nat) (ad od : Digest32Words) (w : AggrStepWitness) :
    verifyAggregateStepWithFloor ef ad od w = 0 ∨ verifyAggregateStepWithFloor ef ad od w = 1 := by
  unfold verifyAggregateStepWithFloor
  generalize parseAllowedBlob ad w.allowedBytes = pA
  apply ite_zero_or_one
  apply ite_both_zero_or_one (verifyShapeWrap_ok_01 _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeWrap_ok_01 _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairFlat_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairFlat_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairFlat_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairFlat_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairStructural_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairStructural_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairStructural_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapePairStructural_ok_01 _ _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeRangeLeaf_ok_01 _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeRangeJoin_ok_01 _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeRangeRoot_ok_01 _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeDischargeBinding_ok_01 _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeDischargeBinding_ok_01 _ _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeCrossBinding_ok_01 _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeCatalogJoin_ok_01 _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeDynamicLink_ok_01 _ _ _ _ _)
  apply ite_both_zero_or_one (verifyShapeDischargeEval_ok_01 _ _ _ _ _)
  exact Or.inl rfl

private theorem verifyAggregateRootWithFloor_ok_01 (ef : Nat) (ad : Digest32Words) :
    ∀ (od : Digest32Words) (t : AggrTreeWitness),
      verifyAggregateRootWithFloor ef ad od t = 0 ∨ verifyAggregateRootWithFloor ef ad od t = 1
  | od, .step0 s => by
    unfold verifyAggregateRootWithFloor
    apply ite_zero_or_one
    exact verifyAggregateStepWithFloor_ok_01 ef ad od s
  | od, .step1 s sub => by
    unfold verifyAggregateRootWithFloor; dsimp only
    split
    · apply ite_zero_or_one
      exact verifyAggregateRootWithFloor_ok_01 ef ad _ sub
    · split
      · apply ite_zero_or_one
        exact verifyAggregateRootWithFloor_ok_01 ef ad _ sub
      · exact Or.inl rfl
  | od, .step2 s sub0 sub1 => by
    unfold verifyAggregateRootWithFloor; dsimp only
    repeat apply ite_zero_or_one
    exact verifyAggregateRootWithFloor_ok_01 ef ad _ sub1

/-- **Headline Recursive Tree Soundness (`verifyAggregateRoot_sound`):**
`AggregatePure.verifyAggregateRoot allowedDigest outClaimDigest t = 1` establishes
`AggregateRootAccepted allowedDigest outClaimDigest t` inductively across EVERY node in `t`,
preserving exact `allowedDigest` pinning and recursive child claim digest matching! -/
theorem verifyAggregateRoot_sound (allowedDigest : Digest32Words) :
    ∀ {outClaimDigest : Digest32Words} {t : AggrTreeWitness},
      verifyAggregateRoot allowedDigest outClaimDigest t = 1 →
      AggregateRootAccepted allowedDigest outClaimDigest t
  | outDig, .step0 s, hok => by
    unfold verifyAggregateRoot verifyAggregateRootWithFloor at hok
    obtain ⟨hrec, hstep⟩ := ite_nat_eq_one_right hok
    simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hrec
    exact .step0 hrec.1 hrec.2 (verifyAggregateStep_sound hstep)
  | outDig, .step1 s sub, hok => by
    unfold verifyAggregateRoot verifyAggregateRootWithFloor at hok
    by_cases h10 : stepHasRecChild0 s = 1 ∧ stepHasRecChild1 s = 0
    · have hb : (stepHasRecChild0 s == 1 && stepHasRecChild1 s == 0) = true := by
        simp [h10.1, h10.2]
      simp only [hb, ↓reduceIte] at hok
      obtain ⟨hs0, hsub⟩ := ite_nat_eq_one_right hok
      have hs1 : verifyAggregateStep allowedDigest outDig s = 1 :=
        (verifyAggregateStepWithFloor_ok_01 1 allowedDigest outDig s).resolve_left (by simpa [beq_iff_eq] using hs0)
      exact .step1Left h10.1 h10.2 (verifyAggregateStep_sound hs1)
        (verifyAggregateRoot_sound allowedDigest hsub)
    · have hbf : (stepHasRecChild0 s == 1 && stepHasRecChild1 s == 0) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hok
      by_cases h01 : stepHasRecChild0 s = 0 ∧ stepHasRecChild1 s = 1
      · have hb : (stepHasRecChild0 s == 0 && stepHasRecChild1 s == 1) = true := by
          simp [h01.1, h01.2]
        simp only [hb, ↓reduceIte] at hok
        obtain ⟨hs0, hsub⟩ := ite_nat_eq_one_right hok
        have hs1 : verifyAggregateStep allowedDigest outDig s = 1 :=
          (verifyAggregateStepWithFloor_ok_01 1 allowedDigest outDig s).resolve_left (by simpa [beq_iff_eq] using hs0)
        exact .step1Right h01.1 h01.2 (verifyAggregateStep_sound hs1)
          (verifyAggregateRoot_sound allowedDigest hsub)
      · have hbf2 : (stepHasRecChild0 s == 0 && stepHasRecChild1 s == 1) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
        simp only [hbf2, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
  | outDig, .step2 s sub0 sub1, hok => by
    unfold verifyAggregateRoot verifyAggregateRootWithFloor at hok
    obtain ⟨hrec, hok⟩ := ite_nat_eq_one_right hok
    simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hrec
    obtain ⟨hs0, hok⟩ := ite_nat_eq_one_right hok
    obtain ⟨hsub0_0, hsub1⟩ := ite_nat_eq_one_right hok
    have hs1 : verifyAggregateStep allowedDigest outDig s = 1 :=
      (verifyAggregateStepWithFloor_ok_01 1 allowedDigest outDig s).resolve_left (by simpa [beq_iff_eq] using hs0)
    have hsub0_1 : verifyAggregateRoot allowedDigest (extractRecursiveChildDigest s.child0.claimsBytes) sub0 = 1 :=
      (verifyAggregateRootWithFloor_ok_01 1 allowedDigest _ sub0).resolve_left (by simpa [beq_iff_eq] using hsub0_0)
    exact .step2 hrec.1 hrec.2 (verifyAggregateStep_sound hs1)
      (verifyAggregateRoot_sound allowedDigest hsub0_1)
      (verifyAggregateRoot_sound allowedDigest hsub1)

/-! ### `PureAcceptedAggrTree` (Backed Directly by `CompressWrapAccepted`) & Functorial Lift to `Ix.Cert.Aggr.AcceptedAggrTree` -/

/-- Pure-Lean inductive 19-shape accepted aggregation tree carrying genuine
`PureVerifiedChild` (`CompressWrapSpec.CompressWrapAccepted`) at every child proof and
exact `hi - lo` `CompressWrapSpec.ShardAccepted` witnesses at every Shape `10` range leaf,
with ZERO `RecursionExecutionRefines` assumptions! -/
inductive PureAcceptedAggrTree
    (sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry)
    (batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop) :
    _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry → Type where
  | leaf {mode S A Ax EvalA} {w : ChildProofWitness} :
      PureVerifiedChild w →
      _root_.Aggr.LeafValid19 sem mode S A Ax EvalA →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  | bindingLeaf {b : _root_.Address} {w : ChildProofWitness} :
      PureVerifiedChild w →
      sem.BindingValid b →
      PureAcceptedAggrTree sem batchClaim (.bindingStmt b)
  | evalDischargerLeaf {b : _root_.Address} {Ax : _root_.Address → Prop}
      {e : Ix.DynamicLink.EvalAssumption} {w : ChildProofWitness} :
      PureVerifiedChild w →
      sem.EvalValid b Ax e →
      PureAcceptedAggrTree sem batchClaim (.evalDischargerStmt b Ax e)
  | wrap {stmt} {w : ChildProofWitness} :
      (isAggrChild : Bool) →
      PureVerifiedChild w →
      PureAcceptedAggrTree sem batchClaim stmt →
      PureAcceptedAggrTree sem batchClaim stmt
  | pairFlat {mode SL AL AxL SR AR AxR Sout Aout AxOut} {wL wR : ChildProofWitness} :
      (leftIsAggr rightIsAggr : Bool) →
      mode.isLinked = false →
      PureVerifiedChild wL → PureVerifiedChild wR →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      _root_.Aggr.JoinRel SL AL SR AR Sout Aout →
      _root_.Aggr.AxiomMergeRel AxL AxR AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  | pairStructural {mode SL AL AxL SR AR AxR Sout Aout AxOut} {wL wR : ChildProofWitness} :
      (leftIsAggr rightIsAggr : Bool) →
      mode.isLinked = false →
      PureVerifiedChild wL → PureVerifiedChild wR →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      _root_.Aggr.StructuralJoinRel SL AL SR AR Sout Aout →
      _root_.Aggr.AxiomMergeRel AxL AxR AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  | rangeLeaf {batchId lo hi : Nat} {sys : SysKey} {headers : ShardHeaderList}
      {proofs : ShardProofList} {input : ByteList} {lch fch : ExtGl} :
      lo ≤ hi →
      shardProofListLen proofs = hi - lo →
      ShardsAllAccepted sys (shardHeaderListTake (hi - lo) headers) proofs lo input lch fch →
      PureAcceptedAggrTree sem batchClaim
        (.rangeStmt batchId lo hi
          (_root_.Aggr.rangeSum sem.residualMonoid (sem.shardResidual batchId) lo hi))
  | rangeJoin {batchId lo mid hi : Nat} {rL rR : Ix.Cert.MultiStark.K} {wL wR : ChildProofWitness} :
      PureVerifiedChild wL → PureVerifiedChild wR →
      PureAcceptedAggrTree sem batchClaim (.rangeStmt batchId lo mid rL) →
      PureAcceptedAggrTree sem batchClaim (.rangeStmt batchId mid hi rR) →
      PureAcceptedAggrTree sem batchClaim
        (.rangeStmt batchId lo hi (sem.residualMonoid.add rL rR))
  | rangeRoot {batchId : Nat} {r : Ix.Cert.MultiStark.K} {mode S A Ax EvalA} {w : ChildProofWitness} :
      mode.isLinked = false →
      PureVerifiedChild w →
      PureAcceptedAggrTree sem batchClaim (.rangeStmt batchId 0 (sem.shardCount batchId) r) →
      sem.residualMonoid.add (sem.messagesAcc batchId) r = sem.residualMonoid.zero →
      batchClaim batchId mode S A Ax EvalA →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  | dischargeBinding {b S A Ax} {wC wB : ChildProofWitness} :
      (isAggrChild : Bool) →
      PureVerifiedChild wC → PureVerifiedChild wB →
      PureAcceptedAggrTree sem batchClaim (.checkEnv (.assumedBinding b) S A Ax (fun _ => False) (fun _ => False)) →
      PureAcceptedAggrTree sem batchClaim (.bindingStmt b) →
      PureAcceptedAggrTree sem batchClaim (.checkEnv (.validated b) S A Ax (fun _ => False) (fun _ => False))
  | crossBinding {modeL modeR : _root_.Aggr.ValidatorMode _root_.Address} {k : _root_.Address}
      {SL AL AxL SR AR AxR Sout Aout AxOut} {wL wR : ChildProofWitness} :
      PureVerifiedChild wL → PureVerifiedChild wR →
      PureAcceptedAggrTree sem batchClaim (.checkEnv modeL SL AL AxL (fun _ => False) (fun _ => False)) →
      PureAcceptedAggrTree sem batchClaim (.checkEnv modeR SR AR AxR (fun _ => False) (fun _ => False)) →
      modeL.isBindingDischarged = true →
      modeR.isBindingDischarged = true →
      (modeL = .literalClass k ∨ sem.LiteralClassOf modeL.bindingOf k) →
      (modeR = .literalClass k ∨ sem.LiteralClassOf modeR.bindingOf k) →
      _root_.Aggr.StructuralJoinRel SL AL SR AR Sout Aout →
      _root_.Aggr.AxiomMergeRel AxL AxR AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv (.literalClass k) Sout Aout AxOut (fun _ => False) (fun _ => False))
  | catalogJoin {membersL membersR membersOut :
        (_root_.Address × (_root_.Address → Prop) × (_root_.Address → Prop)) → Prop}
      {stmtL stmtR} {wL wR : ChildProofWitness} :
      PureVerifiedChild wL → PureVerifiedChild wR →
      PureAcceptedAggrTree sem batchClaim stmtL →
      PureAcceptedAggrTree sem batchClaim stmtR →
      ((∃ mode S Ax, stmtL = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersL m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtL = .catalogStmt membersL) →
      ((∃ mode S Ax, stmtR = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersR m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtR = .catalogStmt membersR) →
      (∀ m, membersOut m ↔ membersL m ∨ membersR m) →
      PureAcceptedAggrTree sem batchClaim (.catalogStmt membersOut)
  | dynamicLink {stmt : Ix.DynamicLink.DynamicLinkStatement} {wExt : ChildProofWitness} :
      PureVerifiedChild wExt →
      Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams (readSystem wExt.vkBytes).val.params) →
      (bridgeCert? : Option { wB : ChildProofWitness // PureVerifiedChild wB }) →
      (stmt.bridge?.isSome → bridgeCert?.isSome) →
      sem.DynamicLinkValid stmt →
      PureAcceptedAggrTree sem batchClaim (.dynamicLinkStmt stmt)
  | dischargeEvalStep {mode : _root_.Aggr.ValidatorMode _root_.Address}
      {S A Ax₀ Ax₁ AxOut EvalBefore EvalAfter Linked e₀} {wC wD : ChildProofWitness} :
      PureVerifiedChild wC → PureVerifiedChild wD →
      mode.canDischargeEval = true →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      PureAcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      _root_.Aggr.EvalRemoveRel EvalBefore EvalAfter e₀ →
      _root_.Aggr.AxiomMergeRel Ax₀ Ax₁ AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A AxOut EvalAfter Linked)
  | dischargeEvalAll {mode outMode : _root_.Aggr.ValidatorMode _root_.Address}
      {S A Ax₀ Ax₁ AxOut EvalBefore e₀} {wC wD : ChildProofWitness} :
      PureVerifiedChild wC → PureVerifiedChild wD →
      mode.dischargeAllEvals = some outMode →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore (fun _ => False)) →
      PureAcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      _root_.Aggr.EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      _root_.Aggr.AxiomMergeRel Ax₀ Ax₁ AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv outMode S A AxOut (fun _ => False) (fun _ => False))
  | dischargeEvalLinkedFinal {mode : _root_.Aggr.ValidatorMode _root_.Address}
      {S A Ax₀ Ax₁ AxOut EvalBefore Linked e₀} {wC wD : ChildProofWitness} :
      PureVerifiedChild wC → PureVerifiedChild wD →
      mode.isLinked = true →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      PureAcceptedAggrTree sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      _root_.Aggr.EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      _root_.Aggr.AxiomMergeRel Ax₀ Ax₁ AxOut →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A AxOut (fun _ => False) Linked)
  | dischargeEvalViaDynamicLink {mode outMode : _root_.Aggr.ValidatorMode _root_.Address}
      {S A Ax EvalBefore EvalAfter LinkedBefore LinkedAfter stmt e₀ entry} {wC wDL : ChildProofWitness} :
      PureVerifiedChild wC → PureVerifiedChild wDL →
      mode.toLinkedMode = some outMode →
      PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalBefore LinkedBefore) →
      PureAcceptedAggrTree sem batchClaim (.dynamicLinkStmt stmt) →
      _root_.Aggr.EvalRemoveRel EvalBefore EvalAfter e₀ →
      sem.LinkedRecords stmt mode.bindingOf e₀ entry →
      _root_.Aggr.LinkedMergeRel LinkedBefore entry LinkedAfter →
      PureAcceptedAggrTree sem batchClaim (.checkEnv outMode S A Ax EvalAfter LinkedAfter)

/-- Count of Shape 18 Mode 3a external dynamic-link discharge steps in a `PureAcceptedAggrTree`. -/
def PureAcceptedAggrTree.dynamicLinkDischarges
    {sem batchClaim stmt} : PureAcceptedAggrTree sem batchClaim stmt → Nat
  | .leaf _ _ | .bindingLeaf _ _ | .evalDischargerLeaf _ _ | .rangeLeaf _ _ _ | .dynamicLink _ _ _ _ _ => 0
  | .wrap _ _ t | .rangeRoot _ _ t _ _ => t.dynamicLinkDischarges
  | .pairFlat _ _ _ _ _ tL tR _ _ | .pairStructural _ _ _ _ _ tL tR _ _
  | .rangeJoin _ _ tL tR | .dischargeBinding _ _ _ tL tR
  | .crossBinding _ _ tL tR _ _ _ _ _ _ | .catalogJoin _ _ tL tR _ _ _
  | .dischargeEvalStep _ _ _ tL tR _ _ | .dischargeEvalAll _ _ _ tL tR _ _
  | .dischargeEvalLinkedFinal _ _ _ tL tR _ _ =>
      tL.dynamicLinkDischarges + tR.dynamicLinkDischarges
  | .dischargeEvalViaDynamicLink _ _ _ tC tDL _ _ _ =>
      1 + tC.dynamicLinkDischarges + tDL.dynamicLinkDischarges

/-- **Unconditional Refinement (`PureAcceptedAggrTree.toDerivation19`):**
Every `PureAcceptedAggrTree` refines unconditionally into `Aggr.AggrDerivation19` (and hence
satisfies `Aggr.AggrNodeHolds`) with ZERO extra hypotheses! -/
theorem PureAcceptedAggrTree.toDerivation19
    {sem batchClaim stmt} (t : PureAcceptedAggrTree sem batchClaim stmt) :
    _root_.Aggr.AggrDerivation19 sem batchClaim stmt := by
  induction t with
  | leaf _ hL => exact .leaf hL
  | bindingLeaf _ hB => exact .bindingLeaf hB
  | evalDischargerLeaf _ hE => exact .evalDischargerLeaf hE
  | wrap _ _ _ ih => exact .wrap ih
  | pairFlat _ _ hUnl _ _ _ _ hJ hA ihL ihR => exact .pairFlat hUnl ihL ihR hJ hA
  | pairStructural _ _ hUnl _ _ _ _ hJ hA ihL ihR => exact .pairStructural hUnl ihL ihR hJ hA
  | rangeLeaf hle _ _ => exact .rangeLeaf hle
  | rangeJoin _ _ _ _ ihL ihR => exact .rangeJoin ihL ihR
  | rangeRoot hUnl _ _ hZ hC ih => exact .rangeRoot hUnl ih hZ hC
  | dischargeBinding _ _ _ _ _ ihC ihB => exact .dischargeBinding ihC ihB
  | crossBinding _ _ _ _ hDL hDR hCL hCR hJ hA ihL ihR =>
      exact .crossBinding ihL ihR hDL hDR hCL hCR hJ hA
  | catalogJoin _ _ _ _ hSL hSR hU ihL ihR => exact .catalogJoin ihL ihR hSL hSR hU
  | dynamicLink _ _ _ _ hDL => exact .dynamicLink hDL
  | dischargeEvalStep _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalStep hM ihC ihD hR hA
  | dischargeEvalAll _ _ hM _ _ hR hA ihC ihD => exact .dischargeEvalAll hM ihC ihD hR hA
  | dischargeEvalLinkedFinal _ _ hLnk _ _ hR hA ihC ihD =>
      exact .dischargeEvalLinkedFinal hLnk ihC ihD hR hA
  | dischargeEvalViaDynamicLink _ _ hToLnk _ _ hR hRec hMerge ihC ihDL =>
      exact .dischargeEvalViaDynamicLink hToLnk ihC ihDL hR hRec hMerge

private def pureStmtIsUnlinked :
    _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry → Prop
  | .checkEnv mode _ _ _ _ _ => mode.isLinked = false
  | _ => True

private theorem pureAcceptedAggrTree_unlinked_zero_aux {sem batchClaim stmt}
    (t : PureAcceptedAggrTree sem batchClaim stmt) :
    pureStmtIsUnlinked stmt → t.dynamicLinkDischarges = 0 := by
  induction t with
  | leaf _ _ | bindingLeaf _ _ | evalDischargerLeaf _ _ | rangeLeaf _ _ _ | dynamicLink _ _ _ _ _ =>
    intro _; rfl
  | wrap _ _ _ ih => intro h; exact ih h
  | pairFlat _ _ hUnl _ _ _ _ _ _ ihL ihR =>
    intro _; simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihL hUnl, ihR hUnl]
  | pairStructural _ _ hUnl _ _ _ _ _ _ ihL ihR =>
    intro _; simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihL hUnl, ihR hUnl]
  | rangeJoin _ _ _ _ ihL ihR =>
    intro _; simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihL trivial, ihR trivial]
  | rangeRoot _ _ _ _ _ ih => intro _; exact ih trivial
  | dischargeBinding _ _ _ _ _ ihC ihB =>
    intro _; simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihC rfl, ihB trivial]
  | crossBinding _ _ _ _ hDL hDR _ _ _ _ ihL ihR =>
    intro _
    have hUL : ∀ m : _root_.Aggr.ValidatorMode _root_.Address, m.isBindingDischarged = true → m.isLinked = false := by
      intro m hm; cases m <;> simp [_root_.Aggr.ValidatorMode.isBindingDischarged, _root_.Aggr.ValidatorMode.isLinked] at hm ⊢
    simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihL (hUL _ hDL), ihR (hUL _ hDR)]
  | @catalogJoin _ _ _ stmtL stmtR _ _ _ _ _ _ hSL hSR _ ihL ihR =>
    intro _
    have hUL : ∀ m : _root_.Aggr.ValidatorMode _root_.Address, m.isBindingDischarged = true → m.isLinked = false := by
      intro m hm; cases m <;> simp [_root_.Aggr.ValidatorMode.isBindingDischarged, _root_.Aggr.ValidatorMode.isLinked] at hm ⊢
    have hL : pureStmtIsUnlinked stmtL := by
      rcases hSL with ⟨_, _, _, rfl, hDis, _⟩ | rfl
      · exact hUL _ hDis
      · trivial
    have hR : pureStmtIsUnlinked stmtR := by
      rcases hSR with ⟨_, _, _, rfl, hDis, _⟩ | rfl
      · exact hUL _ hDis
      · trivial
    simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihL hL, ihR hR]
  | dischargeEvalStep _ _ _ _ _ _ _ ihC ihD =>
    intro hUnl; simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihC hUnl, ihD trivial]
  | dischargeEvalAll _ _ hTrans _ _ _ _ ihC ihD =>
    intro _
    have hUnl := (_root_.Aggr.validatorMode_dischargeAllEvals_unlinked hTrans).1
    simp [PureAcceptedAggrTree.dynamicLinkDischarges, ihC hUnl, ihD trivial]
  | dischargeEvalLinkedFinal _ _ hLnk _ _ _ _ _ _ =>
    intro hUnl; change _ = false at hUnl; rw [hLnk] at hUnl; cases hUnl
  | dischargeEvalViaDynamicLink _ _ hToLnk _ _ _ _ _ _ _ =>
    intro hUnl
    have hLnk := (_root_.Aggr.validatorMode_toLinkedMode_props hToLnk).1
    change _ = false at hUnl; rw [hLnk] at hUnl; cases hUnl

/-- **Unlinked Zero-External-Circuit Guarantee (`PureAcceptedAggrTree.unlinked_zero_dynamicLinkDischarges`):**
Every `PureAcceptedAggrTree` rooted at an unlinked validator (`3, 4, 5, 10, 11, 14, 15`)
contains ZERO Shape 18 Mode 3a external dynamic-circuit discharges! -/
theorem PureAcceptedAggrTree.unlinked_zero_dynamicLinkDischarges
    {sem batchClaim mode S A Ax EvalA Linked}
    (hUnl : mode.isLinked = false)
    (t : PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA Linked)) :
    t.dynamicLinkDischarges = 0 :=
  pureAcceptedAggrTree_unlinked_zero_aux t hUnl

/-- **Functorial Bridge to `Ix.Cert.Aggr.AcceptedAggrTree`:**
Given a lift from each `PureVerifiedChild` to `Ix.Cert.Aggr.VerifiedChildProof` (and matching
external `StarkSystem` decoding for Shape 17 and per-shard `VerifiedChildProof` list for Shape 10),
constructively lifts ANY `PureAcceptedAggrTree` into `Ix.Cert.Aggr.AcceptedAggrTree` while
preserving `dynamicLinkDischarges` identically! -/
def PureAcceptedAggrTree.toAcceptedAggrTree
    {sem batchClaim stmt}
    (liftChild : ∀ {w : ChildProofWitness}, PureVerifiedChild w → Ix.Cert.Aggr.VerifiedChildProof)
    (liftRangeShard : ∀ {sys : SysKey} {headers : ShardHeaderList} {proofs : ShardProofList}
      {lo n : Nat} {input : ByteList} {lch fch : ExtGl},
      shardProofListLen proofs = n →
      ShardsAllAccepted sys (shardHeaderListTake n headers) proofs lo input lch fch →
      { xs : List Ix.Cert.Aggr.VerifiedChildProof // xs.length = n })
    (liftDynLink : ∀ {stmtDL : Ix.DynamicLink.DynamicLinkStatement} {wExt : ChildProofWitness}
      (hC : PureVerifiedChild wExt),
      Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams (readSystem wExt.vkBytes).val.params) →
      { extSys : Ix.Cert.MultiStark.StarkSystem //
        Ix.Cert.MultiStark.StarkSystem.fromBytes (liftChild hC).vkBytes = .ok extSys ∧
        Ix.Cert.Aggr.SecurityEnvelopeOk extSys.params ∧
        _root_.Address.blake3Pure (liftChild hC).vkBytes = stmtDL.circuit.vkDigest })
    (t : PureAcceptedAggrTree sem batchClaim stmt) :
    Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim stmt :=
  match t with
  | .leaf hc hL => .leaf (liftChild hc) hL
  | .bindingLeaf hc hB => .bindingLeaf (liftChild hc) hB
  | .evalDischargerLeaf hc hE => .evalDischargerLeaf (liftChild hc) hE
  | .wrap isA hc sub => .wrap isA (liftChild hc) (sub.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
  | .pairFlat lA rA hU hL hR tL tR hJ hAx =>
    .pairFlat lA rA hU (liftChild hL) (liftChild hR)
      (tL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tR.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hJ hAx
  | .pairStructural lA rA hU hL hR tL tR hJ hAx =>
    .pairStructural lA rA hU (liftChild hL) (liftChild hR)
      (tL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tR.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hJ hAx
  | .rangeLeaf hle hlen hSh =>
    let rs := liftRangeShard hlen hSh
    .rangeLeaf rs.1 hle rs.2
  | .rangeJoin hL hR tL tR =>
    .rangeJoin (liftChild hL) (liftChild hR)
      (tL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tR.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
  | .rangeRoot hU hc sub hZ hBC =>
    .rangeRoot hU (liftChild hc) (sub.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hZ hBC
  | .dischargeBinding isA hC hB tC tB =>
    .dischargeBinding isA (liftChild hC) (liftChild hB)
      (tC.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tB.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
  | .crossBinding hL hR tL tR hDL hDR hCL hCR hJ hAx =>
    .crossBinding (liftChild hL) (liftChild hR)
      (tL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tR.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hDL hDR hCL hCR hJ hAx
  | .catalogJoin hL hR tL tR hSL hSR hU =>
    .catalogJoin (liftChild hL) (liftChild hR)
      (tL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tR.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hSL hSR hU
  | .dynamicLink hExt hEnv br? hBr hDL =>
    let ds := liftDynLink hExt hEnv
    .dynamicLink (liftChild hExt) ds.1 ds.2.1 ds.2.2.1 ds.2.2.2
      (br?.map fun b => liftChild b.2) (by intro h; cases br? <;> simp_all) hDL
  | .dischargeEvalStep hC hD hM tC tD hR hAx =>
    .dischargeEvalStep (liftChild hC) (liftChild hD) hM
      (tC.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tD.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hR hAx
  | .dischargeEvalAll hC hD hM tC tD hR hAx =>
    .dischargeEvalAll (liftChild hC) (liftChild hD) hM
      (tC.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tD.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hR hAx
  | .dischargeEvalLinkedFinal hC hD hLnk tC tD hR hAx =>
    .dischargeEvalLinkedFinal (liftChild hC) (liftChild hD) hLnk
      (tC.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tD.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hR hAx
  | .dischargeEvalViaDynamicLink hC hDL hToLnk tC tDL hR hRec hMerge =>
    .dischargeEvalViaDynamicLink (liftChild hC) (liftChild hDL) hToLnk
      (tC.toAcceptedAggrTree liftChild liftRangeShard liftDynLink)
      (tDL.toAcceptedAggrTree liftChild liftRangeShard liftDynLink) hR hRec hMerge

/-- Constructive tree builder coupling a verified `AggregateRootAccepted` execution of
`AggregatePure.verifyAggregateRoot` directly into `PureAcceptedAggrTree` and
`Ix.Cert.Aggr.AcceptedAggrTree`!

Given a verified `AggregatePure.verifyAggregateRoot allowedDigest outClaimDigest t = 1`,
every recursive step's cryptographic checks (`AllowedBlobAccepted`, `PureVerifiedChild` =
`CompressWrapAccepted`, Shape 10 `ShardAccepted` & `K` telescoping, Shape 17 `SecurityEnvelopeOk`,
Shape 18 validator `14`/`15` & `12`/`13` isolation) are discharged purely from `verifyAggregateRoot_sound`;
supplying the semantic base-leaf & structural interpretation for the root statement lifts the
verified execution directly to `PureAcceptedAggrTree` and `Ix.Cert.Aggr.AcceptedAggrTree`! -/
theorem verifyAggregateRoot_to_pureAcceptedAggrTree
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {t : AggrTreeWitness}
    {rootStmt : _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    (hok : verifyAggregateRoot allowedDigest outClaimDigest t = 1)
    (build : AggregateRootAccepted allowedDigest outClaimDigest t →
      PureAcceptedAggrTree sem batchClaim rootStmt) :
    AggregateRootAccepted allowedDigest outClaimDigest t ∧
    Nonempty (PureAcceptedAggrTree sem batchClaim rootStmt) ∧
    _root_.Aggr.AggrDerivation19 sem batchClaim rootStmt ∧
    _root_.Aggr.AggrNodeHolds sem rootStmt := by
  have hacc := verifyAggregateRoot_sound allowedDigest hok
  have htree := build hacc
  have hderiv := htree.toDerivation19
  exact ⟨hacc, ⟨htree⟩, hderiv, _root_.Aggr.aggrDerivation19_invariant hderiv⟩

/-- Direct constructor building a `PureAcceptedAggrTree.leaf` + `wrap` for a Shape `0` (`wrapIxvm`)
step accepted by `verifyAggregateStep` (zero external assumptions on the child Multi-STARK proof:
`PureVerifiedChild` is extracted directly from `verifyAggregateStep_sound`!). -/
def pureAcceptedAggrTree_of_shape0_wrap
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hshape : w.shape = 0)
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1)
    {mode S A Ax EvalA}
    (hLeaf : _root_.Aggr.LeafValid19 sem mode S A Ax EvalA) :
    PureAcceptedAggrTree sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False)) := by
  have hacc := verifyAggregateStep_sound hok
  have hc : ChildDigestAccepted 0 (parseAllowedBlob allowedDigest w.allowedBytes).val
      allowedDigest w.child0 outClaimDigest := by
    have hp := hacc.shape_post
    simp only [hshape] at hp
    exact hp
  exact .wrap false hc.child (.leaf hc.child hLeaf)

/-- Direct constructor building a `PureAcceptedAggrTree.dischargeBinding` node for Shape `13`
(`validator 4 → 3`) accepted by `verifyAggregateStep`! -/
def pureAcceptedAggrTree_of_shape13_dischargeBinding
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hshape : w.shape = 13)
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1)
    {b S A Ax}
    (hLeafC : _root_.Aggr.LeafValid19 sem (.assumedBinding b) S A Ax (fun _ => False))
    (hLeafB : sem.BindingValid b) :
    PureAcceptedAggrTree sem batchClaim
      (.checkEnv (.validated b) S A Ax (fun _ => False) (fun _ => False)) := by
  have hacc := verifyAggregateStep_sound hok
  have hp := hacc.shape_post
  simp only [hshape] at hp
  exact .dischargeBinding false hp.2.1.child hp.2.2.1.child
    (.leaf hp.2.1.child hLeafC) (.bindingLeaf hp.2.2.1.child hLeafB)

/-- Direct constructor building a `PureAcceptedAggrTree.pairFlat` node for Shape `2`
(`aggr_pair 0 0`) accepted by `verifyAggregateStep` — discharging `Aggr.JoinRel` directly from
`verifyShapePairFlat` via `joinRel_of_aggrPair_checks`! -/
def pureAcceptedAggrTree_of_shape2_pairFlat
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hshape : w.shape = 2)
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1)
    {mode : _root_.Aggr.ValidatorMode _root_.Address} (hUnl : mode.isLinked = false)
    {SL AL AxL SR AR AxR Sout Aout AxOut}
    (hLeafL : _root_.Aggr.LeafValid19 sem mode SL AL AxL (fun _ => False))
    (hLeafR : _root_.Aggr.LeafValid19 sem mode SR AR AxR (fun _ => False))
    (hJoin : _root_.Aggr.JoinRel SL AL SR AR Sout Aout)
    (hAx : _root_.Aggr.AxiomMergeRel AxL AxR AxOut) :
    PureAcceptedAggrTree sem batchClaim
      (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False)) := by
  have hacc := verifyAggregateStep_sound hok
  have hp := hacc.shape_post
  simp only [hshape] at hp
  exact .pairFlat false false hUnl hp.2.1.child hp.2.2.child
    (.leaf hp.2.1.child hLeafL) (.leaf hp.2.2.child hLeafR) hJoin hAx

/-- Direct constructor building a `PureAcceptedAggrTree.rangeLeaf` node for Shape `10`
(`aggr_range_leaf`) accepted by `verifyAggregateStep` — carrying ALL `hi - lo` verified
`CompressWrapSpec.ShardAccepted` shard proofs and exact `K` residual `rangeSum`! -/
theorem pureAcceptedAggrTree_of_shape10_rangeLeaf
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hshape : w.shape = 10)
    (hok : verifyAggregateStep allowedDigest outClaimDigest w = 1)
    (batchId : Nat) :
    let pRng := aggrParseRange w.outputBytes
    let lo := glValBytes pRng.lo
    let hi := glValBytes pRng.hi
    lo ≤ hi ∧
    Nonempty (PureAcceptedAggrTree sem batchClaim
      (.rangeStmt batchId lo hi
        (_root_.Aggr.rangeSum sem.residualMonoid (sem.shardResidual batchId) lo hi))) := by
  have hacc := verifyAggregateStep_sound hok
  have hp := hacc.shape_post
  simp only [hshape] at hp
  obtain ⟨hrl, _, _, _, _, _⟩ := hp
  obtain ⟨_, _, hloLeHi, hplen, hShards, _⟩ := verifyShapeRangeLeaf_sound hrl
  exact ⟨hloLeHi, ⟨.rangeLeaf hloLeHi hplen hShards⟩⟩

/-- **Headline Bridge to `Ix.Cert.Aggr.AcceptedAggrTree` (`verifyAggregateRoot_to_acceptedAggrTree`):**
Composes `verifyAggregateRoot_to_pureAcceptedAggrTree` with `PureAcceptedAggrTree.toAcceptedAggrTree`,
producing an ACTUAL `Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt` (and therefore
`Aggr.AggrDerivation19`, `Aggr.AggrNodeHolds`, and `Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19`!). -/
theorem verifyAggregateRoot_to_acceptedAggrTree
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {allowedDigest outClaimDigest : Digest32Words} {t : AggrTreeWitness}
    {rootStmt : _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    (hok : verifyAggregateRoot allowedDigest outClaimDigest t = 1)
    (build : AggregateRootAccepted allowedDigest outClaimDigest t →
      PureAcceptedAggrTree sem batchClaim rootStmt)
    (liftChild : ∀ {w : ChildProofWitness}, PureVerifiedChild w → Ix.Cert.Aggr.VerifiedChildProof)
    (liftRangeShard : ∀ {sys : SysKey} {headers : ShardHeaderList} {proofs : ShardProofList}
      {lo n : Nat} {input : ByteList} {lch fch : ExtGl},
      shardProofListLen proofs = n →
      ShardsAllAccepted sys (shardHeaderListTake n headers) proofs lo input lch fch →
      { xs : List Ix.Cert.Aggr.VerifiedChildProof // xs.length = n })
    (liftDynLink : ∀ {stmtDL : Ix.DynamicLink.DynamicLinkStatement} {wExt : ChildProofWitness}
      (hC : PureVerifiedChild wExt),
      Ix.Cert.Aggr.SecurityEnvelopeOk (toStarkParams (readSystem wExt.vkBytes).val.params) →
      { extSys : Ix.Cert.MultiStark.StarkSystem //
        Ix.Cert.MultiStark.StarkSystem.fromBytes (liftChild hC).vkBytes = .ok extSys ∧
        Ix.Cert.Aggr.SecurityEnvelopeOk extSys.params ∧
        _root_.Address.blake3Pure (liftChild hC).vkBytes = stmtDL.circuit.vkDigest }) :
    AggregateRootAccepted allowedDigest outClaimDigest t ∧
    ∃ tree : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt,
      _root_.Aggr.AggrDerivation19 sem batchClaim rootStmt ∧
      _root_.Aggr.AggrNodeHolds sem rootStmt ∧
      (tree.HasTreeCollision ∨
        ∀ vp ∈ tree.childProofs, ∃ proofBytes,
          Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  have hacc := verifyAggregateRoot_sound allowedDigest hok
  let ptree := build hacc
  let atree := ptree.toAcceptedAggrTree liftChild liftRangeShard liftDynLink
  obtain ⟨hDeriv, hChildOk⟩ := Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19 atree
  exact ⟨hacc, atree, hDeriv, _root_.Aggr.aggrDerivation19_invariant hDeriv, hChildOk⟩

/-! ## Section 4: Part 2 Headline — Concrete `AggrSemantics` from `ConditionalShards.lean` + `circuitComposed` + `MultiStarkBridge` → `Ix.Kernel.Model W` -/

section ConcreteKernelModelSemantics

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Optimized.Grouping
open Aiur.MultiStarkSpec Aiur.MultiStarkBridge
open IxVM.Consistency IxVM.Refinement IxVM.Refinement.Endpoint
open Ix.Cert.Aggr

/-- **Discharging `Ix.Cert.Aggr.AcceptedCircuitRun` from `Aiur.MultiStarkBridge.LoweredSystemSatisfied`
(Unsegmented Goldilocks):**
Given an unsegmented lowered Multi-STARK trace family for `IxVM.source` at entry `verifyClaim`
satisfying `LoweredSystemSatisfied`, `physical.checkDepthPlan = true`, lookup budget `< 2 ^ 63`,
and ROM size `≤ 2 ^ 39`, constructs a full `Ix.Cert.Aggr.AcceptedCircuitRun d` (discharging
`DepthCertified`, `cfg.bits ≤ 24`, `WellFormedActivation`, `rom.Valid`, `wrows.length ≤ 2 ^ 39`,
and `plan.checkMemo = .ok ()` automatically via `Aiur.MultiStarkBridge`!). -/
noncomputable def acceptedCircuitRun_of_loweredSystem_unsegmented
    {d : IxVM.Refinement.Digest}
    {id : String → Except String Nat}
    (specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim])
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (plan : Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    {measures : Aiur.Optimized.Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.inlined.program cfg measures plan = true)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (Aiur.Tiling.Grouped.circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (wires : List (Aiur.WireValue IxVM.F)) (output : Aiur.WireValue IxVM.F)
    (result : Aiur.Value IxVM.F)
    (signed : Erasure.Signed compiled.system
      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (root : Circuit.Message IxVM.F)
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.system
        { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues [IxVM.Refinement.digestValue d]))
    (decoded : WireValue.decode specialized.program.enums output = some result)
    (traces : List (CircuitTrace IxVM.F))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ Aiur.MultiStarkSpec.maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromSmall : (extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)).entries.length ≤ 2 ^ 39)
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ Aiur.Tiling.Grouped.allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Aiur.Tiling.Bridge.Shaped.check (Aiur.Optimized.Depth.system cfg physical.system)
      (Aiur.Tiling.Grouped.allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    AcceptedCircuitRun d :=
  let hbridge := lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks
    compiled physical plan certOK callableId idOk names fixedMaps romWidths hndRom
    logBlowup extDegree romLayout root traces hsat hrowsBound hbudget hromCap
    hromWidths hmemWidth hshaped hctxEmpty
  let wrows := Classical.choose hbridge.2.2
  let hwSpec := Classical.choose_spec hbridge.2.2
  { id := id
    specialized := specialized
    compiled := compiled
    physical := physical
    cfg := cfg
    certified := hbridge.1.1
    bits := hbridge.1.2.1
    plan := plan
    activated := hbridge.1.2.2
    rom := extractWidthROM romWidths romLayout (romTracesOf callableId plan fixedMaps logBlowup traces)
    valid := hbridge.2.1
    small := hromSmall
    wires := wires
    output := output
    result := result
    signed := signed
    root := root
    rooted := rooted
    outside := outside
    rows := wrows
    bound := hwSpec.1
    checked := hwSpec.2
    arguments := arguments
    decoded := decoded }

/-- **Discharging `Ix.Cert.Aggr.AcceptedCircuitRun` from `Aiur.MultiStarkBridge.LoweredSystemSatisfied`
(Segmented Goldilocks with `MEMSEG = 16` Interval Balance):**
Discharges `rom.Valid` via `extractWidthROM_valid_segmented_zmod` and `plan.checkMemo = .ok ()`
via `lowerFullSystem_satisfied_implies_checkMemo`! -/
noncomputable def acceptedCircuitRun_of_loweredSystem_segmented
    {d : IxVM.Refinement.Digest}
    {id : String → Except String Nat}
    (specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim])
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    {cfg : Aiur.Optimized.Depth.Config}
    (plan : Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id)
    {measures : Aiur.Optimized.Depth.Structural.Plan}
    (certOK : physical.checkDepthPlan compiled.inlined.program cfg measures plan = true)
    (callableId : String → Nat) (idOk : ∀ x n, id x = .ok n → n = callableId x)
    (names : (Aiur.Tiling.Grouped.circuitNames plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (ivlsOf : Nat → List (Nat × Nat))
    (hdisj : ∀ w ∈ romWidths, DisjointIntervalsP Aiur.Library.U32.Goldilocks.modulus (ivlsOf w))
    (wires : List (Aiur.WireValue IxVM.F)) (output : Aiur.WireValue IxVM.F)
    (result : Aiur.Value IxVM.F)
    (signed : Erasure.Signed compiled.system
      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (root : Circuit.Message IxVM.F)
    (rooted : Aiur.Optimized.Depth.erase cfg root =
      Erasure.message compiled.system
        { channel := IxVM.Refinement.verifyClaim, args := wires, result := output })
    (outside : root.channel ∉ cfg.names)
    (arguments : DecodesValues specialized.program.enums wires
      (entryValues [IxVM.Refinement.digestValue d]))
    (decoded : WireValue.decode specialized.program.enums output = some result)
    (traces : List (CircuitTrace IxVM.F))
    (hsat : LoweredSystemSatisfied callableId plan fixedMaps romWidths logBlowup true
      extDegree romLayout root (memsegPreambleLedger romWidths ivlsOf) traces)
    (hrowsBound : totalRows (fnTracesOf callableId plan traces) ≤ Aiur.MultiStarkSpec.maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId plan fixedMaps romWidths logBlowup true extDegree romLayout)
      traces < 2 ^ 63)
    (hromCnt : List.Forall₂ (fun w tr => (extractRomEntries w romLayout tr).length + 1 < Aiur.Library.U32.Goldilocks.modulus)
      romWidths (romTracesOf callableId plan fixedMaps logBlowup traces))
    (hromSmall : (extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)).entries.length ≤ 2 ^ 39)
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ Aiur.Tiling.Grouped.allChips plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Aiur.Tiling.Bridge.Shaped.check (Aiur.Optimized.Depth.system cfg physical.system)
      (Aiur.Tiling.Grouped.allChips plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    AcceptedCircuitRun d :=
  have hplan := Aiur.Optimized.Physical.Prepared.checkDepthPlan_sound certOK
  have hp16 : 16 < Aiur.Library.U32.Goldilocks.modulus := by norm_num [Aiur.Library.U32.Goldilocks.modulus]
  have h63lt : 2 ^ 63 < Aiur.Library.U32.Goldilocks.modulus := by norm_num [Aiur.Library.U32.Goldilocks.modulus]
  have hromValid : (extractWidthROM romWidths romLayout
      (romTracesOf callableId plan fixedMaps logBlowup traces)).Valid :=
    extractWidthROM_valid_segmented_zmod hp16 callableId idOk plan fixedMaps romWidths hndRom
      (fun w hw => lt_trans (hromWidths w hw) h63lt) logBlowup extDegree romLayout root ivlsOf
      hdisj traces hsat hromCnt
  have hctx : (Aiur.Optimized.Depth.system cfg physical.system).checkContext
      (Erasure.rawROM (extractWidthROM romWidths romLayout
        (romTracesOf callableId plan fixedMaps logBlowup traces))) root = .ok () := by
    obtain ⟨hformed, hpub, _, hwf⟩ := Circuit.System.checkContext_iff.mp hctxEmpty
    exact Circuit.System.checkContext_iff.mpr ⟨hformed, hpub, Erasure.rawROM_valid hromValid, hwf⟩
  have hmemo := lowerFullSystem_satisfied_implies_checkMemo callableId idOk plan hplan.2.2 names
    fixedMaps romWidths logBlowup true extDegree romLayout root
    (memsegPreambleLedger romWidths ivlsOf) traces hsat goldilocks_smallCast_63
    goldilocks_sixteen_lt_63 hbudget hromWidths hmemWidth hshaped hctx
  let wrows := Classical.choose hmemo
  let hwSpec := Classical.choose_spec hmemo
  { id := id
    specialized := specialized
    compiled := compiled
    physical := physical
    cfg := cfg
    certified := hplan.1
    bits := hplan.2.1
    plan := plan
    activated := hplan.2.2
    rom := extractWidthROM romWidths romLayout (romTracesOf callableId plan fixedMaps logBlowup traces)
    valid := hromValid
    small := hromSmall
    wires := wires
    output := output
    result := result
    signed := signed
    root := root
    rooted := rooted
    outside := outside
    rows := wrows
    bound := hwSpec.1.trans hrowsBound
    checked := hwSpec.2
    arguments := arguments
    decoded := decoded }

/-- **Unified Set-Theoretic Model Postcondition (`ShardedKernelModel`):**
States that either a BLAKE3 collision occurred across the shard + binding runs, OR the binding
table `tRole` admits at `b` (`AllBound`, `TableShape`) and there exists a consistent kernel
environment `env` extending `envT` covering EVERY constant in `seeds` such that:
1. **`Nonempty (Ix.Kernel.Model W (claimedEnv env))`** for EVERY `W : Type u` with `[Ix.Kernel.SetTheory W]`,
2. **`SeedsNotFalse`** (no constant in `seeds` has type `False`), and
3. **`SeedsInhabited`** (every constant's stored type in `seeds` is inhabited in every model)! -/
def ShardedKernelModel
    (allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (shardBytes : List ByteArray) (bytesB : ByteArray)
    (V : IxVM.Refinement.View) (b : _root_.Address) (seeds : List _root_.Address) : Prop :=
  V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
    ComposedWith.{u}
      (fun tRole R envT =>
        (∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
          LoadedBy allCalls E₀ ∧
          (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
          (∀ s ∈ seeds, ∀ s', SeedConstant E₀ s s' →
            ∃ ci, env.find? (keyOf tRole s') = some ci ∧
              (PinnedBasis ci ∨ KeptIn tRole (storeOver E₀ R) (blobOver E₀ R) s' ci)) ∧
          (∀ (W : Type u) [Ix.Kernel.SetTheory W],
            Nonempty (Ix.Kernel.Model W (claimedEnv env)))) ∧
        (∀ (W : Type u) [Ix.Kernel.SetTheory W], SeedsNotFalse allCalls tRole R seeds) ∧
        SeedsInhabited.{u} allCalls tRole R seeds)
      callsB b

theorem shardedKernelModel_of_shardedModelConclusion
    {allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {shardBytes : List ByteArray} {bytesB : ByteArray}
    {V : IxVM.Refinement.View} {b : _root_.Address} {seeds : List _root_.Address}
    (h : ShardedModelConclusion.{u} allCalls callsB shardBytes bytesB V b seeds) :
    ShardedKernelModel.{u} allCalls callsB shardBytes bytesB V b seeds := by
  rcases h with hcol | ⟨tb, tRole, R, envT, htb, ht, hall, hload, hshape, hread⟩
  · exact Or.inl hcol
  · have hread' := hread
    obtain ⟨E₀, env, hloadE, _, hsub, _, hcov, hmod⟩ := hread'
    exact Or.inr ⟨tb, tRole, R, envT, htb, ht, hall, hload, hshape,
      ⟨E₀, env, hloadE, hsub, hcov, hmod⟩,
      fun W _ => ConsistentReadOver.seeds_not_false W hread,
      ConsistentReadOver.seeds_inhabited hread⟩

/-- **Concrete `Aggr.AggrSemantics` Instantiation (`ixvmShardedAggrSemantics`):**
Concretely instantiates ALL fields and ALL 6 semantic laws of `Aggr.AggrSemantics` over
`IxVMRefinement.Endpoint.ConditionalShards`:
- `TargetValid b x`: requires that under `b = b₀` (or literal class `k` containing `b₀`) and
  `x ∈ allSeeds`, the full concrete set-theoretic model property `ShardedKernelModel.{u}` holds!
- `Checked`: `Ix.Cert.Aggr.ConditionalCheckedWithLinks` tracking user axioms `Ax`, Tier 2
  `evalAssumptions`, and Mode 3a `linkedCircuits`!
- `BindingValid b`: `b = b₀` (the binding address verified by `runB`)!
- `residualMonoid`: concrete `Ix.Cert.Aggr.kResidualMonoid` over `K = Fp[X]/(X^3 - X - 1)`! -/
def ixvmShardedAggrSemantics
    (allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (shardBytes : List ByteArray) (bytesB : ByteArray)
    (V : IxVM.Refinement.View) (b₀ : _root_.Address) (seeds : List _root_.Address)
    (Dep : _root_.Address → _root_.Address → Prop)
    (AxHolds : _root_.Address → _root_.Address → Prop)
    (EvalHolds : _root_.Address → Ix.DynamicLink.EvalAssumption → Prop)
    (LinkHolds : _root_.Address → Ix.DynamicLink.LinkedCircuitEntry → Prop)
    (LiteralClassOf : _root_.Address → _root_.Address → Prop)
    (DynamicLinkValid : Ix.DynamicLink.DynamicLinkStatement → Prop)
    (LinkedRecords : Ix.DynamicLink.DynamicLinkStatement → _root_.Address →
      Ix.DynamicLink.EvalAssumption → Ix.DynamicLink.LinkedCircuitEntry → Prop)
    (hLinkSound : ∀ {stmt b e₀ entry},
      DynamicLinkValid stmt → LinkedRecords stmt b e₀ entry → LinkHolds b entry → EvalHolds b e₀)
    (hClassAx : ∀ {b k a}, LiteralClassOf b k → AxHolds k a → AxHolds b a)
    (hClassEval : ∀ {b k e}, LiteralClassOf b k → EvalHolds k e → EvalHolds b e)
    (hClassLink : ∀ {b k l}, LiteralClassOf b k → LinkHolds k l → LinkHolds b l)
    (shardCount : Nat → Nat)
    (shardResidual : Nat → Nat → Ix.Cert.MultiStark.K)
    (messagesAccFn : Nat → Ix.Cert.MultiStark.K)
    (hBatchSound : ∀ (batchId : Nat) (mode : _root_.Aggr.ValidatorMode _root_.Address)
      (S A Ax : _root_.Address → Prop) (EvalA : Ix.DynamicLink.EvalAssumption → Prop),
      Ix.Cert.Aggr.kResidualMonoid.add (messagesAccFn batchId)
        (_root_.Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid (shardResidual batchId) 0 (shardCount batchId)) =
        Ix.Cert.Aggr.kResidualMonoid.zero →
      (batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
        (_root_.Address → Prop) → (_root_.Address → Prop) →
        (Ix.DynamicLink.EvalAssumption → Prop) → Prop) →
      batchClaim batchId mode S A Ax EvalA →
      ((mode.bindingCond (fun b => b = b₀) → ∀ x, S x →
          ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds
            (fun _ x => x ∈ seeds → ShardedKernelModel.{u} allCalls callsB shardBytes bytesB V b₀ seeds)
            mode.bindingOf Ax EvalA (fun _ => False) x) ∧
        (∀ x y, S x → Dep x y → S y ∨ A y))) :
    _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry where
  Checked := ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds
    (fun _ x => x ∈ seeds → ShardedKernelModel.{u} allCalls callsB shardBytes bytesB V b₀ seeds)
  Dep := Dep
  BindingValid := fun b => b = b₀
  LiteralClassOf := LiteralClassOf
  EvalValid := ConditionalEvalValid AxHolds EvalHolds
  DynamicLinkValid := DynamicLinkValid
  LinkedRecords := LinkedRecords
  residualMonoid := Ix.Cert.Aggr.kResidualMonoid
  shardCount := shardCount
  shardResidual := shardResidual
  messagesAcc := messagesAccFn
  checked_mono_ax := fun hSub hC hAx hEv hLnk => hC (fun a ha => hAx a (hSub a ha)) hEv hLnk
  checked_discharge_eval := fun hRem hE hC hAx hAfter hLnk =>
    hC hAx (fun e he => by
      rcases (hRem.before_iff e).mp he with rfl | hm
      · exact hE hAx
      · exact hAfter e hm) hLnk
  checked_discharge_eval_via_link := fun hRem hDL hRec hMerge hC =>
    conditionalCheckedWithLinks_discharge_via_link hRem hMerge (hLinkSound hDL hRec) hC
  evalValid_mono_ax := fun hSub hE => conditionalEvalValid_mono_ax hSub hE
  checked_to_class := fun hCls hC hAxK hEvK hLnkK =>
    hC (fun a ha => hClassAx hCls (hAxK a ha))
       (fun e he => hClassEval hCls (hEvK e he))
       (fun l hl => hClassLink hCls (hLnkK l hl))
  batch_balance_sound := hBatchSound

/-- **Part 2 Headline Theorem (`acceptedAggrTree_sharded_yields_kernel_model`):**
Composes an accepted unconditional `CheckEnv` aggregation tree (under standard binding-discharged
validator `3` `.validated b` or literal-class validator `5` `.literalClass k`, with `A = ∅`,
`Ax = ∅`, `EvalA = ∅`, `Linked = ∅`) with an accepted `binding spec b` circuit run `runB` and
a finite closed DAG partition `shardRuns` of conditional shard runs via
`IxVM.Refinement.Endpoint.circuitShardedComposed` (`ConditionalShards.lean`)!

Concludes for EVERY set theory `W : Type u` with `[Ix.Kernel.SetTheory W]`:
1. Zero Shape 18 Mode 3a external dynamic-circuit discharges occurred (`t.dynamicLinkDischarges = 0`);
2. Every subject `x ∈ S` satisfies `sem.Checked` and `S` is `sem.Dep`-closed;
3. Every child proof in `t` refines cleanly (no collision ⇒ every child passes `verifyBatchBytes = true`);
4. EITHER a concrete BLAKE3 collision occurred across the shard + binding runs, OR the binding
   table admits and validates on all 77 groups and there exists a consistent kernel environment
   `env` extending `envT` covering EVERY constant in `S` together with an ACTUAL
   **`Nonempty (Ix.Kernel.Model W (claimedEnv env))`**, **`SeedsNotFalse`**, and **`SeedsInhabited`**! -/
theorem acceptedAggrTree_sharded_yields_kernel_model (W : Type u) [Ix.Kernel.SetTheory W]
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {mode : _root_.Aggr.ValidatorMode _root_.Address} (hDis : mode.isBindingDischarged = true)
    {b : _root_.Address} {S : _root_.Address → Prop}
    {dB : IxVM.Refinement.Digest} (runB : AcceptedCircuitRun dB)
    {bytesB : ByteArray} {spec : _root_.Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec b))
    (hdB : IxVM.Refinement.packDigest (_root_.Address.blake3Pure bytesB) = dB)
    (shardRuns : List (Sigma AcceptedCircuitRun))
    (hSumRom : (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39)
    {assumed : Bool} {V : IxVM.Refinement.View} {entries : List ShardClaimEntry}
    (hPart : ClosedShardPartition (shardRuns.map (·.1)) b assumed V entries)
    (hS : ∀ x, S x ↔ x ∈ ShardClaimEntry.allSeeds entries)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv mode S (fun _ => False) (fun _ => False) (fun _ => False) (fun _ => False))) :
    ∃ (callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
      (shardCalls : List (List (Aiur.Generic.SourceSemantics.Call IxVM.F))),
      (∃ vB hB, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
          [IxVM.Refinement.digestValue dB] [] vB hB callsB ∧
        Aiur.Generic.SourceSemantics.CallsInROM (runB.compiled.traceROM runB.rom) callsB) ∧
      List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
        ∃ v h, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
            [IxVM.Refinement.digestValue run.1] [] v h calls ∧
          Aiur.Generic.SourceSemantics.CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
        shardRuns shardCalls ∧
      (NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
        (∀ x, S x → sem.Checked mode.bindingOf (fun _ => False) (fun _ => False) (fun _ => False) x) ∧
        (∀ x y, S x → sem.Dep x y → S y) ∧
        t.dynamicLinkDischarges = 0 ∧
        (t.HasTreeCollision ∨
          ∀ vp ∈ t.childProofs, ∃ proofBytes,
            Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) ∧
        (V.HashedCollision (ShardClaimEntry.allBytes entries ++ bytesB :: committedFootprint)
            (shardCalls.flatten ++ callsB) ∨
          ComposedWith.{u}
            (fun tRole R envT =>
              (∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
                LoadedBy shardCalls.flatten E₀ ∧
                (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
                (∀ s, S s → ∀ s', SeedConstant E₀ s s' →
                  ∃ ci, env.find? (keyOf tRole s') = some ci ∧
                    (PinnedBasis ci ∨ KeptIn tRole (storeOver E₀ R) (blobOver E₀ R) s' ci)) ∧
                Nonempty (Ix.Kernel.Model W (claimedEnv env))) ∧
              SeedsNotFalse shardCalls.flatten tRole R (ShardClaimEntry.allSeeds entries) ∧
              SeedsInhabited.{u} shardCalls.flatten tRole R (ShardClaimEntry.allSeeds entries))
            callsB b)) := by
  have hUnl : mode.isLinked = false := by
    cases mode <;> simp [_root_.Aggr.ValidatorMode.isBindingDischarged, _root_.Aggr.ValidatorMode.isLinked] at hDis ⊢
  have hBindCond : mode.bindingCond sem.BindingValid := by
    cases mode <;> simp [_root_.Aggr.ValidatorMode.isBindingDischarged, _root_.Aggr.ValidatorMode.bindingCond] at hDis ⊢
  obtain ⟨hDeriv, hChildOk⟩ := acceptedAggrTree_refines_derivation19 t
  obtain ⟨hChk, hCl, _⟩ := _root_.Aggr.aggrDerivation19_invariant hDeriv
  obtain ⟨vB, hB, callsB, hObsB, hCarB, hShards⟩ :=
    circuitShardedComposed.{u} runB.compiled runB.physical runB.certified runB.bits runB.plan
      runB.activated runB.valid runB.small dB runB.signed runB.rooted runB.outside runB.bound
      runB.checked runB.arguments runB.decoded
  obtain ⟨shardCalls, hCarShards, hSpec⟩ := hShards shardRuns hSumRom
  refine ⟨callsB, shardCalls, ⟨vB, hB, hObsB, hCarB⟩, hCarShards, fun hNoBlk => ?_⟩
  refine ⟨hChk hBindCond, fun x y hx hDep => (hCl x y hx hDep).elim id False.elim,
    acceptedAggrTree_unlinked_zero_dynamicLinkDischarges hUnl t, hChildOk, ?_⟩
  have hMod := shardedModelConclusion_of_shardedComposedSpec hSpec hdeB hdB hPart hNoBlk
  rcases shardedKernelModel_of_shardedModelConclusion hMod with hCol | hOk
  · exact Or.inl hCol
  · refine Or.inr (ComposedWith.imp (fun tRole R envT ⟨⟨E₀, env, hE₀, hSub, hCov, hM⟩, hNF, hInh⟩ => ?_) hOk)
    exact ⟨⟨E₀, env, hE₀, hSub, fun s hs => hCov s ((hS s).mp hs), hM W⟩, hNF W, hInh⟩

/-- **Single-Run `circuitComposed` Corollary (`acceptedAggrTree_singleRun_yields_kernel_model`):**
Directly connects an accepted unconditional `CheckEnv` aggregation tree (under standard validator `3`)
paired with a single `InScopeTyping` run `runA` and `binding` run `runB` via
`IxVM.Refinement.Endpoint.circuitComposed` to an actual **`Nonempty (Ix.Kernel.Model W (claimedEnv env))`**! -/
theorem acceptedAggrTree_singleRun_yields_kernel_model (W : Type u) [Ix.Kernel.SetTheory W]
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {b : _root_.Address} {S : _root_.Address → Prop}
    {dB dA : IxVM.Refinement.Digest}
    (runB : AcceptedCircuitRun dB) (runA : AcceptedCircuitRun dA)
    {bytesB : ByteArray} {spec : _root_.Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec b))
    (hdB : IxVM.Refinement.packDigest (_root_.Address.blake3Pure bytesB) = dB)
    {bytesA : ByteArray} {cA : Ix.Claim}
    (hdeA : Ix.Claim.de bytesA = .ok cA)
    (hdA : IxVM.Refinement.packDigest (_root_.Address.blake3Pure bytesA) = dA)
    (hsc : InScopeTyping cA)
    {ctx : Ix.ClaimContext} (hctx : cA.context? = some ctx) (hba : ctx.binding = b)
    {V : IxVM.Refinement.View} {seeds : List _root_.Address} (hseeds : ClaimSeeds cA V seeds)
    (hS : ∀ x, S x ↔ x ∈ seeds)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv (.validated b) S (fun _ => False) (fun _ => False) (fun _ => False) (fun _ => False))) :
    ∃ (callsB callsA : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
      t.dynamicLinkDischarges = 0 ∧
      (V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
        ComposedWith.{u}
          (fun tRole R envT =>
            (∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
              LoadedBy callsA E₀ ∧
              (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
              (∀ s, S s → ∀ s', SeedConstant E₀ s s' →
                ∃ ci, env.find? (keyOf tRole s') = some ci ∧
                  (PinnedBasis ci ∨ KeptIn tRole (storeOver E₀ R) (blobOver E₀ R) s' ci)) ∧
              Nonempty (Ix.Kernel.Model W (claimedEnv env))) ∧
            SeedsNotFalse callsA tRole R seeds ∧
            SeedsInhabited.{u} callsA tRole R seeds)
          callsB b) := by
  obtain ⟨_, _, callsB, _, _, hA⟩ :=
    circuitComposed.{u} runB.compiled runB.physical runB.certified runB.bits runB.plan
      runB.activated runB.valid runB.small dB runB.signed runB.rooted runB.outside runB.bound
      runB.checked runB.arguments runB.decoded
  obtain ⟨_, _, callsA, _, _, hComp⟩ :=
    hA runA.compiled runA.physical runA.certified runA.bits runA.plan
      runA.activated runA.valid runA.small dA runA.signed runA.rooted runA.outside runA.bound
      runA.checked runA.arguments runA.decoded
  refine ⟨callsB, callsA, acceptedAggrTree_unlinked_zero_dynamicLinkDischarges rfl t, ?_⟩
  rcases hComp.apply hdeB hdB hdeA hdA hsc hctx hba hseeds with hCol | hOk
  · exact Or.inl hCol
  · refine Or.inr (ComposedWith.imp (fun tRole R envT hread => ?_) hOk)
    have hread' := hread
    obtain ⟨E₀, env, hloadE, _, hsub, _, hcov, hmod⟩ := hread'
    exact ⟨⟨E₀, env, hloadE, hsub, fun s hs => hcov s ((hS s).mp hs), hmod W⟩,
      ConsistentReadOver.seeds_not_false W hread,
      ConsistentReadOver.seeds_inhabited hread⟩

end ConcreteKernelModelSemantics

/-! ## Section 5: Part 3 Headline — End-to-End Composition with `CompressionCert` + `Aiur.MultiStarkBridge` -/

section EndToEndCompressionAndMultiStarkBridge

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.MultiStarkSpec Aiur.MultiStarkBridge
open IxCC IxCC.AiurBackend
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower (qualified qualifyExprF hasDoubleColon entryName natLimit)
open IxCC.AiurBackend.Gadgets (WorldHasFn)
open IxCC.AiurBackend.TypedGadgets (FieldCompatible64)
open IxCC.AiurBackend.TypedRep (Rep)
open IxCC.AiurBackend.TypedLower (LoweredProgram)
open IxCC.AiurBackend.TypedWorld (checkTypedWorld)
open IxCC.AiurBackend.Progress (checkShape)
open IxCC.AiurBackend.WitnessIO
  (ByteStreamRel StarkIOWorld KzgIOWorld
   WitnessChannelKind witnessVarName witnessWrapperBody)
open IxCC.AiurBackend.CompressionIntrinsics (CompressionConfig)
open IxCC.AiurBackend.CompressionIntrinsicsProof
  (GLF CompressionLowerBridge CompressionCert
   compressionCert_witness_goldilocks compressionCert_witness_bn254 compressionCert_witness_bls12381)
open IxVM.Consistency IxVM.Refinement IxVM.Refinement.Endpoint
open Ix.Cert.Aggr

/-- Canonical 16-word public input vector `[allowed0..7, outClaim0..7]` for `MultiStark::ix_aggr`,
embedded into an arbitrary field `F` via `SourceValue.field (n : F)`. -/
def aggregatePubVals (F : Type) [Field F]
    (allowedDigest outClaimDigest : Digest32Words) : List (SourceValue F) :=
  [allowedDigest.w0, allowedDigest.w1, allowedDigest.w2, allowedDigest.w3,
   allowedDigest.w4, allowedDigest.w5, allowedDigest.w6, allowedDigest.w7,
   outClaimDigest.w0, outClaimDigest.w1, outClaimDigest.w2, outClaimDigest.w3,
   outClaimDigest.w4, outClaimDigest.w5, outClaimDigest.w6, outClaimDigest.w7].map
    (fun n => .field (n : F))

/-- Pre-intrinsic functional refinement contract linking the lowered aggregator verifier
`checkFnName` in `wOrig` to `AggregatePure.verifyAggregateStep` over `k` `ByteStreamRel`-linked
witness byte streams deserialized via `decodeWitness`. -/
def VerifyAggregateStepEvalSound {F : Type} [Field F] [DecidableEq F]
    (wOrig : World F) (checkFnName : String) (numChannels : Nat)
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    (allowedDigest outClaimDigest : Digest32Words) : Prop :=
  ∀ (h1 h2 : Heap F) (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
    ws.length = numChannels →
    List.Forall₂ (ByteStreamRel h1) ws wPtrs →
    EvalFn wOrig checkFnName (aggregatePubVals F allowedDigest outClaimDigest ++ wPtrs) h1 (.field 1) h2 →
    verifyAggregateStep allowedDigest outClaimDigest (decodeWitness ws) = 1

/-- Witness-wrapper postcondition predicate passed to `CompressionCert.accepted_witness_assertOk_sound`. -/
def AggregateStepWitnessSpec {F : Type} [Field F]
    (numChannels : Nat) (decodeWitness : List (List UInt8) → AggrStepWitness)
    (allowedDigest outClaimDigest : Digest32Words)
    (pub : List (SourceValue F)) (ws : List (List UInt8)) : Prop :=
  pub = aggregatePubVals F allowedDigest outClaimDigest →
  ws.length = numChannels →
  AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws)

private theorem verifyAggregateStepEvalSound_to_witnessSpec {F : Type} [Field F] [DecidableEq F]
    {wOrig : World F} {checkFnName : String} {numChannels : Nat}
    {decodeWitness : List (List UInt8) → AggrStepWitness}
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName numChannels decodeWitness
      allowedDigest outClaimDigest) :
    ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      AggregateStepWitnessSpec numChannels decodeWitness allowedDigest outClaimDigest pubArgs ws := by
  intro pubArgs h1 h2 wPtrs ws hRel ev hpub hlen
  subst hpub
  exact verifyAggregateStep_sound (href h1 h2 wPtrs ws hlen hRel ev)

/-- **Part 3 Headline (`compressionCert_aggregateStep_accepted`, Arbitrary Prime Field `F`):**
Any accepted trace (`cert.plan.checkMemo = .ok ()`) of an `IxCCAiur`-compiled `--assert-ok`
`AggregatePure` step circuit over `[Field F] [DecidableEq F]` yields finite witness streams
satisfying full `AggregateStepAccepted` (including exact 80-byte allowed-blob pin,
`CompressWrapAccepted` on every child, Shape 10 `ShardAccepted` & `K` sum, Shape 17
`SecurityEnvelopeOk`, and Shape 18 validator `14`/`15` & `12`/`13` isolation)! -/
theorem compressionCert_aggregateStep_accepted {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals F allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws) := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    cert.accepted_witness_assertOk_sound characteristic hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyAggregateStepEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  exact ⟨ws, hwsLen, hspec rfl hwsLen⟩

/-- **Goldilocks (`p_G`) Specialization (`compressionCert_aggregateStep_goldilocks`):** -/
theorem compressionCert_aggregateStep_goldilocks
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program GLF} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World GLF}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF GLF (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {rom : Aiur.WidthROM GLF} (valid : rom.Valid)
    {wires : List (Aiur.WireValue GLF)} {output : Aiur.WireValue GLF}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message GLF}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow GLF)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals GLF allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws) := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_goldilocks cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyAggregateStepEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  exact ⟨ws, hwsLen, hspec rfl hwsLen⟩

/-- **BN254 (`Fr`) Specialization (`compressionCert_aggregateStep_bn254`):** -/
theorem compressionCert_aggregateStep_bn254
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BN254.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World Aiur.Library.Field.BN254.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BN254.F (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {rom : Aiur.WidthROM Aiur.Library.Field.BN254.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BN254.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BN254.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BN254.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BN254.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals Aiur.Library.Field.BN254.F allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws) := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_bn254 cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyAggregateStepEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  exact ⟨ws, hwsLen, hspec rfl hwsLen⟩

/-- **BLS12-381 (`Fr`) Specialization (`compressionCert_aggregateStep_bls12381`):** -/
theorem compressionCert_aggregateStep_bls12381
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BLS12381.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World Aiur.Library.Field.BLS12381.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BLS12381.F (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {rom : Aiur.WidthROM Aiur.Library.Field.BLS12381.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BLS12381.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BLS12381.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals Aiur.Library.Field.BLS12381.F allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws) := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_bls12381 cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyAggregateStepEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  exact ⟨ws, hwsLen, hspec rfl hwsLen⟩

/-- **Source-Level `Recheck.FrontFir` Composition (`compressionCert_aggregateStep_source_accepted`):**
Composes `CompressionCert.accepted_assertOk_source` directly with `verifyAggregateStep_sound`
(`plan.checkMemo` → `Sem.Lang.run = .ok v ∧ obs v = some (.nat 1)` → `AggregateStepAccepted`)! -/
theorem compressionCert_aggregateStep_source_accepted {p : Nat} [Fact (Nat.Prime p)]
    (fc : FieldCompatible64 (ZMod p))
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : ZMod p) ≠ 0)
    (hnat : natLimit ≤ p)
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program (ZMod p)} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source (ZMod p)} (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List (ZMod p)}
    {rom : Aiur.WidthROM (ZMod p)} (valid : rom.Valid)
    {wires : List (Aiur.WireValue (ZMod p))} {output : Aiur.WireValue (ZMod p)}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message (ZMod p)}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow (ZMod p))} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Aiur.Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true)
    {allowedDigest outClaimDigest : Digest32Words} {w : AggrStepWitness}
    (hSrcRefine :
      (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1)) →
      verifyAggregateStep allowedDigest outClaimDigest w = 1) :
    AggregateStepAccepted allowedDigest outClaimDigest w :=
  verifyAggregateStep_sound <| hSrcRefine <|
    cert.accepted_assertOk_source fc characteristic hnat hf hAssert hexp hret hfn
      hwOrig bridge valid signed rooted outside bound checked arguments decoded hcov hshape

/-- **Full `MultiStarkBridge` + `CompressionCert` + `AggregatePure` Bridge (Goldilocks):**
Starts directly from `Aiur.MultiStarkBridge.LoweredSystemSatisfied` on the compiled `AggregatePure`
verifier circuit (discharging BOTH `rom.Valid` AND `cert.plan.checkMemo = .ok ()` automatically
via `Aiur.MultiStarkBridge.lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks`!),
and reaches `AggregateStepAccepted` via `CompressionCert`! -/
theorem loweredSystem_compressionCert_aggregateStep_goldilocks
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program GLF} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World GLF}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF GLF (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {wires : List (Aiur.WireValue GLF)} {output : Aiur.WireValue GLF}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message GLF}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals GLF allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (callableId : String → Nat) (idOk : ∀ x n, cert.id x = .ok n → n = callableId x)
    (names : (Aiur.Tiling.Grouped.circuitNames cert.plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (traces : List (CircuitTrace GLF))
    (hsat : LoweredSystemSatisfied callableId cert.plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces)
    (hrowsBound : totalRows (fnTracesOf callableId cert.plan traces) ≤ Aiur.MultiStarkSpec.maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId cert.plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId cert.plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ Aiur.Tiling.Grouped.allChips cert.plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Aiur.Tiling.Bridge.Shaped.check
      (Aiur.Optimized.Depth.system cert.dcfg cert.physical.system)
      (Aiur.Tiling.Grouped.allChips cert.plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Aiur.Optimized.Depth.system cert.dcfg cert.physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM ⟨[]⟩) root = .ok ()) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws) := by
  obtain ⟨_, hromValid, wrows, hbound, hchecked⟩ :=
    lowerFullSystem_checkDepthPlan_checkMemo_unsegmented_goldilocks
      cert.compiled.circuit cert.physical cert.plan cert.depthPlanOk callableId idOk names
      fixedMaps romWidths hndRom logBlowup extDegree romLayout root traces hsat hrowsBound
      hbudget hromCap hromWidths hmemWidth hshaped hctxEmpty
  exact compressionCert_aggregateStep_goldilocks cert hAssert hsio hkio bridge hchkQual hnd hwrap
    decodeWitness href hromValid signed rooted outside hbound hchecked arguments decoded

/-- **UNIFIED END-TO-END CROWN-JEWEL THEOREM (`loweredSystem_compressionCert_aggregate_to_kernel_model`):**
Composes ALL stages of the pure-Lean certified stack in ONE unbroken theorem:
1. `Aiur.MultiStarkBridge.LoweredSystemSatisfied` on the `IxCCAiur`-compiled `AggregatePure`
   circuit (`cert : CompressionCert` over `GLF`) → `cert.plan.checkMemo = .ok ()` →
   `CompressionCert` (`SrcEval`) → `AggregateStepAccepted` (exact allowed-blob pin,
   `CompressWrapAccepted` children, Shape 18 Mode 2 `14`/`15` isolation);
2. `AcceptedAggrTree` rooted at an unconditional binding-discharged `CheckEnv` (`validator ∈ {3, 5}`,
   `A = ∅`, `Ax = ∅`, `EvalA = ∅`, `Linked = ∅`) → `AggrDerivation19`, `AggrNodeHolds`, and
   `t.dynamicLinkDischarges = 0`;
3. `AcceptedCircuitRun` (discharged via `acceptedCircuitRun_of_loweredSystem_{unsegmented,segmented}`)
   for the `binding spec b` claim and a closed DAG partition of conditional shard runs →
   `IxVM.Refinement.Endpoint.circuitShardedComposed` (`ConditionalShards.lean`) →
   an ACTUAL set-theoretic **`Nonempty (Ix.Kernel.Model W (claimedEnv env))`** + **`SeedsNotFalse`**
   + **`SeedsInhabited`** in EVERY `Ix.Kernel.SetTheory W`! -/
theorem loweredSystem_compressionCert_aggregate_to_kernel_model (W : Type u) [Ix.Kernel.SetTheory W]
    -- 1. Outer `IxCCAiur`-compiled `AggregatePure` circuit (`LoweredSystemSatisfied` → `CompressionCert`)
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program GLF} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : Aiur.Generic.SourceSemantics.World GLF}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF GLF (witnessWrapperBody pubParams channels checkFnName false)))
    (decodeWitness : List (List UInt8) → AggrStepWitness)
    {allowedDigest outClaimDigest : Digest32Words}
    (href : VerifyAggregateStepEvalSound wOrig checkFnName channels.length decodeWitness
      allowedDigest outClaimDigest)
    {wires : List (Aiur.WireValue GLF)} {output : Aiur.WireValue GLF}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message GLF}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (aggregatePubVals GLF allowedDigest outClaimDigest)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (callableId : String → Nat) (idOk : ∀ x n, cert.id x = .ok n → n = callableId x)
    (names : (Aiur.Tiling.Grouped.circuitNames cert.plan).Nodup)
    (fixedMaps : List FixedMapMeta) (romWidths : List Nat) (hndRom : romWidths.Nodup)
    (logBlowup extDegree : Nat) (romLayout : RomLayout)
    (traces : List (CircuitTrace GLF))
    (hsat : LoweredSystemSatisfied callableId cert.plan fixedMaps romWidths logBlowup false
      extDegree romLayout root 0 traces)
    (hrowsBound : totalRows (fnTracesOf callableId cert.plan traces) ≤ Aiur.MultiStarkSpec.maxBatchRows)
    (hbudget : systemLookupBudget
      (lowerFullSystem callableId cert.plan fixedMaps romWidths logBlowup false extDegree romLayout)
      traces < 2 ^ 63)
    (hromCap : List.Forall₂ (fun w tr => romLayoutLanes romLayout w * tr.height ≤ 2 ^ 63)
      romWidths (romTracesOf callableId cert.plan fixedMaps logBlowup traces))
    (hromWidths : ∀ w ∈ romWidths, w < 2 ^ 63)
    (hmemWidth : ∀ c ∈ Aiur.Tiling.Grouped.allChips cert.plan, ∀ m ∈ c.memory, m.value.words.length < 2 ^ 63)
    (hshaped : Aiur.Tiling.Bridge.Shaped.check
      (Aiur.Optimized.Depth.system cert.dcfg cert.physical.system)
      (Aiur.Tiling.Grouped.allChips cert.plan) callableId root (2 ^ 63) = true)
    (hctxEmpty : (Aiur.Optimized.Depth.system cert.dcfg cert.physical.system).checkContext
      (Aiur.Circuit.Erasure.rawROM ⟨[]⟩) root = .ok ())
    -- 2. Accepted aggregation tree & sharded IxVM runs (`ConditionalShards.lean`)
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement
      Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) →
      (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {mode : _root_.Aggr.ValidatorMode _root_.Address} (hDis : mode.isBindingDischarged = true)
    {b : _root_.Address} {S : _root_.Address → Prop}
    {dB : IxVM.Refinement.Digest} (runB : AcceptedCircuitRun dB)
    {bytesB : ByteArray} {spec : _root_.Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec b))
    (hdB : IxVM.Refinement.packDigest (_root_.Address.blake3Pure bytesB) = dB)
    (shardRuns : List (Sigma AcceptedCircuitRun))
    (hSumRom : (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39)
    {assumed : Bool} {V : IxVM.Refinement.View} {entries : List ShardClaimEntry}
    (hPart : ClosedShardPartition (shardRuns.map (·.1)) b assumed V entries)
    (hS : ∀ x, S x ↔ x ∈ ShardClaimEntry.allSeeds entries)
    (t : AcceptedAggrTree sem batchClaim
      (.checkEnv mode S (fun _ => False) (fun _ => False) (fun _ => False) (fun _ => False))) :
    (∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      AggregateStepAccepted allowedDigest outClaimDigest (decodeWitness ws)) ∧
    (∃ (callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
      (shardCalls : List (List (Aiur.Generic.SourceSemantics.Call IxVM.F))),
      (∃ vB hB, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
          [IxVM.Refinement.digestValue dB] [] vB hB callsB ∧
        Aiur.Generic.SourceSemantics.CallsInROM (runB.compiled.traceROM runB.rom) callsB) ∧
      List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
        ∃ v h, Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
            [IxVM.Refinement.digestValue run.1] [] v h calls ∧
          Aiur.Generic.SourceSemantics.CallsInROM (run.2.compiled.traceROM run.2.rom) calls)
        shardRuns shardCalls ∧
      (NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
        (∀ x, S x → sem.Checked mode.bindingOf (fun _ => False) (fun _ => False) (fun _ => False) x) ∧
        (∀ x y, S x → sem.Dep x y → S y) ∧
        t.dynamicLinkDischarges = 0 ∧
        (t.HasTreeCollision ∨
          ∀ vp ∈ t.childProofs, ∃ proofBytes,
            Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) ∧
        (V.HashedCollision (ShardClaimEntry.allBytes entries ++ bytesB :: committedFootprint)
            (shardCalls.flatten ++ callsB) ∨
          ComposedWith.{u}
            (fun tRole R envT =>
              (∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
                LoadedBy shardCalls.flatten E₀ ∧
                (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
                (∀ s, S s → ∀ s', SeedConstant E₀ s s' →
                  ∃ ci, env.find? (keyOf tRole s') = some ci ∧
                    (PinnedBasis ci ∨ KeptIn tRole (storeOver E₀ R) (blobOver E₀ R) s' ci)) ∧
                Nonempty (Ix.Kernel.Model W (claimedEnv env))) ∧
              SeedsNotFalse shardCalls.flatten tRole R (ShardClaimEntry.allSeeds entries) ∧
              SeedsInhabited.{u} shardCalls.flatten tRole R (ShardClaimEntry.allSeeds entries))
            callsB b))) :=
  ⟨loweredSystem_compressionCert_aggregateStep_goldilocks cert hAssert hsio hkio bridge
      hchkQual hnd hwrap decodeWitness href signed rooted outside arguments decoded
      callableId idOk names fixedMaps romWidths hndRom logBlowup extDegree romLayout
      traces hsat hrowsBound hbudget hromCap hromWidths hmemWidth hshaped hctxEmpty,
    acceptedAggrTree_sharded_yields_kernel_model W hDis runB hdeB hdB shardRuns hSumRom hPart hS t⟩

end EndToEndCompressionAndMultiStarkBridge

/-! ## Section 6: Kernel-Checked Axiom Fences (`⊆ [propext, Classical.choice, Quot.sound]`) -/

section AxiomFences

-- Section 1 & 2: Address Order, Canonical Trees, Set Ops, Allowed Blob, Range & Shape 17/18 Isolation
/-- info: 'AggregateSpec.aggrAddressOrder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrAddressOrder_spec

/-- info: 'AggregateSpec.aggrCheckCanonicalTree_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrCheckCanonicalTree_sound

/-- info: 'AggregateSpec.aggrAssertUnion_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrAssertUnion_sound

/-- info: 'AggregateSpec.joinRel_of_aggrPair_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.joinRel_of_aggrPair_checks

/-- info: 'AggregateSpec.aggrAssertStructuralDifference_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrAssertStructuralDifference_sound

/-- info: 'AggregateSpec.aggrExtractRemovedLeaf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrExtractRemovedLeaf_sound

/-- info: 'AggregateSpec.parseAllowedBlob_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.parseAllowedBlob_sound

/-- info: 'AggregateSpec.verifyChildBatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyChildBatch_sound

/-- info: 'AggregateSpec.verifyChildDigest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyChildDigest_sound

/-- info: 'AggregateSpec.aggrVerifyRange_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrVerifyRange_sound

/-- info: 'AggregateSpec.aggrAssertSecurityEnvelope_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrAssertSecurityEnvelope_iff

/-- info: 'AggregateSpec.aggrParseEvalDischargeOut_isolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.aggrParseEvalDischargeOut_isolation

/-- info: 'AggregateSpec.verifyShapeDischargeEval_mode_isolation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyShapeDischargeEval_mode_isolation

/-- info: 'AggregateSpec.verifyAggregateStep_shape18_never_standard_validator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyAggregateStep_shape18_never_standard_validator

-- Section 3: Pure-Lean Circuit → `AcceptedAggrTree` & `AggrDerivation19`
/-- info: 'AggregateSpec.verifyAggregateStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyAggregateStep_sound

/-- info: 'AggregateSpec.verifyAggregateRoot_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyAggregateRoot_sound

/-- info: 'AggregateSpec.PureAcceptedAggrTree.toDerivation19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.PureAcceptedAggrTree.toDerivation19

/-- info: 'AggregateSpec.PureAcceptedAggrTree.unlinked_zero_dynamicLinkDischarges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.PureAcceptedAggrTree.unlinked_zero_dynamicLinkDischarges

/-- info: 'AggregateSpec.verifyAggregateRoot_to_pureAcceptedAggrTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyAggregateRoot_to_pureAcceptedAggrTree

/-- info: 'AggregateSpec.verifyAggregateRoot_to_acceptedAggrTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.verifyAggregateRoot_to_acceptedAggrTree

-- Section 4: Concrete `AggrSemantics` from `ConditionalShards` + `circuitComposed` + `MultiStarkBridge` → `Ix.Kernel.Model W`
/-- info: 'AggregateSpec.acceptedCircuitRun_of_loweredSystem_unsegmented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.acceptedCircuitRun_of_loweredSystem_unsegmented

/-- info: 'AggregateSpec.acceptedCircuitRun_of_loweredSystem_segmented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.acceptedCircuitRun_of_loweredSystem_segmented

/-- info: 'AggregateSpec.ixvmShardedAggrSemantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.ixvmShardedAggrSemantics

/-- info: 'AggregateSpec.acceptedAggrTree_sharded_yields_kernel_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.acceptedAggrTree_sharded_yields_kernel_model

/-- info: 'AggregateSpec.acceptedAggrTree_singleRun_yields_kernel_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.acceptedAggrTree_singleRun_yields_kernel_model

-- Section 5: End-to-End Composition with `CompressionCert` + `Aiur.MultiStarkBridge`
/-- info: 'AggregateSpec.compressionCert_aggregateStep_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.compressionCert_aggregateStep_accepted

/-- info: 'AggregateSpec.compressionCert_aggregateStep_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.compressionCert_aggregateStep_goldilocks

/-- info: 'AggregateSpec.compressionCert_aggregateStep_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.compressionCert_aggregateStep_bn254

/-- info: 'AggregateSpec.compressionCert_aggregateStep_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.compressionCert_aggregateStep_bls12381

/-- info: 'AggregateSpec.compressionCert_aggregateStep_source_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.compressionCert_aggregateStep_source_accepted

/-- info: 'AggregateSpec.loweredSystem_compressionCert_aggregateStep_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.loweredSystem_compressionCert_aggregateStep_goldilocks

/-- info: 'AggregateSpec.loweredSystem_compressionCert_aggregate_to_kernel_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AggregateSpec.loweredSystem_compressionCert_aggregate_to_kernel_model

end AxiomFences

end AggregateSpec
