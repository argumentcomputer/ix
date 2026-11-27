import Blake3.Pure
import Aiur.Library.Field.Goldilocks.Emulated
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.Bls12381.Field
import Ix.Cert.Compression.Bls12381.EndToEnd
import Ix.Cert.Compression.Security128Audit

/-! # Statement-Digest Propagation, `PackedPolicy` (`IXAUKG01`), and Stage Manifest Binding

Formalizes the exact binary codecs, domain separators, statement-digest propagation,
`PackedPolicy` (`IXAUKG01`) key/anchor pinning, and `ix-aiur-stages-v1` manifest binding
connecting all stages of the Lean-compiled Aiur compression pipeline:

`ix_aggr` root `(rootKeyBytes, rootClaimsBytes)` →
`CompressWrap::verify_root([0;8], stmtWords)` →
`CompressGL::verify_root([0;8], stmtWords)` →
`CompressNarrowFixed::step_v1(policyDigest, 1, stmtWords)` →
`CompressFinalNarrow::verify_accumulator_v1(stmtLow, stmtHigh)` →
outer PLONK/Groth16 public inputs.

Key proved guarantees:
1. Exact injectivity of `"ix/compress-wrap/v1\0"` preimage encoding, 8-word little-endian
   `u32` packing (`Blake3::pack_digest`), and 2×128-bit terminal limb packing
   (`CompressFinalNarrow::statement`), with zero modular wrap-around in both `BN254Fr`
   and `BLS12381Fr`.
2. Zero ambient wrap-around for emulated Goldilocks arithmetic over both `BN254Fr`
   and `BLS12381Fr`.
3. Exact 208-byte `IXAUKG01` `PackedPolicy` injectivity and BLAKE3 digest binding (with
   explicit collision escape).
4. `ix-aiur-stages-v1` manifest pinning requiring at least one digest pin per setup
   product and binding root key, GL key, narrow key, policy digest, and 128-byte pairing
   anchors end-to-end.
5. `AiurCompression128Ok` security profile pairing `v6` 128-bit post-quantum Multi-STARK (`Fp^3`,
   64-byte RFC 7693 `BLAKE2b-512`) with 128-bit-class BLS12-381 (`PairingCurve128Ok`).

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.EndToEnd
open Ix.Cert.MultiStark.Security128

/-! ## 1. Domain Separators & `"ix/compress-wrap/v1\0"` Preimage Binding -/

/-- Exact 20-byte ASCII domain separator `"ix/compress-wrap/v1\0"` matching
`CompressWrap::statement_bytes` (`MultiStark/MultiStark/Modules/CompressWrap.lean`) and
`stark_verifier::compress_wrap::STATEMENT_DOMAIN`. -/
def compressWrapDomain : List UInt8 :=
  [ 105, 120, 47, 99, 111, 109, 112, 114,
    101, 115, 115, 45, 119, 114, 97, 112,
    47, 118, 49, 0 ]

/-- Exact 31-byte ASCII domain separator `"ix/aiur/kzg/fold-transcript/v1\0"` matching
`CompressBNPacked::fold_domain` (`MultiStark/MultiStark/BN/CompressBNPacked.lean`). -/
def foldTranscriptDomain : List UInt8 :=
  [ 105, 120, 47, 97, 105, 117, 114, 47,
    107, 122, 103, 47, 102, 111, 108, 100,
    45, 116, 114, 97, 110, 115, 99, 114,
    105, 112, 116, 47, 118, 49, 0 ]

/-- Exact 84-byte `CompressWrap` statement preimage:
`"ix/compress-wrap/v1\0" ‖ keyDigest ‖ claimsDigest`. -/
def compressWrapPreimage (keyDigest claimsDigest : List UInt8) : List UInt8 :=
  compressWrapDomain ++ keyDigest ++ claimsDigest

/-- Canonical 32-byte `CompressWrap` statement digest computed via `Blake3.Pure.digest`. -/
def compressWrapStatementDigest (keyDigest claimsDigest : List UInt8) : Vector UInt8 32 :=
  Blake3.Pure.digest (compressWrapPreimage keyDigest claimsDigest)

/-- Explicit BLAKE3 collision predicate on two distinct byte lists. -/
def Blake3Collision (a b : List UInt8) : Prop :=
  a ≠ b ∧ Blake3.Pure.digest a = Blake3.Pure.digest b

theorem compressWrapPreimage_length {k c : List UInt8} (hk : k.length = 32) (hc : c.length = 32) :
    (compressWrapPreimage k c).length = 84 := by
  simp [compressWrapPreimage, compressWrapDomain, hk, hc]

theorem compressWrapPreimage_injective {k₁ c₁ k₂ c₂ : List UInt8}
    (hk₁ : k₁.length = 32) (hk₂ : k₂.length = 32)
    (heq : compressWrapPreimage k₁ c₁ = compressWrapPreimage k₂ c₂) :
    k₁ = k₂ ∧ c₁ = c₂ := by
  unfold compressWrapPreimage at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have hrest : k₁ ++ c₁ = k₂ ++ c₂ := List.append_cancel_left heq
  exact List.append_inj hrest (hk₁.trans hk₂.symm)

/-- Equal `CompressWrap` statement digests either arise from identical `(keyDigest, claimsDigest)`
or exhibit a concrete 84-byte BLAKE3 collision. -/
theorem compressWrap_statement_binds_root_or_collision {k₁ c₁ k₂ c₂ : List UInt8}
    (hk₁ : k₁.length = 32) (hk₂ : k₂.length = 32)
    (hdig : compressWrapStatementDigest k₁ c₁ = compressWrapStatementDigest k₂ c₂) :
    Blake3Collision (compressWrapPreimage k₁ c₁) (compressWrapPreimage k₂ c₂) ∨
      (k₁ = k₂ ∧ c₁ = c₂) := by
  by_cases heq : compressWrapPreimage k₁ c₁ = compressWrapPreimage k₂ c₂
  · exact Or.inr (compressWrapPreimage_injective hk₁ hk₂ heq)
  · exact Or.inl ⟨heq, hdig⟩

/-! ## 2. Little-Endian `u32` Packing, 2×`u128` Terminal Limbs & Zero-Wrap Embeddings -/

/-- Pack four canonical bytes into one little-endian `u32` natural number. -/
def u32leOf4 (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat

theorem u32leOf4_lt (b0 b1 b2 b3 : UInt8) : u32leOf4 b0 b1 b2 b3 < 2 ^ 32 := by
  unfold u32leOf4
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  omega

theorem u32leOf4_injective {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8}
    (h : u32leOf4 a0 a1 a2 a3 = u32leOf4 b0 b1 b2 b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  unfold u32leOf4 at h
  have ha0 := a0.toNat_lt; have ha1 := a1.toNat_lt; have ha2 := a2.toNat_lt; have ha3 := a3.toNat_lt
  have hb0 := b0.toNat_lt; have hb1 := b1.toNat_lt; have hb2 := b2.toNat_lt; have hb3 := b3.toNat_lt
  have e0 : a0.toNat = b0.toNat := by omega
  have e1 : a1.toNat = b1.toNat := by omega
  have e2 : a2.toNat = b2.toNat := by omega
  have e3 : a3.toNat = b3.toNat := by omega
  exact ⟨UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq e0),
    UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq e1),
    UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq e2),
    UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq e3)⟩

/-- Pack a 32-byte digest into 8 little-endian `u32` words, matching `Blake3::pack_digest`
and `MultiStark.BN.PackedTerminal.digestWords`. -/
def packBytes32ToU32Words (bs : List UInt8) : List Nat :=
  (List.range 8).map fun i =>
    u32leOf4 (bs.getD (4 * i) 0) (bs.getD (4 * i + 1) 0)
      (bs.getD (4 * i + 2) 0) (bs.getD (4 * i + 3) 0)

theorem packBytes32ToU32Words_length (bs : List UInt8) :
    (packBytes32ToU32Words bs).length = 8 := by
  simp [packBytes32ToU32Words]

theorem packBytes32ToU32Words_lt (bs : List UInt8) :
    ∀ w ∈ packBytes32ToU32Words bs, w < 2 ^ 32 := by
  intro w hw
  unfold packBytes32ToU32Words at hw
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
  exact u32leOf4_lt _ _ _ _

/-- Strict injectivity of `packBytes32ToU32Words` on 32-byte digests. -/
theorem packBytes32ToU32Words_injective {a b : List UInt8}
    (ha : a.length = 32) (hb : b.length = 32)
    (heq : packBytes32ToU32Words a = packBytes32ToU32Words b) :
    a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro k hk1 hk2
  have hk32 : k < 32 := ha ▸ hk1
  have hi : k / 4 < 8 := by omega
  have hword :
      u32leOf4 (a.getD (4 * (k / 4)) 0) (a.getD (4 * (k / 4) + 1) 0)
        (a.getD (4 * (k / 4) + 2) 0) (a.getD (4 * (k / 4) + 3) 0) =
      u32leOf4 (b.getD (4 * (k / 4)) 0) (b.getD (4 * (k / 4) + 1) 0)
        (b.getD (4 * (k / 4) + 2) 0) (b.getD (4 * (k / 4) + 3) 0) := by
    have hidx := congrArg (fun l => l[k / 4]?) heq
    unfold packBytes32ToU32Words at hidx
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at hidx
    exact hidx
  obtain ⟨h0, h1, h2, h3⟩ := u32leOf4_injective hword
  have hget : ∀ j (hj : j < 32), a.getD j 0 = b.getD j 0 → a[j]'(ha ▸ hj) = b[j]'(hb ▸ hj) := by
    intro j hj hdj
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (ha ▸ hj),
      List.getElem?_eq_getElem (hb ▸ hj)] using hdj
  have hmod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with hm | hm | hm | hm
  · have hdj : a.getD k 0 = b.getD k 0 := by rw [show k = 4 * (k / 4) by omega]; exact h0
    exact hget k hk32 hdj
  · have hdj : a.getD k 0 = b.getD k 0 := by rw [show k = 4 * (k / 4) + 1 by omega]; exact h1
    exact hget k hk32 hdj
  · have hdj : a.getD k 0 = b.getD k 0 := by rw [show k = 4 * (k / 4) + 2 by omega]; exact h2
    exact hget k hk32 hdj
  · have hdj : a.getD k 0 = b.getD k 0 := by rw [show k = 4 * (k / 4) + 3 by omega]; exact h3
    exact hget k hk32 hdj

/-- Pack four little-endian `u32` words into one 128-bit limb (`< 2^128`), matching
`statement_arguments` in `final_program.rs`. -/
def pack4U32ToU128 (w0 w1 w2 w3 : Nat) : Nat :=
  w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3

/-- Unpack one 128-bit limb into four little-endian `u32` words, matching
`CompressFinalNarrow::statement` (`MultiStark/MultiStark/CompressFinalNarrow.lean`). -/
def unpackU128To4U32 (x : Nat) : List Nat :=
  [ x % 2 ^ 32
  , (x / 2 ^ 32) % 2 ^ 32
  , (x / 2 ^ 64) % 2 ^ 32
  , (x / 2 ^ 96) % 2 ^ 32 ]

theorem pack4U32ToU128_lt {w0 w1 w2 w3 : Nat}
    (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32) (h3 : w3 < 2 ^ 32) :
    pack4U32ToU128 w0 w1 w2 w3 < 2 ^ 128 := by
  unfold pack4U32ToU128
  omega

theorem unpack_pack4U32 {w0 w1 w2 w3 : Nat}
    (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32) (h3 : w3 < 2 ^ 32) :
    unpackU128To4U32 (pack4U32ToU128 w0 w1 w2 w3) = [w0, w1, w2, w3] := by
  unfold unpackU128To4U32 pack4U32ToU128
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Pack an 8-word `u32` statement digest into the two 128-bit public limbs `(low, high)`
passed to `CompressFinalNarrow::verify_accumulator_v1(statement_low, statement_high)`. -/
def packU32WordsToLimbs (ws : List Nat) : Nat × Nat :=
  ( pack4U32ToU128 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0)
  , pack4U32ToU128 (ws.getD 4 0) (ws.getD 5 0) (ws.getD 6 0) (ws.getD 7 0) )

/-- Unpack two 128-bit terminal statement limbs back to the 8-word `u32` digest. -/
def unpackLimbsToU32Words (low high : Nat) : List Nat :=
  unpackU128To4U32 low ++ unpackU128To4U32 high

theorem packU32WordsToLimbs_lt {ws : List Nat} (hlen : ws.length = 8)
    (hu32 : ∀ w ∈ ws, w < 2 ^ 32) :
    (packU32WordsToLimbs ws).1 < 2 ^ 128 ∧ (packU32WordsToLimbs ws).2 < 2 ^ 128 := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hlen
  simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_implies] at hu32
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := hu32
  exact ⟨pack4U32ToU128_lt h0 h1 h2 h3, pack4U32ToU128_lt h4 h5 h6 h7⟩

/-- Exact round-trip: `CompressFinalNarrow::statement` recovers the exact 8 `u32` words
from the two 128-bit terminal limbs. -/
theorem unpack_pack_u32Words_roundtrip {ws : List Nat} (hlen : ws.length = 8)
    (hu32 : ∀ w ∈ ws, w < 2 ^ 32) :
    unpackLimbsToU32Words (packU32WordsToLimbs ws).1 (packU32WordsToLimbs ws).2 = ws := by
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at hlen
  simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_implies] at hu32
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := hu32
  unfold unpackLimbsToU32Words packU32WordsToLimbs
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  rw [unpack_pack4U32 h0 h1 h2 h3, unpack_pack4U32 h4 h5 h6 h7]
  rfl

theorem packU32WordsToLimbs_injective {ws₁ ws₂ : List Nat}
    (hl₁ : ws₁.length = 8) (hu₁ : ∀ w ∈ ws₁, w < 2 ^ 32)
    (hl₂ : ws₂.length = 8) (hu₂ : ∀ w ∈ ws₂, w < 2 ^ 32)
    (heq : packU32WordsToLimbs ws₁ = packU32WordsToLimbs ws₂) :
    ws₁ = ws₂ := by
  have h1 := unpack_pack_u32Words_roundtrip hl₁ hu₁
  have h2 := unpack_pack_u32Words_roundtrip hl₂ hu₂
  rw [← h1, ← h2, heq]

/-- `2 ^ 128 < bn254FrModulus` and `2 ^ 128 < bls12381FrModulus`. -/
theorem two_pow_128_lt_both_fr :
    2 ^ 128 < bn254FrModulus ∧ 2 ^ 128 < bls12381FrModulus := by
  refine ⟨by decide, by decide⟩

/-- Lossless embedding of 128-bit terminal statement limbs into `BN254Fr` (zero wrap-around). -/
theorem limbs_embed_bn254_injective {a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ 128) (hb₁ : b₁ < 2 ^ 128) (ha₂ : a₂ < 2 ^ 128) (hb₂ : b₂ < 2 ^ 128)
    (heqA : (a₁ : BN254Fr) = (a₂ : BN254Fr)) (heqB : (b₁ : BN254Fr) = (b₂ : BN254Fr)) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hmod := two_pow_128_lt_both_fr.1
  have hA := congrArg ZMod.val heqA
  have hB := congrArg ZMod.val heqB
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.lt_trans ha₁ hmod), Nat.mod_eq_of_lt (Nat.lt_trans ha₂ hmod)] at hA
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.lt_trans hb₁ hmod), Nat.mod_eq_of_lt (Nat.lt_trans hb₂ hmod)] at hB
  exact ⟨hA, hB⟩

/-- Lossless embedding of 128-bit terminal statement limbs into `BLS12381Fr` (zero wrap-around). -/
theorem limbs_embed_bls12381_injective {a₁ b₁ a₂ b₂ : Nat}
    (ha₁ : a₁ < 2 ^ 128) (hb₁ : b₁ < 2 ^ 128) (ha₂ : a₂ < 2 ^ 128) (hb₂ : b₂ < 2 ^ 128)
    (heqA : (a₁ : BLS12381Fr) = (a₂ : BLS12381Fr)) (heqB : (b₁ : BLS12381Fr) = (b₂ : BLS12381Fr)) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hmod := two_pow_128_lt_both_fr.2
  have hA := congrArg ZMod.val heqA
  have hB := congrArg ZMod.val heqB
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.lt_trans ha₁ hmod), Nat.mod_eq_of_lt (Nat.lt_trans ha₂ hmod)] at hA
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Nat.lt_trans hb₁ hmod), Nat.mod_eq_of_lt (Nat.lt_trans hb₂ hmod)] at hB
  exact ⟨hA, hB⟩

/-- Emulated Goldilocks multiplication and reduction equations cannot wrap in `BN254Fr`
(directly reusing `Aiur.Library.Field.Goldilocks.Emulated.{product_bound, reduction_bound}`). -/
theorem goldilocks_emulation_no_wrap_bn254 :
    (goldilocksP - 1) ^ 2 < bn254FrModulus ∧
    (2 ^ 64 - 1) * goldilocksP + (goldilocksP - 1) < bn254FrModulus :=
  ⟨Aiur.Library.Field.Goldilocks.Emulated.product_bound,
   Aiur.Library.Field.Goldilocks.Emulated.reduction_bound⟩

/-- Emulated Goldilocks multiplication and reduction equations also cannot wrap in `BLS12381Fr`
(for the BLS12-381 `CompressGL` port). -/
theorem goldilocks_emulation_no_wrap_bls12381 :
    (goldilocksP - 1) ^ 2 < bls12381FrModulus ∧
    (2 ^ 64 - 1) * goldilocksP + (goldilocksP - 1) < bls12381FrModulus := by
  refine ⟨by decide, by decide⟩

/-! ## 3. Canonical `PackedPolicy` (`IXAUKG01`) Codec & Key-Pin Binding -/

/-- Exact 8-byte magic header `"IXAUKG01"` matching `KzgPackedDeserialize::chain_policy`
and `PACKED_CHAIN_POLICY_MAGIC`. -/
def packedPolicyMagic : List UInt8 :=
  [73, 88, 65, 85, 75, 71, 48, 49]

/-- Canonical two-key packed compression policy (`IXAUKG01`):
binds the 128-byte pairing anchors, the authorized `CompressGL` key digest & entry ID,
and the authorized narrow stage key digest & entry ID. -/
structure PackedPolicy where
  anchors : List UInt8
  glKeyDigest : List UInt8
  glEntry : Nat
  narrowKeyDigest : List UInt8
  narrowEntry : Nat
  deriving DecidableEq, Repr

/-- Well-formedness of a `PackedPolicy`: exact byte lengths and `u32` entry bounds. -/
def PackedPolicy.WellFormed (p : PackedPolicy) : Prop :=
  p.anchors.length = 128 ∧
  p.glKeyDigest.length = 32 ∧
  p.glEntry < 2 ^ 32 ∧
  p.narrowKeyDigest.length = 32 ∧
  p.narrowEntry < 2 ^ 32

/-- Exact 208-byte wire encoding of `PackedPolicy` (`8 + 128 + 32 + 4 + 32 + 4 = 208`),
matching `PackedPolicy::chain` and `KzgPackedDeserialize::chain_policy`. -/
def PackedPolicy.encode (p : PackedPolicy) : List UInt8 :=
  packedPolicyMagic ++
  p.anchors ++
  p.glKeyDigest ++
  encodeU32LE p.glEntry ++
  p.narrowKeyDigest ++
  encodeU32LE p.narrowEntry

/-- Canonical 32-byte BLAKE3 digest of `p.encode`. -/
def PackedPolicy.digest (p : PackedPolicy) : Vector UInt8 32 :=
  Blake3.Pure.digest p.encode

private theorem encodeU32LE_length (n : Nat) : (encodeU32LE n).length = 4 := rfl

private theorem encodeU32LE_injective {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (heq : encodeU32LE a = encodeU32LE b) : a = b := by
  unfold encodeU32LE at heq
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨h0, h1, h2, h3⟩ := heq
  have c0 := congrArg UInt8.toNat h0
  have c1 := congrArg UInt8.toNat h1
  have c2 := congrArg UInt8.toNat h2
  have c3 := congrArg UInt8.toNat h3
  simp only [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat, Nat.reducePow] at c0 c1 c2 c3
  omega

theorem PackedPolicy.encode_length {p : PackedPolicy} (hp : p.WellFormed) :
    p.encode.length = 208 := by
  obtain ⟨ha, hgl, _, hnr, _⟩ := hp
  simp [PackedPolicy.encode, packedPolicyMagic, encodeU32LE, ha, hgl, hnr]

/-- Exact injectivity of the 208-byte `IXAUKG01` `PackedPolicy` wire format. -/
theorem PackedPolicy.encode_injective {p₁ p₂ : PackedPolicy}
    (hp₁ : p₁.WellFormed) (hp₂ : p₂.WellFormed) (heq : p₁.encode = p₂.encode) :
    p₁ = p₂ := by
  obtain ⟨ha₁, hgl₁, hgle₁, hnr₁, hnre₁⟩ := hp₁
  obtain ⟨ha₂, hgl₂, hgle₂, hnr₂, hnre₂⟩ := hp₂
  unfold PackedPolicy.encode at heq
  simp only [List.append_assoc] at heq
  have h1 := List.append_cancel_left heq
  have ⟨hanc, h2⟩ := List.append_inj h1 (ha₁.trans ha₂.symm)
  have ⟨hgl, h3⟩ := List.append_inj h2 (hgl₁.trans hgl₂.symm)
  have ⟨hgle_enc, h4⟩ := List.append_inj h3 (by simp [encodeU32LE_length])
  have ⟨hnr, hnre_enc⟩ := List.append_inj h4 (hnr₁.trans hnr₂.symm)
  have hgle := encodeU32LE_injective hgle₁ hgle₂ hgle_enc
  have hnre := encodeU32LE_injective hnre₁ hnre₂ hnre_enc
  cases p₁; cases p₂
  simp only at hanc hgl hgle hnr hnre
  subst hanc; subst hgl; subst hgle; subst hnr; subst hnre
  rfl

/-- Equal `PackedPolicy` digests either prove identical `(anchors, glKeyDigest, glEntry,
narrowKeyDigest, narrowEntry)` or exhibit a concrete 208-byte BLAKE3 collision. -/
theorem packedPolicy_digest_binds_or_collision {p₁ p₂ : PackedPolicy}
    (hp₁ : p₁.WellFormed) (hp₂ : p₂.WellFormed) (hdig : p₁.digest = p₂.digest) :
    Blake3Collision p₁.encode p₂.encode ∨ p₁ = p₂ := by
  by_cases henc : p₁.encode = p₂.encode
  · exact Or.inr (PackedPolicy.encode_injective hp₁ hp₂ henc)
  · exact Or.inl ⟨henc, hdig⟩

/-! ## 4. Stage Manifest (`ix-aiur-stages-v1`) Pinning & Chain Key Integrity -/

/-- Exact manifest format string enforced by `stages.rs:56,116`. -/
def stagesManifestFormat : String := "ix-aiur-stages-v1"

/-- A pinned setup product in an `ix-aiur-stages-v1` manifest (`stages.rs:162-203`). -/
structure ProductPin where
  bytes : List UInt8
  blake3Pin : Option (Vector UInt8 32)
  sha256Pin : Option (List UInt8)
  deriving DecidableEq

/-- `stages.rs:198` requires every setup product to carry at least one cryptographic digest pin. -/
def ProductPin.HasDigestPin (p : ProductPin) : Prop :=
  p.blake3Pin.isSome ∨ p.sha256Pin.isSome

/-- A product is validly pinned when it declares at least one digest AND its bytes match every
declared BLAKE3 and/or SHA-256 digest (`Product::check` in `stages.rs:176-202`). -/
def ProductPin.Pinned (sha256 : List UInt8 → List UInt8) (p : ProductPin) : Prop :=
  p.HasDigestPin ∧
  (∀ h, p.blake3Pin = some h → Blake3.Pure.digest p.bytes = h) ∧
  (∀ h, p.sha256Pin = some h → sha256 p.bytes = h)

/-- Full manifest state for an L3 / BLS12-381 Lean-compiled Aiur compression pipeline. -/
structure StageManifest where
  format : String
  manifestBytes : List UInt8
  manifestCallerPin : Vector UInt8 32
  rootKeyPin : Vector UInt8 32
  wrapPkg : ProductPin
  wrapLayout : ProductPin
  wrapKeyDigest : Vector UInt8 32
  wrapLayoutKeyPin : Vector UInt8 32
  glPkg : ProductPin
  glKey : ProductPin
  narrowPkg : ProductPin
  narrowPolicyFile : ProductPin
  narrowKey : ProductPin
  terminalPkg : ProductPin
  terminalScs : ProductPin
  preparedManifest : ProductPin
  outerVk : ProductPin
  policy : PackedPolicy
  glKeyAnchors : List UInt8
  narrowKeyAnchors : List UInt8
  finalPolicyDigestWords : List Nat
  finalAnchors : List UInt8
  outerPairingAnchors : List UInt8

/-- Full manifest & cross-stage key/policy/anchor pinning invariant (`ManifestPinned`). -/
structure ManifestPinned (sha256 : List UInt8 → List UInt8) (m : StageManifest) : Prop where
  format_ok : m.format = stagesManifestFormat
  caller_pin_ok : Blake3.Pure.digest m.manifestBytes = m.manifestCallerPin
  wrapPkg_ok : m.wrapPkg.Pinned sha256
  wrapLayout_ok : m.wrapLayout.Pinned sha256
  wrapKey_matches_layout : m.wrapKeyDigest = m.wrapLayoutKeyPin
  glPkg_ok : m.glPkg.Pinned sha256
  glKey_ok : m.glKey.Pinned sha256
  narrowPkg_ok : m.narrowPkg.Pinned sha256
  narrowPolicy_ok : m.narrowPolicyFile.Pinned sha256
  narrowKey_ok : m.narrowKey.Pinned sha256
  terminalPkg_ok : m.terminalPkg.Pinned sha256
  terminalScs_ok : m.terminalScs.Pinned sha256
  preparedManifest_ok : m.preparedManifest.Pinned sha256
  outerVk_ok : m.outerVk.Pinned sha256
  policy_wf : m.policy.WellFormed
  policy_file_matches : m.narrowPolicyFile.bytes = m.policy.encode
  policy_binds_glKey : m.policy.glKeyDigest = (Blake3.Pure.digest m.glKey.bytes).toList
  policy_binds_narrowKey : m.policy.narrowKeyDigest = (Blake3.Pure.digest m.narrowKey.bytes).toList
  final_binds_policy : m.finalPolicyDigestWords = packBytes32ToU32Words m.policy.digest.toList
  gl_anchors_match : m.glKeyAnchors = m.policy.anchors
  narrow_anchors_match : m.narrowKeyAnchors = m.policy.anchors
  final_anchors_match : m.finalAnchors = m.policy.anchors
  outer_anchors_match : m.outerPairingAnchors = m.policy.anchors

/-- Transitive anchor & key-pin integrity derived from `ManifestPinned`. -/
theorem manifestPinned_chain_integrity {sha256 : List UInt8 → List UInt8} {m : StageManifest}
    (hm : ManifestPinned sha256 m) :
    m.glKeyAnchors = m.outerPairingAnchors ∧
    m.narrowKeyAnchors = m.outerPairingAnchors ∧
    m.finalAnchors = m.outerPairingAnchors ∧
    m.policy.glKeyDigest = (Blake3.Pure.digest m.glKey.bytes).toList ∧
    m.policy.narrowKeyDigest = (Blake3.Pure.digest m.narrowKey.bytes).toList ∧
    m.finalPolicyDigestWords = packBytes32ToU32Words m.policy.digest.toList :=
  ⟨hm.gl_anchors_match.trans hm.outer_anchors_match.symm,
   hm.narrow_anchors_match.trans hm.outer_anchors_match.symm,
   hm.final_anchors_match.trans hm.outer_anchors_match.symm,
   hm.policy_binds_glKey, hm.policy_binds_narrowKey, hm.final_binds_policy⟩

/-! ## 5. End-to-End Stage Statement-Digest Propagation Chain -/

/-- Exact statement propagation record tying the root `ix_aggr` `(rootKeyBytes, rootClaimsBytes)`
through `CompressWrap → CompressGL → CompressNarrowFixed → CompressFinalNarrow` to the two
128-bit terminal public limbs `(terminalLow, terminalHigh)`. -/
structure AiurStageStatementChain (rootKeyPin : Vector UInt8 32) where
  rootKeyBytes : List UInt8
  rootClaimsBytes : List UInt8
  rootKey_pinned : Blake3.Pure.digest rootKeyBytes = rootKeyPin
  wrapStatementWords : List Nat
  wrap_eq : wrapStatementWords = packBytes32ToU32Words
    (compressWrapStatementDigest (Blake3.Pure.digest rootKeyBytes).toList
      (Blake3.Pure.digest rootClaimsBytes).toList).toList
  glStatementWords : List Nat
  gl_eq : glStatementWords = wrapStatementWords
  narrowStatementWords : List Nat
  narrow_eq : narrowStatementWords = glStatementWords
  terminalLow : Nat
  terminalHigh : Nat
  terminal_eq : (terminalLow, terminalHigh) = packU32WordsToLimbs narrowStatementWords

theorem AiurStageStatementChain.terminal_bounds {pin : Vector UInt8 32}
    (c : AiurStageStatementChain pin) :
    c.terminalLow < 2 ^ 128 ∧ c.terminalHigh < 2 ^ 128 := by
  have hw : c.narrowStatementWords = packBytes32ToU32Words
      (compressWrapStatementDigest (Blake3.Pure.digest c.rootKeyBytes).toList
        (Blake3.Pure.digest c.rootClaimsBytes).toList).toList :=
    c.narrow_eq.trans (c.gl_eq.trans c.wrap_eq)
  have hlen : c.narrowStatementWords.length = 8 := by
    rw [hw]; exact packBytes32ToU32Words_length _
  have hu32 : ∀ w ∈ c.narrowStatementWords, w < 2 ^ 32 := by
    rw [hw]; exact packBytes32ToU32Words_lt _
  have hlt := packU32WordsToLimbs_lt hlen hu32
  rw [← c.terminal_eq] at hlt
  exact hlt

theorem AiurStageStatementChain.unpack_recovers_root_statement {pin : Vector UInt8 32}
    (c : AiurStageStatementChain pin) :
    unpackLimbsToU32Words c.terminalLow c.terminalHigh =
      packBytes32ToU32Words
        (compressWrapStatementDigest pin.toList (Blake3.Pure.digest c.rootClaimsBytes).toList).toList := by
  have hw : c.narrowStatementWords = packBytes32ToU32Words
      (compressWrapStatementDigest pin.toList (Blake3.Pure.digest c.rootClaimsBytes).toList).toList := by
    rw [c.narrow_eq, c.gl_eq, c.wrap_eq, c.rootKey_pinned]
  have hlen : c.narrowStatementWords.length = 8 := by
    rw [hw]; exact packBytes32ToU32Words_length _
  have hu32 : ∀ w ∈ c.narrowStatementWords, w < 2 ^ 32 := by
    rw [hw]; exact packBytes32ToU32Words_lt _
  have hlow : c.terminalLow = (packU32WordsToLimbs c.narrowStatementWords).1 :=
    congrArg Prod.fst c.terminal_eq
  have hhigh : c.terminalHigh = (packU32WordsToLimbs c.narrowStatementWords).2 :=
    congrArg Prod.snd c.terminal_eq
  rw [hlow, hhigh, unpack_pack_u32Words_roundtrip hlen hu32, hw]

/-- **End-to-End Statement Uniqueness (Up to Explicit BLAKE3 Collision):**
If two `AiurStageStatementChain`s (even under potentially different root key pins `pin₁, pin₂`)
produce equal outer terminal limbs `(low, high)` in `Nat` (and hence in `BN254Fr` or `BLS12381Fr`),
then EITHER a concrete BLAKE3 collision occurred (on `ix/compress-wrap/v1\0`, `rootKeyBytes`,
or `rootClaimsBytes`) OR both chains bind the exact same `rootKeyPin`, `rootKeyBytes`, and
`rootClaimsBytes`! -/
theorem statementChain_unique_or_collision {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pin₁) (c₂ : AiurStageStatementChain pin₂)
    (hLow : c₁.terminalLow = c₂.terminalLow) (hHigh : c₁.terminalHigh = c₂.terminalHigh) :
    Blake3Collision
        (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
        (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList) ∨
      Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
      Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes ∨
      (pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have hunpack :
      packBytes32ToU32Words
        (compressWrapStatementDigest pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList).toList =
      packBytes32ToU32Words
        (compressWrapStatementDigest pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList).toList := by
    rw [← c₁.unpack_recovers_root_statement, ← c₂.unpack_recovers_root_statement, hLow, hHigh]
  have hdigList :
      (compressWrapStatementDigest pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList).toList =
      (compressWrapStatementDigest pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList).toList :=
    packBytes32ToU32Words_injective (by simp) (by simp) hunpack
  have hdig :
      compressWrapStatementDigest pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList =
      compressWrapStatementDigest pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList :=
    Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hdigList
      simpa [Vector.getElem?_toList, hi] using this
  rcases compressWrap_statement_binds_root_or_collision (by simp) (by simp) hdig with hcol | ⟨hpinList, hclList⟩
  · exact Or.inl hcol
  · have hpin : pin₁ = pin₂ := Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hpinList
      simpa [Vector.getElem?_toList, hi] using this
    have hclDig : Blake3.Pure.digest c₁.rootClaimsBytes = Blake3.Pure.digest c₂.rootClaimsBytes :=
      Vector.ext fun i hi => by
        have := congrArg (fun l => l[i]?) hclList
        simpa [Vector.getElem?_toList, hi] using this
    have hkDig : Blake3.Pure.digest c₁.rootKeyBytes = Blake3.Pure.digest c₂.rootKeyBytes :=
      c₁.rootKey_pinned.trans (hpin.trans c₂.rootKey_pinned.symm)
    by_cases hk : c₁.rootKeyBytes = c₂.rootKeyBytes
    · by_cases hcl : c₁.rootClaimsBytes = c₂.rootClaimsBytes
      · exact Or.inr (Or.inr (Or.inr ⟨hpin, hk, hcl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hcl, hclDig⟩))
    · exact Or.inr (Or.inl ⟨hk, hkDig⟩)

/-- Same uniqueness lifted directly from `BN254Fr` terminal public inputs. -/
theorem statementChain_unique_bn254_or_collision {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pin₁) (c₂ : AiurStageStatementChain pin₂)
    (hLow : (c₁.terminalLow : BN254Fr) = (c₂.terminalLow : BN254Fr))
    (hHigh : (c₁.terminalHigh : BN254Fr) = (c₂.terminalHigh : BN254Fr)) :
    Blake3Collision
        (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
        (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList) ∨
      Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
      Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes ∨
      (pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have ⟨hl, hh⟩ := limbs_embed_bn254_injective c₁.terminal_bounds.1 c₁.terminal_bounds.2
    c₂.terminal_bounds.1 c₂.terminal_bounds.2 hLow hHigh
  exact statementChain_unique_or_collision c₁ c₂ hl hh

/-- Same uniqueness lifted directly from `BLS12381Fr` terminal public inputs. -/
theorem statementChain_unique_bls12381_or_collision {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pin₁) (c₂ : AiurStageStatementChain pin₂)
    (hLow : (c₁.terminalLow : BLS12381Fr) = (c₂.terminalLow : BLS12381Fr))
    (hHigh : (c₁.terminalHigh : BLS12381Fr) = (c₂.terminalHigh : BLS12381Fr)) :
    Blake3Collision
        (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
        (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList) ∨
      Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
      Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes ∨
      (pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have ⟨hl, hh⟩ := limbs_embed_bls12381_injective c₁.terminal_bounds.1 c₁.terminal_bounds.2
    c₂.terminal_bounds.1 c₂.terminal_bounds.2 hLow hHigh
  exact statementChain_unique_or_collision c₁ c₂ hl hh

/-! ## 6. 128-Bit Aiur Compression Security Profile (`v6` STARK + BLS12-381 Outer Curve) -/

/-- Supported outer pairing curve targets for the Aiur compression pipeline. -/
inductive OuterPairingCurve where
  | bls12381
  | bn254
  deriving DecidableEq, Repr

/-- 128-bit Aiur compression security profile:
1. Root & wrap Multi-STARK stages satisfy `Security128Profile` (`v6`, `Fp^3`, 64-byte RFC 7693
   `BLAKE2b-512`, 128-bit UD or Johnson FRI parameters);
2. Outer pairing curve satisfies `PairingCurve128Ok` (`|Fq| ≥ 2^380`, `|Fr| ≥ 2^254`,
   mandatory `G1` prime-order subgroup check when `h1 > 1`). -/
def AiurCompression128Ok (extDeg protoVer digestBytes : Nat)
    (starkParams : Ix.Cert.MultiStark.StarkParams) (requireUd : Bool)
    (outerCurve : OuterPairingCurve)
    (curveSpec : Ix.Cert.Compression.Security128.PairingCurveSpec) : Prop :=
  Security128Profile extDeg protoVer digestBytes starkParams requireUd ∧
  Ix.Cert.Compression.Security128.PairingCurve128Ok curveSpec ∧
  (match outerCurve with
   | .bls12381 => curveSpec.fqModulus = bls12381FqModulus ∧ curveSpec.frModulus = bls12381FrModulus ∧
       curveSpec.g1Cofactor = bls12381G1Cofactor
   | .bn254 => curveSpec.fqModulus = bn254FqModulus ∧ curveSpec.frModulus = bn254FrModulus)

/-- Positive 128-bit Aiur compression profile: `v6` UD `(2, 160, 0, 20)` + `BLAKE2b-512` + BLS12-381. -/
theorem aiurCompression128_v6_ud_bls12381_ok :
    AiurCompression128Ok 3 6 64 v6Ud160Params true .bls12381
      Ix.Cert.Compression.Security128.bls12381CurveSpec :=
  ⟨Ix.Cert.Compression.Security128.stark128Blake2b512_profile_ok,
   Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok, ⟨rfl, rfl, rfl⟩⟩

/-- Positive 128-bit Aiur compression profile: `v6` Johnson `(2, 128, 0, 20)` + `BLAKE2b-512` + BLS12-381. -/
theorem aiurCompression128_v6_johnson128_bls12381_ok :
    AiurCompression128Ok 3 6 64 v6Johnson128Params false .bls12381
      Ix.Cert.Compression.Security128.bls12381CurveSpec :=
  ⟨v6_positive_128_profiles.2.2,
   Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok, ⟨rfl, rfl, rfl⟩⟩

end Ix.Cert.AiurCompression
