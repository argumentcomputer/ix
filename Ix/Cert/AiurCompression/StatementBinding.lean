import Blake3.Pure
import Aiur.Library.Field.Goldilocks.Emulated
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.OuterRelation
import Ix.Cert.Compression.Bls12381.Field

/-! # Statement-Digest Propagation, `StatementPolicy`, `PackedPolicy` (`IXAUKG01`), and Manifest Binding

Formalizes the exact binary codecs, domain separators, single- and two-layer statement-digest
propagation (`StatementPolicy`), `PackedPolicy` (`IXAUKG01`) key/anchor pinning, and
`ix-aiur-stages-v1` manifest binding for the Lean-compiled L3 BN254 Aiur compression pipeline:

- **Deployed two-layer `--aiur-stages` policy (`StatementPolicy.twoLayerWrap wp`):**
  1. `ix_aggr` root `(rootKeyBytes, rootClaimsBytes)` →
     `S_root = H("ix/compress-wrap/v1\0" ‖ H(rootKey) ‖ H(rootClaims))` (`CompressWrap`);
  2. `WrapPolicy::claims_for` / `WrapPolicy::statement_for` (`compress_gl.rs:550-568`) and
     `IxL3PlonkVerifier.sol` / `l3_verifier.rs` →
     `S_gl = H("ix/compress-wrap/v1\0" ‖ wp.wrapKeyDigest ‖ H(claims_bytes([[prefix0, prefix1, 0×8, S_root]])))`
     (`CompressGL`);
  3. `CompressNarrowFixed::step_v1(policyDigest, 1, S_gl)` →
     `CompressFinalNarrow::verify_accumulator_v1(stmtLow, stmtHigh)` →
     outer `ix-aiur-scs-v1` native Rust PLONK (`aiur_backend::plonk::native` /
     `IxL3PlonkVerifier.sol`) public inputs `(stmtLow, stmtHigh)`.
- **Single-layer direct fixed-wrapper policy (`StatementPolicy.singleLayerDirect`):**
  `CompressGLFixed` / direct wrapper publishes `S_gl = S_root` directly to
  `CompressNarrowFixed` → `CompressFinalNarrow` → outer PLONK.

Also retains standalone BLS12-381 arithmetic/embedding lemmas (`limbs_embed_bls12381_injective`,
`goldilocks_emulation_no_wrap_bls12381`, `statementChain_unique_bls12381_or_collision`).

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field

/-! ## 1. Domain Separators, Collision Predicates & `"ix/compress-wrap/v1\0"` Preimage Binding -/

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

/-- Explicit SHA-256 collision predicate on two distinct byte lists under a hash function `sha256`. -/
def Sha256Collision (sha256 : List UInt8 → List UInt8) (a b : List UInt8) : Prop :=
  a ≠ b ∧ sha256 a = sha256 b

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

/-! ## 2. Little-Endian `u32`/`u64` Packing, 2×`u128` Terminal Limbs & Zero-Wrap Embeddings -/

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

/-- Little-endian 8-byte encoding of a `u64` natural number (`u64::to_le_bytes`), matching
`stark_verifier::claims_bytes` (`crates/stark-verifier/src/lib.rs:133-143`). -/
def encodeU64LE (n : Nat) : List UInt8 :=
  encodeU32LE (n % 2 ^ 32) ++ encodeU32LE (n / 2 ^ 32)

theorem encodeU64LE_length (n : Nat) : (encodeU64LE n).length = 8 := rfl

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

theorem encodeU64LE_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (heq : encodeU64LE a = encodeU64LE b) : a = b := by
  unfold encodeU64LE at heq
  have ⟨hlo, hhi⟩ := List.append_inj heq (by simp [encodeU32LE_length])
  have elo := encodeU32LE_injective (Nat.mod_lt a (by decide)) (Nat.mod_lt b (by decide)) hlo
  have ehi := encodeU32LE_injective (by omega) (by omega) hhi
  omega

/-- Canonical `stark_verifier::claims_bytes(&[claim])` wire encoding of a single Goldilocks
claim row (`crates/stark-verifier/src/lib.rs:133-143`):
`1u64.to_le_bytes() ‖ (claim.len() as u64).to_le_bytes() ‖ flatMap u64::to_le_bytes claim`. -/
def encodeSingleClaimBytes (row : List Nat) : List UInt8 :=
  encodeU64LE 1 ++ encodeU64LE row.length ++ row.flatMap encodeU64LE

private theorem flatMap_encodeU64LE_injective :
    ∀ {xs ys : List Nat},
      xs.length = ys.length →
      (∀ x ∈ xs, x < 2 ^ 64) →
      (∀ y ∈ ys, y < 2 ^ 64) →
      xs.flatMap encodeU64LE = ys.flatMap encodeU64LE →
      xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hlen, hxs, hys, heq => by
      simp only [List.flatMap_cons] at heq
      have ⟨hhd, htl⟩ := List.append_inj heq (by simp [encodeU64LE_length])
      have hxy := encodeU64LE_injective
        (hxs x List.mem_cons_self) (hys y List.mem_cons_self) hhd
      have hrest := flatMap_encodeU64LE_injective
        (by simpa using hlen)
        (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
        (fun b hb => hys b (List.mem_cons_of_mem _ hb)) htl
      rw [hxy, hrest]
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen

/-- Strict injectivity of `encodeSingleClaimBytes` on rows whose length and words fit in `u64`. -/
theorem encodeSingleClaimBytes_injective {r₁ r₂ : List Nat}
    (hl₁ : r₁.length < 2 ^ 64) (hl₂ : r₂.length < 2 ^ 64)
    (hw₁ : ∀ x ∈ r₁, x < 2 ^ 64) (hw₂ : ∀ x ∈ r₂, x < 2 ^ 64)
    (heq : encodeSingleClaimBytes r₁ = encodeSingleClaimBytes r₂) :
    r₁ = r₂ := by
  unfold encodeSingleClaimBytes at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have h1 := List.append_cancel_left heq
  have ⟨hlenBytes, hbody⟩ := List.append_inj h1 (by simp [encodeU64LE_length])
  have hlen : r₁.length = r₂.length := encodeU64LE_injective hl₁ hl₂ hlenBytes
  exact flatMap_encodeU64LE_injective hlen hw₁ hw₂ hbody

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

/-- Emulated Goldilocks multiplication and reduction equations cannot wrap in `BLS12381Fr`
(standalone arithmetic lemma). -/
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

/-- Full manifest state for an L3 BN254 Lean-compiled Aiur compression pipeline. -/
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

/-! ## 5. Deployed `WrapPolicy` & Parameterized `StatementPolicy` Propagation Chain -/

theorem encodeSingleClaimBytes_length (row : List Nat) :
    (encodeSingleClaimBytes row).length = 16 + 8 * row.length := by
  unfold encodeSingleClaimBytes
  have hfm : ∀ xs : List Nat, (xs.flatMap encodeU64LE).length = 8 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, encodeU64LE_length, ih, List.length_cons]
      omega
  simp only [List.length_append, encodeU64LE_length, hfm]

/-- Exact encoding of `root_claims_bytes` from a 10-word root statement prefix and arbitrary
`claimBytes` (`u64le(1) || u64le(18) || rootPrefix[0..10] || pack_u32_le(BLAKE3(claimBytes))[0..8]`,
160 bytes = 20 LE u64s), matching `crates/proof-compression/src/aiur_backend/l3_verifier.rs` and
`contracts/plonk/src/IxL3PlonkVerifier.sol`. -/
def rootClaimsBytesOfClaim (rootPrefix : List Nat) (claimBytes : List UInt8) : List UInt8 :=
  encodeSingleClaimBytes (rootPrefix ++ packBytes32ToU32Words (Blake3.Pure.digest claimBytes).toList)

theorem rootClaimsBytesOfClaim_length {rootPrefix : List Nat} (hp : rootPrefix.length = 10)
    (claimBytes : List UInt8) :
    (rootClaimsBytesOfClaim rootPrefix claimBytes).length = 160 := by
  simp [rootClaimsBytesOfClaim, encodeSingleClaimBytes_length, hp, packBytes32ToU32Words_length]

/-- Equal `rootClaimsBytesOfClaim` under canonical 10-word Goldilocks prefixes imply identical
prefixes and identical `claimBytes` up to a concrete BLAKE3 collision. -/
theorem rootClaimsBytesOfClaim_binds_or_collision {p₁ p₂ : List Nat} {c₁ c₂ : List UInt8}
    (hl₁ : p₁.length = 10) (hl₂ : p₂.length = 10)
    (hu₁ : ∀ w ∈ p₁, w < goldilocksP) (hu₂ : ∀ w ∈ p₂, w < goldilocksP)
    (heq : rootClaimsBytesOfClaim p₁ c₁ = rootClaimsBytesOfClaim p₂ c₂) :
    Blake3Collision c₁ c₂ ∨ (p₁ = p₂ ∧ c₁ = c₂) := by
  have hgp : goldilocksP < 2 ^ 64 := by decide
  have h232 : 2 ^ 32 < 2 ^ 64 := by decide
  have hlen1 : (p₁ ++ packBytes32ToU32Words (Blake3.Pure.digest c₁).toList).length < 2 ^ 64 := by
    simp [hl₁, packBytes32ToU32Words_length]
  have hlen2 : (p₂ ++ packBytes32ToU32Words (Blake3.Pure.digest c₂).toList).length < 2 ^ 64 := by
    simp [hl₂, packBytes32ToU32Words_length]
  have hw1 : ∀ x ∈ p₁ ++ packBytes32ToU32Words (Blake3.Pure.digest c₁).toList, x < 2 ^ 64 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Nat.lt_trans (hu₁ x h) hgp
    · exact Nat.lt_trans (packBytes32ToU32Words_lt _ x h) h232
  have hw2 : ∀ x ∈ p₂ ++ packBytes32ToU32Words (Blake3.Pure.digest c₂).toList, x < 2 ^ 64 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact Nat.lt_trans (hu₂ x h) hgp
    · exact Nat.lt_trans (packBytes32ToU32Words_lt _ x h) h232
  have hrow := encodeSingleClaimBytes_injective hlen1 hlen2 hw1 hw2 heq
  obtain ⟨hpEq, hwEq⟩ := List.append_inj hrow (hl₁.trans hl₂.symm)
  have hdigList := packBytes32ToU32Words_injective (by simp) (by simp) hwEq
  have hdig : Blake3.Pure.digest c₁ = Blake3.Pure.digest c₂ :=
    Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hdigList
      simpa [Vector.getElem?_toList, hi] using this
  by_cases hc : c₁ = c₂
  · exact Or.inr ⟨hpEq, hc⟩
  · exact Or.inl ⟨hc, hdig⟩

/-- Exact Lean specification of `compress_gl::WrapPolicy` (`compress_gl.rs:518-568`):
pins the `CompressWrap` verifying key digest `wrapKeyDigest` and the two-word Goldilocks
claim prefix `[claimPrefix0, claimPrefix1]` (`[call_tag, callable_id]`). -/
structure WrapPolicySpec where
  wrapKeyDigest : Vector UInt8 32
  claimPrefix0 : Nat
  claimPrefix1 : Nat
  prefix0_lt : claimPrefix0 < goldilocksP
  prefix1_lt : claimPrefix1 < goldilocksP
  deriving DecidableEq

/-- Exact `WrapPolicy::claims_for` (`compress_gl.rs:550-558`):
encodes the single 18-word Goldilocks wrapper claim `[prefix0, prefix1, 0×8, rootStmtWords]`
using `stark_verifier::claims_bytes` (160 bytes = 20 LE u64s). -/
def WrapPolicySpec.claimsBytes (wp : WrapPolicySpec) (rootStmtWords : List Nat) : List UInt8 :=
  encodeSingleClaimBytes ([wp.claimPrefix0, wp.claimPrefix1] ++ List.replicate 8 0 ++ rootStmtWords)

theorem WrapPolicySpec.claimsBytes_length (wp : WrapPolicySpec) {rootStmtWords : List Nat}
    (hr : rootStmtWords.length = 8) :
    (wp.claimsBytes rootStmtWords).length = 160 := by
  simp [WrapPolicySpec.claimsBytes, encodeSingleClaimBytes_length, hr]

/-- Exact `WrapPolicy::statement_for` (`compress_gl.rs:561-568`):
computes the 32-byte `CompressGL` statement digest
`H("ix/compress-wrap/v1\0" ‖ wp.wrapKeyDigest ‖ H(wp.claimsBytes rootStmtWords))`. -/
def WrapPolicySpec.glStatementDigest (wp : WrapPolicySpec) (rootStmtWords : List Nat) :
    Vector UInt8 32 :=
  compressWrapStatementDigest wp.wrapKeyDigest.toList
    (Blake3.Pure.digest (wp.claimsBytes rootStmtWords)).toList

/-- Packed 8-word `u32` representation of `wp.glStatementDigest rootStmtWords`. -/
def WrapPolicySpec.glStatementWords (wp : WrapPolicySpec) (rootStmtWords : List Nat) : List Nat :=
  packBytes32ToU32Words (wp.glStatementDigest rootStmtWords).toList

theorem WrapPolicySpec.claimsBytes_injective {wp₁ wp₂ : WrapPolicySpec}
    {r₁ r₂ : List Nat} (hr₁ : r₁.length = 8) (hr₂ : r₂.length = 8)
    (hu₁ : ∀ w ∈ r₁, w < 2 ^ 32) (hu₂ : ∀ w ∈ r₂, w < 2 ^ 32)
    (hKey : wp₁.wrapKeyDigest = wp₂.wrapKeyDigest)
    (heq : wp₁.claimsBytes r₁ = wp₂.claimsBytes r₂) :
    wp₁ = wp₂ ∧ r₁ = r₂ := by
  have hgp : goldilocksP < 2 ^ 64 := by decide
  have h232 : 2 ^ 32 < 2 ^ 64 := by decide
  have hlen1 : ([wp₁.claimPrefix0, wp₁.claimPrefix1] ++ List.replicate 8 0 ++ r₁).length < 2 ^ 64 := by
    simp [hr₁]
  have hlen2 : ([wp₂.claimPrefix0, wp₂.claimPrefix1] ++ List.replicate 8 0 ++ r₂).length < 2 ^ 64 := by
    simp [hr₂]
  have hw1 : ∀ x ∈ ([wp₁.claimPrefix0, wp₁.claimPrefix1] ++ List.replicate 8 0 ++ r₁), x < 2 ^ 64 := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at hx
    rcases hx with ((rfl | rfl) | ⟨_, rfl⟩) | hmem
    · exact Nat.lt_trans wp₁.prefix0_lt hgp
    · exact Nat.lt_trans wp₁.prefix1_lt hgp
    · omega
    · exact Nat.lt_trans (hu₁ x hmem) h232
  have hw2 : ∀ x ∈ ([wp₂.claimPrefix0, wp₂.claimPrefix1] ++ List.replicate 8 0 ++ r₂), x < 2 ^ 64 := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at hx
    rcases hx with ((rfl | rfl) | ⟨_, rfl⟩) | hmem
    · exact Nat.lt_trans wp₂.prefix0_lt hgp
    · exact Nat.lt_trans wp₂.prefix1_lt hgp
    · omega
    · exact Nat.lt_trans (hu₂ x hmem) h232
  have hrow := encodeSingleClaimBytes_injective hlen1 hlen2 hw1 hw2 heq
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrow
  obtain ⟨hp0, hp1, htail⟩ := hrow
  have hr : r₁ = r₂ := List.append_cancel_left htail
  cases wp₁; cases wp₂
  simp only at hKey hp0 hp1
  subst hKey; subst hp0; subst hp1
  exact ⟨rfl, hr⟩

/-- Statement propagation policy connecting the root `(rootKeyPin, rootClaimsBytes)` to the
`CompressGL` / `CompressNarrowFixed` / `CompressFinalNarrow` public statement:
- `twoLayerWrap wp`: deployed `--aiur-stages` chain where `CompressGL` verifies `CompressWrap`
  under `wp : WrapPolicySpec` (`WrapPolicy::statement_for`), producing a two-layer hash;
- `singleLayerDirect`: single-layer fixed-wrapper chain (`CompressGLFixed` verifying the root
  directly), where `CompressGL` publishes the root statement digest directly. -/
inductive StatementPolicy where
  | twoLayerWrap (wp : WrapPolicySpec)
  | singleLayerDirect
  deriving DecidableEq

/-- Canonical 32-byte root statement digest `H("ix/compress-wrap/v1\0" ‖ rootKeyPin ‖ H(rootClaimsBytes))`. -/
def rootStatementDigest (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    Vector UInt8 32 :=
  compressWrapStatementDigest rootKeyPin.toList (Blake3.Pure.digest rootClaimsBytes).toList

/-- Packed 8-word `u32` root statement digest. -/
def rootStatementWords (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) : List Nat :=
  packBytes32ToU32Words (rootStatementDigest rootKeyPin rootClaimsBytes).toList

theorem rootStatementWords_length (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    (rootStatementWords rootKeyPin rootClaimsBytes).length = 8 :=
  packBytes32ToU32Words_length _

theorem rootStatementWords_lt (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    ∀ w ∈ rootStatementWords rootKeyPin rootClaimsBytes, w < 2 ^ 32 :=
  packBytes32ToU32Words_lt _

/-- Map the 8-word root statement digest to the 8-word `CompressGL` / `CompressNarrowFixed`
statement digest according to `pol : StatementPolicy`. -/
def StatementPolicy.glStatementWords : StatementPolicy → List Nat → List Nat
  | .twoLayerWrap wp, rootWords => wp.glStatementWords rootWords
  | .singleLayerDirect, rootWords => rootWords

/-- The 8-word terminal statement digest published to `CompressGL` / `CompressNarrowFixed` /
`CompressFinalNarrow` for `(pol, rootKeyPin, rootClaimsBytes)`. -/
def StatementPolicy.terminalStatementWords (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) : List Nat :=
  pol.glStatementWords (rootStatementWords rootKeyPin rootClaimsBytes)

theorem StatementPolicy.terminalStatementWords_length (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    (pol.terminalStatementWords rootKeyPin rootClaimsBytes).length = 8 := by
  cases pol <;> simp [StatementPolicy.terminalStatementWords, StatementPolicy.glStatementWords,
    WrapPolicySpec.glStatementWords, rootStatementWords, packBytes32ToU32Words_length]

theorem StatementPolicy.terminalStatementWords_lt (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    ∀ w ∈ pol.terminalStatementWords rootKeyPin rootClaimsBytes, w < 2 ^ 32 := by
  cases pol with
  | twoLayerWrap wp => exact packBytes32ToU32Words_lt _
  | singleLayerDirect => exact packBytes32ToU32Words_lt _

/-- The two 128-bit outer public statement limbs `(stmtLow, stmtHigh)` published to
`CompressFinalNarrow::verify_accumulator_v1` and the `ix-aiur-scs-v1` outer PLONK circuit. -/
def StatementPolicy.terminalLimbs (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) : Nat × Nat :=
  packU32WordsToLimbs (pol.terminalStatementWords rootKeyPin rootClaimsBytes)

theorem StatementPolicy.terminalLimbs_lt (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    (pol.terminalLimbs rootKeyPin rootClaimsBytes).1 < 2 ^ 128 ∧
    (pol.terminalLimbs rootKeyPin rootClaimsBytes).2 < 2 ^ 128 :=
  packU32WordsToLimbs_lt
    (pol.terminalStatementWords_length rootKeyPin rootClaimsBytes)
    (pol.terminalStatementWords_lt rootKeyPin rootClaimsBytes)

theorem StatementPolicy.unpack_terminalLimbs (pol : StatementPolicy)
    (rootKeyPin : Vector UInt8 32) (rootClaimsBytes : List UInt8) :
    unpackLimbsToU32Words
      (pol.terminalLimbs rootKeyPin rootClaimsBytes).1
      (pol.terminalLimbs rootKeyPin rootClaimsBytes).2 =
    pol.terminalStatementWords rootKeyPin rootClaimsBytes :=
  unpack_pack_u32Words_roundtrip
    (pol.terminalStatementWords_length rootKeyPin rootClaimsBytes)
    (pol.terminalStatementWords_lt rootKeyPin rootClaimsBytes)

/-- Exact statement propagation record tying the root `ix_aggr` `(rootKeyBytes, rootClaimsBytes)`
through `CompressWrap` (when `twoLayerWrap`) → `CompressGL` → `CompressNarrowFixed` →
`CompressFinalNarrow` to the two 128-bit terminal public limbs `(terminalLow, terminalHigh)`,
parameterized cleanly over `pol : StatementPolicy`. -/
structure AiurStageStatementChain (pol : StatementPolicy) (rootKeyPin : Vector UInt8 32) where
  rootKeyBytes : List UInt8
  rootClaimsBytes : List UInt8
  rootKey_pinned : Blake3.Pure.digest rootKeyBytes = rootKeyPin
  wrapStatementWords : List Nat
  wrap_eq : wrapStatementWords = packBytes32ToU32Words
    (compressWrapStatementDigest (Blake3.Pure.digest rootKeyBytes).toList
      (Blake3.Pure.digest rootClaimsBytes).toList).toList
  glStatementWords : List Nat
  gl_eq : glStatementWords = pol.glStatementWords wrapStatementWords
  narrowStatementWords : List Nat
  narrow_eq : narrowStatementWords = glStatementWords
  terminalLow : Nat
  terminalHigh : Nat
  terminal_eq : (terminalLow, terminalHigh) = packU32WordsToLimbs narrowStatementWords

theorem AiurStageStatementChain.narrowWords_eq {pol : StatementPolicy} {pin : Vector UInt8 32}
    (c : AiurStageStatementChain pol pin) :
    c.narrowStatementWords = pol.terminalStatementWords pin c.rootClaimsBytes := by
  rw [c.narrow_eq, c.gl_eq, c.wrap_eq, c.rootKey_pinned]
  rfl

theorem AiurStageStatementChain.terminal_bounds {pol : StatementPolicy} {pin : Vector UInt8 32}
    (c : AiurStageStatementChain pol pin) :
    c.terminalLow < 2 ^ 128 ∧ c.terminalHigh < 2 ^ 128 := by
  have hlt := pol.terminalLimbs_lt pin c.rootClaimsBytes
  have hEq : (c.terminalLow, c.terminalHigh) = pol.terminalLimbs pin c.rootClaimsBytes := by
    rw [c.terminal_eq, c.narrowWords_eq]; rfl
  rw [← hEq] at hlt
  exact hlt

theorem AiurStageStatementChain.unpack_recovers_terminal_statement
    {pol : StatementPolicy} {pin : Vector UInt8 32} (c : AiurStageStatementChain pol pin) :
    unpackLimbsToU32Words c.terminalLow c.terminalHigh =
      pol.terminalStatementWords pin c.rootClaimsBytes := by
  have hEq : (c.terminalLow, c.terminalHigh) = pol.terminalLimbs pin c.rootClaimsBytes := by
    rw [c.terminal_eq, c.narrowWords_eq]; rfl
  have hlow : c.terminalLow = (pol.terminalLimbs pin c.rootClaimsBytes).1 := congrArg Prod.fst hEq
  have hhigh : c.terminalHigh = (pol.terminalLimbs pin c.rootClaimsBytes).2 := congrArg Prod.snd hEq
  rw [hlow, hhigh, pol.unpack_terminalLimbs]

/-- Explicit finite disjunction of the exact BLAKE3 collisions that could cause two
`AiurStageStatementChain`s (under policies `pol₁, pol₂`) to share equal terminal limbs. -/
def StatementChainCollision {pol₁ pol₂ : StatementPolicy} {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pol₁ pin₁) (c₂ : AiurStageStatementChain pol₂ pin₂) : Prop :=
  (match pol₁, pol₂ with
   | .twoLayerWrap wp₁, .twoLayerWrap wp₂ =>
     Blake3Collision
       (compressWrapPreimage wp₁.wrapKeyDigest.toList
         (Blake3.Pure.digest (wp₁.claimsBytes (rootStatementWords pin₁ c₁.rootClaimsBytes))).toList)
       (compressWrapPreimage wp₂.wrapKeyDigest.toList
         (Blake3.Pure.digest (wp₂.claimsBytes (rootStatementWords pin₂ c₂.rootClaimsBytes))).toList) ∨
     Blake3Collision
       (wp₁.claimsBytes (rootStatementWords pin₁ c₁.rootClaimsBytes))
       (wp₂.claimsBytes (rootStatementWords pin₂ c₂.rootClaimsBytes))
   | .twoLayerWrap wp₁, .singleLayerDirect =>
     Blake3Collision
       (compressWrapPreimage wp₁.wrapKeyDigest.toList
         (Blake3.Pure.digest (wp₁.claimsBytes (rootStatementWords pin₁ c₁.rootClaimsBytes))).toList)
       (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList)
   | .singleLayerDirect, .twoLayerWrap wp₂ =>
     Blake3Collision
       (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
       (compressWrapPreimage wp₂.wrapKeyDigest.toList
         (Blake3.Pure.digest (wp₂.claimsBytes (rootStatementWords pin₂ c₂.rootClaimsBytes))).toList)
   | .singleLayerDirect, .singleLayerDirect => False) ∨
  Blake3Collision
    (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
    (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList) ∨
  Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
  Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes

private theorem vector32_eq_of_toList_eq {v₁ v₂ : Vector UInt8 32} (h : v₁.toList = v₂.toList) :
    v₁ = v₂ :=
  Vector.ext fun i hi => by
    have := congrArg (fun l => l[i]?) h
    simpa [Vector.getElem?_toList, hi] using this

/-- Core uniqueness lemma on root statement words: equal `rootStatementWords` either produce a
concrete BLAKE3 collision or bind the exact same `(pin, rootKeyBytes, rootClaimsBytes)`. -/
theorem rootStatementWords_unique_or_collision {pin₁ pin₂ : Vector UInt8 32}
    {k₁ c₁ k₂ c₂ : List UInt8}
    (hk₁ : Blake3.Pure.digest k₁ = pin₁) (hk₂ : Blake3.Pure.digest k₂ = pin₂)
    (hWords : rootStatementWords pin₁ c₁ = rootStatementWords pin₂ c₂) :
    Blake3Collision
        (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁).toList)
        (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂).toList) ∨
      Blake3Collision k₁ k₂ ∨
      Blake3Collision c₁ c₂ ∨
      (pin₁ = pin₂ ∧ k₁ = k₂ ∧ c₁ = c₂) := by
  have hdigList :
      (rootStatementDigest pin₁ c₁).toList = (rootStatementDigest pin₂ c₂).toList :=
    packBytes32ToU32Words_injective (by simp) (by simp) hWords
  have hdig : rootStatementDigest pin₁ c₁ = rootStatementDigest pin₂ c₂ :=
    vector32_eq_of_toList_eq hdigList
  rcases compressWrap_statement_binds_root_or_collision (by simp) (by simp) hdig with
    hcol | ⟨hpinList, hclList⟩
  · exact Or.inl hcol
  · have hpin : pin₁ = pin₂ := vector32_eq_of_toList_eq hpinList
    have hclDig : Blake3.Pure.digest c₁ = Blake3.Pure.digest c₂ := vector32_eq_of_toList_eq hclList
    have hkDig : Blake3.Pure.digest k₁ = Blake3.Pure.digest k₂ := hk₁.trans (hpin.trans hk₂.symm)
    by_cases hk : k₁ = k₂
    · by_cases hcl : c₁ = c₂
      · exact Or.inr (Or.inr (Or.inr ⟨hpin, hk, hcl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hcl, hclDig⟩))
    · exact Or.inr (Or.inl ⟨hk, hkDig⟩)

/-- **End-to-End Statement Uniqueness for Both Two-Layer (`WrapPolicy`) and Single-Layer Policies:**
If two `AiurStageStatementChain`s using the same policy family (either both `.twoLayerWrap`,
possibly with distinct `wp₁, wp₂`, or both `.singleLayerDirect`) produce equal outer terminal
limbs `(low, high)` in `Nat`, then EITHER a concrete BLAKE3 collision occurred (in
`StatementChainCollision c₁ c₂`) OR both chains bind the exact same `StatementPolicy`
(including `wp₁ = wp₂`), `rootKeyPin`, `rootKeyBytes`, and `rootClaimsBytes`! -/
theorem statementChain_unique_or_collision {pol₁ pol₂ : StatementPolicy} {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pol₁ pin₁) (c₂ : AiurStageStatementChain pol₂ pin₂)
    (hSameKind : (pol₁ = .singleLayerDirect ↔ pol₂ = .singleLayerDirect))
    (hLow : c₁.terminalLow = c₂.terminalLow) (hHigh : c₁.terminalHigh = c₂.terminalHigh) :
    StatementChainCollision c₁ c₂ ∨
      (pol₁ = pol₂ ∧ pin₁ = pin₂ ∧
       c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have hunpack :
      pol₁.terminalStatementWords pin₁ c₁.rootClaimsBytes =
      pol₂.terminalStatementWords pin₂ c₂.rootClaimsBytes := by
    rw [← c₁.unpack_recovers_terminal_statement, ← c₂.unpack_recovers_terminal_statement, hLow, hHigh]
  cases pol₁ with
  | singleLayerDirect =>
    cases pol₂ with
    | twoLayerWrap wp₂ => exact absurd (hSameKind.mp rfl) (by simp)
    | singleLayerDirect =>
      rcases rootStatementWords_unique_or_collision c₁.rootKey_pinned c₂.rootKey_pinned hunpack with
        hcol | hcol | hcol | ⟨hpin, hk, hc⟩
      · exact Or.inl (Or.inr (Or.inl hcol))
      · exact Or.inl (Or.inr (Or.inr (Or.inl hcol)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr hcol)))
      · exact Or.inr ⟨rfl, hpin, hk, hc⟩
  | twoLayerWrap wp₁ =>
    cases pol₂ with
    | singleLayerDirect => exact absurd (hSameKind.mpr rfl) (by simp)
    | twoLayerWrap wp₂ =>
      have hOuterDigList :
          (wp₁.glStatementDigest (rootStatementWords pin₁ c₁.rootClaimsBytes)).toList =
          (wp₂.glStatementDigest (rootStatementWords pin₂ c₂.rootClaimsBytes)).toList :=
        packBytes32ToU32Words_injective (by simp) (by simp) hunpack
      have hOuterDig :
          wp₁.glStatementDigest (rootStatementWords pin₁ c₁.rootClaimsBytes) =
          wp₂.glStatementDigest (rootStatementWords pin₂ c₂.rootClaimsBytes) :=
        vector32_eq_of_toList_eq hOuterDigList
      rcases compressWrap_statement_binds_root_or_collision (by simp) (by simp) hOuterDig with
        hOuterCol | ⟨hWrapKeyList, hWrapClaimsDigList⟩
      · exact Or.inl (Or.inl (Or.inl hOuterCol))
      · have hWrapKey : wp₁.wrapKeyDigest = wp₂.wrapKeyDigest :=
          vector32_eq_of_toList_eq hWrapKeyList
        have hWrapClaimsDig :
            Blake3.Pure.digest (wp₁.claimsBytes (rootStatementWords pin₁ c₁.rootClaimsBytes)) =
            Blake3.Pure.digest (wp₂.claimsBytes (rootStatementWords pin₂ c₂.rootClaimsBytes)) :=
          vector32_eq_of_toList_eq hWrapClaimsDigList
        by_cases hClaimsEq :
            wp₁.claimsBytes (rootStatementWords pin₁ c₁.rootClaimsBytes) =
            wp₂.claimsBytes (rootStatementWords pin₂ c₂.rootClaimsBytes)
        · obtain ⟨hWpEq, hRootWordsEq⟩ := WrapPolicySpec.claimsBytes_injective
            (rootStatementWords_length _ _) (rootStatementWords_length _ _)
            (rootStatementWords_lt _ _) (rootStatementWords_lt _ _) hWrapKey hClaimsEq
          rcases rootStatementWords_unique_or_collision c₁.rootKey_pinned c₂.rootKey_pinned hRootWordsEq with
            hcol | hcol | hcol | ⟨hpin, hk, hc⟩
          · exact Or.inl (Or.inr (Or.inl hcol))
          · exact Or.inl (Or.inr (Or.inr (Or.inl hcol)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr hcol)))
          · exact Or.inr ⟨congrArg StatementPolicy.twoLayerWrap hWpEq, hpin, hk, hc⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hClaimsEq, hWrapClaimsDig⟩))

/-- Statement uniqueness lifted directly from `BN254Fr` terminal public inputs. -/
theorem statementChain_unique_bn254_or_collision {pol₁ pol₂ : StatementPolicy}
    {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pol₁ pin₁) (c₂ : AiurStageStatementChain pol₂ pin₂)
    (hSameKind : (pol₁ = .singleLayerDirect ↔ pol₂ = .singleLayerDirect))
    (hLow : (c₁.terminalLow : BN254Fr) = (c₂.terminalLow : BN254Fr))
    (hHigh : (c₁.terminalHigh : BN254Fr) = (c₂.terminalHigh : BN254Fr)) :
    StatementChainCollision c₁ c₂ ∨
      (pol₁ = pol₂ ∧ pin₁ = pin₂ ∧
       c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have ⟨hl, hh⟩ := limbs_embed_bn254_injective c₁.terminal_bounds.1 c₁.terminal_bounds.2
    c₂.terminal_bounds.1 c₂.terminal_bounds.2 hLow hHigh
  exact statementChain_unique_or_collision c₁ c₂ hSameKind hl hh

/-- Statement uniqueness lifted directly from `BLS12381Fr` terminal public inputs
(standalone arithmetic lemma). -/
theorem statementChain_unique_bls12381_or_collision {pol₁ pol₂ : StatementPolicy}
    {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pol₁ pin₁) (c₂ : AiurStageStatementChain pol₂ pin₂)
    (hSameKind : (pol₁ = .singleLayerDirect ↔ pol₂ = .singleLayerDirect))
    (hLow : (c₁.terminalLow : BLS12381Fr) = (c₂.terminalLow : BLS12381Fr))
    (hHigh : (c₁.terminalHigh : BLS12381Fr) = (c₂.terminalHigh : BLS12381Fr)) :
    StatementChainCollision c₁ c₂ ∨
      (pol₁ = pol₂ ∧ pin₁ = pin₂ ∧
       c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  have ⟨hl, hh⟩ := limbs_embed_bls12381_injective c₁.terminal_bounds.1 c₁.terminal_bounds.2
    c₂.terminal_bounds.1 c₂.terminal_bounds.2 hLow hHigh
  exact statementChain_unique_or_collision c₁ c₂ hSameKind hl hh

end Ix.Cert.AiurCompression
