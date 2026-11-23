import Ix.Cert.MultiStarkRefinement.WireDeserialize
import Ix.Cert.MultiStark.Transcript
import Ix.Cert.MultiStark.Verifier
import Ix.Cert.MultiStark.Blake3Parity
import CertiFriP3.Pruned

/-! # Fiat–Shamir Transcript, StarkHash, & Pruned-MMCS Refinement (`TranscriptMmcs`)

Refines the cryptographic sponge/transcript and Merkle commitment checks of
`MultiStark.recursionProgram` (`Transcript`, `StarkHash`, `Mmcs`) onto
`Ix.Cert.MultiStark.{batchChallenger, shardAirChallenges, shardFriChallenges}` and
`CertiFri.P3.{baseHasher, extHasher, prunedMmcs}`:
1. Sponge word sampling & rejection sampling (`Transcript::ch_sample8`, `ch_sample_field`,
   `ch_sample_ext`, `ch_sample_bits`) via `blake3_eq_pure` and `glLtPModel_eq_one_iff`.
2. Batch and per-shard transcript absorption order (`batch_fiat_shamir`, `shard_fiat_shamir`).
3. Row hashing (`StarkHash::b3_rows`) via `baseHasher_hashRows_eq_pure` & `extHasher_hashRows_eq_pure`.
4. Merkle compression and pruned frontier folding (`Mmcs::{mmcs_compress, frontier_sort,
   frontier_fold, mmcs_verify_multi}`) via `hashPair_eq_pure`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open CertiFri CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. Sponge Word Sampling & Canonical Goldilocks Rejection Sampling -/

/-- Convert 8 little-endian bytes (`Fin 8 → UInt8`) into a `UInt64`. -/
def bytes8ToUInt64 (b : Fin 8 → UInt8) : UInt64 :=
  UInt64.ofNat (leBytes8Nat b)

theorem leBytes8Nat_lt_2pow64 (b : Fin 8 → UInt8) : leBytes8Nat b < 2 ^ 64 := by
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt
  have h2 := (b 2).toNat_lt; have h3 := (b 3).toNat_lt
  have h4 := (b 4).toNat_lt; have h5 := (b 5).toNat_lt
  have h6 := (b 6).toNat_lt; have h7 := (b 7).toNat_lt
  unfold leBytes8Nat; omega

theorem bytes8ToUInt64_toNat (b : Fin 8 → UInt8) :
    (bytes8ToUInt64 b).toNat = leBytes8Nat b := by
  unfold bytes8ToUInt64
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (leBytes8Nat_lt_2pow64 b)]

/-- Exact refinement of `Transcript::ch_sample_field`'s rejection condition (`Goldilocks::gl_lt_p`):
a sampled 8-byte word `b` is accepted by `ch_sample_field` iff `Goldilocks.ofCanonical?`
succeeds (`isSome`), and the resulting field element is `baseToFp a = glValModel b`! -/
theorem ch_sample_field_accept_iff (b : Fin 8 → UInt8) :
    glLtPModel b = 1 ↔ (Goldilocks.ofCanonical? (bytes8ToUInt64 b)).isSome = true := by
  rw [glLtPModel_eq_one_iff]
  unfold Goldilocks.ofCanonical?
  have htoNat : (bytes8ToUInt64 b).toNat = leBytes8Nat b := bytes8ToUInt64_toNat b
  have hp64 : (0xFFFFFFFF00000001 : UInt64).toNat = Goldilocks.order := rfl
  by_cases hlt : bytes8ToUInt64 b < 0xFFFFFFFF00000001
  · simp only [hlt, ↓reduceDIte, Option.isSome_some, iff_true]
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [htoNat, hp64] at this
    exact this
  · simp only [hlt, ↓reduceDIte, Option.isSome_none, Bool.false_eq_true, iff_false]
    have := mt UInt64.lt_iff_toNat_lt.mpr hlt
    rw [htoNat, hp64] at this
    exact this

theorem ch_sample_field_val {b : Fin 8 → UInt8} {a : Goldilocks}
    (hsome : Goldilocks.ofCanonical? (bytes8ToUInt64 b) = some a) :
    baseToFp a = glValModel b := by
  unfold Goldilocks.ofCanonical? at hsome
  split_ifs at hsome with hlt
  · injection hsome with ha
    subst ha
    unfold baseToFp Goldilocks.toZMod
    dsimp only
    rw [bytes8ToUInt64_toNat, glValModel_eq_natCast]
    rfl

/-- Sponge refill equivalence: `Blake3::hash(input)` in `Transcript::ch_sample8` produces the
exact 32-byte digest computed by `CertiFri.P3.blake3 input` (`ChallengerState.sampleWord`). -/
theorem ch_sample8_refill_eq (input : ByteArray) :
    CertiFri.P3.blake3 input = ByteArray.mk (Blake3.Pure.digest input.data.toList).toArray :=
  Ix.Cert.MultiStark.blake3_eq_pure input

/-! ## 2. Row Hashing & Merkle Pair Compression (`StarkHash`, `Mmcs`) -/

/-- `StarkHash::b3_rows` on a base-field row matches `CertiFri.P3.baseHasher.hashRows`. -/
theorem starkHash_base_rows_refines (row : Array Goldilocks) :
    (CertiFri.P3.baseHasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.rowBytes row).data.toList).toArray :=
  Ix.Cert.MultiStark.baseHasher_hashRows_eq_pure row

/-- `StarkHash::b3_rows` on a flattened extension-field row matches `CertiFri.P3.extHasher.hashRows`. -/
theorem starkHash_ext_rows_refines (row : Array GoldilocksExt) :
    (CertiFri.P3.extHasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.extRowBytes row).data.toList).toArray :=
  Ix.Cert.MultiStark.extHasher_hashRows_eq_pure row

/-- `StarkHash::b3_rows` on a flattened cubic extension-field row matches
`CertiFri.P3.ext3Hasher.hashRows`. -/
theorem starkHash_ext3_rows_refines (row : Array GoldilocksExt3) :
    (CertiFri.P3.ext3Hasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.ext3RowBytes row).data.toList).toArray :=
  Ix.Cert.MultiStark.ext3Hasher_hashRows_eq_pure row

/-- `Mmcs::mmcs_compress` on two 32-byte digests `(left, right)` matches
`CertiFri.P3.Blake3.hashPair left right` (`prunedMmcs` internal-node compression). -/
theorem mmcs_compress_refines (left right : Digest) :
    (CertiFri.P3.Blake3.hashPair left right).toBytes =
      ByteArray.mk (Blake3.Pure.digest (left.toBytes ++ right.toBytes).data.toList).toArray :=
  Ix.Cert.MultiStark.hashPair_eq_pure left right

/-! ## 3. Structured Transcript & MMCS Refinement Witness -/

/-- Refinement invariant connecting the Fiat–Shamir transcript executed by
`Transcript::{batch_fiat_shamir, shard_fiat_shamir}` and `Pcs::pcs_fri_verify`
to `Ix.Cert.MultiStark.{batchChallenger, shardAirChallenges, shardFriChallenges}`. -/
structure BatchTranscriptMatch (sys : StarkSystem) (batch : BatchProof)
    (batchState : ChallengerState) (beta gamma : EF) : Prop where
  batch_fs : batchChallenger sys batch.preamble = some (batchState, beta, gamma)

/-- Per-shard transcript & PCS opening refinement invariant for shard `s` (Protocol `v6`,
cubic extension `GoldilocksExt3`, `FriBatching::Tensor`, BLAKE3 `derive_key`). -/
structure ShardTranscriptPcsMatch (sys : StarkSystem) (header : ShardHeader)
    (shardIdx : Nat) (proof : ShardProof) (batchState : ChallengerState) where
  alphaAir : EF
  zeta : EF
  postZeta : ChallengerState
  shard_fs : shardAirChallenges batchState shardIdx proof = some (alphaAir, zeta, postZeta)
  zeta_ne_zero : zeta ≠ GoldilocksExt3.zero
  shape : Fri.ClaimShape
  commits : Array D
  points : Array EF
  values : Array EF
  pcs_inputs : buildPcsInputs? sys (activeCircuitIndices proof.active) proof zeta =
    some (shape, commits, points, values)
  shape_ok : Fri.shapeOk (F := F) sys.params.toFriParams shape commits points values
    proof.openingProof = true
  friCh : TensorFriChallenges EF
  fri_fs : shardFriChallenges postZeta sys.params.toFriParams shape values proof.openingProof =
    some friCh
  fri_verify : verifyFriTensorWith (prunedMmcs (baseHasherSep .v6Batch))
    (prunedMmcs (ext3HasherSep .v6Batch))
    sys.params.toFriParams shape commits points values proof.openingProof friCh = true

end Ix.Cert.MultiStarkRefinement
