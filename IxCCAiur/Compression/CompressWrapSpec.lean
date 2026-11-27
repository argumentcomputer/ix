import IxCCAiur.Compression.StarkWire
import IxCCAiur.Compression.CompressWrapPure
import Ix.Cert.MultiStark.Wire
import Ix.Cert.MultiStark.Preamble
import Ix.Cert.MultiStark.Transcript
import Ix.Cert.MultiStark.Blake3Parity
import Ix.Cert.AiurCompression.StatementBinding
import IxCCAiur.Blake3KeyedSpec
import IxCCAiur.CompressionIntrinsicsProof
import Ix.Aiur.Parameters

/-! # Pure-Lean Functional Correctness of `StarkWire` & `CompressWrapPure` (`CompressWrapSpec`)

Establishes pure mathematical soundness theorems for `IxCCAiur/Compression/StarkWire.lean`
and `IxCCAiur/Compression/CompressWrapPure.lean`, linking them directly to
`Ix.Cert.MultiStark.{Wire, Preamble, Transcript, Blake3Parity}`,
`Ix.Cert.AiurCompression.StatementBinding`, `IxCC.AiurBackend.Blake3KeyedSpec`,
and `IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert`:

1. **Wire Decoder & Structural Validation Soundness (`StarkWire`)**:
   - Exact byte-length, cursor consumption, `< 256` byte validity, `< p_GL` Goldilocks
     canonicality, prefix-append determinism, and canonical trailing-byte rejection for
     `readU8`, `readU16LE`, `readU32LE`, `readU64LE`, `readCount`, `readGlCanonical`,
     `readExtGl`, `readDigest`, `readClaims`, `readSystem`, and `readBatchProof`.
   - Exact structural verifying-key invariants enforced by `readSystem`:
     Protocol `v6` / `ext_deg = 3` / `fri_batching = 1` header pin,
     `1 ≤ lookupGroupSize ≤ 8`, DAG acyclicity (`SysNodesTopological`),
     `prepWidth = 0 ↔ prepHeight = 0`, exact bit-popcount power-of-two `prepHeight`,
     `NoCommit ⇒ NoIdx`, length-1 `SomeCommit` cap, and strictly monotonic `OptIdx` ranking.
2. **Pure BLAKE3 Parity, `"ix/compress-wrap/v1\0"` Statement Binding & Protocol `v6` Challenger**:
   - Full multi-block / multi-chunk equivalence of `StarkWire.blake3HashBytesWithCv`,
     `blake3HashBytes`, `v6TranscriptBatchHash`, `v6MerkleLeafHashChecked`, and
     `v6MerkleCompress` against `Blake3.Pure`, `Blake3KeyedSpec`, and `CertiFri.P3`.
   - Exact 84-byte `"ix/compress-wrap/v1\0"` statement digest equality matching
     `Ix.Cert.AiurCompression.{compressWrapPreimage, compressWrapStatementDigest,
     rootStatementWords, WrapPolicySpec}`, injective up to an explicit `Blake3Collision`.
   - Exact Protocol `v6` keyed BLAKE3 Fiat–Shamir challenger equivalence
     (`chSample8`, `chSampleGl`, `chSampleExt`, `chSampleBits`) against
     `CertiFri.P3.ChallengerState` and `Ix.Cert.MultiStark.{Transcript, Blake3Parity}`.
3. **Security Floor, Zero-PoW Canonicalization, MMCS, FRI, AIR, LogUp & MEMSEG Soundness**:
   - All in-circuit security-floor assertions (`capHeight = 0`, `1 ≤ maxLogArity ≤ 3`,
     `1 ≤ logBlowup ≤ 4`, `1 ≤ numQueries`, `commitPowBits ≤ 32`, `queryPowBits ≤ 32`,
     conjectured `≥ 220` bits, unique-decoding `≥ 80` bits, finite-`m` Johnson `≥ 128` bits,
     and derived per-`logBlowup` minimum query counts `211 / 101 / 66 / 53`) plus direct
     bridge to `Aiur.meetsSecurityFloor` and `Aiur.meetsSecurityFloor128Johnson`.
   - Zero-PoW witness canonicalization: `(pcsCheckWitness input witness 0).ok = 1 ↔ witness = u64Zero`.
   - Batched pruned MMCS soundness (`mmcsVerifyMulti_sound`): valid per-query keyed-BLAKE3
     Merkle path opening (`MmcsPathValid`) to the unique cap root with duplicate-index consistency.
   - DEEP quotient, multi-arity FRI folding (`log_arity ∈ {1, 2, 3}`), Horner final-polynomial
     match, topological AIR DAG evaluation, per-shard OOD quotient identity, global LogUp
     running-sum closure, ROM-lane-weighted `≤ 2^39` row bound, and strict monotonic disjoint
     `MEMSEG = 16` closure-pair validation.
4. **End-to-End Composition with `CompressionIntrinsicsProof.CompressionCert`**:
   - Composes `CompressWrapAccepted` directly with
     `IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert` over arbitrary prime fields
     and concretely over Goldilocks (`p_G`), BN254 (`Fr`), and BLS12-381 (`Fr`).

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`,
zero `partial`/`unsafe`; strictly `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

namespace CompressWrapSpec

open StarkWire CompressWrapPure

/-! ## Section 1: Core Conversions, Byte/Goldilocks Canonicality & Bit Lemmas -/

/-- Convert a monomorphic `ByteList` to a standard `List Nat`. -/
def byteListToList : ByteList → List Nat
  | .nil => []
  | .cons b rest => b :: byteListToList rest

/-- Convert a monomorphic `ByteList` to a `List UInt8` (truncating each element mod 256). -/
def byteListToUInt8List : ByteList → List UInt8
  | .nil => []
  | .cons b rest => UInt8.ofNat b :: byteListToUInt8List rest

/-- Convert a `List UInt8` to a canonical `ByteList`. -/
def ofUInt8List : List UInt8 → ByteList
  | [] => .nil
  | b :: rest => .cons b.toNat (ofUInt8List rest)

/-- Convert a `ByteList` to a `ByteArray`. -/
def byteListToByteArray (xs : ByteList) : ByteArray :=
  ByteArray.mk (byteListToUInt8List xs).toArray

/-- Every byte in `xs` is strictly below `256`. -/
def ValidBytes : ByteList → Prop
  | .nil => True
  | .cons b rest => b < 256 ∧ ValidBytes rest

/-- Every one of the 8 bytes in a `U64Bytes` is strictly below `256`. -/
def ValidU64Bytes (x : U64Bytes) : Prop :=
  x.b0 < 256 ∧ x.b1 < 256 ∧ x.b2 < 256 ∧ x.b3 < 256 ∧
  x.b4 < 256 ∧ x.b5 < 256 ∧ x.b6 < 256 ∧ x.b7 < 256

/-- Every one of the 4 `U64Bytes` words in a `DigestBytes` has all bytes `< 256`. -/
def ValidDigestBytes (d : DigestBytes) : Prop :=
  ValidU64Bytes d.d0 ∧ ValidU64Bytes d.d1 ∧ ValidU64Bytes d.d2 ∧ ValidU64Bytes d.d3

/-- Exact little-endian 64-bit natural number value of `U64Bytes`. -/
def u64BytesToNat (x : U64Bytes) : Nat :=
  (x.b0 + 256 * x.b1 + 65536 * x.b2 + 16777216 * x.b3) +
  4294967296 * (x.b4 + 256 * x.b5 + 65536 * x.b6 + 16777216 * x.b7)

/-- Exact little-endian natural number value of a `ByteList`. -/
def leNatOfBytes : ByteList → Nat
  | .nil => 0
  | .cons b rest => b + 256 * leNatOfBytes rest

/-- Convert `Digest32` to `Blake3.Pure.CV`. -/
def digest32ToCV (d : Digest32) : Blake3.Pure.CV :=
  #v[d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7]

/-- Convert `Digest32` to 32-byte `Blake3.Pure.Digest`. -/
def digest32ToBytes (d : Digest32) : Blake3.Pure.Digest :=
  Blake3.Pure.cvBytes (digest32ToCV d)

/-- Convert `Digest32Words` to an 8-element `List Nat`. -/
def digest32WordsToList (w : Digest32Words) : List Nat :=
  [w.w0, w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7]

/-- Convert `DigestBytes` to 8 little-endian `UInt32` words as `Blake3.Pure.CV`. -/
def digestBytesToCV (d : DigestBytes) : Blake3.Pure.CV :=
  #v[u64LoU32 d.d0, u64HiU32 d.d0, u64LoU32 d.d1, u64HiU32 d.d1,
     u64LoU32 d.d2, u64HiU32 d.d2, u64LoU32 d.d3, u64HiU32 d.d3]

/-- Convert `DigestBytes` to a 32-byte `List UInt8`. -/
def digestBytesToUInt8List (d : DigestBytes) : List UInt8 :=
  byteListToUInt8List (digestBytesOnto d .nil)

/-- Convert `Digest32` to `CertiFri.P3.Digest`. -/
def digest32ToP3 (d : Digest32) : CertiFri.P3.Digest :=
  ⟨d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7⟩

/-- Length of an `OptIdxList`. -/
def optIdxListLen : OptIdxList → Nat
  | .nil => 0
  | .cons _ rest => 1 + optIdxListLen rest

/-! ### Basic Monomorphic List & Byte Lemmas -/

theorem byteListLen_eq_length (xs : ByteList) :
    byteListLen xs = (byteListToList xs).length := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListLen, byteListToList, ih]; omega

theorem byteListToUInt8List_length (xs : ByteList) :
    (byteListToUInt8List xs).length = byteListLen xs := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListLen, byteListToUInt8List, ih]; omega

theorem byteListAppend_nil_right (xs : ByteList) :
    byteListAppend xs .nil = xs := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListAppend, ih]

theorem byteListAppend_assoc (xs ys zs : ByteList) :
    byteListAppend (byteListAppend xs ys) zs = byteListAppend xs (byteListAppend ys zs) := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListAppend, ih]

theorem byteListLen_append (xs ys : ByteList) :
    byteListLen (byteListAppend xs ys) = byteListLen xs + byteListLen ys := by
  induction xs with
  | nil => simp [byteListAppend, byteListLen]
  | cons b rest ih => simp [byteListAppend, byteListLen, ih]; omega

theorem byteListToList_append (xs ys : ByteList) :
    byteListToList (byteListAppend xs ys) = byteListToList xs ++ byteListToList ys := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListAppend, byteListToList, ih]

theorem byteListToUInt8List_append (xs ys : ByteList) :
    byteListToUInt8List (byteListAppend xs ys) = byteListToUInt8List xs ++ byteListToUInt8List ys := by
  induction xs with
  | nil => rfl
  | cons b rest ih => simp [byteListAppend, byteListToUInt8List, ih]

theorem byteListRevOnto_toUInt8List (xs acc : ByteList) :
    byteListToUInt8List (byteListRevOnto xs acc) =
      (byteListToUInt8List xs).reverse ++ byteListToUInt8List acc := by
  induction xs generalizing acc with
  | nil => simp [byteListRevOnto, byteListToUInt8List]
  | cons b rest ih =>
    simp [byteListRevOnto, byteListToUInt8List, ih, List.append_assoc]

theorem validBytes_append {xs ys : ByteList} :
    ValidBytes (byteListAppend xs ys) ↔ ValidBytes xs ∧ ValidBytes ys := by
  induction xs with
  | nil => simp [byteListAppend, ValidBytes]
  | cons b rest ih =>
    simp only [byteListAppend, ValidBytes, ih, and_assoc]

theorem validBytes_revOnto {xs acc : ByteList} (hx : ValidBytes xs) (ha : ValidBytes acc) :
    ValidBytes (byteListRevOnto xs acc) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons b rest ih => exact ih hx.2 ⟨hx.1, ha⟩

theorem validBytes_ofUInt8List (bs : List UInt8) :
    ValidBytes (ofUInt8List bs) := by
  induction bs with
  | nil => trivial
  | cons b rest ih => exact ⟨b.toNat_lt, ih⟩

theorem byteListToUInt8List_ofUInt8List (bs : List UInt8) :
    byteListToUInt8List (ofUInt8List bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp [ofUInt8List, byteListToUInt8List, ih]

theorem ofUInt8List_byteListToUInt8List {xs : ByteList} (hv : ValidBytes xs) :
    ofUInt8List (byteListToUInt8List xs) = xs := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [byteListToUInt8List, ofUInt8List, ByteList.cons.injEq]
    refine ⟨?_, ih hv.2⟩
    have hlt : b < 256 := hv.1
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]

theorem byteListLen_ofUInt8List (bs : List UInt8) :
    byteListLen (ofUInt8List bs) = bs.length := by
  rw [← byteListToUInt8List_length, byteListToUInt8List_ofUInt8List]

theorem byteList_eq_of_toUInt8List_eq {xs ys : ByteList}
    (hx : ValidBytes xs) (hy : ValidBytes ys)
    (heq : byteListToUInt8List xs = byteListToUInt8List ys) : xs = ys := by
  rw [← ofUInt8List_byteListToUInt8List hx, ← ofUInt8List_byteListToUInt8List hy, heq]

theorem byteListToList_ofUInt8List (bs : List UInt8) :
    byteListToList (ofUInt8List bs) = bs.map UInt8.toNat := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [ofUInt8List, byteListToList, ih]

theorem validBytes_iff_isValidByteList (xs : ByteList) :
    ValidBytes xs ↔ IxCC.AiurBackend.WitnessIO.isValidByteList (byteListToList xs) := by
  induction xs with
  | nil =>
    simp [ValidBytes, byteListToList, IxCC.AiurBackend.WitnessIO.isValidByteList]
  | cons b rest ih =>
    simp [ValidBytes, byteListToList, IxCC.AiurBackend.WitnessIO.isValidByteList, ih]

theorem validBytes_u64BytesOnto {x : U64Bytes} {tail : ByteList} :
    ValidBytes (u64BytesOnto x tail) ↔ ValidU64Bytes x ∧ ValidBytes tail := by
  simp only [u64BytesOnto, ValidBytes, ValidU64Bytes, and_assoc]

theorem validBytes_u64BytesOfU32 (v : Nat) : ValidU64Bytes (u64BytesOfU32 v) := by
  simp only [u64BytesOfU32, ValidU64Bytes]
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), by decide, by decide, by decide, by decide⟩

theorem validBytes_u64BytesOfNat (v : Nat) : ValidU64Bytes (u64BytesOfNat v) := by
  simp only [u64BytesOfNat, ValidU64Bytes]
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

theorem validBytes_u32Onto (w : UInt32) {tail : ByteList} (ht : ValidBytes tail) :
    ValidBytes (u32Onto w tail) := by
  simp only [u32Onto, ValidBytes]
  have hlt := w.toNat_lt
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    by omega, ht⟩

theorem validBytes_digest32Onto (h : Digest32) {tail : ByteList} (ht : ValidBytes tail) :
    ValidBytes (digest32Onto h tail) := by
  unfold digest32Onto
  exact validBytes_u32Onto _ (validBytes_u32Onto _ (validBytes_u32Onto _ (validBytes_u32Onto _
    (validBytes_u32Onto _ (validBytes_u32Onto _ (validBytes_u32Onto _ (validBytes_u32Onto _ ht)))))))

theorem byteListLen_u32Onto (w : UInt32) (tail : ByteList) :
    byteListLen (u32Onto w tail) = 4 + byteListLen tail := by
  simp only [u32Onto, byteListLen]; omega

theorem byteListLen_digest32Onto (h : Digest32) (tail : ByteList) :
    byteListLen (digest32Onto h tail) = 32 + byteListLen tail := by
  unfold digest32Onto
  simp only [byteListLen_u32Onto]; omega

theorem validU64Bytes_u64Zero : ValidU64Bytes u64Zero := by
  simp only [ValidU64Bytes, u64Zero]; omega

theorem validU64Bytes_u64OfTwoU32 (lo hi : UInt32) : ValidU64Bytes (u64OfTwoU32 lo hi) := by
  simp only [ValidU64Bytes, u64OfTwoU32]
  have hl := lo.toNat_lt
  have hh := hi.toNat_lt
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    by omega, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
    by omega⟩

theorem validDigestBytes_digest32ToDigestBytes (h : Digest32) :
    ValidDigestBytes (digest32ToDigestBytes h) :=
  ⟨validU64Bytes_u64OfTwoU32 _ _, validU64Bytes_u64OfTwoU32 _ _,
   validU64Bytes_u64OfTwoU32 _ _, validU64Bytes_u64OfTwoU32 _ _⟩

/-! ### Exact Goldilocks Canonicality, Comparisons & Popcount Theorems -/

theorem glPrime_val : glPrime = 18446744069414584321 := rfl

theorem glPrime_eq_p3Order : glPrime = CertiFri.P3.Goldilocks.order := rfl

theorem glPrime_eq_glModulus : glPrime = IxCC.AiurBackend.CompressionIntrinsicsProof.glModulus := rfl

theorem u64BytesToNat_lt (x : U64Bytes) (hv : ValidU64Bytes x) :
    u64BytesToNat x < 2 ^ 64 := by
  unfold ValidU64Bytes at hv
  unfold u64BytesToNat
  omega

/-- Exact canonicality characterization: on any valid 8-byte word `x`, `glLtPBytes x = 1`
if and only if its little-endian 64-bit value is strictly less than `p_GL = 2^64 - 2^32 + 1`. -/
theorem glLtPBytes_eq_one_iff {x : U64Bytes} (hv : ValidU64Bytes x) :
    glLtPBytes x = 1 ↔ u64BytesToNat x < glPrime := by
  rcases x with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  simp only [ValidU64Bytes] at hv
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  simp only [glLtPBytes, u64BytesToNat]
  rw [glPrime_val]
  by_cases hhi : b4 + b5 + b6 + b7 = 1020
  · simp only [hhi, beq_self_eq_true, ↓reduceIte]
    by_cases hlo : b0 + b1 + b2 + b3 = 0
    · simp only [hlo, beq_self_eq_true, ↓reduceIte, true_iff]
      omega
    · have hloB : (b0 + b1 + b2 + b3 == 0) = false := beq_false_of_ne hlo
      simp only [hloB, Bool.false_eq_true, ↓reduceIte]
      omega
  · have hhiB : (b4 + b5 + b6 + b7 == 1020) = false := beq_false_of_ne hhi
    simp only [hhiB, Bool.false_eq_true, ↓reduceIte, true_iff]
    omega

theorem glLtPBytes_zero_or_one (x : U64Bytes) : glLtPBytes x = 0 ∨ glLtPBytes x = 1 := by
  simp only [glLtPBytes]
  split <;> [split <;> simp; simp]

/-- `glValBytes x` computes `u64BytesToNat x % glPrime`. -/
theorem glValBytes_eq_mod (x : U64Bytes) :
    glValBytes x = u64BytesToNat x % glPrime := by
  simp only [glValBytes, glOfU32Pair, glAdd, glMul, u64BytesToNat]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_comm _ 4294967296]

/-- For a valid canonical `U64Bytes` (`glLtPBytes x = 1`), `glValBytes x` equals `u64BytesToNat x`
and is strictly below `glPrime`. -/
theorem glValBytes_of_ltP {x : U64Bytes} (hv : ValidU64Bytes x) (hlt : glLtPBytes x = 1) :
    glValBytes x = u64BytesToNat x ∧ glValBytes x < glPrime := by
  have hltP : u64BytesToNat x < glPrime := (glLtPBytes_eq_one_iff hv).mp hlt
  rw [glValBytes_eq_mod, Nat.mod_eq_of_lt hltP]
  exact ⟨rfl, hltP⟩

theorem u64BytesToNat_u64BytesOfNat {v : Nat} (hv : v < 2 ^ 64) :
    u64BytesToNat (u64BytesOfNat v) = v := by
  unfold u64BytesToNat u64BytesOfNat
  dsimp only
  omega

theorem u64BytesToNat_u64BytesOfU32 {v : Nat} (hv : v < 2 ^ 32) :
    u64BytesToNat (u64BytesOfU32 v) = v := by
  unfold u64BytesToNat u64BytesOfU32
  dsimp only
  omega

theorem u64BytesToNat_u64Zero : u64BytesToNat u64Zero = 0 := rfl

theorem u64BytesEq_eq_one_iff (a b : U64Bytes) :
    u64BytesEq a b = 1 ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases b with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  unfold u64BytesEq
  simp only [U64Bytes.mk.injEq]
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

theorem u64BytesEq_zero_or_one (a b : U64Bytes) :
    u64BytesEq a b = 0 ∨ u64BytesEq a b = 1 := by
  unfold u64BytesEq; split <;> simp

theorem digestBytesEq_eq_one_iff (a b : DigestBytes) :
    digestBytesEq a b = 1 ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  unfold digestBytesEq
  simp only [DigestBytes.mk.injEq]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq, u64BytesEq_eq_one_iff] at h
    rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    simp
  · rename_i h
    constructor
    · intro h0; cases h0
    · intro heq
      rcases heq with ⟨rfl, rfl, rfl, rfl⟩
      simp [u64BytesEq_eq_one_iff] at h

theorem u64BytesLe_eq_one_iff {a b : U64Bytes}
    (ha : ValidU64Bytes a) (hb : ValidU64Bytes b) :
    u64BytesLe a b = 1 ↔ u64BytesToNat a ≤ u64BytesToNat b := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  rcases b with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  simp only [ValidU64Bytes] at ha hb
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  simp only [u64BytesLe, u64BytesToNat]
  by_cases h7 : a7 = b7
  · subst h7; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    by_cases h6 : a6 = b6
    · subst h6; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h5 : a5 = b5
      · subst h5; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : a4 = b4
        · subst h4; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : a3 = b3
          · subst h3; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            by_cases h2 : a2 = b2
            · subst h2; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
              by_cases h1 : a1 = b1
              · subst h1; simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                split <;> omega
              · have h1b : (a1 != b1) = true := bne_iff_ne.mpr h1
                simp only [h1b, ↓reduceIte]; split <;> omega
            · have h2b : (a2 != b2) = true := bne_iff_ne.mpr h2
              simp only [h2b, ↓reduceIte]; split <;> omega
          · have h3b : (a3 != b3) = true := bne_iff_ne.mpr h3
            simp only [h3b, ↓reduceIte]; split <;> omega
        · have h4b : (a4 != b4) = true := bne_iff_ne.mpr h4
          simp only [h4b, ↓reduceIte]; split <;> omega
      · have h5b : (a5 != b5) = true := bne_iff_ne.mpr h5
        simp only [h5b, ↓reduceIte]; split <;> omega
    · have h6b : (a6 != b6) = true := bne_iff_ne.mpr h6
      simp only [h6b, ↓reduceIte]; split <;> omega
  · have h7b : (a7 != b7) = true := bne_iff_ne.mpr h7
    simp only [h7b, ↓reduceIte]; split <;> omega

theorem assertSameLimbs_eq_one_iff (a b : U64List) :
    assertSameLimbs a b = 1 ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp [assertSameLimbs]
  | cons x ra ih =>
    cases b with
    | nil => simp [assertSameLimbs]
    | cons y rb =>
      unfold assertSameLimbs
      by_cases hxy : u64BytesEq x y = 1
      · simp only [hxy, beq_self_eq_true, ↓reduceIte, ih, U64List.cons.injEq]
        rw [(u64BytesEq_eq_one_iff x y).mp hxy]
        simp
      · have hbf : (u64BytesEq x y == 1) = false := beq_false_of_ne hxy
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, U64List.cons.injEq]
        constructor
        · intro h; cases h
        · intro ⟨heq, _⟩; exact absurd ((u64BytesEq_eq_one_iff x y).mpr heq) hxy

theorem assertSameClaims_eq_one_iff (a b : U64ListList) :
    assertSameClaims a b = 1 ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp [assertSameClaims]
  | cons x ra ih =>
    cases b with
    | nil => simp [assertSameClaims]
    | cons y rb =>
      unfold assertSameClaims
      by_cases hxy : assertSameLimbs x y = 1
      · simp only [hxy, beq_self_eq_true, ↓reduceIte, ih, U64ListList.cons.injEq]
        rw [(assertSameLimbs_eq_one_iff x y).mp hxy]
        simp
      · have hbf : (assertSameLimbs x y == 1) = false := beq_false_of_ne hxy
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, U64ListList.cons.injEq]
        constructor
        · intro h; cases h
        · intro ⟨heq, _⟩; exact absurd ((assertSameLimbs_eq_one_iff x y).mpr heq) hxy

theorem assertSameNatList_eq_one_iff (a b : NatList) :
    assertSameNatList a b = 1 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [assertSameNatList]
  | cons x ra ih =>
    cases b with
    | nil => simp [assertSameNatList]
    | cons y rb =>
      simp only [assertSameNatList]
      by_cases hxy : x = y
      · subst hxy; simp [ih]
      · have hbf : (x == y) = false := beq_false_of_ne hxy
        simp [hbf, hxy]

theorem assertSameCap_eq_one_iff (a b : DigestBytesList) :
    assertSameCap a b = 1 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [assertSameCap]
  | cons x ra ih =>
    cases b with
    | nil => simp [assertSameCap]
    | cons y rb =>
      unfold assertSameCap
      by_cases hxy : digestBytesEq x y = 1
      · simp only [hxy, beq_self_eq_true, ↓reduceIte, ih, DigestBytesList.cons.injEq]
        rw [(digestBytesEq_eq_one_iff x y).mp hxy]; simp
      · have hbf : (digestBytesEq x y == 1) = false := beq_false_of_ne hxy
        simp only [hbf, Bool.false_eq_true, ↓reduceIte, DigestBytesList.cons.injEq]
        constructor
        · intro h; cases h
        · intro ⟨heq, _⟩; exact absurd ((digestBytesEq_eq_one_iff x y).mpr heq) hxy

theorem glIsZero_eq_one_iff (a : Nat) : glIsZero a = 1 ↔ a % glPrime = 0 := by
  unfold glIsZero
  by_cases h : a % glPrime = 0
  · simp [h]
  · have hb : (a % glPrime == 0) = false := beq_false_of_ne h
    simp [hb, h]

theorem glEq_eq_one_iff (a b : Nat) : glEq a b = 1 ↔ a % glPrime = b % glPrime := by
  unfold glEq
  by_cases h : a % glPrime = b % glPrime
  · simp [h]
  · have hb : (a % glPrime == b % glPrime) = false := beq_false_of_ne h
    simp [hb, h]

theorem extIsZero_eq_one_iff (a : ExtGl) :
    extIsZero a = 1 ↔ a.c0 % glPrime = 0 ∧ a.c1 % glPrime = 0 ∧ a.c2 % glPrime = 0 := by
  unfold extIsZero
  by_cases h0 : glIsZero a.c0 = 1
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    by_cases h1 : glIsZero a.c1 = 1
    · simp only [h1, beq_self_eq_true, ↓reduceIte]
      rw [glIsZero_eq_one_iff, (glIsZero_eq_one_iff _).mp h0, (glIsZero_eq_one_iff _).mp h1]
      simp
    · have hb1 : (glIsZero a.c1 == 1) = false := beq_false_of_ne h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro ⟨_, hc1, _⟩; exact absurd ((glIsZero_eq_one_iff _).mpr hc1) h1
  · have hb0 : (glIsZero a.c0 == 1) = false := beq_false_of_ne h0
    simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h; cases h
    · intro ⟨hc0, _, _⟩; exact absurd ((glIsZero_eq_one_iff _).mpr hc0) h0

theorem extEq_eq_one_iff (a b : ExtGl) :
    extEq a b = 1 ↔
      a.c0 % glPrime = b.c0 % glPrime ∧
      a.c1 % glPrime = b.c1 % glPrime ∧
      a.c2 % glPrime = b.c2 % glPrime := by
  unfold extEq
  by_cases h0 : glEq a.c0 b.c0 = 1
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    by_cases h1 : glEq a.c1 b.c1 = 1
    · simp only [h1, beq_self_eq_true, ↓reduceIte]
      rw [glEq_eq_one_iff, (glEq_eq_one_iff _ _).mp h0, (glEq_eq_one_iff _ _).mp h1]
      simp
    · have hb1 : (glEq a.c1 b.c1 == 1) = false := beq_false_of_ne h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro ⟨_, hc1, _⟩; exact absurd ((glEq_eq_one_iff _ _).mpr hc1) h1
  · have hb0 : (glEq a.c0 b.c0 == 1) = false := beq_false_of_ne h0
    simp only [hb0, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h; cases h
    · intro ⟨hc0, _, _⟩; exact absurd ((glEq_eq_one_iff _ _).mpr hc0) h0

/-! ### Exact Byte Popcount & Power-of-Two `prepHeight` Characterization -/

theorem bytePopcount_eq_sum (b : Nat) :
    bytePopcount b =
      b % 2 + (b / 2) % 2 + (b / 4) % 2 + (b / 8) % 2 +
      (b / 16) % 2 + (b / 32) % 2 + (b / 64) % 2 + (b / 128) % 2 := by
  simp only [bytePopcount, Nat.div_div_eq_div_mul]

private theorem byte_bit_decomp {b : Nat} (hb : b < 256) :
    b = b % 2 + 2 * ((b / 2) % 2) + 4 * ((b / 4) % 2) + 8 * ((b / 8) % 2) +
        16 * ((b / 16) % 2) + 32 * ((b / 32) % 2) + 64 * ((b / 64) % 2) +
        128 * ((b / 128) % 2) := by
  have d0 : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
  have d1 : 2 * (b / 4) + (b / 2) % 2 = b / 2 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 2) 2
  have d2 : 2 * (b / 8) + (b / 4) % 2 = b / 4 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 4) 2
  have d3 : 2 * (b / 16) + (b / 8) % 2 = b / 8 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 8) 2
  have d4 : 2 * (b / 32) + (b / 16) % 2 = b / 16 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 16) 2
  have d5 : 2 * (b / 64) + (b / 32) % 2 = b / 32 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 32) 2
  have d6 : 2 * (b / 128) + (b / 64) % 2 = b / 64 := by
    simpa [Nat.div_div_eq_div_mul] using Nat.div_add_mod (b / 64) 2
  have d7 : (b / 128) % 2 = b / 128 := Nat.mod_eq_of_lt (by omega)
  omega

theorem bytePopcount_eq_zero_iff {b : Nat} (hb : b < 256) :
    bytePopcount b = 0 ↔ b = 0 := by
  rw [bytePopcount_eq_sum]
  have hd := byte_bit_decomp hb
  generalize b % 2 = x0 at hd ⊢
  generalize (b / 2) % 2 = x1 at hd ⊢
  generalize (b / 4) % 2 = x2 at hd ⊢
  generalize (b / 8) % 2 = x3 at hd ⊢
  generalize (b / 16) % 2 = x4 at hd ⊢
  generalize (b / 32) % 2 = x5 at hd ⊢
  generalize (b / 64) % 2 = x6 at hd ⊢
  generalize (b / 128) % 2 = x7 at hd ⊢
  omega

theorem bytePopcount_eq_one_iff {b : Nat} (hb : b < 256) :
    bytePopcount b = 1 ↔ ∃ k < 8, b = 2 ^ k := by
  constructor
  · intro h
    rw [bytePopcount_eq_sum] at h
    have hd := byte_bit_decomp hb
    generalize b % 2 = x0 at hd h
    generalize (b / 2) % 2 = x1 at hd h
    generalize (b / 4) % 2 = x2 at hd h
    generalize (b / 8) % 2 = x3 at hd h
    generalize (b / 16) % 2 = x4 at hd h
    generalize (b / 32) % 2 = x5 at hd h
    generalize (b / 64) % 2 = x6 at hd h
    generalize (b / 128) % 2 = x7 at hd h
    by_cases h0 : x0 = 1
    · exact ⟨0, by decide, by omega⟩
    · by_cases h1 : x1 = 1
      · exact ⟨1, by decide, by omega⟩
      · by_cases h2 : x2 = 1
        · exact ⟨2, by decide, by omega⟩
        · by_cases h3 : x3 = 1
          · exact ⟨3, by decide, by omega⟩
          · by_cases h4 : x4 = 1
            · exact ⟨4, by decide, by omega⟩
            · by_cases h5 : x5 = 1
              · exact ⟨5, by decide, by omega⟩
              · by_cases h6 : x6 = 1
                · exact ⟨6, by decide, by omega⟩
                · exact ⟨7, by decide, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> decide

private theorem u32_byte_decomp {n : Nat} (hn : n < 2 ^ 32) :
    n = n % 256 + 256 * ((n / 256) % 256) +
        65536 * ((n / 256 / 256) % 256) + 16777216 * ((n / 256 / 256 / 256) % 256) := by
  have d0 : 256 * (n / 256) + n % 256 = n := Nat.div_add_mod n 256
  have d1 : 256 * (n / 256 / 256) + (n / 256) % 256 = n / 256 := Nat.div_add_mod (n / 256) 256
  have d2 : 256 * (n / 256 / 256 / 256) + (n / 256 / 256) % 256 = n / 256 / 256 :=
    Nat.div_add_mod (n / 256 / 256) 256
  have d3 : (n / 256 / 256 / 256) % 256 = n / 256 / 256 / 256 := by
    apply Nat.mod_eq_of_lt
    simp only [Nat.div_div_eq_div_mul]
    omega
  omega

/-- Exact bit-popcount power-of-two characterization for 32-bit `prepHeight`:
the sum of `bytePopcount` across the four bytes of `n < 2^32` is `≤ 1` if and only if
`n = 0` or `n = 2^k` for some `k < 32`. -/
theorem u32_popcount_le_one_iff {n : Nat} (hn : n < 2 ^ 32) :
    let u := u64BytesOfU32 n
    bytePopcount u.b0 + bytePopcount u.b1 + bytePopcount u.b2 + bytePopcount u.b3 ≤ 1 ↔
      n = 0 ∨ ∃ k < 32, n = 2 ^ k := by
  dsimp only [u64BytesOfU32]
  have hb0 : n % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb1 : (n / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb2 : (n / 256 / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb3 : (n / 256 / 256 / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
  have hrec := u32_byte_decomp hn
  constructor
  · intro hsum
    by_cases h0 : bytePopcount (n % 256) = 1
    · have h1 := (bytePopcount_eq_zero_iff hb1).mp (by omega)
      have h2 := (bytePopcount_eq_zero_iff hb2).mp (by omega)
      have h3 := (bytePopcount_eq_zero_iff hb3).mp (by omega)
      obtain ⟨k, hk, heq⟩ := (bytePopcount_eq_one_iff hb0).mp h0
      exact Or.inr ⟨k, by omega, by rw [hrec, heq, h1, h2, h3]; omega⟩
    · have h0z := (bytePopcount_eq_zero_iff hb0).mp (by omega)
      by_cases h1 : bytePopcount ((n / 256) % 256) = 1
      · have h2 := (bytePopcount_eq_zero_iff hb2).mp (by omega)
        have h3 := (bytePopcount_eq_zero_iff hb3).mp (by omega)
        obtain ⟨k, hk, heq⟩ := (bytePopcount_eq_one_iff hb1).mp h1
        refine Or.inr ⟨k + 8, by omega, ?_⟩
        rw [hrec, h0z, heq, h2, h3, Nat.pow_add]
        have : (2 : Nat) ^ 8 = 256 := rfl
        omega
      · have h1z := (bytePopcount_eq_zero_iff hb1).mp (by omega)
        by_cases h2 : bytePopcount ((n / 256 / 256) % 256) = 1
        · have h3 := (bytePopcount_eq_zero_iff hb3).mp (by omega)
          obtain ⟨k, hk, heq⟩ := (bytePopcount_eq_one_iff hb2).mp h2
          refine Or.inr ⟨k + 16, by omega, ?_⟩
          rw [hrec, h0z, h1z, heq, h3, Nat.pow_add]
          have : (2 : Nat) ^ 16 = 65536 := rfl
          omega
        · have h2z := (bytePopcount_eq_zero_iff hb2).mp (by omega)
          by_cases h3 : bytePopcount ((n / 256 / 256 / 256) % 256) = 1
          · obtain ⟨k, hk, heq⟩ := (bytePopcount_eq_one_iff hb3).mp h3
            refine Or.inr ⟨k + 24, by omega, ?_⟩
            rw [hrec, h0z, h1z, h2z, heq, Nat.pow_add]
            have : (2 : Nat) ^ 24 = 16777216 := rfl
            omega
          · have h3z := (bytePopcount_eq_zero_iff hb3).mp (by omega)
            exact Or.inl (by omega)
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · decide
    · interval_cases k <;> decide

/-! ## Section 2: Wire Decoder & Structural Validation Soundness (`StarkWire.lean`) -/

private theorem mul_eq_one_of_le_one {a b : Nat} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a with
  | zero => simp at h
  | succ a' =>
    cases b with
    | zero => simp at h
    | succ b' =>
      have : a' * b' + a' + b' + 1 = 1 := by
        have hmul : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
        omega
      omega

theorem readLeNatAux_ok_zero_or_one (rem : Nat) (s : ByteList) (shift acc : Nat) :
    (readLeNatAux rem s shift acc).ok = 0 ∨ (readLeNatAux rem s shift acc).ok = 1 := by
  induction rem generalizing s shift acc with
  | zero => exact Or.inr rfl
  | succ rem' ih =>
    cases s with
    | nil => exact Or.inl rfl
    | cons b rest =>
      simp only [readLeNatAux]
      split
      · exact ih rest _ _
      · exact Or.inl rfl

theorem readU64LE_ok_zero_or_one (s : ByteList) :
    (readU64LE s).ok = 0 ∨ (readU64LE s).ok = 1 := by
  simp only [readU64LE]
  rcases readLeNatAux_ok_zero_or_one 4 s 1 0 with h1 | h1 <;>
    rcases readLeNatAux_ok_zero_or_one 4 (readLeNatAux 4 s 1 0).rest 1 0 with h2 | h2 <;>
    simp [h1, h2]

theorem readCount_ok_zero_or_one (s : ByteList) :
    (readCount s).ok = 0 ∨ (readCount s).ok = 1 := by
  simp only [readCount]
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inl rfl

theorem readGlCanonical_ok_zero_or_one (s : ByteList) :
    (readGlCanonical s).ok = 0 ∨ (readGlCanonical s).ok = 1 := by
  simp only [readGlCanonical]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem readCanonicalU64VecN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readCanonicalU64VecN s n).ok = 0 ∨ (readCanonicalU64VecN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readCanonicalU64VecN]
    split
    · exact Or.inl rfl
    · exact ih _

theorem readClaimsN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readClaimsN s n).ok = 0 ∨ (readClaimsN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readClaimsN]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact ih _

theorem u64BytesOnto_append (x : U64Bytes) (xs ys : ByteList) :
    byteListAppend (u64BytesOnto x xs) ys = u64BytesOnto x (byteListAppend xs ys) := rfl

theorem byteListLen_u64BytesOnto (x : U64Bytes) (xs : ByteList) :
    byteListLen (u64BytesOnto x xs) = 8 + byteListLen xs := by
  simp only [u64BytesOnto, byteListLen]; omega

theorem digestBytesOnto_append (d : DigestBytes) (xs ys : ByteList) :
    byteListAppend (digestBytesOnto d xs) ys = digestBytesOnto d (byteListAppend xs ys) := rfl

theorem byteListLen_digestBytesOnto (d : DigestBytes) (xs : ByteList) :
    byteListLen (digestBytesOnto d xs) = 32 + byteListLen xs := by
  simp only [digestBytesOnto, byteListLen_u64BytesOnto]; omega

theorem leNatOfBytes_lt : ∀ {bs : ByteList}, ValidBytes bs →
    leNatOfBytes bs < 256 ^ byteListLen bs
  | .nil, _ => by simp [leNatOfBytes, byteListLen]
  | .cons b rest, ⟨hb, hr⟩ => by
    have ih := leNatOfBytes_lt hr
    simp only [leNatOfBytes, byteListLen]
    rw [show 1 + byteListLen rest = byteListLen rest + 1 by omega, Nat.pow_succ]
    omega

/-- Exact soundness of `readLeNatAux`: acceptance implies exact `rem`-byte consumption,
`< 256` validity of every consumed byte, exact prefix decomposition, cursor arithmetic,
and exact little-endian value. -/
theorem readLeNatAux_sound (rem : Nat) (s : ByteList) (shift acc : Nat)
    (hok : (readLeNatAux rem s shift acc).ok = 1) :
    let r := readLeNatAux rem s shift acc
    ∃ consumed : ByteList,
      byteListLen consumed = rem ∧
      ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + rem = byteListLen s ∧
      r.val = acc + shift * leNatOfBytes consumed := by
  induction rem generalizing s shift acc with
  | zero =>
    refine ⟨.nil, rfl, trivial, rfl, by simp [readLeNatAux], by simp [readLeNatAux, leNatOfBytes]⟩
  | succ rem' ih =>
    cases s with
    | nil =>
      change (0 : Nat) = 1 at hok
      cases hok
    | cons b rest =>
      simp only [readLeNatAux] at hok ⊢
      by_cases hb : b < 256
      · simp only [hb, ↓reduceIte] at hok ⊢
        obtain ⟨consumed, hlen, hv, hs, hcur, hval⟩ := ih rest (shift * 256) (acc + b * shift) hok
        refine ⟨.cons b consumed, ?_, ⟨hb, hv⟩, ?_, ?_, ?_⟩
        · simp [byteListLen, hlen]; omega
        · simp only [byteListAppend]; exact congrArg (ByteList.cons b) hs
        · simp [byteListLen]; omega
        · simp only [leNatOfBytes]
          rw [hval]
          have h1 : b * shift + shift * 256 * leNatOfBytes consumed =
              shift * (b + 256 * leNatOfBytes consumed) := by ring
          omega
      · simp only [hb, ↓reduceIte] at hok
        cases hok

/-- Prefix-append monotonicity for `readLeNatAux`: whenever `readLeNatAux` accepts `s`,
appending any `extra` bytes leaves `ok` and `val` identical and appends `extra` to `rest`. -/
theorem readLeNatAux_append (rem : Nat) (s extra : ByteList) (shift acc : Nat)
    (hok : (readLeNatAux rem s shift acc).ok = 1) :
    readLeNatAux rem (byteListAppend s extra) shift acc =
      { (readLeNatAux rem s shift acc) with
        rest := byteListAppend (readLeNatAux rem s shift acc).rest extra } := by
  induction rem generalizing s shift acc with
  | zero => rfl
  | succ rem' ih =>
    cases s with
    | nil => simp [readLeNatAux] at hok
    | cons b rest =>
      unfold readLeNatAux at hok ⊢
      by_cases hb : b < 256
      · simp only [hb, ↓reduceIte, byteListAppend] at hok ⊢
        exact ih rest (shift * 256) (acc + b * shift) hok
      · simp only [hb, ↓reduceIte] at hok
        cases hok

/-- `readU8` consumes exactly 1 byte `< 256` and preserves prefix-append determinism. -/
theorem readU8_sound (s : ByteList) (hok : (readU8 s).ok = 1) :
    let r := readU8 s
    r.val < 256 ∧
    s = .cons r.val r.rest ∧
    byteListLen r.rest + 1 = byteListLen s := by
  obtain ⟨c, hlen, hv, hs, hcur, hval⟩ := readLeNatAux_sound 1 s 1 0 hok
  cases c with
  | nil => simp [byteListLen] at hlen
  | cons b tail =>
    cases tail with
    | cons _ _ => simp [byteListLen] at hlen
    | nil =>
      simp only [ValidBytes, leNatOfBytes, byteListAppend, Nat.mul_zero, Nat.add_zero,
        Nat.one_mul, Nat.zero_add] at hv hs hval
      dsimp only [readU8]
      rw [hval]
      exact ⟨hv.1, hs, hcur⟩

theorem readU8_append (s extra : ByteList) (hok : (readU8 s).ok = 1) :
    readU8 (byteListAppend s extra) =
      { (readU8 s) with rest := byteListAppend (readU8 s).rest extra } :=
  readLeNatAux_append 1 s extra 1 0 hok

/-- `readU16LE` consumes exactly 2 valid bytes (`< 2^16`). -/
theorem readU16LE_sound (s : ByteList) (hok : (readU16LE s).ok = 1) :
    let r := readU16LE s
    ∃ consumed : ByteList,
      byteListLen consumed = 2 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 2 = byteListLen s ∧
      r.val = leNatOfBytes consumed ∧ r.val < 2 ^ 16 := by
  obtain ⟨c, hlen, hv, hs, hcur, hval⟩ := readLeNatAux_sound 2 s 1 0 hok
  have hlt := leNatOfBytes_lt hv
  rw [hlen] at hlt
  have hval' : (readU16LE s).val = leNatOfBytes c := by
    change (readLeNatAux 2 s 1 0).val = _; omega
  refine ⟨c, hlen, hv, hs, hcur, hval', ?_⟩
  rw [hval']; exact hlt

theorem readU16LE_append (s extra : ByteList) (hok : (readU16LE s).ok = 1) :
    readU16LE (byteListAppend s extra) =
      { (readU16LE s) with rest := byteListAppend (readU16LE s).rest extra } :=
  readLeNatAux_append 2 s extra 1 0 hok

theorem readU16Limb_sound (s : ByteList) (hok : (readU16Limb s).ok = 1) :
    let r := readU16Limb s
    ∃ consumed : ByteList,
      byteListLen consumed = 2 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 2 = byteListLen s ∧
      r.val = leNatOfBytes consumed ∧ r.val < 2 ^ 16 ∧
      ValidU64Bytes r.limb ∧ u64BytesToNat r.limb = r.val := by
  have h1 : (readU16LE s).ok = 1 := hok
  obtain ⟨c, hlen, hv, hs, hcur, hval, hlt⟩ := readU16LE_sound s h1
  have hlt' : (readLeNatAux 2 s 1 0).val < 2 ^ 16 := hlt
  refine ⟨c, hlen, hv, hs, hcur, hval, hlt, ?_, ?_⟩
  · simp only [readU16Limb, ValidU64Bytes]
    refine ⟨Nat.mod_lt _ (by decide), by omega, by decide, by decide,
      by decide, by decide, by decide, by decide⟩
  · simp only [readU16Limb, u64BytesToNat]; omega

theorem readU16Limb_append (s extra : ByteList) (hok : (readU16Limb s).ok = 1) :
    readU16Limb (byteListAppend s extra) =
      { (readU16Limb s) with rest := byteListAppend (readU16Limb s).rest extra } := by
  unfold readU16Limb
  have h1 : (readLeNatAux 2 s 1 0).ok = 1 := hok
  rw [readLeNatAux_append 2 s extra 1 0 h1]

/-- `readU32LE` consumes exactly 4 valid bytes (`< 2^32`). -/
theorem readU32LE_sound (s : ByteList) (hok : (readU32LE s).ok = 1) :
    let r := readU32LE s
    ∃ consumed : ByteList,
      byteListLen consumed = 4 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 4 = byteListLen s ∧
      r.val = leNatOfBytes consumed ∧ r.val < 2 ^ 32 := by
  obtain ⟨c, hlen, hv, hs, hcur, hval⟩ := readLeNatAux_sound 4 s 1 0 hok
  have hlt := leNatOfBytes_lt hv
  rw [hlen] at hlt
  have hval' : (readU32LE s).val = leNatOfBytes c := by
    change (readLeNatAux 4 s 1 0).val = _; omega
  refine ⟨c, hlen, hv, hs, hcur, hval', ?_⟩
  rw [hval']; exact hlt

theorem readU32LE_append (s extra : ByteList) (hok : (readU32LE s).ok = 1) :
    readU32LE (byteListAppend s extra) =
      { (readU32LE s) with rest := byteListAppend (readU32LE s).rest extra } :=
  readLeNatAux_append 4 s extra 1 0 hok

theorem readU32Limb_sound (s : ByteList) (hok : (readU32Limb s).ok = 1) :
    let r := readU32Limb s
    ∃ consumed : ByteList,
      byteListLen consumed = 4 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 4 = byteListLen s ∧
      r.val = leNatOfBytes consumed ∧ r.val < 2 ^ 32 ∧
      ValidU64Bytes r.limb ∧ u64BytesToNat r.limb = r.val := by
  have h1 : (readU32LE s).ok = 1 := hok
  obtain ⟨c, hlen, hv, hs, hcur, hval, hlt⟩ := readU32LE_sound s h1
  refine ⟨c, hlen, hv, hs, hcur, hval, hlt, validBytes_u64BytesOfU32 _, ?_⟩
  exact u64BytesToNat_u64BytesOfU32 hlt

theorem readU32Limb_append (s extra : ByteList) (hok : (readU32Limb s).ok = 1) :
    readU32Limb (byteListAppend s extra) =
      { (readU32Limb s) with rest := byteListAppend (readU32Limb s).rest extra } := by
  unfold readU32Limb
  have h1 : (readLeNatAux 4 s 1 0).ok = 1 := hok
  rw [readLeNatAux_append 4 s extra 1 0 h1]

private theorem u32_bytes_reconstruct (c : ByteList) (v : Nat) (tail : ByteList)
    (hl : byteListLen c = 4) (hv : ValidBytes c) (heq : v = leNatOfBytes c) :
    let u := u64BytesOfU32 v
    byteListAppend c tail = .cons u.b0 (.cons u.b1 (.cons u.b2 (.cons u.b3 tail))) := by
  rcases c with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _⟩⟩⟩⟩⟩
  · simp [byteListLen] at hl
  · simp [byteListLen] at hl
  · simp [byteListLen] at hl
  · simp [byteListLen] at hl
  · rcases hv with ⟨hx0, hx1, hx2, hx3, _⟩
    simp only [leNatOfBytes] at heq
    subst heq
    simp only [byteListAppend, u64BytesOfU32, ByteList.cons.injEq, and_true]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · simp [byteListLen] at hl; omega

/-- `readU64LE` consumes exactly 8 valid bytes, returning `ValidU64Bytes` whose exact byte
stream equals the consumed 8-byte prefix. -/
theorem readU64LE_sound (s : ByteList) (hok : (readU64LE s).ok = 1) :
    let r := readU64LE s
    ValidU64Bytes r.val ∧
    s = u64BytesOnto r.val r.rest ∧
    byteListLen r.rest + 8 = byteListLen s := by
  simp only [readU64LE] at hok ⊢
  obtain ⟨hlo, hhi⟩ := mul_eq_one_of_le_one hok
  set r0 := readLeNatAux 4 s 1 0
  set r1 := readLeNatAux 4 r0.rest 1 0
  obtain ⟨c0, hlen0, hv0, hs0, hcur0, hval0, _⟩ := readU32LE_sound s hlo
  obtain ⟨c1, hlen1, hv1, hs1, hcur1, hval1, _⟩ := readU32LE_sound r0.rest hhi
  change s = byteListAppend c0 r0.rest at hs0
  change r0.rest = byteListAppend c1 r1.rest at hs1
  change byteListLen r0.rest + 4 = byteListLen s at hcur0
  change byteListLen r1.rest + 4 = byteListLen r0.rest at hcur1
  have h0 := validBytes_u64BytesOfU32 r0.val
  have h1 := validBytes_u64BytesOfU32 r1.val
  refine ⟨⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1⟩, ?_, ?_⟩
  · have hc0 := u32_bytes_reconstruct c0 r0.val r0.rest hlen0 hv0 hval0
    have hc1 := u32_bytes_reconstruct c1 r1.val r1.rest hlen1 hv1 hval1
    calc s = byteListAppend c0 r0.rest := hs0
      _ = .cons (u64BytesOfU32 r0.val).b0 (.cons (u64BytesOfU32 r0.val).b1
            (.cons (u64BytesOfU32 r0.val).b2 (.cons (u64BytesOfU32 r0.val).b3 r0.rest))) := hc0
      _ = .cons (u64BytesOfU32 r0.val).b0 (.cons (u64BytesOfU32 r0.val).b1
            (.cons (u64BytesOfU32 r0.val).b2 (.cons (u64BytesOfU32 r0.val).b3 (byteListAppend c1 r1.rest)))) := by
          rw [hs1]
      _ = u64BytesOnto _ r1.rest := by rw [hc1]; rfl
  · omega

theorem readU64LE_append (s extra : ByteList) (hok : (readU64LE s).ok = 1) :
    readU64LE (byteListAppend s extra) =
      { (readU64LE s) with rest := byteListAppend (readU64LE s).rest extra } := by
  simp only [readU64LE] at hok ⊢
  obtain ⟨hlo, hhi⟩ := mul_eq_one_of_le_one hok
  rw [readLeNatAux_append 4 s extra 1 0 hlo, readLeNatAux_append 4 _ extra 1 0 hhi]

/-- `readCount` consumes 8 valid bytes, enforces `hi32 = 0` (`val < 2^32`) and `val ≤ remaining`. -/
theorem readCount_sound (s : ByteList) (hok : (readCount s).ok = 1) :
    let r := readCount s
    ∃ consumed : ByteList,
      byteListLen consumed = 8 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 8 = byteListLen s ∧
      r.val < 2 ^ 32 ∧ r.val ≤ byteListLen r.rest := by
  simp only [readCount] at hok ⊢
  by_cases h0 : (readU64LE s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU64LE s).ok = 1 :=
      (readU64LE_ok_zero_or_one s).resolve_left h0
    have h0b : ((readU64LE s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    obtain ⟨hv, hs, hcur⟩ := readU64LE_sound s h1
    set u := (readU64LE s).val
    by_cases hhi : u.b4 + u.b5 + u.b6 + u.b7 = 0
    · simp only [hhi, beq_self_eq_true, ↓reduceIte] at hok ⊢
      by_cases hle : u.b0 + 256 * u.b1 + 65536 * u.b2 + 16777216 * u.b3 ≤ byteListLen (readU64LE s).rest
      · simp only [hle, ↓reduceIte] at hok ⊢
        refine ⟨u64BytesOnto u .nil, rfl, validBytes_u64BytesOnto.mpr ⟨hv, trivial⟩, ?_, hcur, ?_, trivial⟩
        · exact hs.trans rfl
        · unfold ValidU64Bytes at hv; omega
      · simp only [hle, ↓reduceIte] at hok; cases hok
    · have hhib : (u.b4 + u.b5 + u.b6 + u.b7 == 0) = false := beq_false_of_ne hhi
      simp only [hhib, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

theorem readCount_append (s extra : ByteList) (hok : (readCount s).ok = 1) :
    readCount (byteListAppend s extra) =
      { (readCount s) with rest := byteListAppend (readCount s).rest extra } := by
  simp only [readCount] at hok ⊢
  by_cases h0 : (readU64LE s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU64LE s).ok = 1 :=
      (readU64LE_ok_zero_or_one s).resolve_left h0
    have h0b : ((readU64LE s).ok == 0) = false := beq_false_of_ne h0
    rw [readU64LE_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    set u := (readU64LE s).val
    by_cases hhi : u.b4 + u.b5 + u.b6 + u.b7 = 0
    · simp only [hhi, beq_self_eq_true, ↓reduceIte] at hok ⊢
      by_cases hle : u.b0 + 256 * u.b1 + 65536 * u.b2 + 16777216 * u.b3 ≤ byteListLen (readU64LE s).rest
      · have hle' : u.b0 + 256 * u.b1 + 65536 * u.b2 + 16777216 * u.b3 ≤
            byteListLen (byteListAppend (readU64LE s).rest extra) := by
          rw [byteListLen_append]; omega
        simp only [hle, hle', ↓reduceIte]
      · simp only [hle, ↓reduceIte] at hok; cases hok
    · have hhib : (u.b4 + u.b5 + u.b6 + u.b7 == 0) = false := beq_false_of_ne hhi
      simp only [hhib, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

/-- `readGlCanonical` consumes exactly 8 valid bytes and returns a canonical Goldilocks element `< p_GL`. -/
theorem readGlCanonical_sound (s : ByteList) (hok : (readGlCanonical s).ok = 1) :
    let r := readGlCanonical s
    ∃ w : U64Bytes,
      ValidU64Bytes w ∧
      u64BytesToNat w < glPrime ∧
      r.val = u64BytesToNat w ∧
      r.val < glPrime ∧
      s = u64BytesOnto w r.rest ∧
      byteListLen r.rest + 8 = byteListLen s := by
  simp only [readGlCanonical] at hok ⊢
  by_cases hc : (readU64LE s).ok * glLtPBytes (readU64LE s).val = 1
  · simp only [hc, beq_self_eq_true, ↓reduceIte]
    obtain ⟨h1, hlt⟩ := mul_eq_one_of_le_one hc
    obtain ⟨hv, hs, hcur⟩ := readU64LE_sound s h1
    obtain ⟨hveq, hvlt⟩ := glValBytes_of_ltP hv hlt
    exact ⟨(readU64LE s).val, hv, (glLtPBytes_eq_one_iff hv).mp hlt, hveq, hvlt, hs, hcur⟩
  · have hcb : ((readU64LE s).ok * glLtPBytes (readU64LE s).val == 1) = false := beq_false_of_ne hc
    simp only [hcb, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

theorem readGlCanonical_append (s extra : ByteList) (hok : (readGlCanonical s).ok = 1) :
    readGlCanonical (byteListAppend s extra) =
      { (readGlCanonical s) with rest := byteListAppend (readGlCanonical s).rest extra } := by
  simp only [readGlCanonical] at hok ⊢
  by_cases hc : (readU64LE s).ok * glLtPBytes (readU64LE s).val = 1
  · obtain ⟨h1, _⟩ := mul_eq_one_of_le_one hc
    rw [readU64LE_append s extra h1]
    simp only [hc, beq_self_eq_true, ↓reduceIte]
  · have hcb : ((readU64LE s).ok * glLtPBytes (readU64LE s).val == 1) = false := beq_false_of_ne hc
    simp only [hcb, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

/-- `readExtGl` consumes exactly 24 valid bytes and produces a canonical cubic extension element
(`c0, c1, c2 < p_GL`). -/
theorem readExtGl_sound (s : ByteList) (hok : (readExtGl s).ok = 1) :
    let r := readExtGl s
    ∃ consumed : ByteList,
      byteListLen consumed = 24 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 24 = byteListLen s ∧
      extCanonical r.val = true ∧
      r.val.c0 < glPrime ∧ r.val.c1 < glPrime ∧ r.val.c2 < glPrime := by
  simp only [readExtGl] at hok ⊢
  set r0 := readGlCanonical s
  set r1 := readGlCanonical r0.rest
  set r2 := readGlCanonical r1.rest
  by_cases hz : r0.ok * r1.ok * r2.ok = 0
  · simp [hz] at hok
  · have h012 : r0.ok = 1 ∧ r1.ok = 1 ∧ r2.ok = 1 := by
      have ⟨h01, h2ne⟩ := not_or.mp (mt mul_eq_zero.mpr hz)
      have ⟨h0ne, h1ne⟩ := not_or.mp (mt mul_eq_zero.mpr h01)
      exact ⟨(readGlCanonical_ok_zero_or_one s).resolve_left h0ne,
             (readGlCanonical_ok_zero_or_one r0.rest).resolve_left h1ne,
             (readGlCanonical_ok_zero_or_one r1.rest).resolve_left h2ne⟩
    have hzb : (r0.ok * r1.ok * r2.ok == 0) = false := beq_false_of_ne hz
    simp only [hzb, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨w0, hv0, _, _, hc0, hs0, hcur0⟩ := readGlCanonical_sound s h012.1
    obtain ⟨w1, hv1, _, _, hc1, hs1, hcur1⟩ := readGlCanonical_sound r0.rest h012.2.1
    obtain ⟨w2, hv2, _, _, hc2, hs2, hcur2⟩ := readGlCanonical_sound r1.rest h012.2.2
    change byteListLen r0.rest + 8 = byteListLen s at hcur0
    change byteListLen r1.rest + 8 = byteListLen r0.rest at hcur1
    change byteListLen r2.rest + 8 = byteListLen r1.rest at hcur2
    have hcan : extCanonical { c0 := r0.val, c1 := r1.val, c2 := r2.val } = true := by
      simp only [extCanonical, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hc0, hc1⟩, hc2⟩
    refine ⟨u64BytesOnto w0 (u64BytesOnto w1 (u64BytesOnto w2 .nil)),
      by simp only [byteListLen_u64BytesOnto, byteListLen],
      validBytes_u64BytesOnto.mpr ⟨hv0, validBytes_u64BytesOnto.mpr ⟨hv1,
        validBytes_u64BytesOnto.mpr ⟨hv2, trivial⟩⟩⟩, ?_, by omega, hcan, hc0, hc1, hc2⟩
    calc s = u64BytesOnto w0 r0.rest := hs0
      _ = u64BytesOnto w0 (u64BytesOnto w1 r1.rest) := by rw [← hs1]
      _ = u64BytesOnto w0 (u64BytesOnto w1 (u64BytesOnto w2 r2.rest)) := by rw [← hs2]
      _ = byteListAppend (u64BytesOnto w0 (u64BytesOnto w1 (u64BytesOnto w2 .nil))) r2.rest := rfl

theorem readExtGl_append (s extra : ByteList) (hok : (readExtGl s).ok = 1) :
    readExtGl (byteListAppend s extra) =
      { (readExtGl s) with rest := byteListAppend (readExtGl s).rest extra } := by
  simp only [readExtGl] at hok ⊢
  set r0 := readGlCanonical s
  set r1 := readGlCanonical r0.rest
  set r2 := readGlCanonical r1.rest
  by_cases hz : r0.ok * r1.ok * r2.ok = 0
  · simp [hz] at hok
  · have h012 : r0.ok = 1 ∧ r1.ok = 1 ∧ r2.ok = 1 := by
      have ⟨h01, h2ne⟩ := not_or.mp (mt mul_eq_zero.mpr hz)
      have ⟨h0ne, h1ne⟩ := not_or.mp (mt mul_eq_zero.mpr h01)
      exact ⟨(readGlCanonical_ok_zero_or_one s).resolve_left h0ne,
             (readGlCanonical_ok_zero_or_one r0.rest).resolve_left h1ne,
             (readGlCanonical_ok_zero_or_one r1.rest).resolve_left h2ne⟩
    rw [readGlCanonical_append s extra h012.1,
        readGlCanonical_append r0.rest extra h012.2.1,
        readGlCanonical_append r1.rest extra h012.2.2]
    have hzb : (r0.ok * r1.ok * r2.ok == 0) = false := beq_false_of_ne hz
    change (if (r0.ok * r1.ok * r2.ok == 0) = true then _ else _) = _
    simp only [hzb, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- `readDigest` consumes exactly 32 valid bytes matching `digestBytesOnto r.val r.rest`. -/
theorem readDigest_sound (s : ByteList) (hok : (readDigest s).ok = 1) :
    let r := readDigest s
    ValidDigestBytes r.val ∧
    s = digestBytesOnto r.val r.rest ∧
    byteListLen r.rest + 32 = byteListLen s := by
  simp only [readDigest] at hok ⊢
  obtain ⟨h012, h3⟩ := mul_eq_one_of_le_one hok
  obtain ⟨h01, h2⟩ := mul_eq_one_of_le_one h012
  obtain ⟨h0, h1⟩ := mul_eq_one_of_le_one h01
  set r0 := readU64LE s
  set r1 := readU64LE r0.rest
  set r2 := readU64LE r1.rest
  set r3 := readU64LE r2.rest
  obtain ⟨hv0, hs0, hc0⟩ := readU64LE_sound s h0
  obtain ⟨hv1, hs1, hc1⟩ := readU64LE_sound r0.rest h1
  obtain ⟨hv2, hs2, hc2⟩ := readU64LE_sound r1.rest h2
  obtain ⟨hv3, hs3, hc3⟩ := readU64LE_sound r2.rest h3
  change byteListLen r0.rest + 8 = byteListLen s at hc0
  change byteListLen r1.rest + 8 = byteListLen r0.rest at hc1
  change byteListLen r2.rest + 8 = byteListLen r1.rest at hc2
  change byteListLen r3.rest + 8 = byteListLen r2.rest at hc3
  refine ⟨⟨hv0, hv1, hv2, hv3⟩, ?_, by omega⟩
  unfold digestBytesOnto
  calc s = u64BytesOnto r0.val r0.rest := hs0
    _ = u64BytesOnto r0.val (u64BytesOnto r1.val r1.rest) := by rw [← hs1]
    _ = u64BytesOnto r0.val (u64BytesOnto r1.val (u64BytesOnto r2.val r2.rest)) := by rw [← hs2]
    _ = u64BytesOnto r0.val (u64BytesOnto r1.val (u64BytesOnto r2.val (u64BytesOnto r3.val r3.rest))) := by
        rw [← hs3]

theorem readDigest_ok_zero_or_one (s : ByteList) :
    (readDigest s).ok = 0 ∨ (readDigest s).ok = 1 := by
  simp only [readDigest]
  have ha := readU64LE_ok_zero_or_one s
  have hb := readU64LE_ok_zero_or_one (readU64LE s).rest
  have hc := readU64LE_ok_zero_or_one (readU64LE (readU64LE s).rest).rest
  have hd := readU64LE_ok_zero_or_one (readU64LE (readU64LE (readU64LE s).rest).rest).rest
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd <;>
    simp only [ha, hb, hc, hd] <;> decide

theorem readDigest_append (s extra : ByteList) (hok : (readDigest s).ok = 1) :
    readDigest (byteListAppend s extra) =
      { (readDigest s) with rest := byteListAppend (readDigest s).rest extra } := by
  simp only [readDigest] at hok ⊢
  obtain ⟨h012, h3⟩ := mul_eq_one_of_le_one hok
  obtain ⟨h01, h2⟩ := mul_eq_one_of_le_one h012
  obtain ⟨h0, h1⟩ := mul_eq_one_of_le_one h01
  rw [readU64LE_append s extra h0,
      readU64LE_append _ extra h1,
      readU64LE_append _ extra h2,
      readU64LE_append _ extra h3]

/-! ### `readClaims` Soundness & Canonical Trailing-Byte Rejection -/

/-- Every word in a `U64List` is valid (`< 256` bytes) and canonical (`< p_GL`). -/
def CanonicalU64List : U64List → Prop
  | .nil => True
  | .cons x rest => ValidU64Bytes x ∧ u64BytesToNat x < glPrime ∧ CanonicalU64List rest

/-- Every claim row in a `U64ListList` consists strictly of valid canonical `< p_GL` words. -/
def CanonicalClaims : U64ListList → Prop
  | .nil => True
  | .cons row rest => CanonicalU64List row ∧ CanonicalClaims rest

theorem readCanonicalU64VecN_sound (s : ByteList) (n : Nat)
    (hok : (readCanonicalU64VecN s n).ok = 1) :
    let r := readCanonicalU64VecN s n
    ∃ consumed : ByteList,
      byteListLen consumed = 8 * n ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen r.rest + 8 * n = byteListLen s ∧
      u64ListLen r.val = n ∧
      CanonicalU64List r.val := by
  induction n generalizing s with
  | zero =>
    refine ⟨.nil, rfl, trivial, rfl, by simp [readCanonicalU64VecN], rfl, trivial⟩
  | succ n ih =>
    simp only [readCanonicalU64VecN] at hok ⊢
    by_cases hbad : (readU64LE s).ok = 0 ∨ glLtPBytes (readU64LE s).val = 0
    · have hcond : ((readU64LE s).ok == 0 || glLtPBytes (readU64LE s).val == 0) = true := by
        rcases hbad with h | h <;> simp [h]
      simp only [hcond, ↓reduceIte] at hok; cases hok
    · obtain ⟨h0ne, hltne⟩ := not_or.mp hbad
      have hcond : ((readU64LE s).ok == 0 || glLtPBytes (readU64LE s).val == 0) = false := by
        simp [beq_false_of_ne h0ne, beq_false_of_ne hltne]
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      have h1 : (readU64LE s).ok = 1 := (readU64LE_ok_zero_or_one s).resolve_left h0ne
      have hlt1 : glLtPBytes (readU64LE s).val = 1 :=
        (glLtPBytes_zero_or_one (readU64LE s).val).resolve_left hltne
      obtain ⟨hv, hs, hcur⟩ := readU64LE_sound s h1
      obtain ⟨c, hlen, hvc, hst, hcurt, hul, hcan⟩ := ih (readU64LE s).rest hok
      refine ⟨u64BytesOnto (readU64LE s).val c, ?_, validBytes_u64BytesOnto.mpr ⟨hv, hvc⟩,
        ?_, by omega, by simp [u64ListLen, hul]; omega,
        ⟨hv, (glLtPBytes_eq_one_iff hv).mp hlt1, hcan⟩⟩
      · simp [u64BytesOnto, byteListLen, hlen]; omega
      · rw [u64BytesOnto_append, ← hst, ← hs]

theorem readCanonicalU64VecN_append (s extra : ByteList) (n : Nat)
    (hok : (readCanonicalU64VecN s n).ok = 1) :
    readCanonicalU64VecN (byteListAppend s extra) n =
      { (readCanonicalU64VecN s n) with rest := byteListAppend (readCanonicalU64VecN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readCanonicalU64VecN] at hok ⊢
    by_cases hbad : (readU64LE s).ok = 0 ∨ glLtPBytes (readU64LE s).val = 0
    · have hcond : ((readU64LE s).ok == 0 || glLtPBytes (readU64LE s).val == 0) = true := by
        rcases hbad with h | h <;> simp [h]
      simp only [hcond, ↓reduceIte] at hok; cases hok
    · obtain ⟨h0ne, hltne⟩ := not_or.mp hbad
      have h1 : (readU64LE s).ok = 1 := (readU64LE_ok_zero_or_one s).resolve_left h0ne
      have hcond : ((readU64LE s).ok == 0 || glLtPBytes (readU64LE s).val == 0) = false := by
        simp [beq_false_of_ne h0ne, beq_false_of_ne hltne]
      rw [readU64LE_append s extra h1]
      simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih (readU64LE s).rest hok]

theorem readClaimsN_sound (s : ByteList) (n : Nat) (hok : (readClaimsN s n).ok = 1) :
    let r := readClaimsN s n
    ∃ consumed : ByteList,
      ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      byteListLen consumed ≤ n * (8 + 8 * 2 ^ 32) ∧
      u64ListListLen r.val = n ∧
      CanonicalClaims r.val := by
  induction n generalizing s with
  | zero =>
    refine ⟨.nil, trivial, rfl, by simp [byteListLen], rfl, trivial⟩
  | succ n ih =>
    simp only [readClaimsN] at hok ⊢
    by_cases h0 : (readCount s).ok = 0
    · simp [h0] at hok
    · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
      have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hlen0, hv0, hs0, _, hmlt, _⟩ := readCount_sound s h1
      set rm := readCount s
      by_cases hvok : (readCanonicalU64VecN rm.rest rm.val).ok = 0
      · simp [hvok] at hok
      · have hvok1 : (readCanonicalU64VecN rm.rest rm.val).ok = 1 :=
          (readCanonicalU64VecN_ok_zero_or_one rm.rest rm.val).resolve_left hvok
        have hvokb : ((readCanonicalU64VecN rm.rest rm.val).ok == 0) = false := beq_false_of_ne hvok
        simp only [hvokb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        obtain ⟨c1, hlen1, hv1, hs1, _, _, hcan1⟩ := readCanonicalU64VecN_sound rm.rest rm.val hvok1
        obtain ⟨c2, hv2, hs2, hbound2, hlen2, hcan2⟩ := ih (readCanonicalU64VecN rm.rest rm.val).rest hok
        refine ⟨byteListAppend c0 (byteListAppend c1 c2),
          validBytes_append.mpr ⟨hv0, validBytes_append.mpr ⟨hv1, hv2⟩⟩, ?_, ?_,
          by simp [u64ListListLen, hlen2]; omega, ⟨hcan1, hcan2⟩⟩
        · rw [byteListAppend_assoc, byteListAppend_assoc, ← hs2, ← hs1, ← hs0]
        · simp only [byteListLen_append, hlen0, hlen1]
          have hmul : (n + 1) * (8 + 8 * 2 ^ 32) = (8 + 8 * 2 ^ 32) + n * (8 + 8 * 2 ^ 32) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          omega

theorem readClaimsN_append (s extra : ByteList) (n : Nat) (hok : (readClaimsN s n).ok = 1) :
    readClaimsN (byteListAppend s extra) n =
      { (readClaimsN s n) with rest := byteListAppend (readClaimsN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readClaimsN] at hok ⊢
    by_cases h0 : (readCount s).ok = 0
    · simp [h0] at hok
    · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
      have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
      rw [readCount_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      set rm := readCount s
      by_cases hvok : (readCanonicalU64VecN rm.rest rm.val).ok = 0
      · simp [hvok] at hok
      · have hvok1 : (readCanonicalU64VecN rm.rest rm.val).ok = 1 :=
          (readCanonicalU64VecN_ok_zero_or_one rm.rest rm.val).resolve_left hvok
        have hvokb : ((readCanonicalU64VecN rm.rest rm.val).ok == 0) = false := beq_false_of_ne hvok
        rw [readCanonicalU64VecN_append rm.rest extra rm.val hvok1]
        simp only [hvokb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        rw [ih _ hok]

/-- **Headline Wire Soundness (`readClaims`)**:
acceptance implies complete consumption (`rest = .nil`), `< 256` validity of all bytes,
canonical `< p_GL` validity of every decoded claim word, automatic byte-length bound
`≤ 1024 * 2^64` (clearing BLAKE3's counter ceiling with zero external assumptions), and
strict canonical trailing-byte rejection on any non-empty suffix `extra`. -/
theorem readClaims_sound (s : ByteList) (hok : (readClaims s).ok = 1) :
    let r := readClaims s
    r.rest = .nil ∧
    ValidBytes s ∧
    CanonicalClaims r.val ∧
    byteListLen s ≤ 1024 * 2 ^ 64 ∧
    (∀ extra : ByteList, extra ≠ .nil → (readClaims (byteListAppend s extra)).ok = 0) := by
  simp only [readClaims] at hok ⊢
  by_cases h0 : (readCount s).ok = 0
  · simp [h0] at hok
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    obtain ⟨c0, hlen0, hv0, hs0, _, hnlt, _⟩ := readCount_sound s h1
    set rn := readCount s
    by_cases hrc : (readClaimsN rn.rest rn.val).ok = 0
    · simp [hrc] at hok
    · have hrc1 : (readClaimsN rn.rest rn.val).ok = 1 :=
        (readClaimsN_ok_zero_or_one rn.rest rn.val).resolve_left hrc
      have hrcb : ((readClaimsN rn.rest rn.val).ok == 0) = false := beq_false_of_ne hrc
      simp only [hrcb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      cases hrest : (readClaimsN rn.rest rn.val).rest with
      | cons _ _ => rw [hrest] at hok; cases hok
      | nil =>
        rw [hrest] at hok ⊢
        obtain ⟨c1, hv1, hs1, hbound1, _, hcan⟩ := readClaimsN_sound rn.rest rn.val hrc1
        rw [hrest, byteListAppend_nil_right] at hs1
        have hsEq : s = byteListAppend c0 c1 := by rw [hs0, hs1]
        have hvS : ValidBytes s := hsEq ▸ validBytes_append.mpr ⟨hv0, hv1⟩
        have hlenS : byteListLen s ≤ 1024 * 2 ^ 64 := by
          rw [hsEq, byteListLen_append, hlen0]
          have hmul : rn.val * (8 + 8 * 2 ^ 32) ≤ 2 ^ 32 * (8 + 8 * 2 ^ 32) :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt hnlt)
          omega
        refine ⟨rfl, hvS, hcan, hlenS, ?_⟩
        intro extra hextra
        rw [readCount_append s extra h1]
        simp only [show ((readCount s).ok == 0) = false from h0b, Bool.false_eq_true, ↓reduceIte]
        rw [readClaimsN_append rn.rest extra rn.val hrc1]
        simp only [hrcb, Bool.false_eq_true, ↓reduceIte, hrest, byteListAppend]
        cases extra with
        | nil => exact absurd rfl hextra
        | cons _ _ => rfl

/-! ### `readSystem` Soundness, Structural VK Well-Formedness & Trailing-Byte Rejection -/

/-- Well-formedness of a single `SysNode` at index `nodeIdx`: canonical `< p_GL` constants,
valid `(src, off)` column selectors (`src < 3`, `off < 2`), and strict DAG acyclicity
(`a < nodeIdx`, `b < nodeIdx`). -/
def SysNodeWellFormed (nodeIdx : Nat) : SysNode → Prop
  | .const v => v < glPrime
  | .var src off _ => src < 3 ∧ off < 2
  | .pub idx => idx < 256
  | .isFirstRow | .isLastRow | .isTransition => True
  | .add a b | .sub a b | .mul a b => a < nodeIdx ∧ b < nodeIdx
  | .neg a => a < nodeIdx

/-- Strict topological ordering and node well-formedness across a `SysNodeList` starting at `start`. -/
def SysNodesTopological (start : Nat) : SysNodeList → Prop
  | .nil => True
  | .cons nd rest => SysNodeWellFormed start nd ∧ SysNodesTopological (start + 1) rest

/-- Structural verifying-key invariants enforced on every `SysCircuit` by `readSystem`,
matching `Ix.Cert.MultiStark.Wire`:
1. `1 ≤ lookupGroupSize ≤ 8` (`MAX_LOOKUP_GROUP`),
2. `sysNodeListLen nodes = nodeCount`,
3. strict topological DAG order (`SysNodesTopological 0 nodes`),
4. `prepWidth = 0 ↔ prepHeight = 0`,
5. exact power-of-two `prepHeight` (`0` or `2^k` for `k < 32`),
6. exact `stage2Width = 3 * max 1 (lookupGroupsCount ...)`. -/
structure SysCircuitWellFormed (c : SysCircuit) : Prop where
  lookupGroupSize_pos : 1 ≤ c.lookupGroupSize
  lookupGroupSize_le : c.lookupGroupSize ≤ 8
  nodeCount_eq : sysNodeListLen c.nodes = c.nodeCount
  topological : SysNodesTopological 0 c.nodes
  prep_zero_iff : c.prepWidth = 0 ↔ c.prepHeight = 0
  prepHeight_pow2 : c.prepHeight = 0 ∨ ∃ k < 32, c.prepHeight = 2 ^ k
  stage2Width_eq :
    let g := lookupGroupsCount (sysLookupListLen c.lookups) 0 c.lookupGroupSize
    let slots := if g == 0 then 1 else g
    c.stage2Width = slots + slots + slots

/-- Every circuit in `SysCircuitList` satisfies `SysCircuitWellFormed`. -/
def SysCircuitsWellFormed : SysCircuitList → Prop
  | .nil => True
  | .cons c rest => SysCircuitWellFormed c ∧ SysCircuitsWellFormed rest

/-- Every entry in `OptIdxList` is `.noIdx`. -/
def OptIdxAllNone : OptIdxList → Prop
  | .nil => True
  | .cons .noIdx rest => OptIdxAllNone rest
  | .cons (.someIdx _) _ => False

/-- Strict sequential ranking (`0, 1, 2, ...`) of `.someIdx` entries starting at `cnt`. -/
def OptIdxRanked (cnt : Nat) : OptIdxList → Prop
  | .nil => True
  | .cons .noIdx rest => OptIdxRanked cnt rest
  | .cons (.someIdx v) rest => v = cnt ∧ OptIdxRanked (cnt + 1) rest

/-- Structural verifying-key well-formedness enforced by `StarkWire.readSystem`. -/
structure SysKeyWellFormed (sys : SysKey) : Prop where
  circuits_wf : SysCircuitsWellFormed sys.circuits
  prepIndices_len : optIdxListLen sys.prepIndices = sysCircuitListLen sys.circuits
  noCommit_implies_noIdx : sys.prepCommit = .noCommit → OptIdxAllNone sys.prepIndices
  someCommit_cap_len : ∀ cap, sys.prepCommit = .someCommit cap → digestBytesListLen cap = 1
  prepIndices_ranked : OptIdxRanked 0 sys.prepIndices

private theorem prod_ne_zero {a b : Nat} (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  not_or.mp (mt mul_eq_zero.mpr h)

private theorem readVkCapN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readVkCapN s n).ok = 0 ∨ (readVkCapN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readVkCapN]
    split
    · exact Or.inl rfl
    · exact ih _

private theorem readVkCapN_sound (s : ByteList) (n : Nat) (hok : (readVkCapN s n).ok = 1) :
    let r := readVkCapN s n
    ∃ consumed : ByteList,
      byteListLen consumed = 32 * n ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      digestBytesListLen r.val = n := by
  induction n generalizing s with
  | zero => exact ⟨.nil, rfl, trivial, rfl, rfl⟩
  | succ n ih =>
    simp only [readVkCapN] at hok ⊢
    by_cases h0 : (readDigest s).ok = 0
    · simp [h0] at hok
    · have h1 : (readDigest s).ok = 1 := (readDigest_ok_zero_or_one s).resolve_left h0
      have h0b : ((readDigest s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨hv0, hs0, _⟩ := readDigest_sound s h1
      obtain ⟨c, hlen, hvc, hst, hdl⟩ := ih (readDigest s).rest hok
      refine ⟨digestBytesOnto (readDigest s).val c, ?_, ?_, ?_, by simp [digestBytesListLen, hdl]; omega⟩
      · simp only [byteListLen_digestBytesOnto, hlen]; omega
      · exact validBytes_u64BytesOnto.mpr ⟨hv0.1, validBytes_u64BytesOnto.mpr ⟨hv0.2.1,
          validBytes_u64BytesOnto.mpr ⟨hv0.2.2.1, validBytes_u64BytesOnto.mpr ⟨hv0.2.2.2, hvc⟩⟩⟩⟩
      · rw [digestBytesOnto_append, ← hst, ← hs0]

private theorem readVkCapN_append (s extra : ByteList) (n : Nat) (hok : (readVkCapN s n).ok = 1) :
    readVkCapN (byteListAppend s extra) n =
      { (readVkCapN s n) with rest := byteListAppend (readVkCapN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readVkCapN] at hok ⊢
    by_cases h0 : (readDigest s).ok = 0
    · simp [h0] at hok
    · have h1 : (readDigest s).ok = 1 := (readDigest_ok_zero_or_one s).resolve_left h0
      have h0b : ((readDigest s).ok == 0) = false := beq_false_of_ne h0
      rw [readDigest_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih (readDigest s).rest hok]

private theorem readOneSysNode_ok_zero_or_one (s : ByteList) (nodeIdx : Nat) :
    (readOneSysNode s nodeIdx).ok = 0 ∨ (readOneSysNode s nodeIdx).ok = 1 := by
  unfold readOneSysNode
  dsimp only
  by_cases h0 : ((readU8 s).ok == 0) = true
  · rw [ite_eq_left h0]; exact Or.inl rfl
  · rw [ite_eq_right h0]
    by_cases h1 : ((readU8 s).val == 0) = true
    · rw [ite_eq_left h1]; exact readLeNatAux_ok_zero_or_one 2 _ 1 0
    · rw [ite_eq_right h1]
      by_cases h2 : ((readU8 s).val == 1) = true
      · rw [ite_eq_left h2]; exact readGlCanonical_ok_zero_or_one _
      · rw [ite_eq_right h2]
        by_cases h3 : ((readU8 s).val == 2) = true
        · rw [ite_eq_left h3]; exact readLeNatAux_ok_zero_or_one 1 _ 1 0
        · rw [ite_eq_right h3]
          by_cases h4 : ((readU8 s).val == 3) = true
          · rw [ite_eq_left h4]; exact Or.inr rfl
          · rw [ite_eq_right h4]
            by_cases h5 : ((readU8 s).val == 4) = true
            · rw [ite_eq_left h5]; exact Or.inr rfl
            · rw [ite_eq_right h5]
              by_cases h6 : ((readU8 s).val == 5) = true
              · rw [ite_eq_left h6]; exact Or.inr rfl
              · rw [ite_eq_right h6]
                by_cases h7 : (readU8 s).val < 9
                · rw [ite_eq_left h7]
                  by_cases hc :
                      (((readU16LE (readU8 s).rest).ok *
                          (readU16LE (readU16LE (readU8 s).rest).rest).ok == 1) &&
                        decide ((readU16LE (readU8 s).rest).val < nodeIdx) &&
                        decide ((readU16LE (readU16LE (readU8 s).rest).rest).val < nodeIdx)) = true
                  · rw [ite_eq_left hc]; exact Or.inr rfl
                  · rw [ite_eq_right hc]; exact Or.inl rfl
                · rw [ite_eq_right h7]
                  by_cases h8 : ((readU8 s).val == 9) = true
                  · rw [ite_eq_left h8]
                    by_cases hc :
                        (((readU16LE (readU8 s).rest).ok == 1) &&
                          decide ((readU16LE (readU8 s).rest).val < nodeIdx)) = true
                    · rw [ite_eq_left hc]; exact Or.inr rfl
                    · rw [ite_eq_right hc]; exact Or.inl rfl
                  · rw [ite_eq_right h8]
                    by_cases h9 : (readU8 s).val < 16
                    · rw [ite_eq_left h9]; exact readLeNatAux_ok_zero_or_one 2 _ 1 0
                    · rw [ite_eq_right h9]; exact Or.inl rfl

private theorem readOneSysNode_sound (s : ByteList) (nodeIdx : Nat)
    (hok : (readOneSysNode s nodeIdx).ok = 1) :
    let r := readOneSysNode s nodeIdx
    ∃ consumed : ByteList,
      byteListLen consumed ≤ 9 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      SysNodeWellFormed nodeIdx r.val := by
  simp only [readOneSysNode] at hok ⊢
  by_cases ht0 : (readU8 s).ok = 0
  · simp [ht0] at hok
  · have ht1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left ht0
    have ht0b : ((readU8 s).ok == 0) = false := beq_false_of_ne ht0
    simp only [ht0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    obtain ⟨htlt, hst, _⟩ := readU8_sound s ht1
    set rt := readU8 s
    by_cases h0 : rt.val = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c, hlen, hvc, hsc, _, _, hlt⟩ := readU16LE_sound rt.rest hok
      refine ⟨.cons rt.val c, by simp [byteListLen, hlen], ⟨htlt, hvc⟩, ?_, ?_⟩
      · simp only [byteListAppend]; rw [← hsc, ← hst]
      · simp only [SysNodeWellFormed, glPrime_val]; omega
    · have h0b : (rt.val == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases h1 : rt.val = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte] at hok ⊢
        obtain ⟨w, hvw, _, _, hvlt, hsw, _⟩ := readGlCanonical_sound rt.rest hok
        refine ⟨.cons rt.val (u64BytesOnto w .nil), by simp only [byteListLen, byteListLen_u64BytesOnto]; omega,
          ⟨htlt, validBytes_u64BytesOnto.mpr ⟨hvw, trivial⟩⟩, ?_, hvlt⟩
        simp only [byteListAppend, u64BytesOnto_append]; rw [← hsw, ← hst]
      · have h1b : (rt.val == 1) = false := beq_false_of_ne h1
        simp only [h1b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases h2 : rt.val = 2
        · simp only [h2, beq_self_eq_true, ↓reduceIte] at hok ⊢
          obtain ⟨hilt, hsi, _⟩ := readU8_sound rt.rest hok
          refine ⟨.cons rt.val (.cons (readU8 rt.rest).val .nil), by simp [byteListLen],
            ⟨htlt, hilt, trivial⟩, ?_, hilt⟩
          simp only [byteListAppend]; rw [← hsi, ← hst]
        · have h2b : (rt.val == 2) = false := beq_false_of_ne h2
          simp only [h2b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          by_cases h3 : rt.val = 3
          · simp only [h3, beq_self_eq_true, ↓reduceIte]
            exact ⟨.cons rt.val .nil, by simp [byteListLen], ⟨htlt, trivial⟩, by simp only [byteListAppend]; exact hst, trivial⟩
          · have h3b : (rt.val == 3) = false := beq_false_of_ne h3
            simp only [h3b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
            by_cases h4 : rt.val = 4
            · simp only [h4, beq_self_eq_true, ↓reduceIte]
              exact ⟨.cons rt.val .nil, by simp [byteListLen], ⟨htlt, trivial⟩, by simp only [byteListAppend]; exact hst, trivial⟩
            · have h4b : (rt.val == 4) = false := beq_false_of_ne h4
              simp only [h4b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
              by_cases h5 : rt.val = 5
              · simp only [h5, beq_self_eq_true, ↓reduceIte]
                exact ⟨.cons rt.val .nil, by simp [byteListLen], ⟨htlt, trivial⟩, by simp only [byteListAppend]; exact hst, trivial⟩
              · have h5b : (rt.val == 5) = false := beq_false_of_ne h5
                simp only [h5b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                by_cases h9 : rt.val < 9
                · simp only [h9, ↓reduceIte] at hok ⊢
                  set ra := readU16LE rt.rest
                  set rb := readU16LE ra.rest
                  by_cases hcond : ((ra.ok * rb.ok == 1) && decide (ra.val < nodeIdx) && decide (rb.val < nodeIdx)) = true
                  · simp only [hcond, ↓reduceIte]
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
                    obtain ⟨⟨hab, haLt⟩, hbLt⟩ := hcond
                    obtain ⟨ha1, hb1⟩ := mul_eq_one_of_le_one hab
                    obtain ⟨ca, hla, hva, hsa, _, _, _⟩ := readU16LE_sound rt.rest ha1
                    obtain ⟨cb, hlb, hvb, hsb, _, _, _⟩ := readU16LE_sound ra.rest hb1
                    refine ⟨.cons rt.val (byteListAppend ca cb), by simp [byteListLen, byteListLen_append, hla, hlb],
                      ⟨htlt, validBytes_append.mpr ⟨hva, hvb⟩⟩, ?_, ?_⟩
                    · simp only [byteListAppend, byteListAppend_assoc]; rw [← hsb, ← hsa, ← hst]
                    · split
                      · exact ⟨haLt, hbLt⟩
                      · split <;> exact ⟨haLt, hbLt⟩
                  · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
                · simp only [h9, ↓reduceIte] at hok ⊢
                  by_cases heq9 : rt.val = 9
                  · simp only [heq9, beq_self_eq_true, ↓reduceIte] at hok ⊢
                    set ra := readU16LE rt.rest
                    by_cases hcond : ((ra.ok == 1) && decide (ra.val < nodeIdx)) = true
                    · simp only [hcond, ↓reduceIte]
                      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
                      obtain ⟨ca, hla, hva, hsa, _, _, _⟩ := readU16LE_sound rt.rest hcond.1
                      refine ⟨.cons rt.val ca, by simp [byteListLen, hla], ⟨htlt, hva⟩, ?_, hcond.2⟩
                      simp only [byteListAppend]; rw [← hsa, ← hst]
                    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
                  · have h9b : (rt.val == 9) = false := beq_false_of_ne heq9
                    simp only [h9b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                    by_cases h16 : rt.val < 16
                    · simp only [h16, ↓reduceIte] at hok ⊢
                      obtain ⟨ci, hli, hvi, hsi, _, _, _⟩ := readU16LE_sound rt.rest hok
                      refine ⟨.cons rt.val ci, by simp [byteListLen, hli], ⟨htlt, hvi⟩, ?_, ?_⟩
                      · simp only [byteListAppend]; rw [← hsi, ← hst]
                      · simp only [SysNodeWellFormed]; omega
                    · simp only [h16, ↓reduceIte] at hok; cases hok

private theorem readOneSysNode_append (s extra : ByteList) (nodeIdx : Nat)
    (hok : (readOneSysNode s nodeIdx).ok = 1) :
    readOneSysNode (byteListAppend s extra) nodeIdx =
      { (readOneSysNode s nodeIdx) with rest := byteListAppend (readOneSysNode s nodeIdx).rest extra } := by
  simp only [readOneSysNode] at hok ⊢
  by_cases ht0 : (readU8 s).ok = 0
  · simp [ht0] at hok
  · have ht1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left ht0
    have ht0b : ((readU8 s).ok == 0) = false := beq_false_of_ne ht0
    rw [readU8_append s extra ht1]
    simp only [ht0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    set rt := readU8 s
    by_cases h0 : rt.val = 0
    · simp only [h0, beq_self_eq_true, ↓reduceIte] at hok ⊢
      rw [readU16LE_append rt.rest extra hok]
    · have h0b : (rt.val == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases h1 : rt.val = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte] at hok ⊢
        rw [readGlCanonical_append rt.rest extra hok]
      · have h1b : (rt.val == 1) = false := beq_false_of_ne h1
        simp only [h1b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases h2 : rt.val = 2
        · simp only [h2, beq_self_eq_true, ↓reduceIte] at hok ⊢
          rw [readU8_append rt.rest extra hok]
        · have h2b : (rt.val == 2) = false := beq_false_of_ne h2
          simp only [h2b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          by_cases h3 : rt.val = 3
          · simp only [h3, beq_self_eq_true, ↓reduceIte]
          · have h3b : (rt.val == 3) = false := beq_false_of_ne h3
            simp only [h3b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
            by_cases h4 : rt.val = 4
            · simp only [h4, beq_self_eq_true, ↓reduceIte]
            · have h4b : (rt.val == 4) = false := beq_false_of_ne h4
              simp only [h4b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
              by_cases h5 : rt.val = 5
              · simp only [h5, beq_self_eq_true, ↓reduceIte]
              · have h5b : (rt.val == 5) = false := beq_false_of_ne h5
                simp only [h5b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                by_cases h9 : rt.val < 9
                · simp only [h9, ↓reduceIte] at hok ⊢
                  set ra := readU16LE rt.rest
                  set rb := readU16LE ra.rest
                  by_cases hcond : ((ra.ok * rb.ok == 1) && decide (ra.val < nodeIdx) && decide (rb.val < nodeIdx)) = true
                  · simp only [hcond, ↓reduceIte]
                    have hc := hcond
                    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
                    obtain ⟨ha1, hb1⟩ := mul_eq_one_of_le_one hc.1.1
                    rw [readU16LE_append rt.rest extra ha1, readU16LE_append ra.rest extra hb1]
                    change (if ((ra.ok * rb.ok == 1) && decide (ra.val < nodeIdx) && decide (rb.val < nodeIdx)) = true then _ else _) = _
                    simp only [hcond, ↓reduceIte]
                    rfl
                  · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
                · simp only [h9, ↓reduceIte] at hok ⊢
                  by_cases heq9 : rt.val = 9
                  · simp only [heq9, beq_self_eq_true, ↓reduceIte] at hok ⊢
                    set ra := readU16LE rt.rest
                    by_cases hcond : ((ra.ok == 1) && decide (ra.val < nodeIdx)) = true
                    · simp only [hcond, ↓reduceIte]
                      have hc := hcond
                      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
                      rw [readU16LE_append rt.rest extra hc.1]
                      change (if ((ra.ok == 1) && decide (ra.val < nodeIdx)) = true then _ else _) = _
                      simp only [hcond, ↓reduceIte]
                      rfl
                    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
                  · have h9b : (rt.val == 9) = false := beq_false_of_ne heq9
                    simp only [h9b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                    by_cases h16 : rt.val < 16
                    · simp only [h16, ↓reduceIte] at hok ⊢
                      rw [readU16LE_append rt.rest extra hok]
                    · simp only [h16, ↓reduceIte] at hok; cases hok

private theorem readSysNodesN_ok_zero_or_one (s : ByteList) (n start : Nat) :
    (readSysNodesN s n start).ok = 0 ∨ (readSysNodesN s n start).ok = 1 := by
  induction n generalizing s start with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readSysNodesN]
    split
    · exact Or.inl rfl
    · exact ih _ _

private theorem readSysNodesN_sound (s : ByteList) (n start : Nat)
    (hok : (readSysNodesN s n start).ok = 1) :
    let r := readSysNodesN s n start
    ∃ consumed : ByteList,
      byteListLen consumed ≤ 9 * n ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      sysNodeListLen r.val = n ∧
      SysNodesTopological start r.val := by
  induction n generalizing s start with
  | zero => exact ⟨.nil, by simp [byteListLen], trivial, rfl, rfl, trivial⟩
  | succ n ih =>
    simp only [readSysNodesN] at hok ⊢
    by_cases h0 : (readOneSysNode s start).ok = 0
    · simp [h0] at hok
    · have h1 : (readOneSysNode s start).ok = 1 :=
        (readOneSysNode_ok_zero_or_one s start).resolve_left h0
      have h0b : ((readOneSysNode s start).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hl0, hv0, hs0, hwf0⟩ := readOneSysNode_sound s start h1
      obtain ⟨c1, hl1, hv1, hs1, hnl1, htop1⟩ := ih (readOneSysNode s start).rest (start + 1) hok
      refine ⟨byteListAppend c0 c1, by rw [byteListLen_append]; omega,
        validBytes_append.mpr ⟨hv0, hv1⟩, by rw [byteListAppend_assoc, ← hs1, ← hs0],
        by simp [sysNodeListLen, hnl1]; omega, ⟨hwf0, htop1⟩⟩

private theorem readSysNodesN_append (s extra : ByteList) (n start : Nat)
    (hok : (readSysNodesN s n start).ok = 1) :
    readSysNodesN (byteListAppend s extra) n start =
      { (readSysNodesN s n start) with rest := byteListAppend (readSysNodesN s n start).rest extra } := by
  induction n generalizing s start with
  | zero => rfl
  | succ n ih =>
    simp only [readSysNodesN] at hok ⊢
    by_cases h0 : (readOneSysNode s start).ok = 0
    · simp [h0] at hok
    · have h1 : (readOneSysNode s start).ok = 1 :=
        (readOneSysNode_ok_zero_or_one s start).resolve_left h0
      have h0b : ((readOneSysNode s start).ok == 0) = false := beq_false_of_ne h0
      rw [readOneSysNode_append s extra start h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih _ _ hok]

private theorem readNodeIdsN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readNodeIdsN s n).ok = 0 ∨ (readNodeIdsN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readNodeIdsN]; split; exact Or.inl rfl; exact ih _

private theorem readNodeIdsN_sound (s : ByteList) (n : Nat) (hok : (readNodeIdsN s n).ok = 1) :
    let r := readNodeIdsN s n
    ∃ consumed : ByteList,
      byteListLen consumed = 2 * n ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      natListLen r.val = n := by
  induction n generalizing s with
  | zero => exact ⟨.nil, rfl, trivial, rfl, rfl⟩
  | succ n ih =>
    simp only [readNodeIdsN] at hok ⊢
    by_cases h0 : (readU16LE s).ok = 0
    · simp [h0] at hok
    · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
      have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hl0, hv0, hs0, _, _, _⟩ := readU16LE_sound s h1
      obtain ⟨c1, hl1, hv1, hs1, hnl1⟩ := ih (readU16LE s).rest hok
      refine ⟨byteListAppend c0 c1, by rw [byteListLen_append, hl0, hl1]; omega,
        validBytes_append.mpr ⟨hv0, hv1⟩, by rw [byteListAppend_assoc, ← hs1, ← hs0],
        by simp [natListLen, hnl1]; omega⟩

private theorem readNodeIdsN_append (s extra : ByteList) (n : Nat) (hok : (readNodeIdsN s n).ok = 1) :
    readNodeIdsN (byteListAppend s extra) n =
      { (readNodeIdsN s n) with rest := byteListAppend (readNodeIdsN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readNodeIdsN] at hok ⊢
    by_cases h0 : (readU16LE s).ok = 0
    · simp [h0] at hok
    · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
      have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
      rw [readU16LE_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih _ hok]

private theorem readSysLookup_ok_zero_or_one (s : ByteList) :
    (readSysLookup s).ok = 0 ∨ (readSysLookup s).ok = 1 := by
  simp only [readSysLookup]
  split; exact Or.inl rfl
  split; exact Or.inl rfl
  exact readNodeIdsN_ok_zero_or_one _ _

private theorem readSysLookup_sound (s : ByteList) (hok : (readSysLookup s).ok = 1) :
    let r := readSysLookup s
    ∃ consumed : ByteList,
      byteListLen consumed ≤ 4 + 2 * 2 ^ 16 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest := by
  simp only [readSysLookup] at hok ⊢
  by_cases h0 : (readU16LE s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
    have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    obtain ⟨c0, hl0, hv0, hs0, _, _, _⟩ := readU16LE_sound s h1
    set rm := readU16LE s
    by_cases ha0 : (readU16LE rm.rest).ok = 0
    · simp [ha0] at hok
    · have ha1 : (readU16LE rm.rest).ok = 1 := (readLeNatAux_ok_zero_or_one 2 rm.rest 1 0).resolve_left ha0
      have ha0b : ((readU16LE rm.rest).ok == 0) = false := beq_false_of_ne ha0
      simp only [ha0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c1, hl1, hv1, hs1, _, _, hlt1⟩ := readU16LE_sound rm.rest ha1
      obtain ⟨c2, hl2, hv2, hs2, _⟩ := readNodeIdsN_sound (readU16LE rm.rest).rest (readU16LE rm.rest).val hok
      refine ⟨byteListAppend c0 (byteListAppend c1 c2), ?_,
        validBytes_append.mpr ⟨hv0, validBytes_append.mpr ⟨hv1, hv2⟩⟩,
        by rw [byteListAppend_assoc, byteListAppend_assoc, ← hs2, ← hs1, ← hs0]⟩
      simp only [byteListLen_append, hl0, hl1, hl2]; omega

private theorem readSysLookup_append (s extra : ByteList) (hok : (readSysLookup s).ok = 1) :
    readSysLookup (byteListAppend s extra) =
      { (readSysLookup s) with rest := byteListAppend (readSysLookup s).rest extra } := by
  simp only [readSysLookup] at hok ⊢
  by_cases h0 : (readU16LE s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
    have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
    rw [readU16LE_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    set rm := readU16LE s
    by_cases ha0 : (readU16LE rm.rest).ok = 0
    · simp [ha0] at hok
    · have ha1 : (readU16LE rm.rest).ok = 1 := (readLeNatAux_ok_zero_or_one 2 rm.rest 1 0).resolve_left ha0
      have ha0b : ((readU16LE rm.rest).ok == 0) = false := beq_false_of_ne ha0
      rw [readU16LE_append rm.rest extra ha1]
      simp only [ha0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [readNodeIdsN_append _ extra _ hok]

private theorem readSysLookupsN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readSysLookupsN s n).ok = 0 ∨ (readSysLookupsN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readSysLookupsN]; split; exact Or.inl rfl; exact ih _

private theorem readSysLookupsN_sound (s : ByteList) (n : Nat) (hok : (readSysLookupsN s n).ok = 1) :
    let r := readSysLookupsN s n
    ∃ consumed : ByteList,
      byteListLen consumed ≤ n * (4 + 2 * 2 ^ 16) ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      sysLookupListLen r.val = n := by
  induction n generalizing s with
  | zero => exact ⟨.nil, by simp [byteListLen], trivial, rfl, rfl⟩
  | succ n ih =>
    simp only [readSysLookupsN] at hok ⊢
    by_cases h0 : (readSysLookup s).ok = 0
    · simp [h0] at hok
    · have h1 : (readSysLookup s).ok = 1 := (readSysLookup_ok_zero_or_one s).resolve_left h0
      have h0b : ((readSysLookup s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hl0, hv0, hs0⟩ := readSysLookup_sound s h1
      obtain ⟨c1, hl1, hv1, hs1, hll1⟩ := ih (readSysLookup s).rest hok
      refine ⟨byteListAppend c0 c1, ?_, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0], by simp [sysLookupListLen, hll1]; omega⟩
      rw [byteListLen_append]
      have hmul : (n + 1) * (4 + 2 * 2 ^ 16) = (4 + 2 * 2 ^ 16) + n * (4 + 2 * 2 ^ 16) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega

private theorem readSysLookupsN_append (s extra : ByteList) (n : Nat) (hok : (readSysLookupsN s n).ok = 1) :
    readSysLookupsN (byteListAppend s extra) n =
      { (readSysLookupsN s n) with rest := byteListAppend (readSysLookupsN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readSysLookupsN] at hok ⊢
    by_cases h0 : (readSysLookup s).ok = 0
    · simp [h0] at hok
    · have h1 : (readSysLookup s).ok = 1 := (readSysLookup_ok_zero_or_one s).resolve_left h0
      have h0b : ((readSysLookup s).ok == 0) = false := beq_false_of_ne h0
      rw [readSysLookup_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih _ hok]

private theorem readSysCircuit_ok_zero_or_one (s : ByteList) :
    (readSysCircuit s).ok = 0 ∨ (readSysCircuit s).ok = 1 := by
  simp only [readSysCircuit]
  split; exact Or.inl rfl
  split; exact Or.inl rfl
  exact Or.inr rfl

private theorem readSysCircuit_sound (s : ByteList) (hok : (readSysCircuit s).ok = 1) :
    let r := readSysCircuit s
    ∃ consumed : ByteList,
      byteListLen consumed ≤ 2 ^ 34 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      SysCircuitWellFormed r.val := by
  simp only [readSysCircuit] at hok ⊢
  set rmw := readU16Limb s
  set rpw := readU16Limb rmw.rest
  set rph := readU32Limb rpw.rest
  set rmd := readU16Limb rph.rest
  set rk  := readU8 rmd.rest
  set rnc := readU16LE rk.rest
  set rlp := readU16LE rnc.rest
  set hdrOk := rmw.ok * rpw.ok * rph.ok * rmd.ok * rk.ok * rnc.ok * rlp.ok
  set prepZeroMatch := (rpw.val == 0) == (rph.val == 0)
  set phPop := bytePopcount rph.limb.b0 + bytePopcount rph.limb.b1 +
               bytePopcount rph.limb.b2 + bytePopcount rph.limb.b3
  by_cases hbad1 : ((hdrOk == 0) || (rk.val == 0) || decide (rk.val ≥ 9) ||
      decide (rlp.val > rnc.val) || !prepZeroMatch || decide (phPop > 1)) = true
  · simp only [hbad1, ↓reduceIte] at hok; cases hok
  · have hbad1F : ((hdrOk == 0) || (rk.val == 0) || decide (rk.val ≥ 9) ||
        decide (rlp.val > rnc.val) || !prepZeroMatch || decide (phPop > 1)) = false :=
      Bool.eq_false_iff.mpr hbad1
    simp only [hbad1F, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne, decide_eq_false_iff_not] at hbad1F
    obtain ⟨⟨⟨⟨⟨hhdr, hrk0⟩, hrk9⟩, _⟩, hprepM⟩, hpop⟩ := hbad1F
    have h6 := prod_ne_zero hhdr
    have h5 := prod_ne_zero h6.1
    have h4 := prod_ne_zero h5.1
    have h3 := prod_ne_zero h4.1
    have h2 := prod_ne_zero h3.1
    have h1 := prod_ne_zero h2.1
    have hmw1 : rmw.ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h1.1
    have hpw1 : rpw.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rmw.rest 1 0).resolve_left h1.2
    have hph1 : rph.ok = 1 := (readLeNatAux_ok_zero_or_one 4 rpw.rest 1 0).resolve_left h2.2
    have hmd1 : rmd.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rph.rest 1 0).resolve_left h3.2
    have hrk1 : rk.ok = 1 := (readLeNatAux_ok_zero_or_one 1 rmd.rest 1 0).resolve_left h4.2
    have hnc1 : rnc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rk.rest 1 0).resolve_left h5.2
    have hlp1 : rlp.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rnc.rest 1 0).resolve_left h6.2
    set rnodes := readSysNodesN rlp.rest rnc.val 0
    set rzc := readU16LE rnodes.rest
    set rzeros := readNodeIdsN rzc.rest rzc.val
    set rlc := readU16LE rzeros.rest
    set rlks := readSysLookupsN rlc.rest rlc.val
    set bodyOk := rnodes.ok * rzc.ok * rzeros.ok * rlc.ok * rlks.ok
    by_cases hbad2 : bodyOk = 0
    · simp [hbad2] at hok
    · have hbad2b : (bodyOk == 0) = false := beq_false_of_ne hbad2
      simp only [hbad2b, Bool.false_eq_true, ↓reduceIte]
      have hb4 := prod_ne_zero hbad2
      have hb3 := prod_ne_zero hb4.1
      have hb2 := prod_ne_zero hb3.1
      have hb1 := prod_ne_zero hb2.1
      have hnd1 : rnodes.ok = 1 := (readSysNodesN_ok_zero_or_one rlp.rest rnc.val 0).resolve_left hb1.1
      have hzc1 : rzc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rnodes.rest 1 0).resolve_left hb1.2
      have hzr1 : rzeros.ok = 1 := (readNodeIdsN_ok_zero_or_one rzc.rest rzc.val).resolve_left hb2.2
      have hlc1 : rlc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rzeros.rest 1 0).resolve_left hb3.2
      have hlk1 : rlks.ok = 1 := (readSysLookupsN_ok_zero_or_one rlc.rest rlc.val).resolve_left hb4.2
      obtain ⟨cmw, hlmw, hvmw, hsmw, _, _, _, _, _⟩ := readU16Limb_sound s hmw1
      obtain ⟨cpw, hlpw, hvpw, hspw, _, _, _, _, _⟩ := readU16Limb_sound rmw.rest hpw1
      obtain ⟨cph, hlph, hvph, hsph, _, _, hphlt, _, _⟩ := readU32Limb_sound rpw.rest hph1
      obtain ⟨cmd, hlmd, hvmd, hsmd, _, _, _, _, _⟩ := readU16Limb_sound rph.rest hmd1
      obtain ⟨hvkk, hsk, _⟩ := readU8_sound rmd.rest hrk1
      obtain ⟨cnc, hlnc, hvnc, hsnc, _, _, hnclt⟩ := readU16LE_sound rk.rest hnc1
      obtain ⟨clp, hllp, hvlp, hslp, _, _, _⟩ := readU16LE_sound rnc.rest hlp1
      obtain ⟨cnd, hlnd, hvnd, hsnd, hndLen, htop⟩ := readSysNodesN_sound rlp.rest rnc.val 0 hnd1
      obtain ⟨czc, hlzc, hvzc, hszc, _, _, hzclt⟩ := readU16LE_sound rnodes.rest hzc1
      obtain ⟨czr, hlzr, hvzr, hszr, _⟩ := readNodeIdsN_sound rzc.rest rzc.val hzr1
      obtain ⟨clc, hllc, hvlc, hslc, _, _, hlclt⟩ := readU16LE_sound rzeros.rest hlc1
      obtain ⟨clk, hllk, hvlk, hslk, hlkLen⟩ := readSysLookupsN_sound rlc.rest rlc.val hlk1
      change rph.val < 2 ^ 32 at hphlt
      change rnc.val < 2 ^ 16 at hnclt
      change rzc.val < 2 ^ 16 at hzclt
      change rlc.val < 2 ^ 16 at hlclt
      change byteListLen cnd ≤ 9 * rnc.val at hlnd
      change byteListLen czr = 2 * rzc.val at hlzr
      change byteListLen clk ≤ rlc.val * (4 + 2 * 2 ^ 16) at hllk
      refine ⟨byteListAppend cmw (byteListAppend cpw (byteListAppend cph (byteListAppend cmd
        (.cons rk.val (byteListAppend cnc (byteListAppend clp (byteListAppend cnd
          (byteListAppend czc (byteListAppend czr (byteListAppend clc clk)))))))))),
        ?_, ?_, ?_, ?_⟩
      · simp only [byteListLen_append, byteListLen, hlmw, hlpw, hlph, hlmd, hlnc, hllp, hlzc, hlzr, hllc]
        have h1' : rlc.val * (4 + 2 * 2 ^ 16) ≤ 2 ^ 16 * (4 + 2 * 2 ^ 16) :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt hlclt)
        omega
      · exact validBytes_append.mpr ⟨hvmw, validBytes_append.mpr ⟨hvpw, validBytes_append.mpr ⟨hvph,
          validBytes_append.mpr ⟨hvmd, ⟨hvkk, validBytes_append.mpr ⟨hvnc, validBytes_append.mpr ⟨hvlp,
            validBytes_append.mpr ⟨hvnd, validBytes_append.mpr ⟨hvzc, validBytes_append.mpr ⟨hvzr,
              validBytes_append.mpr ⟨hvlc, hvlk⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
      · simp only [byteListAppend_assoc, byteListAppend]
        rw [← hslk, ← hslc, ← hszr, ← hszc, ← hsnd, ← hslp, ← hsnc, ← hsk, ← hsmd, ← hsph, ← hspw, ← hsmw]
      · refine ⟨Nat.pos_of_ne_zero hrk0, Nat.le_of_lt_succ (Nat.lt_of_not_ge hrk9), hndLen, htop, ?_, ?_, ?_⟩
        · simp only [prepZeroMatch, beq_iff_eq] at hprepM
          constructor <;> intro h
          · have hpw0 : (rpw.val == 0) = true := beq_iff_eq.mpr h
            have hph0 : (rph.val == 0) = true := hprepM.symm.trans hpw0
            exact beq_iff_eq.mp hph0
          · have hph0 : (rph.val == 0) = true := beq_iff_eq.mpr h
            have hpw0 : (rpw.val == 0) = true := hprepM.trans hph0
            exact beq_iff_eq.mp hpw0
        · have hpopLe : phPop ≤ 1 := by omega
          exact (u32_popcount_le_one_iff hphlt).mp hpopLe
        · change sysLookupListLen rlks.val = rlc.val at hlkLen
          dsimp only
          rw [hlkLen]

private theorem readSysCircuit_append (s extra : ByteList) (hok : (readSysCircuit s).ok = 1) :
    readSysCircuit (byteListAppend s extra) =
      { (readSysCircuit s) with rest := byteListAppend (readSysCircuit s).rest extra } := by
  simp only [readSysCircuit] at hok ⊢
  set rmw := readU16Limb s
  set rpw := readU16Limb rmw.rest
  set rph := readU32Limb rpw.rest
  set rmd := readU16Limb rph.rest
  set rk  := readU8 rmd.rest
  set rnc := readU16LE rk.rest
  set rlp := readU16LE rnc.rest
  set hdrOk := rmw.ok * rpw.ok * rph.ok * rmd.ok * rk.ok * rnc.ok * rlp.ok
  set prepZeroMatch := (rpw.val == 0) == (rph.val == 0)
  set phPop := bytePopcount rph.limb.b0 + bytePopcount rph.limb.b1 +
               bytePopcount rph.limb.b2 + bytePopcount rph.limb.b3
  by_cases hbad1 : ((hdrOk == 0) || (rk.val == 0) || decide (rk.val ≥ 9) ||
      decide (rlp.val > rnc.val) || !prepZeroMatch || decide (phPop > 1)) = true
  · simp only [hbad1, ↓reduceIte] at hok; cases hok
  · have hbad1F : ((hdrOk == 0) || (rk.val == 0) || decide (rk.val ≥ 9) ||
        decide (rlp.val > rnc.val) || !prepZeroMatch || decide (phPop > 1)) = false :=
      Bool.eq_false_iff.mpr hbad1
    have hbad1F' := hbad1F
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne, decide_eq_false_iff_not] at hbad1F'
    have hhdr := hbad1F'.1.1.1.1.1
    have h6 := prod_ne_zero hhdr
    have h5 := prod_ne_zero h6.1
    have h4 := prod_ne_zero h5.1
    have h3 := prod_ne_zero h4.1
    have h2 := prod_ne_zero h3.1
    have h1 := prod_ne_zero h2.1
    have hmw1 : rmw.ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h1.1
    have hpw1 : rpw.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rmw.rest 1 0).resolve_left h1.2
    have hph1 : rph.ok = 1 := (readLeNatAux_ok_zero_or_one 4 rpw.rest 1 0).resolve_left h2.2
    have hmd1 : rmd.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rph.rest 1 0).resolve_left h3.2
    have hrk1 : rk.ok = 1 := (readLeNatAux_ok_zero_or_one 1 rmd.rest 1 0).resolve_left h4.2
    have hnc1 : rnc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rk.rest 1 0).resolve_left h5.2
    have hlp1 : rlp.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rnc.rest 1 0).resolve_left h6.2
    rw [readU16Limb_append s extra hmw1,
        readU16Limb_append rmw.rest extra hpw1,
        readU32Limb_append rpw.rest extra hph1,
        readU16Limb_append rph.rest extra hmd1,
        readU8_append rmd.rest extra hrk1,
        readU16LE_append rk.rest extra hnc1,
        readU16LE_append rnc.rest extra hlp1]
    dsimp only
    rw [ite_eq_right hbad1]
    rw [ite_eq_right hbad1]
    rw [ite_eq_right hbad1] at hok
    set rnodes := readSysNodesN rlp.rest rnc.val 0
    set rzc := readU16LE rnodes.rest
    set rzeros := readNodeIdsN rzc.rest rzc.val
    set rlc := readU16LE rzeros.rest
    set rlks := readSysLookupsN rlc.rest rlc.val
    set bodyOk := rnodes.ok * rzc.ok * rzeros.ok * rlc.ok * rlks.ok
    by_cases hbad2 : bodyOk = 0
    · rw [ite_eq_left (beq_iff_eq.mpr hbad2)] at hok; cases hok
    · have hb4 := prod_ne_zero hbad2
      have hb3 := prod_ne_zero hb4.1
      have hb2 := prod_ne_zero hb3.1
      have hb1 := prod_ne_zero hb2.1
      have hnd1 : rnodes.ok = 1 := (readSysNodesN_ok_zero_or_one rlp.rest rnc.val 0).resolve_left hb1.1
      have hzc1 : rzc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rnodes.rest 1 0).resolve_left hb1.2
      have hzr1 : rzeros.ok = 1 := (readNodeIdsN_ok_zero_or_one rzc.rest rzc.val).resolve_left hb2.2
      have hlc1 : rlc.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rzeros.rest 1 0).resolve_left hb3.2
      have hlk1 : rlks.ok = 1 := (readSysLookupsN_ok_zero_or_one rlc.rest rlc.val).resolve_left hb4.2
      rw [readSysNodesN_append rlp.rest extra rnc.val 0 hnd1,
          readU16LE_append rnodes.rest extra hzc1,
          readNodeIdsN_append rzc.rest extra rzc.val hzr1,
          readU16LE_append rzeros.rest extra hlc1,
          readSysLookupsN_append rlc.rest extra rlc.val hlk1]
      dsimp only
      have hb2ne : ¬((bodyOk == 0) = true) := by rw [beq_iff_eq]; exact hbad2
      rw [ite_eq_right hb2ne]
      rw [ite_eq_right hb2ne]

private theorem readSysCircuitsN_ok_zero_or_one (s : ByteList) (n : Nat) :
    (readSysCircuitsN s n).ok = 0 ∨ (readSysCircuitsN s n).ok = 1 := by
  induction n generalizing s with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readSysCircuitsN]; split; exact Or.inl rfl; exact ih _

private theorem readSysCircuitsN_sound (s : ByteList) (n : Nat)
    (hok : (readSysCircuitsN s n).ok = 1) :
    let r := readSysCircuitsN s n
    ∃ consumed : ByteList,
      byteListLen consumed ≤ n * 2 ^ 34 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      sysCircuitListLen r.val = n ∧
      SysCircuitsWellFormed r.val := by
  induction n generalizing s with
  | zero => exact ⟨.nil, by simp [byteListLen], trivial, rfl, rfl, trivial⟩
  | succ n ih =>
    simp only [readSysCircuitsN] at hok ⊢
    by_cases h0 : (readSysCircuit s).ok = 0
    · simp [h0] at hok
    · have h1 : (readSysCircuit s).ok = 1 := (readSysCircuit_ok_zero_or_one s).resolve_left h0
      have h0b : ((readSysCircuit s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hl0, hv0, hs0, hwf0⟩ := readSysCircuit_sound s h1
      obtain ⟨c1, hl1, hv1, hs1, hcl1, hwf1⟩ := ih (readSysCircuit s).rest hok
      refine ⟨byteListAppend c0 c1, ?_, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0],
        by simp [sysCircuitListLen, hcl1]; omega, ⟨hwf0, hwf1⟩⟩
      rw [byteListLen_append]
      have hmul : (n + 1) * 2 ^ 34 = 2 ^ 34 + n * 2 ^ 34 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega

private theorem readSysCircuitsN_append (s extra : ByteList) (n : Nat)
    (hok : (readSysCircuitsN s n).ok = 1) :
    readSysCircuitsN (byteListAppend s extra) n =
      { (readSysCircuitsN s n) with rest := byteListAppend (readSysCircuitsN s n).rest extra } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [readSysCircuitsN] at hok ⊢
    by_cases h0 : (readSysCircuit s).ok = 0
    · simp [h0] at hok
    · have h1 : (readSysCircuit s).ok = 1 := (readSysCircuit_ok_zero_or_one s).resolve_left h0
      have h0b : ((readSysCircuit s).ok == 0) = false := beq_false_of_ne h0
      rw [readSysCircuit_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      rw [ih _ hok]

private theorem readOptCommit_ok_zero_or_one (s : ByteList) :
    (readOptCommit s).ok = 0 ∨ (readOptCommit s).ok = 1 := by
  simp only [readOptCommit]
  split; exact Or.inl rfl
  split; exact Or.inr rfl
  split
  · split; exact Or.inl rfl
    exact readVkCapN_ok_zero_or_one _ 1
  · exact Or.inl rfl

private theorem readOptCommit_sound (s : ByteList) (hok : (readOptCommit s).ok = 1) :
    let r := readOptCommit s
    ∃ consumed : ByteList,
      byteListLen consumed ≤ 35 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      (∀ cap, r.val = .someCommit cap → digestBytesListLen cap = 1) := by
  simp only [readOptCommit] at hok ⊢
  by_cases h0 : (readU8 s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left h0
    have h0b : ((readU8 s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    obtain ⟨hv0, hs0, _⟩ := readU8_sound s h1
    set rt := readU8 s
    by_cases hv : rt.val = 0
    · simp only [hv, beq_self_eq_true, ↓reduceIte]
      exact ⟨.cons rt.val .nil, by simp [byteListLen], ⟨hv0, trivial⟩, by rw [hs0]; rfl,
        fun _ h => nomatch h⟩
    · have hvb : (rt.val == 0) = false := beq_false_of_ne hv
      simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases hv1 : rt.val = 1
      · simp only [hv1, beq_self_eq_true, ↓reduceIte] at hok ⊢
        set rn := readU16LE rt.rest
        by_cases hbad : ((rn.ok == 0) || (rn.val != 1)) = true
        · simp only [hbad, ↓reduceIte] at hok; cases hok
        · have hbadF : ((rn.ok == 0) || (rn.val != 1)) = false := Bool.eq_false_iff.mpr hbad
          simp only [hbadF, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hbadF
          have hrn1 : rn.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rt.rest 1 0).resolve_left hbadF.1
          obtain ⟨cn, hln, hvn, hsn, _, _, _⟩ := readU16LE_sound rt.rest hrn1
          obtain ⟨cc, hlc, hvc, hsc, hdl⟩ := readVkCapN_sound rn.rest 1 hok
          refine ⟨.cons rt.val (byteListAppend cn cc),
            by simp [byteListLen, byteListLen_append, hln, hlc],
            ⟨hv0, validBytes_append.mpr ⟨hvn, hvc⟩⟩, ?_, ?_⟩
          · simp only [byteListAppend, byteListAppend_assoc]; rw [← hsc, ← hsn, ← hs0]
          · intro cap hcap; cases hcap; exact hdl
      · have hv1b : (rt.val == 1) = false := beq_false_of_ne hv1
        simp only [hv1b, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

private theorem readOptCommit_append (s extra : ByteList) (hok : (readOptCommit s).ok = 1) :
    readOptCommit (byteListAppend s extra) =
      { (readOptCommit s) with rest := byteListAppend (readOptCommit s).rest extra } := by
  simp only [readOptCommit] at hok ⊢
  by_cases h0 : (readU8 s).ok = 0
  · simp [h0] at hok
  · have h1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left h0
    have h0b : ((readU8 s).ok == 0) = false := beq_false_of_ne h0
    rw [readU8_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    set rt := readU8 s
    by_cases hv : rt.val = 0
    · simp only [hv, beq_self_eq_true, ↓reduceIte]
    · have hvb : (rt.val == 0) = false := beq_false_of_ne hv
      simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      by_cases hv1 : rt.val = 1
      · simp only [hv1, beq_self_eq_true, ↓reduceIte] at hok ⊢
        set rn := readU16LE rt.rest
        by_cases hbad : ((rn.ok == 0) || (rn.val != 1)) = true
        · simp only [hbad, ↓reduceIte] at hok; cases hok
        · have hbadF : ((rn.ok == 0) || (rn.val != 1)) = false := Bool.eq_false_iff.mpr hbad
          have hbadF' := hbadF
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hbadF'
          have hrn1 : rn.ok = 1 := (readLeNatAux_ok_zero_or_one 2 rt.rest 1 0).resolve_left hbadF'.1
          rw [readU16LE_append rt.rest extra hrn1]
          dsimp only
          rw [ite_eq_right hbad]
          rw [ite_eq_right hbad]
          rw [ite_eq_right hbad] at hok
          rw [readVkCapN_append rn.rest extra 1 hok]
      · have hv1b : (rt.val == 1) = false := beq_false_of_ne hv1
        simp only [hv1b, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

private theorem readOptIdxN_ok_zero_or_one (s : ByteList) (hc n cnt : Nat) :
    (readOptIdxN s hc n cnt).ok = 0 ∨ (readOptIdxN s hc n cnt).ok = 1 := by
  induction n generalizing s cnt with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [readOptIdxN]
    split; exact Or.inl rfl
    split; exact ih _ _
    split; exact ih _ _
    exact Or.inl rfl

private theorem readOptIdxN_sound (s : ByteList) (hc n cnt : Nat)
    (hok : (readOptIdxN s hc n cnt).ok = 1) :
    let r := readOptIdxN s hc n cnt
    ∃ consumed : ByteList,
      byteListLen consumed = 2 * n ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest ∧
      optIdxListLen r.val = n ∧
      OptIdxRanked cnt r.val ∧
      (hc = 0 → OptIdxAllNone r.val) := by
  induction n generalizing s cnt with
  | zero => exact ⟨.nil, rfl, trivial, rfl, rfl, trivial, fun _ => trivial⟩
  | succ n ih =>
    simp only [readOptIdxN] at hok ⊢
    by_cases h0 : (readU16LE s).ok = 0
    · simp [h0] at hok
    · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
      have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      obtain ⟨c0, hl0, hv0, hs0, _, _, _⟩ := readU16LE_sound s h1
      set rv := readU16LE s
      by_cases hnone : rv.val = 65535
      · simp only [hnone, beq_self_eq_true, ↓reduceIte] at hok ⊢
        obtain ⟨c1, hl1, hv1, hs1, hol1, hrk1, hall1⟩ := ih rv.rest cnt hok
        refine ⟨byteListAppend c0 c1, by rw [byteListLen_append, hl0, hl1]; omega,
          validBytes_append.mpr ⟨hv0, hv1⟩, by rw [byteListAppend_assoc, ← hs1, ← hs0],
          by simp [optIdxListLen, hol1]; omega, hrk1, fun hhc => hall1 hhc⟩
      · have hnoneB : (rv.val == 65535) = false := beq_false_of_ne hnone
        simp only [hnoneB, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases hsome : ((hc == 1) && (rv.val == cnt)) = true
        · simp only [hsome, ↓reduceIte] at hok ⊢
          simp only [Bool.and_eq_true, beq_iff_eq] at hsome
          obtain ⟨c1, hl1, hv1, hs1, hol1, hrk1, _⟩ := ih rv.rest (cnt + 1) hok
          refine ⟨byteListAppend c0 c1, by rw [byteListLen_append, hl0, hl1]; omega,
            validBytes_append.mpr ⟨hv0, hv1⟩, by rw [byteListAppend_assoc, ← hs1, ← hs0],
            by simp [optIdxListLen, hol1]; omega, ⟨hsome.2, hrk1⟩,
            fun hhc => by omega⟩
        · simp only [hsome, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

private theorem readOptIdxN_append (s extra : ByteList) (hc n cnt : Nat)
    (hok : (readOptIdxN s hc n cnt).ok = 1) :
    readOptIdxN (byteListAppend s extra) hc n cnt =
      { (readOptIdxN s hc n cnt) with rest := byteListAppend (readOptIdxN s hc n cnt).rest extra } := by
  induction n generalizing s cnt with
  | zero => rfl
  | succ n ih =>
    simp only [readOptIdxN] at hok ⊢
    by_cases h0 : (readU16LE s).ok = 0
    · simp [h0] at hok
    · have h1 : (readU16LE s).ok = 1 := (readLeNatAux_ok_zero_or_one 2 s 1 0).resolve_left h0
      have h0b : ((readU16LE s).ok == 0) = false := beq_false_of_ne h0
      rw [readU16LE_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      set rv := readU16LE s
      by_cases hnone : rv.val = 65535
      · simp only [hnone, beq_self_eq_true, ↓reduceIte] at hok ⊢
        rw [ih rv.rest cnt hok]
      · have hnoneB : (rv.val == 65535) = false := beq_false_of_ne hnone
        simp only [hnoneB, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases hsome : ((hc == 1) && (rv.val == cnt)) = true
        · simp only [hsome, ↓reduceIte] at hok ⊢
          rw [ih rv.rest (cnt + 1) hok]
        · simp only [hsome, Bool.false_eq_true, ↓reduceIte] at hok; cases hok

private theorem readSysParams_ok_zero_or_one (s : ByteList) :
    (readSysParams s).ok = 0 ∨ (readSysParams s).ok = 1 := by
  simp only [readSysParams]; split; exact Or.inl rfl; exact Or.inr rfl

private theorem readSysParams_sound (s : ByteList) (hok : (readSysParams s).ok = 1) :
    let r := readSysParams s
    ∃ consumed : ByteList,
      byteListLen consumed = 14 ∧ ValidBytes consumed ∧
      s = byteListAppend consumed r.rest := by
  simp only [readSysParams] at hok ⊢
  set r0 := readU16Limb s
  set r1 := readU16Limb r0.rest
  set r2 := readU16Limb r1.rest
  set r3 := readU16Limb r2.rest
  set r4 := readU16Limb r3.rest
  set r5 := readU16Limb r4.rest
  set r6 := readU16Limb r5.rest
  by_cases hz : r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok = 0
  · simp [hz] at hok
  · have hzb : (r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok == 0) = false := beq_false_of_ne hz
    simp only [hzb, Bool.false_eq_true, ↓reduceIte]
    have p6 := prod_ne_zero hz
    have p5 := prod_ne_zero p6.1
    have p4 := prod_ne_zero p5.1
    have p3 := prod_ne_zero p4.1
    have p2 := prod_ne_zero p3.1
    have p1 := prod_ne_zero p2.1
    obtain ⟨c0, l0, v0, s0, _, _, _, _, _⟩ := readU16Limb_sound s ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p1.1)
    obtain ⟨c1, l1, v1, s1, _, _, _, _, _⟩ := readU16Limb_sound r0.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p1.2)
    obtain ⟨c2, l2, v2, s2, _, _, _, _, _⟩ := readU16Limb_sound r1.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p2.2)
    obtain ⟨c3, l3, v3, s3, _, _, _, _, _⟩ := readU16Limb_sound r2.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p3.2)
    obtain ⟨c4, l4, v4, s4, _, _, _, _, _⟩ := readU16Limb_sound r3.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p4.2)
    obtain ⟨c5, l5, v5, s5, _, _, _, _, _⟩ := readU16Limb_sound r4.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p5.2)
    obtain ⟨c6, l6, v6, s6, _, _, _, _, _⟩ := readU16Limb_sound r5.rest ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p6.2)
    refine ⟨byteListAppend c0 (byteListAppend c1 (byteListAppend c2 (byteListAppend c3
      (byteListAppend c4 (byteListAppend c5 c6))))),
      by simp [byteListLen_append, l0, l1, l2, l3, l4, l5, l6],
      validBytes_append.mpr ⟨v0, validBytes_append.mpr ⟨v1, validBytes_append.mpr ⟨v2,
        validBytes_append.mpr ⟨v3, validBytes_append.mpr ⟨v4, validBytes_append.mpr ⟨v5, v6⟩⟩⟩⟩⟩⟩,
      by simp only [byteListAppend_assoc]; rw [← s6, ← s5, ← s4, ← s3, ← s2, ← s1, ← s0]⟩

private theorem readSysParams_append (s extra : ByteList) (hok : (readSysParams s).ok = 1) :
    readSysParams (byteListAppend s extra) =
      { (readSysParams s) with rest := byteListAppend (readSysParams s).rest extra } := by
  simp only [readSysParams] at hok ⊢
  set r0 := readU16Limb s
  set r1 := readU16Limb r0.rest
  set r2 := readU16Limb r1.rest
  set r3 := readU16Limb r2.rest
  set r4 := readU16Limb r3.rest
  set r5 := readU16Limb r4.rest
  set r6 := readU16Limb r5.rest
  by_cases hz : r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok = 0
  · simp [hz] at hok
  · have hzb : (r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok == 0) = false := beq_false_of_ne hz
    have p6 := prod_ne_zero hz
    have p5 := prod_ne_zero p6.1
    have p4 := prod_ne_zero p5.1
    have p3 := prod_ne_zero p4.1
    have p2 := prod_ne_zero p3.1
    have p1 := prod_ne_zero p2.1
    rw [readU16Limb_append s extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p1.1),
        readU16Limb_append r0.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p1.2),
        readU16Limb_append r1.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p2.2),
        readU16Limb_append r2.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p3.2),
        readU16Limb_append r3.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p4.2),
        readU16Limb_append r4.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p5.2),
        readU16Limb_append r5.rest extra ((readLeNatAux_ok_zero_or_one 2 _ 1 0).resolve_left p6.2)]
    dsimp only
    have hzne : ¬((r0.ok * r1.ok * r2.ok * r3.ok * r4.ok * r5.ok * r6.ok == 0) = true) := by
      rw [beq_iff_eq]; exact hz
    rw [ite_eq_right hzne]
    rw [ite_eq_right hzne]

/-- **Headline Wire & Structural VK Soundness (`readSystem`)**:
acceptance implies complete consumption (`rest = .nil`), `< 256` validity of all bytes,
exact Protocol `v6` / `ext_deg = 3` / `fri_batching = 1` magic header, full structural
verifying-key well-formedness (`SysKeyWellFormed`: `prepWidth = 0 ↔ prepHeight = 0`,
power-of-two `prepHeight`, `1 ≤ lookupGroupSize ≤ 8`, DAG acyclicity, `NoCommit ⇒ NoIdx`,
monotonic `OptIdx` ranking), automatic byte-length bound `≤ 1024 * 2^64`, and strict
canonical trailing-byte rejection for any non-empty suffix `extra`. -/
theorem readSystem_sound (s : ByteList) (hok : (readSystem s).ok = 1) :
    let r := readSystem s
    r.rest = .nil ∧
    ValidBytes s ∧
    (readU16LE s).val = 6 ∧
    (readU16LE (readU16LE s).rest).val = 3 ∧
    (readU16LE (readU16LE (readU16LE s).rest).rest).val = 1 ∧
    SysKeyWellFormed r.val ∧
    byteListLen s ≤ 1024 * 2 ^ 64 ∧
    (∀ extra : ByteList, extra ≠ .nil → (readSystem (byteListAppend s extra)).ok = 0) := by
  have hP01 : (readU16LE s).ok = 0 ∨ (readU16LE s).ok = 1 := readLeNatAux_ok_zero_or_one 2 s 1 0
  generalize hrP : readU16LE s = rProto at hP01
  have hE01 : (readU16LE rProto.rest).ok = 0 ∨ (readU16LE rProto.rest).ok = 1 :=
    readLeNatAux_ok_zero_or_one 2 rProto.rest 1 0
  generalize hrE : readU16LE rProto.rest = rExt at hE01
  have hB01 : (readU16LE rExt.rest).ok = 0 ∨ (readU16LE rExt.rest).ok = 1 :=
    readLeNatAux_ok_zero_or_one 2 rExt.rest 1 0
  generalize hrB : readU16LE rExt.rest = rBatch at hB01
  have hV01 := readDigest_ok_zero_or_one rBatch.rest
  generalize hrV : readDigest rBatch.rest = rVk at hV01
  have hPa01 := readSysParams_ok_zero_or_one rVk.rest
  generalize hrPa : readSysParams rVk.rest = rParams at hPa01
  have hN01 : (readU16Limb rParams.rest).ok = 0 ∨ (readU16Limb rParams.rest).ok = 1 :=
    readLeNatAux_ok_zero_or_one 2 rParams.rest 1 0
  generalize hrN : readU16Limb rParams.rest = rn at hN01
  set hdrOk := rProto.ok * rExt.ok * rBatch.ok * rVk.ok * rParams.ok * rn.ok
  by_cases hbad1 : ((hdrOk == 0) || (rProto.val != 6) || (rExt.val != 3) || (rBatch.val != 1)) = true
  · have hEq : (readSystem s).ok = 0 := by
      unfold readSystem; dsimp only
      rw [hrP, hrE, hrB, hrV, hrPa, hrN, ite_eq_left hbad1]
    rw [hEq] at hok; cases hok
  · have hbad1F : ((hdrOk == 0) || (rProto.val != 6) || (rExt.val != 3) || (rBatch.val != 1)) = false :=
      Bool.eq_false_iff.mpr hbad1
    have hbad1F' := hbad1F
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hbad1F'
    obtain ⟨⟨⟨hhdr, hProto6⟩, hExt3⟩, hBatch1⟩ := hbad1F'
    have p5 := prod_ne_zero hhdr
    have p4 := prod_ne_zero p5.1
    have p3 := prod_ne_zero p4.1
    have p2 := prod_ne_zero p3.1
    have p1 := prod_ne_zero p2.1
    have hP1 : (readU16LE s).ok = 1 := by rw [hrP]; exact hP01.resolve_left p1.1
    have hE1 : (readU16LE rProto.rest).ok = 1 := by rw [hrE]; exact hE01.resolve_left p1.2
    have hB1 : (readU16LE rExt.rest).ok = 1 := by rw [hrB]; exact hB01.resolve_left p2.2
    have hV1 : (readDigest rBatch.rest).ok = 1 := by rw [hrV]; exact hV01.resolve_left p3.2
    have hPa1 : (readSysParams rVk.rest).ok = 1 := by rw [hrPa]; exact hPa01.resolve_left p4.2
    have hN1 : (readU16Limb rParams.rest).ok = 1 := by rw [hrN]; exact hN01.resolve_left p5.2
    have hC01 := readSysCircuitsN_ok_zero_or_one rn.rest rn.val
    generalize hrC : readSysCircuitsN rn.rest rn.val = rCircs at hC01
    have hCo01 := readOptCommit_ok_zero_or_one rCircs.rest
    generalize hrCo : readOptCommit rCircs.rest = rCommit at hCo01
    set hasCommit := match rCommit.val with | .noCommit => 0 | .someCommit _ => 1
    have hI01 := readOptIdxN_ok_zero_or_one rCommit.rest hasCommit rn.val 0
    generalize hrI : readOptIdxN rCommit.rest hasCommit rn.val 0 = rIdxs at hI01
    by_cases hbad2 : rCircs.ok * rCommit.ok * rIdxs.ok = 0
    · have hEq : (readSystem s).ok = 0 := by
        unfold readSystem; dsimp only
        rw [hrP, hrE, hrB, hrV, hrPa, hrN, ite_eq_right hbad1, hrC, hrCo]
        cases hcv : rCommit.val <;> simp only [hasCommit, hcv] at hrI ⊢ <;>
          rw [hrI, ite_eq_left (beq_iff_eq.mpr hbad2)]
      rw [hEq] at hok; cases hok
    · have q2 := prod_ne_zero hbad2
      have q1 := prod_ne_zero q2.1
      have hC1 : (readSysCircuitsN rn.rest rn.val).ok = 1 := by rw [hrC]; exact hC01.resolve_left q1.1
      have hCo1 : (readOptCommit rCircs.rest).ok = 1 := by rw [hrCo]; exact hCo01.resolve_left q1.2
      have hI1 : (readOptIdxN rCommit.rest hasCommit rn.val 0).ok = 1 := by rw [hrI]; exact hI01.resolve_left q2.2
      cases hrest : rIdxs.rest with
      | cons _ _ =>
        have hEq : (readSystem s).ok = 0 := by
          unfold readSystem; dsimp only
          rw [hrP, hrE, hrB, hrV, hrPa, hrN, ite_eq_right hbad1, hrC, hrCo]
          cases hcv : rCommit.val <;> simp only [hasCommit, hcv] at hrI ⊢ <;>
            rw [hrI, ite_eq_right (by rw [beq_iff_eq]; exact hbad2), hrest]
        rw [hEq] at hok; cases hok
      | nil =>
        have hSysEq : readSystem s =
            { ok := 1
              val :=
                { params := rParams.val
                  transcriptLimbs := u64ListAppend
                    (.cons { b0 := 3, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
                      (.cons { b0 := 2, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
                        (.cons u64Zero
                          (.cons { b0 := 1, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
                            rParams.limbs))))
                    (.cons { b0 := 3, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
                      (.cons { b0 := 2, b1 := 0, b2 := 0, b3 := 0, b4 := 0, b5 := 0, b6 := 0, b7 := 0 }
                        (.cons rVk.val.d0 (.cons rVk.val.d1 (.cons rVk.val.d2 (.cons rVk.val.d3
                          (.cons rn.limb rCircs.limbs)))))))
                  circuits := rCircs.val
                  prepCommit := rCommit.val
                  prepIndices := rIdxs.val }
              rest := .nil } := by
          unfold readSystem; dsimp only
          rw [hrP, hrE, hrB, hrV, hrPa, hrN, ite_eq_right hbad1, hrC, hrCo]
          cases hcv : rCommit.val <;> simp only [hasCommit, hcv] at hrI ⊢ <;>
            rw [hrI, ite_eq_right (by rw [beq_iff_eq]; exact hbad2), hrest]
        obtain ⟨cP, lP, vP, sP, _, _, _⟩ := readU16LE_sound s hP1
        obtain ⟨cE, lE, vE, sE, _, _, _⟩ := readU16LE_sound rProto.rest hE1
        obtain ⟨cB, lB, vB, sB, _, _, _⟩ := readU16LE_sound rExt.rest hB1
        obtain ⟨vVk, sVk, _⟩ := readDigest_sound rBatch.rest hV1
        obtain ⟨cPa, lPa, vPa, sPa⟩ := readSysParams_sound rVk.rest hPa1
        obtain ⟨cN, lN, vN, sN, _, _, hNlt, _, _⟩ := readU16Limb_sound rParams.rest hN1
        obtain ⟨cC, lC, vC, sC, hCLen, hCwf⟩ := readSysCircuitsN_sound rn.rest rn.val hC1
        obtain ⟨cCo, lCo, vCo, sCo, hCapLen⟩ := readOptCommit_sound rCircs.rest hCo1
        obtain ⟨cI, lI, vI, sI, hILen, hIRank, hINone⟩ := readOptIdxN_sound rCommit.rest hasCommit rn.val 0 hI1
        rw [hrP] at sP; rw [hrE] at sE; rw [hrB] at sB; rw [hrV] at vVk sVk
        rw [hrPa] at sPa; rw [hrN] at sN hNlt; rw [hrC] at sC hCLen hCwf
        rw [hrCo] at sCo hCapLen; rw [hrI] at sI hILen hIRank hINone
        rw [hrest, byteListAppend_nil_right] at sI
        have hvVkB : ValidBytes (digestBytesOnto rVk.val .nil) :=
          validBytes_u64BytesOnto.mpr ⟨vVk.1, validBytes_u64BytesOnto.mpr ⟨vVk.2.1,
            validBytes_u64BytesOnto.mpr ⟨vVk.2.2.1, validBytes_u64BytesOnto.mpr ⟨vVk.2.2.2, trivial⟩⟩⟩⟩
        have hsEq : s = byteListAppend cP (byteListAppend cE (byteListAppend cB
            (byteListAppend (digestBytesOnto rVk.val .nil) (byteListAppend cPa (byteListAppend cN
              (byteListAppend cC (byteListAppend cCo cI))))))) := by
          have hdig : byteListAppend (digestBytesOnto rVk.val .nil) rVk.rest = digestBytesOnto rVk.val rVk.rest := rfl
          rw [← sI, ← sCo, ← sC, ← sN, ← sPa, hdig, ← sVk, ← sB, ← sE, ← sP]
        have hvS : ValidBytes s :=
          hsEq ▸ validBytes_append.mpr ⟨vP, validBytes_append.mpr ⟨vE, validBytes_append.mpr ⟨vB,
            validBytes_append.mpr ⟨hvVkB, validBytes_append.mpr ⟨vPa, validBytes_append.mpr ⟨vN,
              validBytes_append.mpr ⟨vC, validBytes_append.mpr ⟨vCo, vI⟩⟩⟩⟩⟩⟩⟩⟩
        have hlenS : byteListLen s ≤ 1024 * 2 ^ 64 := by
          rw [hsEq]
          simp only [byteListLen_append, lP, lE, lB, lPa, lN, lI, byteListLen_digestBytesOnto, byteListLen]
          have hmul : rn.val * 2 ^ 34 ≤ 2 ^ 16 * 2 ^ 34 :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt hNlt)
          omega
        have hwfKey : SysKeyWellFormed (readSystem s).val := by
          rw [hSysEq]
          refine ⟨hCwf, by rw [hILen, hCLen], ?_, hCapLen, hIRank⟩
          intro hnc
          dsimp only at hnc
          exact hINone (by dsimp only [hasCommit]; rw [hnc])
        refine ⟨by rw [hSysEq], hvS, hProto6, hExt3, hBatch1, hwfKey, hlenS, ?_⟩
        intro extra hextra
        unfold readSystem; dsimp only
        rw [readU16LE_append s extra hP1, hrP]; dsimp only
        rw [readU16LE_append rProto.rest extra hE1, hrE]; dsimp only
        rw [readU16LE_append rExt.rest extra hB1, hrB]; dsimp only
        rw [readDigest_append rBatch.rest extra hV1, hrV]; dsimp only
        rw [readSysParams_append rVk.rest extra hPa1, hrPa]; dsimp only
        rw [readU16Limb_append rParams.rest extra hN1, hrN]; dsimp only
        rw [ite_eq_right hbad1]
        rw [readSysCircuitsN_append rn.rest extra rn.val hC1, hrC]; dsimp only
        rw [readOptCommit_append rCircs.rest extra hCo1, hrCo]; dsimp only
        have hIApp := readOptIdxN_append rCommit.rest extra hasCommit rn.val 0 hI1
        cases hcv : rCommit.val <;> simp only [hasCommit, hcv] at hIApp hrI ⊢ <;>
          rw [hIApp, hrI] <;> dsimp only <;>
          rw [ite_eq_right (by rw [beq_iff_eq]; exact hbad2), hrest, byteListAppend] <;>
          cases extra with
          | nil => exact absurd rfl hextra
          | cons _ _ => rfl

/-! ### `readBatchProof` Soundness & Canonical Trailing-Byte Rejection -/

/-- Every `U64Bytes` in a `U64List` has valid bytes `< 256`. -/
def ValidU64List : U64List → Prop
  | .nil => True
  | .cons x rest => ValidU64Bytes x ∧ ValidU64List rest

/-- Every `ExtGl` in an `ExtGlList` is canonical (`c0, c1, c2 < p_GL`). -/
def CanonicalExtList : ExtGlList → Prop
  | .nil => True
  | .cons e rest => extCanonical e = true ∧ CanonicalExtList rest

/-- Every `ExtGl` in a 2D `ExtGlListList` is canonical. -/
def CanonicalExtListList : ExtGlListList → Prop
  | .nil => True
  | .cons row rest => CanonicalExtList row ∧ CanonicalExtListList rest

/-- Every `ExtGl` in an `OpenedRound` is canonical. -/
def CanonicalOpenedRound : OpenedRound → Prop
  | .nil => True
  | .cons mat rest => CanonicalExtListList mat ∧ CanonicalOpenedRound rest

/-- Every Merkle cap in `MerkleCapList` has exact length `1` and valid digest bytes. -/
def ValidMerkleCapList : MerkleCapList → Prop
  | .nil => True
  | .cons cap rest => digestBytesListLen cap = 1 ∧ ValidMerkleCapList rest

/-- Every `CommitPhaseMultiStep` has canonical `< p_GL` sibling values. -/
def CanonicalCommitSteps : CommitPhaseMultiStepList → Prop
  | .nil => True
  | .cons st rest => st.logArity < 256 ∧ CanonicalExtListList st.siblingValues ∧ CanonicalCommitSteps rest

/-- Structural & canonicality invariants enforced on every `ShardHeader` by `readBatchProof`. -/
structure ShardHeaderDecodedWF (h : ShardHeader) : Prop where
  stage1_cap_len : digestBytesListLen h.stage1 = 1
  claims_canonical : CanonicalClaims h.claims

def ShardHeadersDecodedWF : ShardHeaderList → Prop
  | .nil => True
  | .cons h rest => ShardHeaderDecodedWF h ∧ ShardHeadersDecodedWF rest

/-- Structural & canonicality invariants enforced on every `BatchMessage` by `readBatchProof`. -/
structure BatchMessageDecodedWF (m : BatchMessage) : Prop where
  args_canonical : CanonicalU64List m.args
  mult_valid : ValidU64Bytes m.multiplicity
  mult_lt_p : u64BytesToNat m.multiplicity < glPrime

def BatchMessagesDecodedWF : BatchMessageList → Prop
  | .nil => True
  | .cons m rest => BatchMessageDecodedWF m ∧ BatchMessagesDecodedWF rest

/-- Structural & canonicality invariants enforced on every `ShardProof` by `readBatchProof`. -/
structure ShardProofDecodedWF (p : ShardProof) : Prop where
  stage1_cap_len : digestBytesListLen p.commitments.stage1 = 1
  stage2_cap_len : digestBytesListLen p.commitments.stage2 = 1
  quotient_cap_len : digestBytesListLen p.commitments.quotient = 1
  intermediateAccs_canonical : CanonicalExtList p.intermediateAccs
  commitCaps_valid : ValidMerkleCapList p.openingProof.commitPhaseCommits
  commitPow_valid : ValidU64List p.openingProof.commitPowWitnesses
  commitSteps_canonical : CanonicalCommitSteps p.openingProof.commitPhaseOpenings
  finalPoly_canonical : CanonicalExtList p.openingProof.finalPoly
  queryPow_valid : ValidU64Bytes p.openingProof.queryPowWitness
  quotientOpened_canonical : CanonicalOpenedRound p.quotientOpened
  preprocessedOpened_canonical :
    match p.preprocessedOpened with
    | .noPreprocessed => True
    | .somePreprocessed r => CanonicalOpenedRound r
  stage1Opened_canonical : CanonicalOpenedRound p.stage1Opened
  stage2Opened_canonical : CanonicalOpenedRound p.stage2Opened

def ShardProofsDecodedWF : ShardProofList → Prop
  | .nil => True
  | .cons p rest => ShardProofDecodedWF p ∧ ShardProofsDecodedWF rest

/-- Complete decoded well-formedness enforced by `StarkWire.readBatchProof`. -/
structure BatchProofDecodedWellFormed (b : BatchProof) : Prop where
  headers_wf : ShardHeadersDecodedWF b.headers
  messages_wf : BatchMessagesDecodedWF b.messages
  proofs_wf : ShardProofsDecodedWF b.proofs

private theorem u64ListAllLtP_canonical : ∀ {xs : U64List},
    ValidU64List xs → u64ListAllLtP xs = 1 → CanonicalU64List xs
  | .nil, _, _ => trivial
  | .cons x rest, ⟨hvx, hvr⟩, h => by
    simp only [u64ListAllLtP] at h
    by_cases hx : glLtPBytes x = 1
    · simp only [hx, beq_self_eq_true, ↓reduceIte] at h
      exact ⟨hvx, (glLtPBytes_eq_one_iff hvx).mp hx, u64ListAllLtP_canonical hvr h⟩
    · have hxb : (glLtPBytes x == 1) = false := beq_false_of_ne hx
      simp only [hxb, Bool.false_eq_true, ↓reduceIte] at h; cases h

private theorem u64ListAllLtP_zero_or_one : ∀ xs : U64List,
    u64ListAllLtP xs = 0 ∨ u64ListAllLtP xs = 1
  | .nil => Or.inr rfl
  | .cons x rest => by
    simp only [u64ListAllLtP]; split
    · exact u64ListAllLtP_zero_or_one rest
    · exact Or.inl rfl

private theorem u64ListListAllLtP_zero_or_one : ∀ xss : U64ListList,
    u64ListListAllLtP xss = 0 ∨ u64ListListAllLtP xss = 1
  | .nil => Or.inr rfl
  | .cons xs rest => by
    simp only [u64ListListAllLtP]; split
    · exact u64ListListAllLtP_zero_or_one rest
    · exact Or.inl rfl

private def ValidU64ListList : U64ListList → Prop
  | .nil => True
  | .cons xs rest => ValidU64List xs ∧ ValidU64ListList rest

private theorem u64ListListAllLtP_canonical : ∀ {xss : U64ListList},
    ValidU64ListList xss → u64ListListAllLtP xss = 1 → CanonicalClaims xss
  | .nil, _, _ => trivial
  | .cons xs rest, ⟨hvxs, hvr⟩, h => by
    simp only [u64ListListAllLtP] at h
    by_cases hxs : u64ListAllLtP xs = 1
    · simp only [hxs, beq_self_eq_true, ↓reduceIte] at h
      exact ⟨u64ListAllLtP_canonical hvxs hxs, u64ListListAllLtP_canonical hvr h⟩
    · have hxsb : (u64ListAllLtP xs == 1) = false := beq_false_of_ne hxs
      simp only [hxsb, Bool.false_eq_true, ↓reduceIte] at h; cases h

-- Concise combined `ok ∈ {0,1} + sound + append` lemmas for every `ProofDeserialize` sub-reader:

private theorem readU8VecN_props (s : ByteList) (n : Nat) :
    ((readU8VecN s n).ok = 0 ∨ (readU8VecN s n).ok = 1) ∧
    ((readU8VecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU8VecN s n).rest) ∧
      (∀ extra, readU8VecN (byteListAppend s extra) n =
        { (readU8VecN s n) with rest := byteListAppend (readU8VecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readU8VecN]
    by_cases h0 : (readU8 s).ok = 0
    · simp [h0]
    · have h1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left h0
      have h0b : ((readU8 s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readU8 s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨hv0, hs0, _⟩ := readU8_sound s h1
      obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
      refine ⟨⟨.cons (readU8 s).val c1, ⟨hv0, hv1⟩, ?_⟩, fun extra => ?_⟩
      · simp only [byteListAppend]; rw [← hs1, ← hs0]
      rw [readU8_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU8Vec_props (s : ByteList) :
    ((readU8Vec s).ok = 0 ∨ (readU8Vec s).ok = 1) ∧
    ((readU8Vec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU8Vec s).rest) ∧
      (∀ extra, readU8Vec (byteListAppend s extra) =
        { (readU8Vec s) with rest := byteListAppend (readU8Vec s).rest extra })) := by
  simp only [readU8Vec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readU8VecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64VecN_props (s : ByteList) (n : Nat) :
    ((readU64VecN s n).ok = 0 ∨ (readU64VecN s n).ok = 1) ∧
    ((readU64VecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64VecN s n).rest) ∧
      ValidU64List (readU64VecN s n).val ∧
      (∀ extra, readU64VecN (byteListAppend s extra) n =
        { (readU64VecN s n) with rest := byteListAppend (readU64VecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readU64VecN]
    by_cases h0 : (readU64LE s).ok = 0
    · simp [h0]
    · have h1 : (readU64LE s).ok = 1 := (readU64LE_ok_zero_or_one s).resolve_left h0
      have h0b : ((readU64LE s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readU64LE s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨hv0, hs0, _⟩ := readU64LE_sound s h1
      obtain ⟨⟨c1, hv1, hs1⟩, hvl1, happ1⟩ := hst hok
      refine ⟨⟨u64BytesOnto (readU64LE s).val c1, validBytes_u64BytesOnto.mpr ⟨hv0, hv1⟩,
        by rw [u64BytesOnto_append, ← hs1, ← hs0]⟩, ⟨hv0, hvl1⟩, fun extra => ?_⟩
      rw [readU64LE_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64Vec_props (s : ByteList) :
    ((readU64Vec s).ok = 0 ∨ (readU64Vec s).ok = 1) ∧
    ((readU64Vec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64Vec s).rest) ∧
      ValidU64List (readU64Vec s).val ∧
      (∀ extra, readU64Vec (byteListAppend s extra) =
        { (readU64Vec s) with rest := byteListAppend (readU64Vec s).rest extra })) := by
  simp only [readU64Vec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readU64VecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hvl1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hvl1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64VecVecN_props (s : ByteList) (n : Nat) :
    ((readU64VecVecN s n).ok = 0 ∨ (readU64VecVecN s n).ok = 1) ∧
    ((readU64VecVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64VecVecN s n).rest) ∧
      ValidU64ListList (readU64VecVecN s n).val ∧
      (∀ extra, readU64VecVecN (byteListAppend s extra) n =
        { (readU64VecVecN s n) with rest := byteListAppend (readU64VecVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readU64VecVecN]
    obtain ⟨h01r, hsr⟩ := readU64Vec_props s
    by_cases h0 : (readU64Vec s).ok = 0
    · simp [h0]
    · have h1 : (readU64Vec s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readU64Vec s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readU64Vec s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hvl0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hvl1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hvl0, hvl1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64VecVec_props (s : ByteList) :
    ((readU64VecVec s).ok = 0 ∨ (readU64VecVec s).ok = 1) ∧
    ((readU64VecVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64VecVec s).rest) ∧
      ValidU64ListList (readU64VecVec s).val ∧
      (∀ extra, readU64VecVec (byteListAppend s extra) =
        { (readU64VecVec s) with rest := byteListAppend (readU64VecVec s).rest extra })) := by
  simp only [readU64VecVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readU64VecVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hvl1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hvl1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64VecVecVecN_props (s : ByteList) (n : Nat) :
    ((readU64VecVecVecN s n).ok = 0 ∨ (readU64VecVecVecN s n).ok = 1) ∧
    ((readU64VecVecVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64VecVecVecN s n).rest) ∧
      (∀ extra, readU64VecVecVecN (byteListAppend s extra) n =
        { (readU64VecVecVecN s n) with rest := byteListAppend (readU64VecVecVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readU64VecVecVecN]
    obtain ⟨h01r, hsr⟩ := readU64VecVec_props s
    by_cases h0 : (readU64VecVec s).ok = 0
    · simp [h0]
    · have h1 : (readU64VecVec s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readU64VecVec s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readU64VecVec s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, _, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readU64VecVecVec_props (s : ByteList) :
    ((readU64VecVecVec s).ok = 0 ∨ (readU64VecVecVec s).ok = 1) ∧
    ((readU64VecVecVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readU64VecVecVec s).rest) ∧
      (∀ extra, readU64VecVecVec (byteListAppend s extra) =
        { (readU64VecVecVec s) with rest := byteListAppend (readU64VecVecVec s).rest extra })) := by
  simp only [readU64VecVecVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readU64VecVecVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readExtGl_ok_zero_or_one (s : ByteList) :
    (readExtGl s).ok = 0 ∨ (readExtGl s).ok = 1 := by
  simp only [readExtGl]; split; exact Or.inl rfl; exact Or.inr rfl

private theorem readExtVecN_props (s : ByteList) (n : Nat) :
    ((readExtVecN s n).ok = 0 ∨ (readExtVecN s n).ok = 1) ∧
    ((readExtVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readExtVecN s n).rest) ∧
      CanonicalExtList (readExtVecN s n).val ∧
      (∀ extra, readExtVecN (byteListAppend s extra) n =
        { (readExtVecN s n) with rest := byteListAppend (readExtVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readExtVecN]
    by_cases h0 : (readExtGl s).ok = 0
    · simp [h0]
    · have h1 : (readExtGl s).ok = 1 := (readExtGl_ok_zero_or_one s).resolve_left h0
      have h0b : ((readExtGl s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readExtGl s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨c0, _, hv0, hs0, _, hcan0, _, _, _⟩ := readExtGl_sound s h1
      obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hcan0, hcan1⟩, fun extra => ?_⟩
      rw [readExtGl_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readExtVec_props (s : ByteList) :
    ((readExtVec s).ok = 0 ∨ (readExtVec s).ok = 1) ∧
    ((readExtVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readExtVec s).rest) ∧
      CanonicalExtList (readExtVec s).val ∧
      (∀ extra, readExtVec (byteListAppend s extra) =
        { (readExtVec s) with rest := byteListAppend (readExtVec s).rest extra })) := by
  simp only [readExtVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readExtVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hcan1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readExtVecVecN_props (s : ByteList) (n : Nat) :
    ((readExtVecVecN s n).ok = 0 ∨ (readExtVecVecN s n).ok = 1) ∧
    ((readExtVecVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readExtVecVecN s n).rest) ∧
      CanonicalExtListList (readExtVecVecN s n).val ∧
      (∀ extra, readExtVecVecN (byteListAppend s extra) n =
        { (readExtVecVecN s n) with rest := byteListAppend (readExtVecVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readExtVecVecN]
    obtain ⟨h01r, hsr⟩ := readExtVec_props s
    by_cases h0 : (readExtVec s).ok = 0
    · simp [h0]
    · have h1 : (readExtVec s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readExtVec s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readExtVec s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hcan0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hcan0, hcan1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readExtVecVec_props (s : ByteList) :
    ((readExtVecVec s).ok = 0 ∨ (readExtVecVec s).ok = 1) ∧
    ((readExtVecVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readExtVecVec s).rest) ∧
      CanonicalExtListList (readExtVecVec s).val ∧
      (∀ extra, readExtVecVec (byteListAppend s extra) =
        { (readExtVecVec s) with rest := byteListAppend (readExtVecVec s).rest extra })) := by
  simp only [readExtVecVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readExtVecVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hcan1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readOpenedRoundN_props (s : ByteList) (n : Nat) :
    ((readOpenedRoundN s n).ok = 0 ∨ (readOpenedRoundN s n).ok = 1) ∧
    ((readOpenedRoundN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readOpenedRoundN s n).rest) ∧
      CanonicalOpenedRound (readOpenedRoundN s n).val ∧
      (∀ extra, readOpenedRoundN (byteListAppend s extra) n =
        { (readOpenedRoundN s n) with rest := byteListAppend (readOpenedRoundN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readOpenedRoundN]
    obtain ⟨h01r, hsr⟩ := readExtVecVec_props s
    by_cases h0 : (readExtVecVec s).ok = 0
    · simp [h0]
    · have h1 : (readExtVecVec s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readExtVecVec s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readExtVecVec s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hcan0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hcan0, hcan1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readOpenedRound_props (s : ByteList) :
    ((readOpenedRound s).ok = 0 ∨ (readOpenedRound s).ok = 1) ∧
    ((readOpenedRound s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readOpenedRound s).rest) ∧
      CanonicalOpenedRound (readOpenedRound s).val ∧
      (∀ extra, readOpenedRound (byteListAppend s extra) =
        { (readOpenedRound s) with rest := byteListAppend (readOpenedRound s).rest extra })) := by
  simp only [readOpenedRound]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readOpenedRoundN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hcan1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readDigestVecN_props (s : ByteList) (n : Nat) :
    ((readDigestVecN s n).ok = 0 ∨ (readDigestVecN s n).ok = 1) ∧
    ((readDigestVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readDigestVecN s n).rest) ∧
      (∀ extra, readDigestVecN (byteListAppend s extra) n =
        { (readDigestVecN s n) with rest := byteListAppend (readDigestVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readDigestVecN]
    by_cases h0 : (readDigest s).ok = 0
    · simp [h0]
    · have h1 : (readDigest s).ok = 1 := (readDigest_ok_zero_or_one s).resolve_left h0
      have h0b : ((readDigest s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readDigest s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨hv0, hs0, _⟩ := readDigest_sound s h1
      obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
      refine ⟨⟨digestBytesOnto (readDigest s).val c1,
        validBytes_u64BytesOnto.mpr ⟨hv0.1, validBytes_u64BytesOnto.mpr ⟨hv0.2.1,
          validBytes_u64BytesOnto.mpr ⟨hv0.2.2.1, validBytes_u64BytesOnto.mpr ⟨hv0.2.2.2, hv1⟩⟩⟩⟩,
        by rw [digestBytesOnto_append, ← hs1, ← hs0]⟩, fun extra => ?_⟩
      rw [readDigest_append s extra h1]
      simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readDigestVec_props (s : ByteList) :
    ((readDigestVec s).ok = 0 ∨ (readDigestVec s).ok = 1) ∧
    ((readDigestVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readDigestVec s).rest) ∧
      (∀ extra, readDigestVec (byteListAppend s extra) =
        { (readDigestVec s) with rest := byteListAppend (readDigestVec s).rest extra })) := by
  simp only [readDigestVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readDigestVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readMerkleCap_props (s : ByteList) :
    ((readMerkleCap s).ok = 0 ∨ (readMerkleCap s).ok = 1) ∧
    ((readMerkleCap s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readMerkleCap s).rest) ∧
      digestBytesListLen (readMerkleCap s).val = 1 ∧
      (∀ extra, readMerkleCap (byteListAppend s extra) =
        { (readMerkleCap s) with rest := byteListAppend (readMerkleCap s).rest extra })) := by
  simp only [readMerkleCap]
  by_cases hbad : ((readCount s).ok == 0 || (readCount s).val != 1) = true
  · simp [hbad]
  · have hbadF : ((readCount s).ok == 0 || (readCount s).val != 1) = false := Bool.eq_false_iff.mpr hbad
    simp only [hbadF, Bool.false_eq_true, ↓reduceIte]
    have hbadF' := hbadF
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hbadF'
    have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left hbadF'.1
    set rn := readCount s
    by_cases hd0 : (readDigest rn.rest).ok = 0
    · simp [hd0]
    · have hd1 : (readDigest rn.rest).ok = 1 := (readDigest_ok_zero_or_one rn.rest).resolve_left hd0
      have hd0b : ((readDigest rn.rest).ok == 0) = false := beq_false_of_ne hd0
      simp only [hd0b, Bool.false_eq_true, ↓reduceIte]
      refine ⟨Or.inr trivial, fun _ => ?_⟩
      obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
      obtain ⟨hv1, hs1, _⟩ := readDigest_sound rn.rest hd1
      have hvd : ValidBytes (digestBytesOnto (readDigest rn.rest).val .nil) :=
        validBytes_u64BytesOnto.mpr ⟨hv1.1, validBytes_u64BytesOnto.mpr ⟨hv1.2.1,
          validBytes_u64BytesOnto.mpr ⟨hv1.2.2.1, validBytes_u64BytesOnto.mpr ⟨hv1.2.2.2, trivial⟩⟩⟩⟩
      refine ⟨⟨byteListAppend c0 (digestBytesOnto (readDigest rn.rest).val .nil),
        validBytes_append.mpr ⟨hv0, hvd⟩, ?_⟩, rfl, fun extra => ?_⟩
      · have hdig : byteListAppend (digestBytesOnto (readDigest rn.rest).val .nil) (readDigest rn.rest).rest =
            digestBytesOnto (readDigest rn.rest).val (readDigest rn.rest).rest := rfl
        rw [byteListAppend_assoc, hdig, ← hs1, ← hs0]
      · rw [readCount_append s extra h1]
        dsimp only
        rw [ite_eq_right hbad]
        rw [readDigest_append rn.rest extra hd1]
        dsimp only
        rw [ite_eq_right (by rw [beq_iff_eq]; exact hd0)]

private theorem readMerkleCapVecN_props (s : ByteList) (n : Nat) :
    ((readMerkleCapVecN s n).ok = 0 ∨ (readMerkleCapVecN s n).ok = 1) ∧
    ((readMerkleCapVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readMerkleCapVecN s n).rest) ∧
      ValidMerkleCapList (readMerkleCapVecN s n).val ∧
      (∀ extra, readMerkleCapVecN (byteListAppend s extra) n =
        { (readMerkleCapVecN s n) with rest := byteListAppend (readMerkleCapVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readMerkleCapVecN]
    obtain ⟨h01r, hsr⟩ := readMerkleCap_props s
    by_cases h0 : (readMerkleCap s).ok = 0
    · simp [h0]
    · have h1 : (readMerkleCap s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readMerkleCap s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readMerkleCap s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hl0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hl1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hl0, hl1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readMerkleCapVec_props (s : ByteList) :
    ((readMerkleCapVec s).ok = 0 ∨ (readMerkleCapVec s).ok = 1) ∧
    ((readMerkleCapVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readMerkleCapVec s).rest) ∧
      ValidMerkleCapList (readMerkleCapVec s).val ∧
      (∀ extra, readMerkleCapVec (byteListAppend s extra) =
        { (readMerkleCapVec s) with rest := byteListAppend (readMerkleCapVec s).rest extra })) := by
  simp only [readMerkleCapVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readMerkleCapVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hl1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hl1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readCommitments_props (s : ByteList) :
    ((readCommitments s).ok = 0 ∨ (readCommitments s).ok = 1) ∧
    ((readCommitments s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readCommitments s).rest) ∧
      digestBytesListLen (readCommitments s).val.stage1 = 1 ∧
      digestBytesListLen (readCommitments s).val.stage2 = 1 ∧
      digestBytesListLen (readCommitments s).val.quotient = 1 ∧
      (∀ extra, readCommitments (byteListAppend s extra) =
        { (readCommitments s) with rest := byteListAppend (readCommitments s).rest extra })) := by
  simp only [readCommitments]
  obtain ⟨h01a, hsa⟩ := readMerkleCap_props s
  by_cases ha : (readMerkleCap s).ok = 0
  · simp [ha]
  · have ha1 : (readMerkleCap s).ok = 1 := h01a.resolve_left ha
    have hab : ((readMerkleCap s).ok == 0) = false := beq_false_of_ne ha
    simp only [hab, Bool.false_eq_true, ↓reduceIte]
    set r0 := readMerkleCap s
    obtain ⟨h01b, hsb⟩ := readMerkleCap_props r0.rest
    by_cases hb : (readMerkleCap r0.rest).ok = 0
    · simp [hb]
    · have hb1 : (readMerkleCap r0.rest).ok = 1 := h01b.resolve_left hb
      have hbb : ((readMerkleCap r0.rest).ok == 0) = false := beq_false_of_ne hb
      simp only [hbb, Bool.false_eq_true, ↓reduceIte]
      set r1 := readMerkleCap r0.rest
      obtain ⟨h01c, hsc⟩ := readMerkleCap_props r1.rest
      by_cases hc : (readMerkleCap r1.rest).ok = 0
      · simp [hc]
      · have hc1 : (readMerkleCap r1.rest).ok = 1 := h01c.resolve_left hc
        have hcb : ((readMerkleCap r1.rest).ok == 0) = false := beq_false_of_ne hc
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨Or.inr trivial, fun _ => ?_⟩
        obtain ⟨⟨ca, hva, hsa'⟩, hla, happa⟩ := hsa ha1
        obtain ⟨⟨cb, hvb, hsb'⟩, hlb, happb⟩ := hsb hb1
        obtain ⟨⟨cc, hvc, hsc'⟩, hlc, happc⟩ := hsc hc1
        refine ⟨⟨byteListAppend ca (byteListAppend cb cc),
          validBytes_append.mpr ⟨hva, validBytes_append.mpr ⟨hvb, hvc⟩⟩,
          by rw [byteListAppend_assoc, byteListAppend_assoc, ← hsc', ← hsb', ← hsa']⟩,
          hla, hlb, hlc, fun extra => ?_⟩
        rw [happa extra]; simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rw [happb extra]; simp only [hbb, Bool.false_eq_true, ↓reduceIte]
        rw [happc extra]; simp only [hcb, Bool.false_eq_true, ↓reduceIte]

private theorem readBatchOpening_props (s : ByteList) :
    ((readBatchOpening s).ok = 0 ∨ (readBatchOpening s).ok = 1) ∧
    ((readBatchOpening s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchOpening s).rest) ∧
      (∀ extra, readBatchOpening (byteListAppend s extra) =
        { (readBatchOpening s) with rest := byteListAppend (readBatchOpening s).rest extra })) := by
  simp only [readBatchOpening]
  obtain ⟨h01a, hsa⟩ := readU64VecVecVec_props s
  by_cases ha : (readU64VecVecVec s).ok = 0
  · simp [ha]
  · have ha1 : (readU64VecVecVec s).ok = 1 := h01a.resolve_left ha
    have hab : ((readU64VecVecVec s).ok == 0) = false := beq_false_of_ne ha
    simp only [hab, Bool.false_eq_true, ↓reduceIte]
    set r0 := readU64VecVecVec s
    obtain ⟨h01b, hsb⟩ := readDigestVec_props r0.rest
    by_cases hb : (readDigestVec r0.rest).ok = 0
    · simp [hb]
    · have hb1 : (readDigestVec r0.rest).ok = 1 := h01b.resolve_left hb
      have hbb : ((readDigestVec r0.rest).ok == 0) = false := beq_false_of_ne hb
      simp only [hbb, Bool.false_eq_true, ↓reduceIte]
      refine ⟨Or.inr trivial, fun _ => ?_⟩
      obtain ⟨⟨ca, hva, hsa'⟩, happa⟩ := hsa ha1
      obtain ⟨⟨cb, hvb, hsb'⟩, happb⟩ := hsb hb1
      refine ⟨⟨byteListAppend ca cb, validBytes_append.mpr ⟨hva, hvb⟩,
        by rw [byteListAppend_assoc, ← hsb', ← hsa']⟩, fun extra => ?_⟩
      rw [happa extra]; simp only [hab, Bool.false_eq_true, ↓reduceIte]
      rw [happb extra]; simp only [hbb, Bool.false_eq_true, ↓reduceIte]

private theorem readBatchOpeningVecN_props (s : ByteList) (n : Nat) :
    ((readBatchOpeningVecN s n).ok = 0 ∨ (readBatchOpeningVecN s n).ok = 1) ∧
    ((readBatchOpeningVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchOpeningVecN s n).rest) ∧
      (∀ extra, readBatchOpeningVecN (byteListAppend s extra) n =
        { (readBatchOpeningVecN s n) with rest := byteListAppend (readBatchOpeningVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readBatchOpeningVecN]
    obtain ⟨h01r, hsr⟩ := readBatchOpening_props s
    by_cases h0 : (readBatchOpening s).ok = 0
    · simp [h0]
    · have h1 : (readBatchOpening s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readBatchOpening s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readBatchOpening s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readBatchOpeningVec_props (s : ByteList) :
    ((readBatchOpeningVec s).ok = 0 ∨ (readBatchOpeningVec s).ok = 1) ∧
    ((readBatchOpeningVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchOpeningVec s).rest) ∧
      (∀ extra, readBatchOpeningVec (byteListAppend s extra) =
        { (readBatchOpeningVec s) with rest := byteListAppend (readBatchOpeningVec s).rest extra })) := by
  simp only [readBatchOpeningVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readBatchOpeningVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readCommitPhaseStep_props (s : ByteList) :
    ((readCommitPhaseStep s).ok = 0 ∨ (readCommitPhaseStep s).ok = 1) ∧
    ((readCommitPhaseStep s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readCommitPhaseStep s).rest) ∧
      (readCommitPhaseStep s).val.logArity < 256 ∧
      CanonicalExtListList (readCommitPhaseStep s).val.siblingValues ∧
      (∀ extra, readCommitPhaseStep (byteListAppend s extra) =
        { (readCommitPhaseStep s) with rest := byteListAppend (readCommitPhaseStep s).rest extra })) := by
  simp only [readCommitPhaseStep]
  by_cases ha : (readU8 s).ok = 0
  · simp [ha]
  · have ha1 : (readU8 s).ok = 1 := (readLeNatAux_ok_zero_or_one 1 s 1 0).resolve_left ha
    have hab : ((readU8 s).ok == 0) = false := beq_false_of_ne ha
    simp only [hab, Bool.false_eq_true, ↓reduceIte]
    set r0 := readU8 s
    obtain ⟨h01b, hsb⟩ := readExtVecVec_props r0.rest
    by_cases hb : (readExtVecVec r0.rest).ok = 0
    · simp [hb]
    · have hb1 : (readExtVecVec r0.rest).ok = 1 := h01b.resolve_left hb
      have hbb : ((readExtVecVec r0.rest).ok == 0) = false := beq_false_of_ne hb
      simp only [hbb, Bool.false_eq_true, ↓reduceIte]
      set r1 := readExtVecVec r0.rest
      obtain ⟨h01c, hsc⟩ := readDigestVec_props r1.rest
      by_cases hc : (readDigestVec r1.rest).ok = 0
      · simp [hc]
      · have hc1 : (readDigestVec r1.rest).ok = 1 := h01c.resolve_left hc
        have hcb : ((readDigestVec r1.rest).ok == 0) = false := beq_false_of_ne hc
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        refine ⟨Or.inr trivial, fun _ => ?_⟩
        obtain ⟨hva, hsa', _⟩ := readU8_sound s ha1
        obtain ⟨⟨cb, hvb, hsb'⟩, hcanb, happb⟩ := hsb hb1
        obtain ⟨⟨cc, hvc, hsc'⟩, happc⟩ := hsc hc1
        refine ⟨⟨.cons r0.val (byteListAppend cb cc),
          ⟨hva, validBytes_append.mpr ⟨hvb, hvc⟩⟩, ?_⟩,
          hva, hcanb, fun extra => ?_⟩
        · simp only [byteListAppend, byteListAppend_assoc]; rw [← hsc', ← hsb', ← hsa']
        · rw [readU8_append s extra ha1]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact ha)]
          rw [happb extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact hb)]
          rw [happc extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact hc)]

private theorem readCommitPhaseStepVecN_props (s : ByteList) (n : Nat) :
    ((readCommitPhaseStepVecN s n).ok = 0 ∨ (readCommitPhaseStepVecN s n).ok = 1) ∧
    ((readCommitPhaseStepVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readCommitPhaseStepVecN s n).rest) ∧
      CanonicalCommitSteps (readCommitPhaseStepVecN s n).val ∧
      (∀ extra, readCommitPhaseStepVecN (byteListAppend s extra) n =
        { (readCommitPhaseStepVecN s n) with rest := byteListAppend (readCommitPhaseStepVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readCommitPhaseStepVecN]
    obtain ⟨h01r, hsr⟩ := readCommitPhaseStep_props s
    by_cases h0 : (readCommitPhaseStep s).ok = 0
    · simp [h0]
    · have h1 : (readCommitPhaseStep s).ok = 1 := h01r.resolve_left h0
      have h0b : ((readCommitPhaseStep s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readCommitPhaseStep s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hla0, hcan0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hla0, hcan0, hcan1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readCommitPhaseStepVec_props (s : ByteList) :
    ((readCommitPhaseStepVec s).ok = 0 ∨ (readCommitPhaseStepVec s).ok = 1) ∧
    ((readCommitPhaseStepVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readCommitPhaseStepVec s).rest) ∧
      CanonicalCommitSteps (readCommitPhaseStepVec s).val ∧
      (∀ extra, readCommitPhaseStepVec (byteListAppend s extra) =
        { (readCommitPhaseStepVec s) with rest := byteListAppend (readCommitPhaseStepVec s).rest extra })) := by
  simp only [readCommitPhaseStepVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 : (readCount s).ok = 1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readCommitPhaseStepVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hcan1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hcan1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readFriProof_props (s : ByteList) :
    ((readFriProof s).ok = 0 ∨ (readFriProof s).ok = 1) ∧
    ((readFriProof s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readFriProof s).rest) ∧
      ValidMerkleCapList (readFriProof s).val.commitPhaseCommits ∧
      ValidU64List (readFriProof s).val.commitPowWitnesses ∧
      CanonicalCommitSteps (readFriProof s).val.commitPhaseOpenings ∧
      CanonicalExtList (readFriProof s).val.finalPoly ∧
      ValidU64Bytes (readFriProof s).val.queryPowWitness ∧
      (∀ extra, readFriProof (byteListAppend s extra) =
        { (readFriProof s) with rest := byteListAppend (readFriProof s).rest extra })) := by
  obtain ⟨h01_0, hs0⟩ := readMerkleCapVec_props s
  generalize hr0 : readMerkleCapVec s = r0 at h01_0 hs0
  by_cases h0 : r0.ok = 0
  · have hEq : (readFriProof s).ok = 0 := by
      unfold readFriProof; dsimp only; rw [hr0, ite_eq_left (beq_iff_eq.mpr h0)]
    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
  · have h0_1 := h01_0.resolve_left h0
    obtain ⟨h01_1, hs1⟩ := readU64Vec_props r0.rest
    generalize hr1 : readU64Vec r0.rest = r1 at h01_1 hs1
    by_cases h1 : r1.ok = 0
    · have hEq : (readFriProof s).ok = 0 := by
        unfold readFriProof; dsimp only
        rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1, ite_eq_left (beq_iff_eq.mpr h1)]
      exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
    · have h1_1 := h01_1.resolve_left h1
      obtain ⟨h01_2, hs2⟩ := readBatchOpeningVec_props r1.rest
      generalize hr2 : readBatchOpeningVec r1.rest = r2 at h01_2 hs2
      by_cases h2 : r2.ok = 0
      · have hEq : (readFriProof s).ok = 0 := by
          unfold readFriProof; dsimp only
          rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
              ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2, ite_eq_left (beq_iff_eq.mpr h2)]
        exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
      · have h2_1 := h01_2.resolve_left h2
        obtain ⟨h01_3, hs3⟩ := readCommitPhaseStepVec_props r2.rest
        generalize hr3 : readCommitPhaseStepVec r2.rest = r3 at h01_3 hs3
        by_cases h3 : r3.ok = 0
        · have hEq : (readFriProof s).ok = 0 := by
            unfold readFriProof; dsimp only
            rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3, ite_eq_left (beq_iff_eq.mpr h3)]
          exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
        · have h3_1 := h01_3.resolve_left h3
          obtain ⟨h01_4, hs4⟩ := readExtVec_props r3.rest
          generalize hr4 : readExtVec r3.rest = r4 at h01_4 hs4
          by_cases h4 : r4.ok = 0
          · have hEq : (readFriProof s).ok = 0 := by
              unfold readFriProof; dsimp only
              rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                  ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                  ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                  ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4, ite_eq_left (beq_iff_eq.mpr h4)]
            exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
          · have h4_1 := h01_4.resolve_left h4
            have h01_5 := readU64LE_ok_zero_or_one r4.rest
            generalize hr5 : readU64LE r4.rest = r5 at h01_5
            by_cases h5 : r5.ok = 0
            · have hEq : (readFriProof s).ok = 0 := by
                unfold readFriProof; dsimp only
                rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                    ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                    ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                    ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                    ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5, ite_eq_left (beq_iff_eq.mpr h5)]
              exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
            · have h5_1 := h01_5.resolve_left h5
              have hEq : readFriProof s =
                  { ok := 1
                    val :=
                      { commitPhaseCommits := r0.val, commitPowWitnesses := r1.val
                        inputOpenings := r2.val, commitPhaseOpenings := r3.val
                        finalPoly := r4.val, queryPowWitness := r5.val }
                    rest := r5.rest } := by
                unfold readFriProof; dsimp only
                rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                    ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                    ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                    ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                    ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5,
                    ite_eq_right (by rw [beq_iff_eq]; exact h5)]
              rw [hEq]
              refine ⟨Or.inr rfl, fun _ => ?_⟩
              obtain ⟨⟨c0, v0, s0'⟩, caps0, app0⟩ := hs0 h0_1
              obtain ⟨⟨c1, v1, s1'⟩, pw1, app1⟩ := hs1 h1_1
              obtain ⟨⟨c2, v2, s2'⟩, app2⟩ := hs2 h2_1
              obtain ⟨⟨c3, v3, s3'⟩, steps3, app3⟩ := hs3 h3_1
              obtain ⟨⟨c4, v4, s4'⟩, fp4, app4⟩ := hs4 h4_1
              have h5_1' : (readU64LE r4.rest).ok = 1 := by rw [hr5]; exact h5_1
              obtain ⟨v5, s5', _⟩ := readU64LE_sound r4.rest h5_1'
              rw [hr5] at v5 s5'
              refine ⟨⟨byteListAppend c0 (byteListAppend c1 (byteListAppend c2
                (byteListAppend c3 (byteListAppend c4 (u64BytesOnto r5.val .nil))))),
                validBytes_append.mpr ⟨v0, validBytes_append.mpr ⟨v1, validBytes_append.mpr ⟨v2,
                  validBytes_append.mpr ⟨v3, validBytes_append.mpr ⟨v4,
                    validBytes_u64BytesOnto.mpr ⟨v5, trivial⟩⟩⟩⟩⟩⟩, ?_⟩,
                caps0, pw1, steps3, fp4, v5, fun extra => ?_⟩
              · simp only [byteListAppend_assoc]
                rw [u64BytesOnto_append, byteListAppend, ← s5', ← s4', ← s3', ← s2', ← s1', ← s0']
              · unfold readFriProof; dsimp only
                rw [app0 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h0)]
                rw [app1 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h1)]
                rw [app2 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h2)]
                rw [app3 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h3)]
                rw [app4 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h4)]
                rw [readU64LE_append r4.rest extra h5_1', hr5]; dsimp only
                rw [ite_eq_right (by rw [beq_iff_eq]; exact h5)]

private theorem readPreprocessedOpt_props (s : ByteList) :
    ((readPreprocessedOpt s).ok = 0 ∨ (readPreprocessedOpt s).ok = 1) ∧
    ((readPreprocessedOpt s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readPreprocessedOpt s).rest) ∧
      (match (readPreprocessedOpt s).val with
        | .noPreprocessed => True
        | .somePreprocessed r => CanonicalOpenedRound r) ∧
      (∀ extra, readPreprocessedOpt (byteListAppend s extra) =
        { (readPreprocessedOpt s) with rest := byteListAppend (readPreprocessedOpt s).rest extra })) := by
  have h01 : (readU8 s).ok = 0 ∨ (readU8 s).ok = 1 := readLeNatAux_ok_zero_or_one 1 s 1 0
  generalize hrt : readU8 s = rt at h01
  by_cases h0 : rt.ok = 0
  · have hEq : (readPreprocessedOpt s).ok = 0 := by
      unfold readPreprocessedOpt; dsimp only; rw [hrt, ite_eq_left (beq_iff_eq.mpr h0)]
    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
  · have h1 : rt.ok = 1 := h01.resolve_left h0
    have h1' : (readU8 s).ok = 1 := by rw [hrt]; exact h1
    by_cases hv0 : rt.val = 0
    · have hEq : readPreprocessedOpt s = { ok := 1, val := .noPreprocessed, rest := rt.rest } := by
        unfold readPreprocessedOpt; dsimp only
        rw [hrt, ite_eq_right (by rw [beq_iff_eq]; exact h0), ite_eq_left (beq_iff_eq.mpr hv0)]
      rw [hEq]
      refine ⟨Or.inr rfl, fun _ => ?_⟩
      obtain ⟨hvt, hst, _⟩ := readU8_sound s h1'
      rw [hrt] at hvt hst
      refine ⟨⟨.cons rt.val .nil, ⟨hvt, trivial⟩, by simp only [byteListAppend]; exact hst⟩, trivial, fun extra => ?_⟩
      unfold readPreprocessedOpt; dsimp only
      rw [readU8_append s extra h1', hrt]; dsimp only
      rw [ite_eq_right (by rw [beq_iff_eq]; exact h0), ite_eq_left (beq_iff_eq.mpr hv0)]
    · by_cases hv1 : rt.val = 1
      · obtain ⟨h01r, hsr⟩ := readOpenedRound_props rt.rest
        have hEq : readPreprocessedOpt s =
            { ok := (readOpenedRound rt.rest).ok
              val := .somePreprocessed (readOpenedRound rt.rest).val
              rest := (readOpenedRound rt.rest).rest } := by
          unfold readPreprocessedOpt; dsimp only
          rw [hrt, ite_eq_right (by rw [beq_iff_eq]; exact h0),
              ite_eq_right (by rw [beq_iff_eq]; exact hv0), ite_eq_left (beq_iff_eq.mpr hv1)]
        rw [hEq]
        refine ⟨h01r, fun hok => ?_⟩
        obtain ⟨hvt, hst, _⟩ := readU8_sound s h1'
        rw [hrt] at hvt hst
        obtain ⟨⟨cr, hvr, hsr'⟩, hcanr, happr⟩ := hsr hok
        refine ⟨⟨.cons rt.val cr, ⟨hvt, hvr⟩, ?_⟩, hcanr, fun extra => ?_⟩
        · simp only [byteListAppend]; rw [← hsr', ← hst]
        · unfold readPreprocessedOpt; dsimp only
          rw [readU8_append s extra h1', hrt]; dsimp only
          rw [ite_eq_right (by rw [beq_iff_eq]; exact h0),
              ite_eq_right (by rw [beq_iff_eq]; exact hv0),
              ite_eq_left (beq_iff_eq.mpr hv1), happr extra]
      · have hEq : (readPreprocessedOpt s).ok = 0 := by
          unfold readPreprocessedOpt; dsimp only
          rw [hrt, ite_eq_right (by rw [beq_iff_eq]; exact h0),
              ite_eq_right (by rw [beq_iff_eq]; exact hv0),
              ite_eq_right (by rw [beq_iff_eq]; exact hv1)]
        exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩

private theorem readShardProof_props (s : ByteList) :
    ((readShardProof s).ok = 0 ∨ (readShardProof s).ok = 1) ∧
    ((readShardProof s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardProof s).rest) ∧
      ShardProofDecodedWF (readShardProof s).val ∧
      (∀ extra, readShardProof (byteListAppend s extra) =
        { (readShardProof s) with rest := byteListAppend (readShardProof s).rest extra })) := by
  obtain ⟨h01a, hsa⟩ := readU8Vec_props s
  generalize hra : readU8Vec s = ra at h01a hsa
  by_cases ha : ra.ok = 0
  · have hEq : (readShardProof s).ok = 0 := by
      unfold readShardProof; dsimp only; rw [hra, ite_eq_left (beq_iff_eq.mpr ha)]
    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
  · have ha1 := h01a.resolve_left ha
    obtain ⟨h01_0, hs0⟩ := readCommitments_props ra.rest
    generalize hr0 : readCommitments ra.rest = r0 at h01_0 hs0
    by_cases h0 : r0.ok = 0
    · have hEq : (readShardProof s).ok = 0 := by
        unfold readShardProof; dsimp only
        rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0, ite_eq_left (beq_iff_eq.mpr h0)]
      exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
    · have h0_1 := h01_0.resolve_left h0
      obtain ⟨h01_1, hs1⟩ := readExtVec_props r0.rest
      generalize hr1 : readExtVec r0.rest = r1 at h01_1 hs1
      by_cases h1 : r1.ok = 0
      · have hEq : (readShardProof s).ok = 0 := by
          unfold readShardProof; dsimp only
          rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
              ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1, ite_eq_left (beq_iff_eq.mpr h1)]
        exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
      · have h1_1 := h01_1.resolve_left h1
        obtain ⟨h01_2, hs2⟩ := readU8Vec_props r1.rest
        generalize hr2 : readU8Vec r1.rest = r2 at h01_2 hs2
        by_cases h2 : r2.ok = 0
        · have hEq : (readShardProof s).ok = 0 := by
            unfold readShardProof; dsimp only
            rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2, ite_eq_left (beq_iff_eq.mpr h2)]
          exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
        · have h2_1 := h01_2.resolve_left h2
          obtain ⟨h01_3, hs3⟩ := readFriProof_props r2.rest
          generalize hr3 : readFriProof r2.rest = r3 at h01_3 hs3
          by_cases h3 : r3.ok = 0
          · have hEq : (readShardProof s).ok = 0 := by
              unfold readShardProof; dsimp only
              rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                  ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                  ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                  ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3, ite_eq_left (beq_iff_eq.mpr h3)]
            exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
          · have h3_1 := h01_3.resolve_left h3
            obtain ⟨h01_4, hs4⟩ := readOpenedRound_props r3.rest
            generalize hr4 : readOpenedRound r3.rest = r4 at h01_4 hs4
            by_cases h4 : r4.ok = 0
            · have hEq : (readShardProof s).ok = 0 := by
                unfold readShardProof; dsimp only
                rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                    ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                    ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                    ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                    ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4, ite_eq_left (beq_iff_eq.mpr h4)]
              exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
            · have h4_1 := h01_4.resolve_left h4
              obtain ⟨h01_5, hs5⟩ := readPreprocessedOpt_props r4.rest
              generalize hr5 : readPreprocessedOpt r4.rest = r5 at h01_5 hs5
              by_cases h5 : r5.ok = 0
              · have hEq : (readShardProof s).ok = 0 := by
                  unfold readShardProof; dsimp only
                  rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                      ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                      ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                      ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                      ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                      ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5, ite_eq_left (beq_iff_eq.mpr h5)]
                exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
              · have h5_1 := h01_5.resolve_left h5
                obtain ⟨h01_6, hs6⟩ := readOpenedRound_props r5.rest
                generalize hr6 : readOpenedRound r5.rest = r6 at h01_6 hs6
                by_cases h6 : r6.ok = 0
                · have hEq : (readShardProof s).ok = 0 := by
                    unfold readShardProof; dsimp only
                    rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                        ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                        ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                        ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                        ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                        ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5,
                        ite_eq_right (by rw [beq_iff_eq]; exact h5), hr6, ite_eq_left (beq_iff_eq.mpr h6)]
                  exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
                · have h6_1 := h01_6.resolve_left h6
                  obtain ⟨h01_7, hs7⟩ := readOpenedRound_props r6.rest
                  generalize hr7 : readOpenedRound r6.rest = r7 at h01_7 hs7
                  by_cases h7 : r7.ok = 0
                  · have hEq : (readShardProof s).ok = 0 := by
                      unfold readShardProof; dsimp only
                      rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                          ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                          ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                          ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                          ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                          ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5,
                          ite_eq_right (by rw [beq_iff_eq]; exact h5), hr6,
                          ite_eq_right (by rw [beq_iff_eq]; exact h6), hr7, ite_eq_left (beq_iff_eq.mpr h7)]
                    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
                  · have h7_1 := h01_7.resolve_left h7
                    have hEq : readShardProof s =
                        { ok := 1
                          val :=
                            { active := ra.val, commitments := r0.val, intermediateAccs := r1.val
                              logDegrees := r2.val, openingProof := r3.val, quotientOpened := r4.val
                              preprocessedOpened := r5.val, stage1Opened := r6.val, stage2Opened := r7.val }
                          rest := r7.rest } := by
                      unfold readShardProof; dsimp only
                      rw [hra, ite_eq_right (by rw [beq_iff_eq]; exact ha), hr0,
                          ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                          ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                          ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                          ite_eq_right (by rw [beq_iff_eq]; exact h3), hr4,
                          ite_eq_right (by rw [beq_iff_eq]; exact h4), hr5,
                          ite_eq_right (by rw [beq_iff_eq]; exact h5), hr6,
                          ite_eq_right (by rw [beq_iff_eq]; exact h6), hr7,
                          ite_eq_right (by rw [beq_iff_eq]; exact h7)]
                    rw [hEq]
                    refine ⟨Or.inr rfl, fun _ => ?_⟩
                    obtain ⟨⟨ca, va, sa'⟩, appa⟩ := hsa ha1
                    obtain ⟨⟨c0, v0, s0'⟩, cs1, cs2, cq, app0⟩ := hs0 h0_1
                    obtain ⟨⟨c1, v1, s1'⟩, acc1, app1⟩ := hs1 h1_1
                    obtain ⟨⟨c2, v2, s2'⟩, app2⟩ := hs2 h2_1
                    obtain ⟨⟨c3, v3, s3'⟩, caps3, pw3, st3, fp3, qp3, app3⟩ := hs3 h3_1
                    obtain ⟨⟨c4, v4, s4'⟩, qo4, app4⟩ := hs4 h4_1
                    obtain ⟨⟨c5, v5, s5'⟩, po5, app5⟩ := hs5 h5_1
                    obtain ⟨⟨c6, v6, s6'⟩, s1o6, app6⟩ := hs6 h6_1
                    obtain ⟨⟨c7, v7, s7'⟩, s2o7, app7⟩ := hs7 h7_1
                    refine ⟨⟨byteListAppend ca (byteListAppend c0 (byteListAppend c1
                      (byteListAppend c2 (byteListAppend c3 (byteListAppend c4
                        (byteListAppend c5 (byteListAppend c6 c7))))))),
                      validBytes_append.mpr ⟨va, validBytes_append.mpr ⟨v0, validBytes_append.mpr ⟨v1,
                        validBytes_append.mpr ⟨v2, validBytes_append.mpr ⟨v3, validBytes_append.mpr ⟨v4,
                          validBytes_append.mpr ⟨v5, validBytes_append.mpr ⟨v6, v7⟩⟩⟩⟩⟩⟩⟩⟩, ?_⟩,
                      ⟨cs1, cs2, cq, acc1, caps3, pw3, st3, fp3, qp3, qo4, po5, s1o6, s2o7⟩,
                      fun extra => ?_⟩
                    · simp only [byteListAppend_assoc]
                      rw [← s7', ← s6', ← s5', ← s4', ← s3', ← s2', ← s1', ← s0', ← sa']
                    · unfold readShardProof; dsimp only
                      rw [appa extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact ha)]
                      rw [app0 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h0)]
                      rw [app1 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h1)]
                      rw [app2 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h2)]
                      rw [app3 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h3)]
                      rw [app4 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h4)]
                      rw [app5 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h5)]
                      rw [app6 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h6)]
                      rw [app7 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h7)]

private theorem readShardProofVecN_props (s : ByteList) (n : Nat) :
    ((readShardProofVecN s n).ok = 0 ∨ (readShardProofVecN s n).ok = 1) ∧
    ((readShardProofVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardProofVecN s n).rest) ∧
      ShardProofsDecodedWF (readShardProofVecN s n).val ∧
      (∀ extra, readShardProofVecN (byteListAppend s extra) n =
        { (readShardProofVecN s n) with rest := byteListAppend (readShardProofVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readShardProofVecN]
    obtain ⟨h01r, hsr⟩ := readShardProof_props s
    by_cases h0 : (readShardProof s).ok = 0
    · simp [h0]
    · have h1 := h01r.resolve_left h0
      have h0b : ((readShardProof s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readShardProof s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hwf0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hwf0, hwf1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readShardProofVec_props (s : ByteList) :
    ((readShardProofVec s).ok = 0 ∨ (readShardProofVec s).ok = 1) ∧
    ((readShardProofVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardProofVec s).rest) ∧
      ShardProofsDecodedWF (readShardProofVec s).val ∧
      (∀ extra, readShardProofVec (byteListAppend s extra) =
        { (readShardProofVec s) with rest := byteListAppend (readShardProofVec s).rest extra })) := by
  simp only [readShardProofVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readShardProofVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hwf1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readShardHeader_props (s : ByteList) :
    ((readShardHeader s).ok = 0 ∨ (readShardHeader s).ok = 1) ∧
    ((readShardHeader s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardHeader s).rest) ∧
      ShardHeaderDecodedWF (readShardHeader s).val ∧
      (∀ extra, readShardHeader (byteListAppend s extra) =
        { (readShardHeader s) with rest := byteListAppend (readShardHeader s).rest extra })) := by
  obtain ⟨h01_0, hs0⟩ := readU8Vec_props s
  generalize hr0 : readU8Vec s = r0 at h01_0 hs0
  by_cases h0 : r0.ok = 0
  · have hEq : (readShardHeader s).ok = 0 := by
      unfold readShardHeader; dsimp only; rw [hr0, ite_eq_left (beq_iff_eq.mpr h0)]
    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
  · have h0_1 := h01_0.resolve_left h0
    obtain ⟨h01_1, hs1⟩ := readMerkleCap_props r0.rest
    generalize hr1 : readMerkleCap r0.rest = r1 at h01_1 hs1
    by_cases h1 : r1.ok = 0
    · have hEq : (readShardHeader s).ok = 0 := by
        unfold readShardHeader; dsimp only
        rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1, ite_eq_left (beq_iff_eq.mpr h1)]
      exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
    · have h1_1 := h01_1.resolve_left h1
      obtain ⟨h01_2, hs2⟩ := readU8Vec_props r1.rest
      generalize hr2 : readU8Vec r1.rest = r2 at h01_2 hs2
      by_cases h2 : r2.ok = 0
      · have hEq : (readShardHeader s).ok = 0 := by
          unfold readShardHeader; dsimp only
          rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
              ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2, ite_eq_left (beq_iff_eq.mpr h2)]
        exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
      · have h2_1 := h01_2.resolve_left h2
        obtain ⟨h01_3, hs3⟩ := readU64VecVec_props r2.rest
        generalize hr3 : readU64VecVec r2.rest = r3 at h01_3 hs3
        by_cases h3 : r3.ok = 0
        · have hEq : (readShardHeader s).ok = 0 := by
            unfold readShardHeader; dsimp only
            rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3, ite_eq_left (beq_iff_eq.mpr h3)]
          exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
        · have h3_1 := h01_3.resolve_left h3
          by_cases hcan : u64ListListAllLtP r3.val = 0
          · have hEq : (readShardHeader s).ok = 0 := by
              unfold readShardHeader; dsimp only
              rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                  ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                  ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                  ite_eq_right (by rw [beq_iff_eq]; exact h3), ite_eq_left (beq_iff_eq.mpr hcan)]
            exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
          · have hcan1 := (u64ListListAllLtP_zero_or_one r3.val).resolve_left hcan
            have hEq : readShardHeader s =
                { ok := 1
                  val := { active := r0.val, stage1 := r1.val, logDegrees := r2.val, claims := r3.val }
                  rest := r3.rest } := by
              unfold readShardHeader; dsimp only
              rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                  ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                  ite_eq_right (by rw [beq_iff_eq]; exact h2), hr3,
                  ite_eq_right (by rw [beq_iff_eq]; exact h3),
                  ite_eq_right (by rw [beq_iff_eq]; exact hcan)]
            rw [hEq]
            refine ⟨Or.inr rfl, fun _ => ?_⟩
            obtain ⟨⟨c0, v0, s0'⟩, app0⟩ := hs0 h0_1
            obtain ⟨⟨c1, v1, s1'⟩, cap1, app1⟩ := hs1 h1_1
            obtain ⟨⟨c2, v2, s2'⟩, app2⟩ := hs2 h2_1
            obtain ⟨⟨c3, v3, s3'⟩, hvl3, app3⟩ := hs3 h3_1
            refine ⟨⟨byteListAppend c0 (byteListAppend c1 (byteListAppend c2 c3)),
              validBytes_append.mpr ⟨v0, validBytes_append.mpr ⟨v1, validBytes_append.mpr ⟨v2, v3⟩⟩⟩,
              by simp only [byteListAppend_assoc]; rw [← s3', ← s2', ← s1', ← s0']⟩,
              ⟨cap1, u64ListListAllLtP_canonical hvl3 hcan1⟩, fun extra => ?_⟩
            unfold readShardHeader; dsimp only
            rw [app0 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h0)]
            rw [app1 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h1)]
            rw [app2 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h2)]
            rw [app3 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h3),
                ite_eq_right (by rw [beq_iff_eq]; exact hcan)]

private theorem readShardHeaderVecN_props (s : ByteList) (n : Nat) :
    ((readShardHeaderVecN s n).ok = 0 ∨ (readShardHeaderVecN s n).ok = 1) ∧
    ((readShardHeaderVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardHeaderVecN s n).rest) ∧
      ShardHeadersDecodedWF (readShardHeaderVecN s n).val ∧
      (∀ extra, readShardHeaderVecN (byteListAppend s extra) n =
        { (readShardHeaderVecN s n) with rest := byteListAppend (readShardHeaderVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readShardHeaderVecN]
    obtain ⟨h01r, hsr⟩ := readShardHeader_props s
    by_cases h0 : (readShardHeader s).ok = 0
    · simp [h0]
    · have h1 := h01r.resolve_left h0
      have h0b : ((readShardHeader s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readShardHeader s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hwf0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hwf0, hwf1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readShardHeaderVec_props (s : ByteList) :
    ((readShardHeaderVec s).ok = 0 ∨ (readShardHeaderVec s).ok = 1) ∧
    ((readShardHeaderVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readShardHeaderVec s).rest) ∧
      ShardHeadersDecodedWF (readShardHeaderVec s).val ∧
      (∀ extra, readShardHeaderVec (byteListAppend s extra) =
        { (readShardHeaderVec s) with rest := byteListAppend (readShardHeaderVec s).rest extra })) := by
  simp only [readShardHeaderVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readShardHeaderVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hwf1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readBatchMessage_props (s : ByteList) :
    ((readBatchMessage s).ok = 0 ∨ (readBatchMessage s).ok = 1) ∧
    ((readBatchMessage s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchMessage s).rest) ∧
      BatchMessageDecodedWF (readBatchMessage s).val ∧
      (∀ extra, readBatchMessage (byteListAppend s extra) =
        { (readBatchMessage s) with rest := byteListAppend (readBatchMessage s).rest extra })) := by
  obtain ⟨h01_0, hs0⟩ := readU64Vec_props s
  generalize hr0 : readU64Vec s = r0 at h01_0 hs0
  by_cases hbad0 : (r0.ok == 0 || u64ListAllLtP r0.val == 0) = true
  · have hEq : (readBatchMessage s).ok = 0 := by
      unfold readBatchMessage; dsimp only; rw [hr0, ite_eq_left hbad0]
    exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
  · have hbad0F : (r0.ok == 0 || u64ListAllLtP r0.val == 0) = false := Bool.eq_false_iff.mpr hbad0
    have hbad0F' := hbad0F
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hbad0F'
    have h0_1 := h01_0.resolve_left hbad0F'.1
    have hcan0 := (u64ListAllLtP_zero_or_one r0.val).resolve_left hbad0F'.2
    have h01_1 := readU64LE_ok_zero_or_one r0.rest
    generalize hr1 : readU64LE r0.rest = r1 at h01_1
    by_cases hbad1 : (r1.ok == 0 || glLtPBytes r1.val == 0) = true
    · have hEq : (readBatchMessage s).ok = 0 := by
        unfold readBatchMessage; dsimp only; rw [hr0, ite_eq_right hbad0, hr1, ite_eq_left hbad1]
      exact ⟨Or.inl hEq, fun h => by rw [hEq] at h; cases h⟩
    · have hbad1F : (r1.ok == 0 || glLtPBytes r1.val == 0) = false := Bool.eq_false_iff.mpr hbad1
      have hbad1F' := hbad1F
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hbad1F'
      have h1_1 := h01_1.resolve_left hbad1F'.1
      have h1_1' : (readU64LE r0.rest).ok = 1 := by rw [hr1]; exact h1_1
      have hlt1 := (glLtPBytes_zero_or_one r1.val).resolve_left hbad1F'.2
      have hEq : readBatchMessage s =
          { ok := 1, val := { args := r0.val, multiplicity := r1.val }, rest := r1.rest } := by
        unfold readBatchMessage; dsimp only; rw [hr0, ite_eq_right hbad0, hr1, ite_eq_right hbad1]
      rw [hEq]
      refine ⟨Or.inr rfl, fun _ => ?_⟩
      obtain ⟨⟨c0, v0, s0'⟩, hvl0, app0⟩ := hs0 h0_1
      obtain ⟨v1, s1', _⟩ := readU64LE_sound r0.rest h1_1'
      rw [hr1] at v1 s1'
      refine ⟨⟨byteListAppend c0 (u64BytesOnto r1.val .nil),
        validBytes_append.mpr ⟨v0, validBytes_u64BytesOnto.mpr ⟨v1, trivial⟩⟩,
        by rw [byteListAppend_assoc, u64BytesOnto_append, byteListAppend, ← s1', ← s0']⟩,
        ⟨u64ListAllLtP_canonical hvl0 hcan0, v1, (glLtPBytes_eq_one_iff v1).mp hlt1⟩,
        fun extra => ?_⟩
      unfold readBatchMessage; dsimp only
      rw [app0 extra]; dsimp only; rw [ite_eq_right hbad0]
      rw [readU64LE_append r0.rest extra h1_1', hr1]; dsimp only; rw [ite_eq_right hbad1]

private theorem readBatchMessageVecN_props (s : ByteList) (n : Nat) :
    ((readBatchMessageVecN s n).ok = 0 ∨ (readBatchMessageVecN s n).ok = 1) ∧
    ((readBatchMessageVecN s n).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchMessageVecN s n).rest) ∧
      BatchMessagesDecodedWF (readBatchMessageVecN s n).val ∧
      (∀ extra, readBatchMessageVecN (byteListAppend s extra) n =
        { (readBatchMessageVecN s n) with rest := byteListAppend (readBatchMessageVecN s n).rest extra })) := by
  induction n generalizing s with
  | zero => exact ⟨Or.inr rfl, fun _ => ⟨⟨.nil, trivial, rfl⟩, trivial, fun _ => rfl⟩⟩
  | succ n ih =>
    simp only [readBatchMessageVecN]
    obtain ⟨h01r, hsr⟩ := readBatchMessage_props s
    by_cases h0 : (readBatchMessage s).ok = 0
    · simp [h0]
    · have h1 := h01r.resolve_left h0
      have h0b : ((readBatchMessage s).ok == 0) = false := beq_false_of_ne h0
      simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h01t, hst⟩ := ih (readBatchMessage s).rest
      refine ⟨h01t, fun hok => ?_⟩
      obtain ⟨⟨c0, hv0, hs0⟩, hwf0, happ0⟩ := hsr h1
      obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
      refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
        by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, ⟨hwf0, hwf1⟩, fun extra => ?_⟩
      rw [happ0 extra]; simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

private theorem readBatchMessageVec_props (s : ByteList) :
    ((readBatchMessageVec s).ok = 0 ∨ (readBatchMessageVec s).ok = 1) ∧
    ((readBatchMessageVec s).ok = 1 →
      (∃ c, ValidBytes c ∧ s = byteListAppend c (readBatchMessageVec s).rest) ∧
      BatchMessagesDecodedWF (readBatchMessageVec s).val ∧
      (∀ extra, readBatchMessageVec (byteListAppend s extra) =
        { (readBatchMessageVec s) with rest := byteListAppend (readBatchMessageVec s).rest extra })) := by
  simp only [readBatchMessageVec]
  by_cases h0 : (readCount s).ok = 0
  · simp [h0]
  · have h1 := (readCount_ok_zero_or_one s).resolve_left h0
    have h0b : ((readCount s).ok == 0) = false := beq_false_of_ne h0
    simp only [h0b, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨h01t, hst⟩ := readBatchMessageVecN_props (readCount s).rest (readCount s).val
    refine ⟨h01t, fun hok => ?_⟩
    obtain ⟨c0, _, hv0, hs0, _, _, _⟩ := readCount_sound s h1
    obtain ⟨⟨c1, hv1, hs1⟩, hwf1, happ1⟩ := hst hok
    refine ⟨⟨byteListAppend c0 c1, validBytes_append.mpr ⟨hv0, hv1⟩,
      by rw [byteListAppend_assoc, ← hs1, ← hs0]⟩, hwf1, fun extra => ?_⟩
    rw [readCount_append s extra h1]
    simp only [h0b, Bool.false_eq_true, ↓reduceIte, happ1 extra]

/-- **Headline Wire Soundness (`readBatchProof`)**:
acceptance implies complete consumption (`rest = .nil`), `< 256` validity of all bytes,
full decoded well-formedness (`BatchProofDecodedWellFormed`: length-1 Merkle caps, canonical
`< p_GL` header claims, batch messages, `ExtGl` openings/siblings/finalPoly), and strict
canonical trailing-byte rejection on any non-empty suffix `extra`. -/
theorem readBatchProof_sound (s : ByteList) (hok : (readBatchProof s).ok = 1) :
    let r := readBatchProof s
    r.rest = .nil ∧
    ValidBytes s ∧
    BatchProofDecodedWellFormed r.val ∧
    (∀ extra : ByteList, extra ≠ .nil → (readBatchProof (byteListAppend s extra)).ok = 0) := by
  obtain ⟨h01_0, hs0⟩ := readShardHeaderVec_props s
  generalize hr0 : readShardHeaderVec s = r0 at h01_0 hs0
  by_cases h0 : r0.ok = 0
  · have hEq : (readBatchProof s).ok = 0 := by
      unfold readBatchProof; dsimp only; rw [hr0, ite_eq_left (beq_iff_eq.mpr h0)]
    rw [hEq] at hok; cases hok
  · have h0_1 := h01_0.resolve_left h0
    obtain ⟨h01_1, hs1⟩ := readBatchMessageVec_props r0.rest
    generalize hr1 : readBatchMessageVec r0.rest = r1 at h01_1 hs1
    by_cases h1 : r1.ok = 0
    · have hEq : (readBatchProof s).ok = 0 := by
        unfold readBatchProof; dsimp only
        rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1, ite_eq_left (beq_iff_eq.mpr h1)]
      rw [hEq] at hok; cases hok
    · have h1_1 := h01_1.resolve_left h1
      obtain ⟨h01_2, hs2⟩ := readShardProofVec_props r1.rest
      generalize hr2 : readShardProofVec r1.rest = r2 at h01_2 hs2
      by_cases h2 : r2.ok = 0
      · have hEq : (readBatchProof s).ok = 0 := by
          unfold readBatchProof; dsimp only
          rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
              ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2, ite_eq_left (beq_iff_eq.mpr h2)]
        rw [hEq] at hok; cases hok
      · have h2_1 := h01_2.resolve_left h2
        cases hrest : r2.rest with
        | cons _ _ =>
          have hEq : (readBatchProof s).ok = 0 := by
            unfold readBatchProof; dsimp only
            rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                ite_eq_right (by rw [beq_iff_eq]; exact h2), hrest]
          rw [hEq] at hok; cases hok
        | nil =>
          have hEq : readBatchProof s =
              { ok := 1, val := { headers := r0.val, messages := r1.val, proofs := r2.val }, rest := .nil } := by
            unfold readBatchProof; dsimp only
            rw [hr0, ite_eq_right (by rw [beq_iff_eq]; exact h0), hr1,
                ite_eq_right (by rw [beq_iff_eq]; exact h1), hr2,
                ite_eq_right (by rw [beq_iff_eq]; exact h2), hrest]
          obtain ⟨⟨c0, v0, s0'⟩, hwfh, app0⟩ := hs0 h0_1
          obtain ⟨⟨c1, v1, s1'⟩, hwfm, app1⟩ := hs1 h1_1
          obtain ⟨⟨c2, v2, s2'⟩, hwfp, app2⟩ := hs2 h2_1
          rw [hrest, byteListAppend_nil_right] at s2'
          have hsEq : s = byteListAppend c0 (byteListAppend c1 c2) := by
            rw [← s2', ← s1', ← s0']
          dsimp only
          rw [hEq]
          refine ⟨rfl, hsEq ▸ validBytes_append.mpr ⟨v0, validBytes_append.mpr ⟨v1, v2⟩⟩,
            ⟨hwfh, hwfm, hwfp⟩, ?_⟩
          intro extra hextra
          unfold readBatchProof; dsimp only
          rw [app0 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h0)]
          rw [app1 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h1)]
          rw [app2 extra]; dsimp only; rw [ite_eq_right (by rw [beq_iff_eq]; exact h2), hrest, byteListAppend]
          cases extra with
          | nil => exact absurd rfl hextra
          | cons _ _ => rfl

/-! ## Section 3: Pure Multi-Block / Multi-Chunk BLAKE3 Parity, Statement Binding & Protocol `v6` Challenger -/

/-! ### Section 3A: Pure Multi-Block / Multi-Chunk BLAKE3 Equivalence -/

/-- Convert `StarkWire.State16` to `Blake3.Pure.Block`. -/
def state16ToPure (s : State16) : Blake3.Pure.Block :=
  #v[s.v0, s.v1, s.v2, s.v3, s.v4, s.v5, s.v6, s.v7,
     s.v8, s.v9, s.v10, s.v11, s.v12, s.v13, s.v14, s.v15]

/-- Convert `StarkWire.Block16` to `Blake3.Pure.Block`. -/
def block16ToPure (m : Block16) : Blake3.Pure.Block :=
  #v[m.m0, m.m1, m.m2, m.m3, m.m4, m.m5, m.m6, m.m7,
     m.m8, m.m9, m.m10, m.m11, m.m12, m.m13, m.m14, m.m15]

/-- Convert `StarkWire.LayerStack` (oldest-first) to a `List Blake3.Pure.CV`. -/
def layerStackToList : LayerStack → List Blake3.Pure.CV
  | .nil => []
  | .push rest d => layerStackToList rest ++ [digest32ToCV d]

theorem layerStackToList_length (layer : LayerStack) :
    (layerStackToList layer).length = layerStackDepth layer := by
  induction layer with
  | nil => rfl
  | push rest d ih =>
    simp only [layerStackToList, layerStackDepth, List.length_append, List.length_singleton, ih]
    omega

private theorem blake3G_eq_mix (a b c d x y : UInt32) :
    Blake3.Pure.mix a b c d x y =
      let q := blake3G a b c d x y
      #v[q.a, q.b, q.c, q.d] := rfl

private theorem b3_g_col0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 4 8 12 x y =
      let q := blake3G v0 v4 v8 v12 x y
      #v[q.a, v1, v2, v3, q.b, v5, v6, v7, q.c, v9, v10, v11, q.d, v13, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v0 v4 v8 v12 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_col1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 5 9 13 x y =
      let q := blake3G v1 v5 v9 v13 x y
      #v[v0, q.a, v2, v3, v4, q.b, v6, v7, v8, q.c, v10, v11, v12, q.d, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v1 v5 v9 v13 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_col2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 6 10 14 x y =
      let q := blake3G v2 v6 v10 v14 x y
      #v[v0, v1, q.a, v3, v4, v5, q.b, v7, v8, v9, q.c, v11, v12, v13, q.d, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v2 v6 v10 v14 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_col3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 7 11 15 x y =
      let q := blake3G v3 v7 v11 v15 x y
      #v[v0, v1, v2, q.a, v4, v5, v6, q.b, v8, v9, v10, q.c, v12, v13, v14, q.d] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v3 v7 v11 v15 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_diag0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 5 10 15 x y =
      let q := blake3G v0 v5 v10 v15 x y
      #v[q.a, v1, v2, v3, v4, q.b, v6, v7, v8, v9, q.c, v11, v12, v13, v14, q.d] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v0 v5 v10 v15 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_diag1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 6 11 12 x y =
      let q := blake3G v1 v6 v11 v12 x y
      #v[v0, q.a, v2, v3, v4, v5, q.b, v7, v8, v9, v10, q.c, q.d, v13, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v1 v6 v11 v12 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_diag2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 7 8 13 x y =
      let q := blake3G v2 v7 v8 v13 x y
      #v[v0, v1, q.a, v3, v4, v5, v6, q.b, q.c, v9, v10, v11, v12, q.d, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v2 v7 v8 v13 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem b3_g_diag3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 4 9 14 x y =
      let q := blake3G v3 v4 v9 v14 x y
      #v[v0, v1, v2, q.a, q.b, v5, v6, v7, v8, q.c, v10, v11, v12, v13, q.d, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v3 v4 v9 v14 x y; _ = _
  rw [blake3G_eq_mix]; rfl

private theorem blake3Round_eq (s : State16) (m : Block16)
    (msg : Blake3.Pure.Block) (sched : Vector (Fin 16) 16)
    (h0 : m.m0 = msg[sched[0]]) (h1 : m.m1 = msg[sched[1]])
    (h2 : m.m2 = msg[sched[2]]) (h3 : m.m3 = msg[sched[3]])
    (h4 : m.m4 = msg[sched[4]]) (h5 : m.m5 = msg[sched[5]])
    (h6 : m.m6 = msg[sched[6]]) (h7 : m.m7 = msg[sched[7]])
    (h8 : m.m8 = msg[sched[8]]) (h9 : m.m9 = msg[sched[9]])
    (h10 : m.m10 = msg[sched[10]]) (h11 : m.m11 = msg[sched[11]])
    (h12 : m.m12 = msg[sched[12]]) (h13 : m.m13 = msg[sched[13]])
    (h14 : m.m14 = msg[sched[14]]) (h15 : m.m15 = msg[sched[15]]) :
    state16ToPure (blake3Round s m) = Blake3.Pure.round (state16ToPure s) msg sched := by
  unfold blake3Round Blake3.Pure.round state16ToPure
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7,
      ← h8, ← h9, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15]
  simp only [b3_g_col0, b3_g_col1, b3_g_col2, b3_g_col3,
    b3_g_diag0, b3_g_diag1, b3_g_diag2, b3_g_diag3]

/-- Exact 7-round BLAKE3 compression equivalence between `StarkWire.blake3Compress` and
`Blake3.Pure.compress` for any 64-bit chunk counter `ctr`. -/
theorem blake3Compress_eq_pure (cv : Digest32) (m : Block16) (ctr : UInt64)
    (blockLen flags : UInt32) :
    digest32ToCV (blake3Compress cv m ctr.toUInt32 (ctr >>> 32).toUInt32 blockLen flags) =
      Blake3.Pure.compress (digest32ToCV cv) (block16ToPure m) ctr blockLen flags := by
  unfold blake3Compress Blake3.Pure.compress
  set s0 : State16 :=
    { v0 := cv.w0, v1 := cv.w1, v2 := cv.w2, v3 := cv.w3
      v4 := cv.w4, v5 := cv.w5, v6 := cv.w6, v7 := cv.w7
      v8 := blake3IV.w0, v9 := blake3IV.w1, v10 := blake3IV.w2, v11 := blake3IV.w3
      v12 := ctr.toUInt32, v13 := (ctr >>> 32).toUInt32, v14 := blockLen, v15 := flags }
  set s7 : State16 :=
    blake3Round (blake3Round (blake3Round (blake3Round
      (blake3Round (blake3Round (blake3Round s0 m)
        (blake3Permute m))
        (blake3Permute (blake3Permute m)))
        (blake3Permute (blake3Permute (blake3Permute m))))
        (blake3Permute (blake3Permute (blake3Permute (blake3Permute m)))))
        (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute m))))))
        (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute m))))))
  have hfold :
      Blake3.Pure.schedules.foldl
        (fun state schedule => Blake3.Pure.round state (block16ToPure m) schedule)
        (Blake3.Pure.initialWords (digest32ToCV cv) ctr blockLen flags) =
      state16ToPure s7 := by
    have hinit : Blake3.Pure.initialWords (digest32ToCV cv) ctr blockLen flags = state16ToPure s0 := rfl
    rw [hinit]
    change
      Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round
        (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round (state16ToPure s0)
          (block16ToPure m) Blake3.Pure.schedules[0])
          (block16ToPure m) Blake3.Pure.schedules[1])
          (block16ToPure m) Blake3.Pure.schedules[2])
          (block16ToPure m) Blake3.Pure.schedules[3])
          (block16ToPure m) Blake3.Pure.schedules[4])
          (block16ToPure m) Blake3.Pure.schedules[5])
          (block16ToPure m) Blake3.Pure.schedules[6] =
      state16ToPure s7
    rw [← blake3Round_eq s0 m (block16ToPure m) Blake3.Pure.schedules[0]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute m) (block16ToPure m) Blake3.Pure.schedules[1]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute (blake3Permute m)) (block16ToPure m) Blake3.Pure.schedules[2]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute (blake3Permute (blake3Permute m)))
      (block16ToPure m) Blake3.Pure.schedules[3]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute (blake3Permute (blake3Permute (blake3Permute m))))
      (block16ToPure m) Blake3.Pure.schedules[4]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute m)))))
      (block16ToPure m) Blake3.Pure.schedules[5]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← blake3Round_eq _ (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute (blake3Permute m))))))
      (block16ToPure m) Blake3.Pure.schedules[6]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
  rw [hfold]
  change digest32ToCV
    { w0 := UInt32.xor s7.v0 s7.v8,  w1 := UInt32.xor s7.v1 s7.v9
      w2 := UInt32.xor s7.v2 s7.v10, w3 := UInt32.xor s7.v3 s7.v11
      w4 := UInt32.xor s7.v4 s7.v12, w5 := UInt32.xor s7.v5 s7.v13
      w6 := UInt32.xor s7.v6 s7.v14, w7 := UInt32.xor s7.v7 s7.v15 } = _
  cases s7; rfl

theorem uint32_add_eq_or_of_validDomainFlags {baseFlag bFlags : UInt32}
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) (hb : bFlags.toNat < 16) :
    UInt32.add baseFlag bFlags = baseFlag ||| bFlags := by
  apply UInt32.toNat_inj.mp
  rw [IxCC.AiurBackend.Blake3KeyedSpec.or_toNat_eq_add_of_validDomainFlags hd hb]
  change (baseFlag + bFlags).toNat = baseFlag.toNat + bFlags.toNat
  rw [UInt32.toNat_add]
  have hlt : baseFlag.toNat + bFlags.toNat < 2 ^ 32 := by have := hd.1; omega
  exact Nat.mod_eq_of_lt hlt

/-! ### Little-Endian Word / Digest Packing Lemmas -/

theorem u32Onto_toUInt8List (w : UInt32) (tail : ByteList) :
    byteListToUInt8List (u32Onto w tail) =
      (Blake3.Pure.wordBytes w).toList ++ byteListToUInt8List tail := by
  have hw := w.toNat_lt
  unfold u32Onto Blake3.Pure.wordBytes
  simp only [byteListToUInt8List]
  have hvec : (Vector.ofFn fun i : Fin 4 => UInt8.ofNat (w.toNat / 256 ^ i.val)).toList =
      [UInt8.ofNat (w.toNat / 256 ^ 0), UInt8.ofNat (w.toNat / 256 ^ 1),
       UInt8.ofNat (w.toNat / 256 ^ 2), UInt8.ofNat (w.toNat / 256 ^ 3)] := rfl
  rw [hvec]
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt8.toNat_ofNat', Nat.div_div_eq_div_mul] <;> omega

theorem digest32Onto_toUInt8List (h : Digest32) (tail : ByteList) :
    byteListToUInt8List (digest32Onto h tail) =
      (Blake3.Pure.cvBytes (digest32ToCV h)).toList ++ byteListToUInt8List tail := by
  have hwb (w : UInt32) :
      (Blake3.Pure.wordBytes w).toList =
        [UInt8.ofNat (w.toNat / 256 ^ 0), UInt8.ofNat (w.toNat / 256 ^ 1),
         UInt8.ofNat (w.toNat / 256 ^ 2), UInt8.ofNat (w.toNat / 256 ^ 3)] := rfl
  have hcv : (Blake3.Pure.cvBytes (digest32ToCV h)).toList =
      (Blake3.Pure.wordBytes h.w0).toList ++ (Blake3.Pure.wordBytes h.w1).toList ++
      (Blake3.Pure.wordBytes h.w2).toList ++ (Blake3.Pure.wordBytes h.w3).toList ++
      (Blake3.Pure.wordBytes h.w4).toList ++ (Blake3.Pure.wordBytes h.w5).toList ++
      (Blake3.Pure.wordBytes h.w6).toList ++ (Blake3.Pure.wordBytes h.w7).toList := by
    simp only [hwb, List.cons_append, List.nil_append]
    apply List.ext_getElem (by simp [Blake3.Pure.cvBytes])
    intro i hi1 hi2
    have hi32 : i < 32 := by simpa using hi1
    simp only [Vector.getElem_toList, Blake3.Pure.cvBytes, Vector.getElem_ofFn, digest32ToCV]
    interval_cases i <;> rfl
  unfold digest32Onto
  simp only [u32Onto_toUInt8List, ← List.append_assoc]
  rw [hcv]

theorem u64OfTwoU32_toUInt8List (lo hi : UInt32) (tail : ByteList) :
    byteListToUInt8List (u64BytesOnto (u64OfTwoU32 lo hi) tail) =
      (Blake3.Pure.wordBytes lo).toList ++ (Blake3.Pure.wordBytes hi).toList ++
      byteListToUInt8List tail := by
  have h1 : u64BytesOnto (u64OfTwoU32 lo hi) tail = u32Onto lo (u32Onto hi tail) := rfl
  rw [h1, u32Onto_toUInt8List, u32Onto_toUInt8List, List.append_assoc]

theorem digest32ToDigestBytes_toUInt8List (h : Digest32) (tail : ByteList) :
    byteListToUInt8List (digestBytesOnto (digest32ToDigestBytes h) tail) =
      (Blake3.Pure.cvBytes (digest32ToCV h)).toList ++ byteListToUInt8List tail := by
  have h1 : digestBytesOnto (digest32ToDigestBytes h) tail = digest32Onto h tail := rfl
  rw [h1, digest32Onto_toUInt8List]

theorem digest32ToDigestBytes_toCV (h : Digest32) :
    digestBytesToCV (digest32ToDigestBytes h) = digest32ToCV h := by
  have hrepack (w : UInt32) :
      u32OfBytes (w.toNat % 256) ((w.toNat / 256) % 256)
        ((w.toNat / 256 / 256) % 256) (w.toNat / 256 / 256 / 256) = w := by
    apply UInt32.toNat_inj.mp
    have hw := w.toNat_lt
    have hd := u32_byte_decomp hw
    unfold u32OfBytes
    rw [UInt32.toNat_ofNat']
    have hq3 : (w.toNat / 256 / 256 / 256) % 256 = w.toNat / 256 / 256 / 256 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hq3] at hd
    rw [← hd, Nat.mod_eq_of_lt hw]
  unfold digestBytesToCV digest32ToDigestBytes digest32ToCV u64LoU32 u64HiU32 u64OfTwoU32
  dsimp only
  simp only [hrepack]

theorem packBytes32ToU32Words_cvBytes (h : Digest32) :
    Ix.Cert.AiurCompression.packBytes32ToU32Words (Blake3.Pure.cvBytes (digest32ToCV h)).toList =
      digest32WordsToList (packDigest h) := by
  have hu32 (w : UInt32) :
      Ix.Cert.AiurCompression.u32leOf4
        (Blake3.Pure.wordBytes w)[0] (Blake3.Pure.wordBytes w)[1]
        (Blake3.Pure.wordBytes w)[2] (Blake3.Pure.wordBytes w)[3] = w.toNat := by
    have hw := w.toNat_lt
    have hd := u32_byte_decomp hw
    unfold Ix.Cert.AiurCompression.u32leOf4 Blake3.Pure.wordBytes
    simp only [Vector.getElem_ofFn, UInt8.toNat_ofNat', Nat.pow_zero, Nat.div_one]
    have h2 : w.toNat / 256 ^ 2 = w.toNat / 256 / 256 := by rw [Nat.div_div_eq_div_mul]; rfl
    have h3 : w.toNat / 256 ^ 3 = w.toNat / 256 / 256 / 256 := by
      simp only [Nat.div_div_eq_div_mul]; rfl
    rw [show 256 ^ 1 = 256 by rfl, h2, h3]
    omega
  unfold Ix.Cert.AiurCompression.packBytes32ToU32Words digest32WordsToList packDigest
  have hget (k : Nat) (hk : k < 32) :
      (Blake3.Pure.cvBytes (digest32ToCV h)).toList.getD k 0 =
        (Blake3.Pure.wordBytes ((digest32ToCV h)[k / 4]'(by omega)))[k % 4]'(Nat.mod_lt _ (by decide)) := by
    rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [Vector.length_toList]; exact hk),
        Option.getD_some, Vector.getElem_toList]
    simp only [Blake3.Pure.cvBytes, Vector.getElem_ofFn]
  change List.map _ [0, 1, 2, 3, 4, 5, 6, 7] = _
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hget 0 (by decide), hget 1 (by decide), hget 2 (by decide), hget 3 (by decide)]; exact hu32 h.w0
  · rw [hget 4 (by decide), hget 5 (by decide), hget 6 (by decide), hget 7 (by decide)]; exact hu32 h.w1
  · rw [hget 8 (by decide), hget 9 (by decide), hget 10 (by decide), hget 11 (by decide)]; exact hu32 h.w2
  · rw [hget 12 (by decide), hget 13 (by decide), hget 14 (by decide), hget 15 (by decide)]; exact hu32 h.w3
  · rw [hget 16 (by decide), hget 17 (by decide), hget 18 (by decide), hget 19 (by decide)]; exact hu32 h.w4
  · rw [hget 20 (by decide), hget 21 (by decide), hget 22 (by decide), hget 23 (by decide)]; exact hu32 h.w5
  · rw [hget 24 (by decide), hget 25 (by decide), hget 26 (by decide), hget 27 (by decide)]; exact hu32 h.w6
  · rw [hget 28 (by decide), hget 29 (by decide), hget 30 (by decide), hget 31 (by decide)]; exact hu32 h.w7

/-! ### `takeU32Word` and `takeBlock64` Soundness -/

private theorem takeU32Word_sound (s : ByteList) (hv : ValidBytes s) :
    let t := takeU32Word s
    let bs := byteListToUInt8List s
    t.word = Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => bs.toArray[b.val]?.getD 0) ∧
    t.got = min 4 (byteListLen s) ∧
    byteListToUInt8List t.rest = bs.drop 4 ∧
    ValidBytes t.rest ∧
    byteListLen t.rest = byteListLen s - 4 := by
  have hword (b0 b1 b2 b3 : UInt8) :
      UInt32.ofNat (0 + b0.toNat * 1 + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216) =
        Blake3.Pure.bytesWord #v[b0, b1, b2, b3] := by
    rw [Aiur.Library.Blake3.bytesWord_eq_wordOfBytes]
    unfold Aiur.Library.Blake3.wordOfBytes Aiur.Library.U32.pack
    congr 1; omega
  have hmod256 {b : Nat} (hb : b < 256) : b % 256 = (UInt8.ofNat b).toNat := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb]
  cases s with
  | nil =>
    refine ⟨?_, rfl, rfl, trivial, rfl⟩
    dsimp only [byteListToUInt8List]
    have h0 : (Vector.ofFn fun b : Fin 4 => ([] : List UInt8).toArray[b.val]?.getD 0) =
        #v[0, 0, 0, 0] := rfl
    rw [h0]; exact hword 0 0 0 0
  | cons b0 r0 =>
    cases r0 with
    | nil =>
      refine ⟨?_, rfl, rfl, trivial, rfl⟩
      dsimp only [byteListToUInt8List]
      have h0 : (Vector.ofFn fun b : Fin 4 => ([UInt8.ofNat b0]).toArray[b.val]?.getD 0) =
          #v[UInt8.ofNat b0, 0, 0, 0] := rfl
      rw [h0]
      change UInt32.ofNat (0 + b0 % 256 * 1) = _
      rw [hmod256 hv.1]
      simpa using hword (UInt8.ofNat b0) 0 0 0
    | cons b1 r1 =>
      cases r1 with
      | nil =>
        refine ⟨?_, rfl, rfl, trivial, rfl⟩
        dsimp only [byteListToUInt8List]
        have h0 : (Vector.ofFn fun b : Fin 4 =>
            ([UInt8.ofNat b0, UInt8.ofNat b1]).toArray[b.val]?.getD 0) =
            #v[UInt8.ofNat b0, UInt8.ofNat b1, 0, 0] := rfl
        rw [h0]
        change UInt32.ofNat (0 + b0 % 256 * 1 + b1 % 256 * 256) = _
        rw [hmod256 hv.1, hmod256 hv.2.1]
        simpa using hword (UInt8.ofNat b0) (UInt8.ofNat b1) 0 0
      | cons b2 r2 =>
        cases r2 with
        | nil =>
          refine ⟨?_, rfl, rfl, trivial, rfl⟩
          dsimp only [byteListToUInt8List]
          have h0 : (Vector.ofFn fun b : Fin 4 =>
              ([UInt8.ofNat b0, UInt8.ofNat b1, UInt8.ofNat b2]).toArray[b.val]?.getD 0) =
              #v[UInt8.ofNat b0, UInt8.ofNat b1, UInt8.ofNat b2, 0] := rfl
          rw [h0]
          change UInt32.ofNat (0 + b0 % 256 * 1 + b1 % 256 * 256 + b2 % 256 * 65536) = _
          rw [hmod256 hv.1, hmod256 hv.2.1, hmod256 hv.2.2.1]
          simpa using hword (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) 0
        | cons b3 r3 =>
          refine ⟨?_, ?_, rfl, hv.2.2.2.2, ?_⟩
          · dsimp only [byteListToUInt8List]
            have h0 : (Vector.ofFn fun b : Fin 4 =>
                (UInt8.ofNat b0 :: UInt8.ofNat b1 :: UInt8.ofNat b2 :: UInt8.ofNat b3 ::
                  byteListToUInt8List r3).toArray[b.val]?.getD 0) =
                #v[UInt8.ofNat b0, UInt8.ofNat b1, UInt8.ofNat b2, UInt8.ofNat b3] := by
              apply Vector.ext; intro i hi
              interval_cases i <;> rfl
            rw [h0]
            change UInt32.ofNat (0 + b0 % 256 * 1 + b1 % 256 * 256 +
              b2 % 256 * 65536 + b3 % 256 * 16777216) = _
            rw [hmod256 hv.1, hmod256 hv.2.1, hmod256 hv.2.2.1, hmod256 hv.2.2.2.1]
            exact hword (UInt8.ofNat b0) (UInt8.ofNat b1) (UInt8.ofNat b2) (UInt8.ofNat b3)
          · change 4 = min 4 (1 + (1 + (1 + (1 + byteListLen r3)))); omega
          · change byteListLen r3 = 1 + (1 + (1 + (1 + byteListLen r3))) - 4; omega

theorem takeBlock64_sound (s : ByteList) (hv : ValidBytes s) :
    let t := takeBlock64 s
    let bs := byteListToUInt8List s
    block16ToPure t.block = Blake3.Pure.blockWords (bs.take 64) ∧
    t.len = min 64 (byteListLen s) ∧
    byteListToUInt8List t.rest = bs.drop 64 ∧
    ValidBytes t.rest ∧
    byteListLen t.rest = byteListLen s - 64 ∧
    (t.rest = .nil ↔ byteListLen s ≤ 64) := by
  dsimp only [takeBlock64]
  have h0 := takeU32Word_sound s hv; generalize ht0 : takeU32Word s = t0 at h0 ⊢
  have h1 := takeU32Word_sound t0.rest h0.2.2.2.1; generalize ht1 : takeU32Word t0.rest = t1 at h1 ⊢
  have h2 := takeU32Word_sound t1.rest h1.2.2.2.1; generalize ht2 : takeU32Word t1.rest = t2 at h2 ⊢
  have h3 := takeU32Word_sound t2.rest h2.2.2.2.1; generalize ht3 : takeU32Word t2.rest = t3 at h3 ⊢
  have h4 := takeU32Word_sound t3.rest h3.2.2.2.1; generalize ht4 : takeU32Word t3.rest = t4 at h4 ⊢
  have h5 := takeU32Word_sound t4.rest h4.2.2.2.1; generalize ht5 : takeU32Word t4.rest = t5 at h5 ⊢
  have h6 := takeU32Word_sound t5.rest h5.2.2.2.1; generalize ht6 : takeU32Word t5.rest = t6 at h6 ⊢
  have h7 := takeU32Word_sound t6.rest h6.2.2.2.1; generalize ht7 : takeU32Word t6.rest = t7 at h7 ⊢
  have h8 := takeU32Word_sound t7.rest h7.2.2.2.1; generalize ht8 : takeU32Word t7.rest = t8 at h8 ⊢
  have h9 := takeU32Word_sound t8.rest h8.2.2.2.1; generalize ht9 : takeU32Word t8.rest = t9 at h9 ⊢
  have h10 := takeU32Word_sound t9.rest h9.2.2.2.1; generalize ht10 : takeU32Word t9.rest = t10 at h10 ⊢
  have h11 := takeU32Word_sound t10.rest h10.2.2.2.1; generalize ht11 : takeU32Word t10.rest = t11 at h11 ⊢
  have h12 := takeU32Word_sound t11.rest h11.2.2.2.1; generalize ht12 : takeU32Word t11.rest = t12 at h12 ⊢
  have h13 := takeU32Word_sound t12.rest h12.2.2.2.1; generalize ht13 : takeU32Word t12.rest = t13 at h13 ⊢
  have h14 := takeU32Word_sound t13.rest h13.2.2.2.1; generalize ht14 : takeU32Word t13.rest = t14 at h14 ⊢
  have h15 := takeU32Word_sound t14.rest h14.2.2.2.1; generalize ht15 : takeU32Word t14.rest = t15 at h15 ⊢
  have hdrop (k : Nat) (bs : List UInt8) (b : Nat) (hb : b < 4) (hk : k < 16) :
      (bs.drop (k * 4)).toArray[b]?.getD 0 = (bs.take 64).toArray[k * 4 + b]?.getD 0 := by
    simp only [List.getElem?_toArray, List.getElem?_drop, List.getElem?_take]
    have hlt64 : k * 4 + b < 64 := by omega
    simp only [hlt64, ↓reduceIte]
  have hd0 : byteListToUInt8List t0.rest = (byteListToUInt8List s).drop 4 := h0.2.2.1
  have hd1 : byteListToUInt8List t1.rest = (byteListToUInt8List s).drop 8 := by rw [h1.2.2.1, hd0, List.drop_drop]
  have hd2 : byteListToUInt8List t2.rest = (byteListToUInt8List s).drop 12 := by rw [h2.2.2.1, hd1, List.drop_drop]
  have hd3 : byteListToUInt8List t3.rest = (byteListToUInt8List s).drop 16 := by rw [h3.2.2.1, hd2, List.drop_drop]
  have hd4 : byteListToUInt8List t4.rest = (byteListToUInt8List s).drop 20 := by rw [h4.2.2.1, hd3, List.drop_drop]
  have hd5 : byteListToUInt8List t5.rest = (byteListToUInt8List s).drop 24 := by rw [h5.2.2.1, hd4, List.drop_drop]
  have hd6 : byteListToUInt8List t6.rest = (byteListToUInt8List s).drop 28 := by rw [h6.2.2.1, hd5, List.drop_drop]
  have hd7 : byteListToUInt8List t7.rest = (byteListToUInt8List s).drop 32 := by rw [h7.2.2.1, hd6, List.drop_drop]
  have hd8 : byteListToUInt8List t8.rest = (byteListToUInt8List s).drop 36 := by rw [h8.2.2.1, hd7, List.drop_drop]
  have hd9 : byteListToUInt8List t9.rest = (byteListToUInt8List s).drop 40 := by rw [h9.2.2.1, hd8, List.drop_drop]
  have hd10 : byteListToUInt8List t10.rest = (byteListToUInt8List s).drop 44 := by rw [h10.2.2.1, hd9, List.drop_drop]
  have hd11 : byteListToUInt8List t11.rest = (byteListToUInt8List s).drop 48 := by rw [h11.2.2.1, hd10, List.drop_drop]
  have hd12 : byteListToUInt8List t12.rest = (byteListToUInt8List s).drop 52 := by rw [h12.2.2.1, hd11, List.drop_drop]
  have hd13 : byteListToUInt8List t13.rest = (byteListToUInt8List s).drop 56 := by rw [h13.2.2.1, hd12, List.drop_drop]
  have hd14 : byteListToUInt8List t14.rest = (byteListToUInt8List s).drop 60 := by rw [h14.2.2.1, hd13, List.drop_drop]
  have hd15 : byteListToUInt8List t15.rest = (byteListToUInt8List s).drop 64 := by rw [h15.2.2.1, hd14, List.drop_drop]
  have hlen15 : byteListLen t15.rest = byteListLen s - 64 := by
    have l0 := h0.2.2.2.2; have l1 := h1.2.2.2.2; have l2 := h2.2.2.2.2; have l3 := h3.2.2.2.2
    have l4 := h4.2.2.2.2; have l5 := h5.2.2.2.2; have l6 := h6.2.2.2.2; have l7 := h7.2.2.2.2
    have l8 := h8.2.2.2.2; have l9 := h9.2.2.2.2; have l10 := h10.2.2.2.2; have l11 := h11.2.2.2.2
    have l12 := h12.2.2.2.2; have l13 := h13.2.2.2.2; have l14 := h14.2.2.2.2; have l15 := h15.2.2.2.2
    omega
  refine ⟨?_, ?_, hd15, h15.2.2.2.1, hlen15, ?_⟩
  · apply Vector.ext
    intro w hw
    unfold Blake3.Pure.blockWords
    simp only [Vector.getElem_ofFn]
    have hmatch (k : Nat) (hk : k < 16) (ti : TakeWordOut) (bs_i : List UInt8)
        (hw_eq : ti.word = Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => bs_i.toArray[b.val]?.getD 0))
        (hbs : bs_i = (byteListToUInt8List s).drop (k * 4)) :
        ti.word = Blake3.Pure.bytesWord
          (Vector.ofFn fun b : Fin 4 => ((byteListToUInt8List s).take 64).toArray[k * 4 + b.val]?.getD 0) := by
      rw [hw_eq, hbs]
      congr 1; apply Vector.ext; intro b hb
      simp only [Vector.getElem_ofFn]
      exact hdrop k (byteListToUInt8List s) b hb hk
    interval_cases w
    · exact hmatch 0 (by decide) t0 _ h0.1 (by simp)
    · exact hmatch 1 (by decide) t1 _ h1.1 hd0
    · exact hmatch 2 (by decide) t2 _ h2.1 hd1
    · exact hmatch 3 (by decide) t3 _ h3.1 hd2
    · exact hmatch 4 (by decide) t4 _ h4.1 hd3
    · exact hmatch 5 (by decide) t5 _ h5.1 hd4
    · exact hmatch 6 (by decide) t6 _ h6.1 hd5
    · exact hmatch 7 (by decide) t7 _ h7.1 hd6
    · exact hmatch 8 (by decide) t8 _ h8.1 hd7
    · exact hmatch 9 (by decide) t9 _ h9.1 hd8
    · exact hmatch 10 (by decide) t10 _ h10.1 hd9
    · exact hmatch 11 (by decide) t11 _ h11.1 hd10
    · exact hmatch 12 (by decide) t12 _ h12.1 hd11
    · exact hmatch 13 (by decide) t13 _ h13.1 hd12
    · exact hmatch 14 (by decide) t14 _ h14.1 hd13
    · exact hmatch 15 (by decide) t15 _ h15.1 hd14
  · have hmin (a b n : Nat) : min a n + min b (n - a) = min (a + b) n := by omega
    rw [h0.2.1, h1.2.1, h2.2.1, h3.2.1, h4.2.1, h5.2.1, h6.2.1, h7.2.1,
        h8.2.1, h9.2.1, h10.2.1, h11.2.1, h12.2.1, h13.2.1, h14.2.1, h15.2.1,
        h14.2.2.2.2, h13.2.2.2.2, h12.2.2.2.2, h11.2.2.2.2, h10.2.2.2.2,
        h9.2.2.2.2, h8.2.2.2.2, h7.2.2.2.2, h6.2.2.2.2, h5.2.2.2.2,
        h4.2.2.2.2, h3.2.2.2.2, h2.2.2.2.2, h1.2.2.2.2, h0.2.2.2.2]
    simp only [Nat.sub_sub, Nat.reduceAdd, hmin]
  · constructor
    · intro hnil
      have : byteListLen t15.rest = 0 := by rw [hnil]; rfl
      omega
    · intro hle
      have h0len : byteListLen t15.rest = 0 := by omega
      cases htr : t15.rest with
      | nil => rfl
      | cons _ _ => rw [htr] at h0len; simp [byteListLen] at h0len

/-! ### Merkle Tree Layer-Folding Equivalence (`blake3NextLayer` / `blake3CompressLayerFuel`) -/

private theorem pairChainingValuesWith_append_even (key : Blake3.Pure.CV) (flags : UInt32) :
    ∀ (left right : List Blake3.Pure.CV), left.length % 2 = 0 →
      IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith key flags (left ++ right) =
        IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith key flags left ++
        IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith key flags right
  | [], _, _ => rfl
  | [_], _, hev => by simp at hev
  | a :: b :: rest, right, hev => by
    have hrest : rest.length % 2 = 0 := by simp at hev; omega
    simp only [List.cons_append, IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith,
      pairChainingValuesWith_append_even key flags rest right hrest]

private theorem blake3NextLayer_isRoot0 (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) :
    ∀ (layer : LayerStack) (digest : Digest32),
      let out := blake3NextLayer keyCv baseFlag layer digest 0
      let cvs := layerStackToList layer ++ [digest32ToCV digest]
      (cvs.length % 2 = 1 →
        out.last = .some digest ∧
        layerStackToList out.layer ++ [digest32ToCV digest] =
          IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag cvs) ∧
      (cvs.length % 2 = 0 →
        out.last = .none ∧
        layerStackToList out.layer =
          IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag cvs)
  | .nil, digest => by
    constructor
    · intro _; exact ⟨rfl, rfl⟩
    · intro hev; simp [layerStackToList] at hev
  | .push rest other, digest => by
    have ih := blake3NextLayer_isRoot0 keyCv baseFlag hd rest other
    generalize hrecEq : blake3NextLayer keyCv baseFlag rest other 0 = recOut at ih
    set prevCvs := layerStackToList rest ++ [digest32ToCV other]
    have hcvs : layerStackToList (.push rest other) ++ [digest32ToCV digest] =
        prevCvs ++ [digest32ToCV digest] := rfl
    have hlen : (prevCvs ++ [digest32ToCV digest]).length = prevCvs.length + 1 := by simp
    constructor
    · intro hodd
      have hpev : prevCvs.length % 2 = 0 := by rw [hcvs, hlen] at hodd; omega
      obtain ⟨hlast, hlay⟩ := ih.2 hpev
      unfold blake3NextLayer
      dsimp only
      rw [hrecEq, hlast]
      refine ⟨rfl, ?_⟩
      rw [hcvs, hlay, pairChainingValuesWith_append_even _ _ prevCvs [digest32ToCV digest] hpev]
      rfl
    · intro hev
      have hpodd : prevCvs.length % 2 = 1 := by rw [hcvs, hlen] at hev; omega
      obtain ⟨hlast, hlay⟩ := ih.1 hpodd
      have hrev_len : (layerStackToList rest).length % 2 = 0 := by
        have : prevCvs.length = (layerStackToList rest).length + 1 := by simp [prevCvs]
        omega
      have hpcv : IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag prevCvs =
          IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag (layerStackToList rest) ++
            [digest32ToCV other] := by
        rw [pairChainingValuesWith_append_even _ _ (layerStackToList rest) [digest32ToCV other] hrev_len]
        rfl
      rw [hpcv] at hlay
      have hlayEq : layerStackToList recOut.layer =
          IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag (layerStackToList rest) := by
        exact (List.append_inj_left' hlay rfl)
      unfold blake3NextLayer
      dsimp only
      rw [hrecEq, hlast]
      refine ⟨rfl, ?_⟩
      dsimp only
      have hfl4 : UInt32.add baseFlag 4 = baseFlag ||| 4 :=
        uint32_add_eq_or_of_validDomainFlags hd (by decide)
      have hbody :
          layerStackToList (.push recOut.layer
            (blake3Compress keyCv
              { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
                m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
                m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
                m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 }
              0 0 64 (baseFlag ||| 4))) =
          IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag
            (layerStackToList (.push rest other) ++ [digest32ToCV digest]) := by
        rw [layerStackToList, hlayEq, hcvs]
        have hpair : prevCvs ++ [digest32ToCV digest] =
            layerStackToList rest ++ [digest32ToCV other, digest32ToCV digest] := by
          simp [prevCvs, List.append_assoc]
        rw [hpair, pairChainingValuesWith_append_even _ _ (layerStackToList rest) _ hrev_len]
        apply congrArg
          (IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag
            (layerStackToList rest) ++ ·)
        have hcomp := blake3Compress_eq_pure keyCv
          { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
            m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
            m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
            m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 }
          0 64 (baseFlag ||| 4)
        have hblk : block16ToPure
          { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
            m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
            m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
            m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 } =
            digest32ToCV other ++ digest32ToCV digest := rfl
        rw [hblk] at hcomp
        change [digest32ToCV (blake3Compress keyCv _ (0 : UInt64).toUInt32 ((0 : UInt64) >>> 32).toUInt32 64 (baseFlag ||| 4))] = _
        rw [hcomp]
        rfl
      cases hrlay : recOut.layer with
      | nil =>
        simp only [show ((0 : Nat) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte, hfl4]
        rw [← hrlay]; exact hbody
      | push _ _ =>
        simp only [hfl4]
        rw [← hrlay]; exact hbody

private theorem blake3CompressLayerFuel_eq_compressLayerWith (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) :
    ∀ (fuel : Nat) (layer : LayerStack),
      2 ≤ layerStackDepth layer →
      layerStackDepth layer ≤ fuel →
      digest32ToCV (blake3CompressLayerFuel keyCv baseFlag fuel layer) =
        IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith (digest32ToCV keyCv) baseFlag
          (layerStackToList layer)
  | 0, layer, h2, hle => by omega
  | fuel + 1, layer, h2, hle => by
    cases layer with
    | nil => simp [layerStackDepth] at h2
    | push rest digest =>
      cases rest with
      | nil => simp [layerStackDepth] at h2
      | push rest2 other =>
        cases rest2 with
        | nil =>
          have hfl12 : UInt32.add baseFlag 12 = baseFlag ||| 12 :=
            uint32_add_eq_or_of_validDomainFlags hd (by decide)
          unfold blake3CompressLayerFuel
          dsimp only
          have hstep : blake3NextLayer keyCv baseFlag (.push .nil other) digest 1 =
              { last := .none
                layer := .push .nil
                  (blake3Compress keyCv
                    { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
                      m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
                      m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
                      m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 }
                    0 0 64 (baseFlag ||| 12)) } := by
            unfold blake3NextLayer; dsimp only
            unfold blake3NextLayer; dsimp only
            simp only [beq_self_eq_true, ↓reduceIte, hfl12]
          rw [hstep]
          dsimp only
          have hret : ∀ d, blake3CompressLayerFuel keyCv baseFlag fuel (.push .nil d) = d := by
            intro d; cases fuel <;> rfl
          rw [hret]
          have hcomp := blake3Compress_eq_pure keyCv
            { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
              m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
              m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
              m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 }
            0 64 (baseFlag ||| 12)
          have hblk : block16ToPure
            { m0 := other.w0, m1 := other.w1, m2 := other.w2, m3 := other.w3
              m4 := other.w4, m5 := other.w5, m6 := other.w6, m7 := other.w7
              m8 := digest.w0, m9 := digest.w1, m10 := digest.w2, m11 := digest.w3
              m12 := digest.w4, m13 := digest.w5, m14 := digest.w6, m15 := digest.w7 } =
              digest32ToCV other ++ digest32ToCV digest := rfl
          rw [hblk] at hcomp
          change digest32ToCV (blake3Compress keyCv _ (0 : UInt64).toUInt32 ((0 : UInt64) >>> 32).toUInt32 64 (baseFlag ||| 12)) = _
          rw [hcomp]
          simp only [layerStackToList, List.nil_append, List.cons_append]
          unfold IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith
          rfl
        | push rest3 third =>
          set inner := LayerStack.push rest3 third
          have hinner_pos : 1 ≤ layerStackDepth inner := by simp [inner, layerStackDepth]
          have hrec := blake3NextLayer_isRoot0 keyCv baseFlag hd inner other
          generalize hrecEq : blake3NextLayer keyCv baseFlag inner other 0 = recOut at hrec
          set prevCvs := layerStackToList inner ++ [digest32ToCV other]
          have hprev_ge2 : 2 ≤ prevCvs.length := by
            simp only [prevCvs, List.length_append, List.length_singleton, layerStackToList_length]
            omega
          have hstep_eq :
              blake3NextLayer keyCv baseFlag (.push inner other) digest 1 =
              blake3NextLayer keyCv baseFlag (.push inner other) digest 0 := by
            unfold blake3NextLayer; dsimp only
            rw [hrecEq]
            cases hrl : recOut.last with
            | none => rfl
            | some prev =>
              dsimp only
              have hlay_ne : recOut.layer ≠ .nil := by
                intro hnil
                by_cases hodd : prevCvs.length % 2 = 1
                · have hlay := (hrec.1 hodd).2
                  rw [hnil, layerStackToList, List.nil_append] at hlay
                  have hplen := congrArg List.length hlay
                  rw [List.length_singleton,
                      IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith_length] at hplen
                  omega
                · have hnone := (hrec.2 (by omega)).1
                  rw [hnone] at hrl; cases hrl
              cases hrlay : recOut.layer with
              | nil => exact absurd hrlay hlay_ne
              | push _ _ => rfl
          have hfull := blake3NextLayer_isRoot0 keyCv baseFlag hd (.push inner other) digest
          have hfull_len : (layerStackToList (.push (.push inner other) digest)).length =
              layerStackDepth (.push (.push inner other) digest) :=
            layerStackToList_length _
          have hfull_ge3 : 3 ≤ (layerStackToList (.push (.push inner other) digest)).length := by
            rw [hfull_len]; simp [layerStackDepth, inner]; omega
          have hcl_step : ∀ (xs : List Blake3.Pure.CV), 3 ≤ xs.length →
              IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith (digest32ToCV keyCv) baseFlag xs =
              IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith (digest32ToCV keyCv) baseFlag
                (IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag xs) := by
            intro xs h3
            rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rs⟩⟩⟩ <;> try (simp at h3)
            conv_lhs => rw [IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith]
          rw [hcl_step _ hfull_ge3]
          unfold blake3CompressLayerFuel; dsimp only
          rw [hstep_eq]
          generalize hstep0 : blake3NextLayer keyCv baseFlag (.push inner other) digest 0 = step0 at hfull ⊢
          have hfull_eq_len :
              (layerStackToList (.push inner other) ++ [digest32ToCV digest]).length =
              (layerStackToList (.push (.push inner other) digest)).length := rfl
          by_cases hodd : (layerStackToList (.push (.push inner other) digest)).length % 2 = 1
          · obtain ⟨hl, hlay⟩ := hfull.1 (by rw [hfull_eq_len]; exact hodd)
            rw [hl]; dsimp only
            have hnext_list :
                layerStackToList (.push step0.layer digest) =
                IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag
                  (layerStackToList (.push (.push inner other) digest)) := hlay
            have hnext_len :
                layerStackDepth (.push step0.layer digest) =
                ((layerStackToList (.push (.push inner other) digest)).length + 1) / 2 := by
              rw [← layerStackToList_length, hnext_list,
                  IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith_length]
            rw [← hnext_list]
            exact blake3CompressLayerFuel_eq_compressLayerWith keyCv baseFlag hd fuel _
              (by rw [hnext_len]; omega) (by rw [hnext_len, hfull_len]; omega)
          · obtain ⟨hl, hlay⟩ := hfull.2 (by rw [hfull_eq_len]; omega)
            rw [hl]; dsimp only
            have hnext_list :
                layerStackToList step0.layer =
                IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith (digest32ToCV keyCv) baseFlag
                  (layerStackToList (.push (.push inner other) digest)) := hlay
            have hnext_len :
                layerStackDepth step0.layer =
                ((layerStackToList (.push (.push inner other) digest)).length + 1) / 2 := by
              rw [← layerStackToList_length, hnext_list,
                  IxCC.AiurBackend.Blake3KeyedSpec.pairChainingValuesWith_length]
            rw [← hnext_list]
            exact blake3CompressLayerFuel_eq_compressLayerWith keyCv baseFlag hd fuel _
              (by rw [hnext_len]; omega) (by rw [hnext_len, hfull_len]; omega)

/-! ### Multi-Block / Multi-Chunk Block Loop Equivalence (`blake3HashBlocksFuel`) -/

private theorem ctr_u64_decomp {c : Nat} (hc : c < 2 ^ 64) :
    c.toUInt64.toUInt32 = UInt32.ofNat (c % 2 ^ 32) ∧
    (c.toUInt64 >>> 32).toUInt32 = UInt32.ofNat (c / 2 ^ 32) := by
  constructor
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (Nat.mod_lt c (by decide))]
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc]
    have hs : (32 : UInt64).toNat % 64 = 32 := rfl
    rw [hs, Nat.shiftRight_eq_div_pow, UInt32.toNat_ofNat']

private theorem ctr_isZero_iff {c : Nat} (hc : c < 2 ^ 64) :
    (c.toUInt64.toUInt32 == 0 && (c.toUInt64 >>> 32).toUInt32 == 0) = true ↔ c = 0 := by
  obtain ⟨hlo, hhi⟩ := ctr_u64_decomp hc
  rw [hlo, hhi, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := congrArg UInt32.toNat h1
    have e2 := congrArg UInt32.toNat h2
    simp only [UInt32.toNat_ofNat', UInt32.toNat_zero,
      Nat.mod_eq_of_lt (Nat.mod_lt c (show 0 < 2 ^ 32 by decide)),
      Nat.mod_eq_of_lt (show c / 2 ^ 32 < 2 ^ 32 by omega)] at e1 e2
    omega
  · rintro rfl; decide

private theorem ctr_succ_pair {c : Nat} (hc : c + 1 < 2 ^ 64) :
    let lo := c.toUInt64.toUInt32
    let hi := (c.toUInt64 >>> 32).toUInt32
    let nextLo := UInt32.add lo 1
    let nextHi := if nextLo == 0 then UInt32.add hi 1 else hi
    nextLo = (c + 1).toUInt64.toUInt32 ∧
    nextHi = ((c + 1).toUInt64 >>> 32).toUInt32 := by
  obtain ⟨hlo, hhi⟩ := ctr_u64_decomp (by omega : c < 2 ^ 64)
  obtain ⟨hlo', hhi'⟩ := ctr_u64_decomp hc
  dsimp only
  rw [hlo, hhi, hlo', hhi']
  have hnl : UInt32.add (UInt32.ofNat (c % 2 ^ 32)) 1 = UInt32.ofNat ((c + 1) % 2 ^ 32) := by
    apply UInt32.toNat_inj.mp
    change (UInt32.ofNat (c % 2 ^ 32) + 1).toNat = _
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (Nat.mod_lt c (by decide)),
        Nat.mod_eq_of_lt (Nat.mod_lt (c + 1) (by decide))]
    omega
  refine ⟨hnl, ?_⟩
  rw [hnl]
  by_cases hwrap : (c + 1) % 2 ^ 32 = 0
  · have hbeq : (UInt32.ofNat ((c + 1) % 2 ^ 32) == 0) = true := by rw [hwrap]; rfl
    rw [ite_eq_left hbeq]
    apply UInt32.toNat_inj.mp
    change (UInt32.ofNat (c / 2 ^ 32) + 1).toNat = _
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_one,
        Nat.mod_eq_of_lt (show c / 2 ^ 32 < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show (c + 1) / 2 ^ 32 < 2 ^ 32 by omega)]
    have hq : (c + 1) / 2 ^ 32 = c / 2 ^ 32 + 1 := by omega
    rw [hq, Nat.mod_eq_of_lt (by omega)]
  · have hne : UInt32.ofNat ((c + 1) % 2 ^ 32) ≠ 0 := by
      intro heq
      have h := congrArg UInt32.toNat heq
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.mod_lt (c + 1) (by decide))] at h
      exact hwrap h
    rw [ite_eq_right (by rw [beq_iff_eq]; exact hne)]
    congr 1; omega

private theorem blake3HashBlocksFuel_singleChunk (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) :
    ∀ (fuel : Nat) (input : ByteList) (blockNo : Nat) (cv : Digest32),
      ValidBytes input →
      blockNo < 16 →
      byteListLen input ≤ 64 * (16 - blockNo) →
      byteListLen input + 1 ≤ fuel →
      ∃ root : Digest32,
        blake3HashBlocksFuel keyCv baseFlag fuel input blockNo 0 0 cv .nil = .push .nil root ∧
        digest32ToCV root =
          let out := IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith baseFlag 0 (digest32ToCV cv)
            (decide (blockNo = 0)) (byteListToUInt8List input)
          Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8)
  | 0, _, _, _, _, _, _, hfuel => by omega
  | fuel + 1, input, blockNo, cv, hv, hbno, hlen, hfuel => by
    have htb := takeBlock64_sound input hv
    set t := takeBlock64 input
    have hlen_bs : (byteListToUInt8List input).length = byteListLen input :=
      byteListToUInt8List_length input
    by_cases hsmall : byteListLen input ≤ 64
    · have hrest : t.rest = .nil := htb.2.2.2.2.2.mpr hsmall
      have htake_eq : (byteListToUInt8List input).take 64 = byteListToUInt8List input :=
        List.take_of_length_le (by omega)
      have htlen : t.len = byteListLen input := by rw [htb.2.1]; omega
      have hbf_lt : ((if blockNo == 0 then 1 else 0) + 2 + 8) < 16 := by split <;> omega
      have hfl_eq :
          UInt32.add baseFlag (UInt32.ofNat ((if blockNo == 0 then 1 else 0) + 2 + 8)) =
          (baseFlag ||| ((if decide (blockNo = 0) then 1 else 0) ||| 2)) ||| 8 := by
        rw [uint32_add_eq_or_of_validDomainFlags hd (by rw [UInt32.toNat_ofNat']; omega)]
        by_cases hb0 : blockNo = 0
        · subst hb0
          apply UInt32.toNat_inj.mp
          simp only [beq_self_eq_true, ↓reduceIte, decide_true, UInt32.toNat_or, Nat.or_assoc]
          rfl
        · have hb0f : (blockNo == 0) = false := beq_false_of_ne hb0
          have hd0f : decide (blockNo = 0) = false := decide_eq_false hb0
          apply UInt32.toNat_inj.mp
          simp only [hb0f, hd0f, Bool.false_eq_true, ↓reduceIte, UInt32.toNat_or, Nat.or_assoc]
          rfl
      unfold blake3HashBlocksFuel
      change let taken := t; _
      dsimp only
      rw [hrest]
      simp only [Bool.true_or, Bool.and_self, ↓reduceIte, beq_self_eq_true]
      refine ⟨_, rfl, ?_⟩
      rw [hfl_eq, htlen, ← hlen_bs]
      rw [IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_le baseFlag 0 (digest32ToCV cv)
            (decide (blockNo = 0)) (byteListToUInt8List input) (by omega)]
      dsimp only
      have hcomp := blake3Compress_eq_pure cv t.block 0 (byteListToUInt8List input).length.toUInt32
        ((baseFlag ||| ((if decide (blockNo = 0) then 1 else 0) ||| 2)) ||| 8)
      rw [htb.1, htake_eq] at hcomp
      exact hcomp
    · have hlarge : 64 < byteListLen input := by omega
      have hne : t.rest ≠ .nil := fun h => hsmall (htb.2.2.2.2.2.mp h)
      have hbno15 : blockNo < 15 := by omega
      have hat15 : (blockNo == 15) = false := beq_false_of_ne (by omega)
      have htlen : t.len = 64 := by rw [htb.2.1]; omega
      have hfl_eq :
          UInt32.add baseFlag (UInt32.ofNat ((if blockNo == 0 then 1 else 0) + 0 + 0)) =
          baseFlag ||| (if decide (blockNo = 0) then 1 else 0) := by
        rw [uint32_add_eq_or_of_validDomainFlags hd (by rw [UInt32.toNat_ofNat']; split <;> omega)]
        by_cases hb0 : blockNo = 0
        · subst hb0; rfl
        · have hb0f : (blockNo == 0) = false := beq_false_of_ne hb0
          have hd0f : decide (blockNo = 0) = false := decide_eq_false hb0
          simp only [hb0f, hd0f, Bool.false_eq_true, ↓reduceIte]; rfl
      have hcomp := blake3Compress_eq_pure cv t.block 0 64
        (baseFlag ||| (if decide (blockNo = 0) then 1 else 0))
      rw [htb.1] at hcomp
      change digest32ToCV (blake3Compress cv t.block 0 0 64 _) = _ at hcomp
      have hnext := blake3HashBlocksFuel_singleChunk keyCv baseFlag hd fuel t.rest (blockNo + 1)
        (blake3Compress cv t.block 0 0 64 (baseFlag ||| (if decide (blockNo = 0) then 1 else 0)))
        htb.2.2.2.1 (by omega) (by rw [htb.2.2.2.2.1]; omega) (by rw [htb.2.2.2.2.1]; omega)
      obtain ⟨root, hrec, hroot⟩ := hnext
      refine ⟨root, ?_, ?_⟩
      · unfold blake3HashBlocksFuel
        dsimp only
        cases htr : t.rest with
        | nil => exact absurd htr hne
        | cons b br =>
          change (if (0 == 1) = true then _ else if (if (blockNo == 15) = true then 1 else 0) == 1 then _ else _) = _
          simp only [hat15, show ((0 : Nat) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte,
            Bool.or_false, Bool.false_and]
          rw [hfl_eq, htlen, ← htr]
          exact hrec
      · rw [hroot,
            IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_gt baseFlag 0 (digest32ToCV cv)
              (decide (blockNo = 0)) (byteListToUInt8List input) (by omega),
            show decide (blockNo + 1 = 0) = false from decide_eq_false (by omega),
            htb.2.2.1, hcomp]

private theorem blake3HashBlocksFuel_chunkStep (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) :
    ∀ (fuel : Nat) (input : ByteList) (blockNo c : Nat) (cv : Digest32) (layer : LayerStack),
      ValidBytes input →
      blockNo < 16 →
      c < 2 ^ 64 →
      (c = 0 → 64 * (16 - blockNo) < byteListLen input) →
      byteListLen input + 1 ≤ fuel →
      (byteListLen input ≤ 64 * (16 - blockNo) →
        ∃ d : Digest32,
          blake3HashBlocksFuel keyCv baseFlag fuel input blockNo
            c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 cv layer = .push layer d ∧
          digest32ToCV d =
            (IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith baseFlag c.toUInt64 (digest32ToCV cv)
              (decide (blockNo = 0)) (byteListToUInt8List input)).chainingValue) ∧
      (64 * (16 - blockNo) < byteListLen input →
        c + 1 < 2 ^ 64 →
        ∃ (d : Digest32) (rest : ByteList) (fuel' : Nat),
          ValidBytes rest ∧
          byteListToUInt8List rest = (byteListToUInt8List input).drop (64 * (16 - blockNo)) ∧
          byteListLen rest = byteListLen input - 64 * (16 - blockNo) ∧
          byteListLen rest + 1 ≤ fuel' ∧
          digest32ToCV d =
            (IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith baseFlag c.toUInt64 (digest32ToCV cv)
              (decide (blockNo = 0)) ((byteListToUInt8List input).take (64 * (16 - blockNo)))).chainingValue ∧
          blake3HashBlocksFuel keyCv baseFlag fuel input blockNo
            c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 cv layer =
          blake3HashBlocksFuel keyCv baseFlag fuel' rest 0
            (c + 1).toUInt64.toUInt32 ((c + 1).toUInt64 >>> 32).toUInt32 keyCv (.push layer d))
  | 0, _, _, _, _, _, _, _, _, _, hfuel => by omega
  | fuel + 1, input, blockNo, c, cv, layer, hv, hbno, hc, hc0, hfuel => by
    have htb := takeBlock64_sound input hv
    set t := takeBlock64 input
    have hlen_bs : (byteListToUInt8List input).length = byteListLen input :=
      byteListToUInt8List_length input
    constructor
    · intro hsmallChunk
      have hcne : c ≠ 0 := fun h => by have := hc0 h; omega
      have hchk0 : (c.toUInt64.toUInt32 == 0 && (c.toUInt64 >>> 32).toUInt32 == 0) = false := by
        cases h : (c.toUInt64.toUInt32 == 0 && (c.toUInt64 >>> 32).toUInt32 == 0)
        · rfl
        · exact absurd ((ctr_isZero_iff hc).mp h) hcne
      by_cases hsmall : byteListLen input ≤ 64
      · have hrest : t.rest = .nil := htb.2.2.2.2.2.mpr hsmall
        have htake_eq : (byteListToUInt8List input).take 64 = byteListToUInt8List input :=
          List.take_of_length_le (by omega)
        have htlen : t.len = byteListLen input := by rw [htb.2.1]; omega
        have hfl_eq :
            UInt32.add baseFlag (UInt32.ofNat ((if blockNo == 0 then 1 else 0) + 2 + 0)) =
            baseFlag ||| ((if decide (blockNo = 0) then 1 else 0) ||| 2) := by
          rw [uint32_add_eq_or_of_validDomainFlags hd (by rw [UInt32.toNat_ofNat']; split <;> omega)]
          by_cases hb0 : blockNo = 0
          · subst hb0; rfl
          · have hb0f : (blockNo == 0) = false := beq_false_of_ne hb0
            have hd0f : decide (blockNo = 0) = false := decide_eq_false hb0
            simp only [hb0f, hd0f, Bool.false_eq_true, ↓reduceIte]; rfl
        unfold blake3HashBlocksFuel
        dsimp only
        rw [hrest, hchk0]
        simp only [Bool.true_or, show ((0 : Nat) == 1) = false from rfl,
          Bool.false_eq_true, Bool.and_false, ↓reduceIte, beq_self_eq_true]
        refine ⟨_, rfl, ?_⟩
        rw [hfl_eq, htlen, ← hlen_bs,
            IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_le baseFlag c.toUInt64 (digest32ToCV cv)
              (decide (blockNo = 0)) (byteListToUInt8List input) (by omega)]
        unfold Blake3.Pure.Output.chainingValue
        have hcomp := blake3Compress_eq_pure cv t.block c.toUInt64
          (byteListToUInt8List input).length.toUInt32
          (baseFlag ||| ((if decide (blockNo = 0) then 1 else 0) ||| 2))
        rw [htb.1, htake_eq] at hcomp
        exact hcomp
      · have hne : t.rest ≠ .nil := fun h => hsmall (htb.2.2.2.2.2.mp h)
        have hbno15 : blockNo < 15 := by omega
        have hat15 : (blockNo == 15) = false := beq_false_of_ne (by omega)
        have htlen : t.len = 64 := by rw [htb.2.1]; omega
        have hfl_eq :
            UInt32.add baseFlag (UInt32.ofNat ((if blockNo == 0 then 1 else 0) + 0 + 0)) =
            baseFlag ||| (if decide (blockNo = 0) then 1 else 0) := by
          rw [uint32_add_eq_or_of_validDomainFlags hd (by rw [UInt32.toNat_ofNat']; split <;> omega)]
          by_cases hb0 : blockNo = 0
          · subst hb0; rfl
          · have hb0f : (blockNo == 0) = false := beq_false_of_ne hb0
            have hd0f : decide (blockNo = 0) = false := decide_eq_false hb0
            simp only [hb0f, hd0f, Bool.false_eq_true, ↓reduceIte]; rfl
        have hcomp := blake3Compress_eq_pure cv t.block c.toUInt64 64
          (baseFlag ||| (if decide (blockNo = 0) then 1 else 0))
        rw [htb.1] at hcomp
        have hnext := (blake3HashBlocksFuel_chunkStep keyCv baseFlag hd fuel t.rest (blockNo + 1) c
          (blake3Compress cv t.block c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 64
            (baseFlag ||| (if decide (blockNo = 0) then 1 else 0))) layer
          htb.2.2.2.1 (by omega) hc (fun h => absurd h hcne)
          (by rw [htb.2.2.2.2.1]; omega)).1 (by rw [htb.2.2.2.2.1]; omega)
        obtain ⟨d, hrec, hd_eq⟩ := hnext
        refine ⟨d, ?_, ?_⟩
        · conv_lhs => unfold blake3HashBlocksFuel
          dsimp only
          cases htr : t.rest with
          | nil => exact absurd htr hne
          | cons b br =>
            simp only [hat15, show ((0 : Nat) == 1) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.false_and]
            rw [hfl_eq, htlen, ← htr]
            exact hrec
        · rw [hd_eq,
              IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_gt baseFlag c.toUInt64 (digest32ToCV cv)
                (decide (blockNo = 0)) (byteListToUInt8List input) (by omega),
              show decide (blockNo + 1 = 0) = false from decide_eq_false (by omega),
              htb.2.2.1, hcomp]
    · intro hbigChunk hc1
      have hne : t.rest ≠ .nil := fun h => by
        have := htb.2.2.2.2.2.mp h; omega
      have htlen : t.len = 64 := by rw [htb.2.1]; omega
      by_cases h15 : blockNo = 15
      · subst h15
        have hfl_eq :
            UInt32.add baseFlag (UInt32.ofNat (0 + 2 + 0)) =
            baseFlag ||| (0 ||| 2) := by
          rw [uint32_add_eq_or_of_validDomainFlags hd (by decide)]; rfl
        have hcomp := blake3Compress_eq_pure cv t.block c.toUInt64 64 (baseFlag ||| (0 ||| 2))
        rw [htb.1] at hcomp
        obtain ⟨hnl, hnh⟩ := ctr_succ_pair hc1
        refine ⟨blake3Compress cv t.block c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 64
          (baseFlag ||| (0 ||| 2)), t.rest, fuel, htb.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using htb.2.2.1
        · simpa using htb.2.2.2.2.1
        · rw [htb.2.2.2.2.1]; omega
        · have htake_len : ((byteListToUInt8List input).take 64).length = 64 := by
            rw [List.length_take, hlen_bs]; omega
          rw [show 64 * (16 - 15) = 64 by rfl,
              show decide (15 = 0) = false from rfl,
              IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_le baseFlag c.toUInt64 (digest32ToCV cv)
                false ((byteListToUInt8List input).take 64) (by omega)]
          unfold Blake3.Pure.Output.chainingValue
          rw [htake_len]
          exact hcomp
        · conv_lhs => unfold blake3HashBlocksFuel
          dsimp only
          cases htr : t.rest with
          | nil => exact absurd htr hne
          | cons b br =>
            simp only [beq_self_eq_true, show ((0 : Nat) == 1) = false from rfl,
              show ((15 : Nat) == 0) = false from rfl, Bool.false_or, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte]
            rw [hfl_eq, htlen, ← htr, hnh, hnl]
            rfl
      · have hbno15 : blockNo < 15 := by omega
        have hat15 : (blockNo == 15) = false := beq_false_of_ne (by omega)
        have hfl_eq :
            UInt32.add baseFlag (UInt32.ofNat ((if blockNo == 0 then 1 else 0) + 0 + 0)) =
            baseFlag ||| (if decide (blockNo = 0) then 1 else 0) := by
          rw [uint32_add_eq_or_of_validDomainFlags hd (by rw [UInt32.toNat_ofNat']; split <;> omega)]
          by_cases hb0 : blockNo = 0
          · subst hb0; rfl
          · have hb0f : (blockNo == 0) = false := beq_false_of_ne hb0
            have hd0f : decide (blockNo = 0) = false := decide_eq_false hb0
            simp only [hb0f, hd0f, Bool.false_eq_true, ↓reduceIte]; rfl
        have hcomp := blake3Compress_eq_pure cv t.block c.toUInt64 64
          (baseFlag ||| (if decide (blockNo = 0) then 1 else 0))
        rw [htb.1] at hcomp
        have hnext := (blake3HashBlocksFuel_chunkStep keyCv baseFlag hd fuel t.rest (blockNo + 1) c
          (blake3Compress cv t.block c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 64
            (baseFlag ||| (if decide (blockNo = 0) then 1 else 0))) layer
          htb.2.2.2.1 (by omega) hc
          (fun _ => by rw [htb.2.2.2.2.1]; omega)
          (by rw [htb.2.2.2.2.1]; omega)).2 (by rw [htb.2.2.2.2.1]; omega) hc1
        obtain ⟨d, rest, fuel', hvR, hdropR, hlenR, hfuelR, hd_eq, hrec⟩ := hnext
        refine ⟨d, rest, fuel', hvR, ?_, ?_, hfuelR, ?_, ?_⟩
        · rw [hdropR, htb.2.2.1, List.drop_drop,
              show 64 + 64 * (16 - (blockNo + 1)) = 64 * (16 - blockNo) by omega]
        · rw [hlenR, htb.2.2.2.2.1]; omega
        · have htake_gt : 64 < ((byteListToUInt8List input).take (64 * (16 - blockNo))).length := by
            rw [List.length_take, hlen_bs]; omega
          rw [IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_gt baseFlag c.toUInt64 (digest32ToCV cv)
                (decide (blockNo = 0)) _ htake_gt]
          have htk64 : ((byteListToUInt8List input).take (64 * (16 - blockNo))).take 64 =
              (byteListToUInt8List input).take 64 := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          have hdp64 : ((byteListToUInt8List input).take (64 * (16 - blockNo))).drop 64 =
              ((byteListToUInt8List input).drop 64).take (64 * (16 - (blockNo + 1))) := by
            rw [List.drop_take, show 64 * (16 - blockNo) - 64 = 64 * (16 - (blockNo + 1)) by omega]
          rw [htk64, hdp64, ← htb.2.2.1, ← hcomp,
              show false = decide (blockNo + 1 = 0) from (decide_eq_false (by omega)).symm]
          exact hd_eq
        · conv_lhs => unfold blake3HashBlocksFuel
          dsimp only
          cases htr : t.rest with
          | nil => exact absurd htr hne
          | cons b br =>
            simp only [hat15, show ((0 : Nat) == 1) = false from rfl,
              Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.false_and]
            rw [hfl_eq, htlen, ← htr]
            exact hrec

private theorem blake3HashBlocksFuel_multiChunk (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag) :
    ∀ (chunksRem : Nat) (fuel : Nat) (input : ByteList) (c : Nat) (layer : LayerStack),
      ValidBytes input →
      byteListLen input ≤ 1024 * chunksRem →
      c < 2 ^ 64 →
      c + chunksRem ≤ 2 ^ 64 →
      (c = 0 → 1024 < byteListLen input) →
      byteListLen input + 1 ≤ fuel →
      layerStackToList
        (blake3HashBlocksFuel keyCv baseFlag fuel input 0
          c.toUInt64.toUInt32 (c.toUInt64 >>> 32).toUInt32 keyCv layer) =
      layerStackToList layer ++
        (IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith (digest32ToCV keyCv) baseFlag c
          (byteListToUInt8List input)).map Blake3.Pure.Output.chainingValue
  | 0, fuel, input, c, layer, hv, hle, hclt, hc, hc0, hfuel => by
    have h0 : byteListLen input = 0 := by omega
    have hcne : c ≠ 0 := fun h => by have := hc0 h; omega
    have hstep := (blake3HashBlocksFuel_chunkStep keyCv baseFlag hd fuel input 0 c keyCv layer
      hv (by decide) hclt (fun h => absurd h hcne) hfuel).1 (by omega)
    obtain ⟨d, hEq, hd_eq⟩ := hstep
    rw [hEq, layerStackToList, hd_eq,
        IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith_small _ _ _ _
          (by rw [byteListToUInt8List_length]; omega)]
    rfl
  | chunksRem + 1, fuel, input, c, layer, hv, hle, hclt, hc, hc0, hfuel => by
    have hlen_bs : (byteListToUInt8List input).length = byteListLen input :=
      byteListToUInt8List_length input
    by_cases hsmall : byteListLen input ≤ 1024
    · have hcne : c ≠ 0 := fun h => by have := hc0 h; omega
      have hstep := (blake3HashBlocksFuel_chunkStep keyCv baseFlag hd fuel input 0 c keyCv layer
        hv (by decide) hclt (fun h => absurd h hcne) hfuel).1 (by omega)
      obtain ⟨d, hEq, hd_eq⟩ := hstep
      rw [hEq, layerStackToList, hd_eq,
          IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith_small _ _ _ _ (by omega)]
      rfl
    · have hlarge : 1024 < byteListLen input := by omega
      have hremPos : 1 ≤ chunksRem := by omega
      have hstep := (blake3HashBlocksFuel_chunkStep keyCv baseFlag hd fuel input 0 c keyCv layer
        hv (by decide) hclt (fun _ => hlarge) hfuel).2 (by omega) (by omega)
      obtain ⟨d, rest, fuel', hvR, hdropR, hlenR, hfuelR, hd_eq, hEq⟩ := hstep
      rw [hEq]
      have hih := blake3HashBlocksFuel_multiChunk keyCv baseFlag hd chunksRem fuel' rest (c + 1)
        (.push layer d) hvR (by omega) (by omega) (by omega) (fun h => by omega) hfuelR
      rw [hih, layerStackToList, List.append_assoc,
          IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith_large (digest32ToCV keyCv) baseFlag c
            (byteListToUInt8List input) (by omega),
          List.map_cons]
      have hdrop1024 : byteListToUInt8List rest = (byteListToUInt8List input).drop 1024 := hdropR
      rw [hdrop1024]
      congr 1
      rw [hd_eq]
      rfl

/-- **Full Multi-Block / Multi-Chunk BLAKE3 Equivalence (`StarkWire.blake3HashBytesWithCv`)**:
For any valid domain flag mask (`0` plain, `16` keyed, `32` `derive_key_context`,
`64` `derive_key_material`) and any valid byte stream of length `≤ 1024 * 2^64` (the full
64-bit BLAKE3 chunk-counter range), `StarkWire.blake3HashBytesWithCv` produces the exact
8-word root chaining value of `IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith`. -/
theorem blake3HashBytesWithCv_eq_digestCVWith (keyCv : Digest32) (baseFlag : UInt32)
    (hd : IxCC.AiurBackend.Blake3KeyedSpec.ValidDomainFlags baseFlag)
    {bytes : ByteList} (hv : ValidBytes bytes) (hlen : byteListLen bytes ≤ 1024 * 2 ^ 64) :
    digest32ToCV (blake3HashBytesWithCv keyCv baseFlag bytes) =
      IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith (digest32ToCV keyCv) baseFlag
        (byteListToUInt8List bytes) := by
  unfold blake3HashBytesWithCv
  dsimp only
  by_cases hsmall : byteListLen bytes ≤ 1024
  · obtain ⟨root, hblk, hroot⟩ := blake3HashBlocksFuel_singleChunk keyCv baseFlag hd
      (byteListLen bytes + 1) bytes 0 keyCv hv (by decide) (by omega) (Nat.le_refl _)
    rw [hblk]
    dsimp only [layerStackDepth]
    change digest32ToCV root = _
    rw [hroot]
    unfold IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith
    rw [IxCC.AiurBackend.Blake3KeyedSpec.subtreeWith_of_le _ _ 0 _
          (by rw [byteListToUInt8List_length]; exact hsmall)]
    rfl
  · have hlarge : 1024 < byteListLen bytes := by omega
    have hlayer := blake3HashBlocksFuel_multiChunk keyCv baseFlag hd (2 ^ 64)
      (byteListLen bytes + 1) bytes 0 .nil hv hlen (by decide) (by omega) (fun _ => hlarge) (Nat.le_refl _)
    set layer := blake3HashBlocksFuel keyCv baseFlag (byteListLen bytes + 1) bytes 0 0 0 keyCv .nil
    have hlayer_list :
        layerStackToList layer =
        (IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith (digest32ToCV keyCv) baseFlag 0
          (byteListToUInt8List bytes)).map Blake3.Pure.Output.chainingValue := by
      simpa [layerStackToList] using hlayer
    have hchunks_ge2 :
        2 ≤ (IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith (digest32ToCV keyCv) baseFlag 0
          (byteListToUInt8List bytes)).length := by
      rw [IxCC.AiurBackend.Blake3KeyedSpec.chunkOutputsWith_length, byteListToUInt8List_length]
      split <;> omega
    have hdepth_ge2 : 2 ≤ layerStackDepth layer := by
      rw [← layerStackToList_length, hlayer_list, List.length_map]
      exact hchunks_ge2
    rw [blake3CompressLayerFuel_eq_compressLayerWith keyCv baseFlag hd (layerStackDepth layer + 1)
          layer hdepth_ge2 (by omega),
        hlayer_list,
        IxCC.AiurBackend.Blake3KeyedSpec.compressLayerWith_spec _ _ _ hchunks_ge2,
        IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith_eq_mergeLevelsWith]

/-- **Plain BLAKE3 Equivalence (`StarkWire.blake3HashBytes` = `Blake3.Pure.digest`)**:
for any valid byte stream of length `≤ 1024 * 2^64`. -/
theorem blake3HashBytes_eq_pure {bytes : ByteList} (hv : ValidBytes bytes)
    (hlen : byteListLen bytes ≤ 1024 * 2 ^ 64) :
    digest32ToBytes (blake3HashBytes bytes) = Blake3.Pure.digest (byteListToUInt8List bytes) := by
  unfold digest32ToBytes blake3HashBytes
  rw [blake3HashBytesWithCv_eq_digestCVWith blake3IV 0
        IxCC.AiurBackend.Blake3KeyedSpec.validDomainFlags_plain hv hlen]
  exact IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith_plain (byteListToUInt8List bytes)

/-! ### Exact Bridge Between `Blake3KeyedSpec` and `Ix.Cert.MultiStark` Parameterized BLAKE3 -/

private theorem chunkLoopWith_bridge (flags : UInt32) (counter : UInt64) (cv : Blake3.Pure.CV)
    (start : Bool) (input : List UInt8) :
    IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith flags counter cv start input =
      Ix.Cert.MultiStark.chunkLoopWith flags counter cv start input := by
  by_cases small : input.length ≤ 64
  · rw [IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_le flags counter cv start input small,
        Ix.Cert.MultiStark.chunkLoopWith_of_le flags counter cv start input small]
  · have large : 64 < input.length := by omega
    rw [IxCC.AiurBackend.Blake3KeyedSpec.chunkLoopWith_of_gt flags counter cv start input large,
        Ix.Cert.MultiStark.chunkLoopWith_of_gt flags counter cv start input large]
    exact chunkLoopWith_bridge flags counter _ false (input.drop 64)
termination_by input.length
decreasing_by simp only [List.length_drop]; omega

private theorem subtreeWith_bridge (key : Blake3.Pure.CV) (flags : UInt32) (counter : Nat)
    (input : List UInt8) :
    IxCC.AiurBackend.Blake3KeyedSpec.subtreeWith key flags counter input =
      Ix.Cert.MultiStark.subtreeWith key flags counter input := by
  by_cases small : input.length ≤ 1024
  · rw [IxCC.AiurBackend.Blake3KeyedSpec.subtreeWith_of_le key flags counter input small,
        Ix.Cert.MultiStark.subtreeWith_of_le key flags counter input small]
    exact chunkLoopWith_bridge flags counter.toUInt64 key true input
  · have large : 1024 < input.length := by omega
    rw [IxCC.AiurBackend.Blake3KeyedSpec.subtreeWith_of_gt key flags counter input large,
        Ix.Cert.MultiStark.subtreeWith_of_gt key flags counter input large,
        subtreeWith_bridge key flags counter (input.take (Blake3.Pure.leftLen input.length)),
        subtreeWith_bridge key flags (counter + Blake3.Pure.leftLen input.length / 1024)
          (input.drop (Blake3.Pure.leftLen input.length))]
    rfl
termination_by input.length
decreasing_by
  · have := Blake3.Pure.leftLen_lt (size := input.length) (by omega)
    simp only [List.length_take]; omega
  · have := Blake3.Pure.leftLen_positive input.length
    simp only [List.length_drop]; omega

theorem digestCVWith_bridge (key : Blake3.Pure.CV) (flags : UInt32) (input : List UInt8) :
    IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith key flags input =
      Ix.Cert.MultiStark.digestCVWith key flags input := by
  unfold IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith Ix.Cert.MultiStark.digestCVWith
  rw [subtreeWith_bridge]

theorem digestDeriveKey_bridge (ctx : String) (input : List UInt8) :
    IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey ctx input =
      Ix.Cert.MultiStark.digestDeriveKey ctx input := by
  unfold IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey Ix.Cert.MultiStark.digestDeriveKey
  rw [IxCC.AiurBackend.Blake3KeyedSpec.digestWith_eq_cvBytes_digestCVWith,
      Ix.Cert.MultiStark.digestWith_eq_cvBytes_digestCVWith,
      digestCVWith_bridge]
  unfold IxCC.AiurBackend.Blake3KeyedSpec.deriveKeyContextCV Ix.Cert.MultiStark.deriveKeyContextCV
  rw [digestCVWith_bridge]
  rfl

/-! ### Exact Protocol `v6` Domain-Separated Hasher Equivalences -/

theorem v6MerkleLeafCv_eq_deriveKeyContextCV :
    digest32ToCV v6MerkleLeafCv =
      IxCC.AiurBackend.Blake3KeyedSpec.deriveKeyContextCV
        "multi-stark/v6/merkle/leaf".toUTF8.data.toList :=
  IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.pinnedCV_eq_deriveKeyContextCV
    .v6MerkleLeaf "multi-stark/v6/merkle/leaf" rfl

theorem v6MerkleCompressCv_eq_deriveKeyContextCV :
    digest32ToCV v6MerkleCompressCv =
      IxCC.AiurBackend.Blake3KeyedSpec.deriveKeyContextCV
        "multi-stark/v6/merkle/compress".toUTF8.data.toList :=
  IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.pinnedCV_eq_deriveKeyContextCV
    .v6MerkleCompress "multi-stark/v6/merkle/compress" rfl

theorem v6TranscriptBatchCv_eq_deriveKeyContextCV :
    digest32ToCV v6TranscriptBatchCv =
      IxCC.AiurBackend.Blake3KeyedSpec.deriveKeyContextCV
        "multi-stark/v6/transcript/batch".toUTF8.data.toList :=
  IxCC.AiurBackend.Blake3KeyedSpec.ProtocolDomain.pinnedCV_eq_deriveKeyContextCV
    .v6TranscriptBatch "multi-stark/v6/transcript/batch" rfl

/-- **Protocol `v6` Transcript Hash Equivalence (`StarkWire.v6TranscriptBatchHash`)**:
matches two-pass pure `digestDeriveKey "multi-stark/v6/transcript/batch"` AND
`CertiFri.P3.blake3Transcript .v6Batch` byte-for-byte. -/
theorem v6TranscriptBatchHash_eq_pure {bytes : ByteList} (hv : ValidBytes bytes)
    (hlen : byteListLen bytes ≤ 1024 * 2 ^ 64) :
    digest32ToBytes (v6TranscriptBatchHash bytes) =
      IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey "multi-stark/v6/transcript/batch"
        (byteListToUInt8List bytes) ∧
    byteListToByteArray (digest32Onto (v6TranscriptBatchHash bytes) .nil) =
      CertiFri.P3.blake3Transcript .v6Batch (byteListToByteArray bytes) := by
  have h1 : digest32ToBytes (v6TranscriptBatchHash bytes) =
      IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey "multi-stark/v6/transcript/batch"
        (byteListToUInt8List bytes) := by
    unfold digest32ToBytes v6TranscriptBatchHash IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey
    rw [blake3HashBytesWithCv_eq_digestCVWith v6TranscriptBatchCv 64
          IxCC.AiurBackend.Blake3KeyedSpec.validDomainFlags_deriveKeyMaterial hv hlen,
        v6TranscriptBatchCv_eq_deriveKeyContextCV,
        IxCC.AiurBackend.Blake3KeyedSpec.digestWith_eq_cvBytes_digestCVWith]
    rfl
  refine ⟨h1, ?_⟩
  rw [Ix.Cert.MultiStark.blake3Transcript_eq_pure]
  apply ByteArray.ext
  change (byteListToUInt8List (digest32Onto (v6TranscriptBatchHash bytes) .nil)).toArray =
    (Ix.Cert.MultiStark.digestDeriveKey "multi-stark/v6/transcript/batch"
      (byteListToUInt8List bytes)).toArray
  rw [digest32Onto_toUInt8List, byteListToUInt8List, List.append_nil]
  change (digest32ToBytes (v6TranscriptBatchHash bytes)).toList.toArray = _
  rw [h1, digestDeriveKey_bridge]
  exact Array.toArray_toList

/-- Every `U64Bytes` in a `U64List` is valid (`< 256` per byte) and canonical `< p_GL`. -/
def ValidCanonicalU64List : U64List → Prop
  | .nil => True
  | .cons x rest => ValidU64Bytes x ∧ u64BytesToNat x < glPrime ∧ ValidCanonicalU64List rest

/-- Every row in a `U64ListList` has valid canonical `< p_GL` words. -/
def ValidCanonicalU64ListList : U64ListList → Prop
  | .nil => True
  | .cons r rest => ValidCanonicalU64List r ∧ ValidCanonicalU64ListList rest

/-- Every `U64Bytes` in a `U64List` has all 8 bytes `< 256`. -/
def ValidU64ListBytes : U64List → Prop
  | .nil => True
  | .cons x rest => ValidU64Bytes x ∧ ValidU64ListBytes rest

/-- Every row in a `U64ListList` has all bytes `< 256`. -/
def ValidU64ListListBytes : U64ListList → Prop
  | .nil => True
  | .cons r rest => ValidU64ListBytes r ∧ ValidU64ListListBytes rest

theorem flattenRowChecked_sound (row : U64List) (tail : ByteList)
    (hvr : ValidU64ListBytes row) (hvt : ValidBytes tail) :
    ValidBytes (flattenRowChecked row tail).bytes ∧
    byteListLen (flattenRowChecked row tail).bytes = 8 * u64ListLen row + byteListLen tail ∧
    ((flattenRowChecked row tail).ok = 1 ↔ ValidCanonicalU64List row) := by
  induction row with
  | nil => exact ⟨hvt, by simp [flattenRowChecked, u64ListLen], by simp [flattenRowChecked, ValidCanonicalU64List]⟩
  | cons x rest ih =>
    obtain ⟨hvB, hlenB, hokB⟩ := ih hvr.2
    unfold flattenRowChecked
    dsimp only
    refine ⟨validBytes_u64BytesOnto.mpr ⟨hvr.1, hvB⟩,
      by simp only [byteListLen_u64BytesOnto, hlenB, u64ListLen]; omega, ?_⟩
    by_cases hlt : glLtPBytes x = 1
    · by_cases hrok : (flattenRowChecked rest tail).ok = 1
      · simp only [hlt, hrok, beq_self_eq_true, Bool.and_self, ↓reduceIte, true_iff,
          ValidCanonicalU64List]
        exact ⟨hvr.1, (glLtPBytes_eq_one_iff hvr.1).mp hlt, hokB.mp hrok⟩
      · have hbf : ((flattenRowChecked rest tail).ok == 1) = false := beq_false_of_ne hrok
        simp only [hlt, hbf, beq_self_eq_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          ValidCanonicalU64List]
        exact ⟨fun h => (by cases h), fun ⟨_, _, hr⟩ => absurd (hokB.mpr hr) hrok⟩
    · have hbf : (glLtPBytes x == 1) = false := beq_false_of_ne hlt
      simp only [hbf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ValidCanonicalU64List]
      exact ⟨fun h => (by cases h), fun ⟨_, hltP, _⟩ => absurd ((glLtPBytes_eq_one_iff hvr.1).mpr hltP) hlt⟩

theorem flattenRowsChecked_sound (rows : U64ListList) (hv : ValidU64ListListBytes rows) :
    ValidBytes (flattenRowsChecked rows).bytes ∧
    ((flattenRowsChecked rows).ok = 1 ↔ ValidCanonicalU64ListList rows) := by
  induction rows with
  | nil => exact ⟨trivial, by simp [flattenRowsChecked, ValidCanonicalU64ListList]⟩
  | cons r rest ih =>
    obtain ⟨hvT, hokT⟩ := ih hv.2
    obtain ⟨hvR, _, hokR⟩ := flattenRowChecked_sound r (flattenRowsChecked rest).bytes hv.1 hvT
    unfold flattenRowsChecked
    dsimp only
    refine ⟨hvR, ?_⟩
    by_cases hr1 : (flattenRowChecked r (flattenRowsChecked rest).bytes).ok = 1
    · by_cases ht1 : (flattenRowsChecked rest).ok = 1
      · simp only [hr1, ht1, beq_self_eq_true, Bool.and_self, ↓reduceIte, true_iff,
          ValidCanonicalU64ListList]
        exact ⟨hokR.mp hr1, hokT.mp ht1⟩
      · have hbf : ((flattenRowsChecked rest).ok == 1) = false := beq_false_of_ne ht1
        simp only [hr1, hbf, beq_self_eq_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          ValidCanonicalU64ListList]
        exact ⟨fun h => (by cases h), fun ⟨_, ht⟩ => absurd (hokT.mpr ht) ht1⟩
    · have hbf : ((flattenRowChecked r (flattenRowsChecked rest).bytes).ok == 1) = false :=
        beq_false_of_ne hr1
      simp only [hbf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ValidCanonicalU64ListList]
      exact ⟨fun h => (by cases h), fun ⟨hr, _⟩ => absurd (hokR.mpr hr) hr1⟩

/-- **Protocol `v6` MMCS Leaf Hash Equivalence (`StarkWire.v6MerkleLeafHashChecked`)**:
returns `ok = 1` iff every opened Goldilocks word in `rows` is canonical `< p_GL`, and its
32-byte digest equals two-pass pure `digestDeriveKey "multi-stark/v6/merkle/leaf"` of the
flattened row bytes. -/
theorem v6MerkleLeafHashChecked_eq_pure {rows : U64ListList}
    (hv : ValidU64ListListBytes rows)
    (hlen : byteListLen (flattenRowsChecked rows).bytes ≤ 1024 * 2 ^ 64) :
    ((v6MerkleLeafHashChecked rows).ok = 1 ↔ ValidCanonicalU64ListList rows) ∧
    ValidDigestBytes (v6MerkleLeafHashChecked rows).digest ∧
    digestBytesToUInt8List (v6MerkleLeafHashChecked rows).digest =
      (IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey "multi-stark/v6/merkle/leaf"
        (byteListToUInt8List (flattenRowsChecked rows).bytes)).toList := by
  obtain ⟨hvFlat, hokFlat⟩ := flattenRowsChecked_sound rows hv
  unfold v6MerkleLeafHashChecked
  dsimp only
  refine ⟨hokFlat, validDigestBytes_digest32ToDigestBytes _, ?_⟩
  unfold digestBytesToUInt8List
  rw [digest32ToDigestBytes_toUInt8List, byteListToUInt8List, List.append_nil,
      blake3HashBytesWithCv_eq_digestCVWith v6MerkleLeafCv 64
        IxCC.AiurBackend.Blake3KeyedSpec.validDomainFlags_deriveKeyMaterial hvFlat hlen,
      v6MerkleLeafCv_eq_deriveKeyContextCV]
  rfl

/-- Convert `DigestBytes` to `CertiFri.P3.Digest`. -/
def digestBytesToP3 (d : DigestBytes) : CertiFri.P3.Digest :=
  ⟨u64LoU32 d.d0, u64HiU32 d.d0, u64LoU32 d.d1, u64HiU32 d.d1,
   u64LoU32 d.d2, u64HiU32 d.d2, u64LoU32 d.d3, u64HiU32 d.d3⟩

theorem digestBytesToP3_toBytes {d : DigestBytes} (hv : ValidDigestBytes d) :
    (digestBytesToP3 d).toBytes.data.toList = digestBytesToUInt8List d := by
  have hrepack (x : U64Bytes) (hx : ValidU64Bytes x) :
      (Blake3.Pure.wordBytes (u64LoU32 x)).toList ++ (Blake3.Pure.wordBytes (u64HiU32 x)).toList =
        [UInt8.ofNat x.b0, UInt8.ofNat x.b1, UInt8.ofNat x.b2, UInt8.ofNat x.b3,
         UInt8.ofNat x.b4, UInt8.ofNat x.b5, UInt8.ofNat x.b6, UInt8.ofNat x.b7] := by
    have h4 (b0 b1 b2 b3 : Nat) (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
        (Blake3.Pure.wordBytes (u32OfBytes b0 b1 b2 b3)).toList =
          [UInt8.ofNat b0, UInt8.ofNat b1, UInt8.ofNat b2, UInt8.ofNat b3] := by
      unfold Blake3.Pure.wordBytes u32OfBytes
      have hlt : b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 < 2 ^ 32 := by omega
      change [UInt8.ofNat _, UInt8.ofNat _, UInt8.ofNat _, UInt8.ofNat _] = _
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
        simp only [UInt8.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt] <;> omega
    rw [u64LoU32, u64HiU32, h4 x.b0 x.b1 x.b2 x.b3 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1,
        h4 x.b4 x.b5 x.b6 x.b7 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2]
    rfl
  rw [show (digestBytesToP3 d).toBytes.data.toList =
      (Blake3.Pure.cvBytes (Ix.Cert.MultiStark.digestToCV (digestBytesToP3 d))).toList by
    rw [Ix.Cert.MultiStark.digest_toBytes_eq_cvBytes]; rfl]
  have hcv : (Blake3.Pure.cvBytes (Ix.Cert.MultiStark.digestToCV (digestBytesToP3 d))).toList =
      ((Blake3.Pure.wordBytes (u64LoU32 d.d0)).toList ++ (Blake3.Pure.wordBytes (u64HiU32 d.d0)).toList) ++
      ((Blake3.Pure.wordBytes (u64LoU32 d.d1)).toList ++ (Blake3.Pure.wordBytes (u64HiU32 d.d1)).toList) ++
      ((Blake3.Pure.wordBytes (u64LoU32 d.d2)).toList ++ (Blake3.Pure.wordBytes (u64HiU32 d.d2)).toList) ++
      ((Blake3.Pure.wordBytes (u64LoU32 d.d3)).toList ++ (Blake3.Pure.wordBytes (u64HiU32 d.d3)).toList) := by
    apply List.ext_getElem (by simp [Blake3.Pure.cvBytes, Blake3.Pure.wordBytes])
    intro i hi1 hi2
    have hi32 : i < 32 := by simpa using hi1
    simp only [Vector.getElem_toList, Blake3.Pure.cvBytes, Vector.getElem_ofFn,
      Ix.Cert.MultiStark.digestToCV, digestBytesToP3]
    interval_cases i <;> rfl
  rw [hcv, hrepack d.d0 hv.1, hrepack d.d1 hv.2.1, hrepack d.d2 hv.2.2.1, hrepack d.d3 hv.2.2.2]
  rfl

/-- **Protocol `v6` MMCS 2-to-1 Compression Equivalence (`StarkWire.v6MerkleCompress`)**:
matches BOTH two-pass pure `digestDeriveKey "multi-stark/v6/merkle/compress"` of `a ‖ b` AND
`(CertiFri.P3.baseHasherSep .v6Batch).compress` byte-for-byte. -/
theorem v6MerkleCompress_eq_pure {a b : DigestBytes}
    (ha : ValidDigestBytes a) (hb : ValidDigestBytes b) :
    ValidDigestBytes (v6MerkleCompress a b) ∧
    digestBytesToUInt8List (v6MerkleCompress a b) =
      (IxCC.AiurBackend.Blake3KeyedSpec.digestDeriveKey "multi-stark/v6/merkle/compress"
        (digestBytesToUInt8List a ++ digestBytesToUInt8List b)).toList ∧
    digestBytesToUInt8List (v6MerkleCompress a b) =
      ((CertiFri.P3.baseHasherSep .v6Batch).compress (digestBytesToP3 a) (digestBytesToP3 b)).toBytes.data.toList := by
  unfold v6MerkleCompress
  refine ⟨validDigestBytes_digest32ToDigestBytes _, ?_, ?_⟩
  · unfold digestBytesToUInt8List
    rw [digest32ToDigestBytes_toUInt8List, byteListToUInt8List, List.append_nil]
    have hcomp := blake3Compress_eq_pure v6MerkleCompressCv
      { m0 := u64LoU32 a.d0, m1 := u64HiU32 a.d0
        m2 := u64LoU32 a.d1, m3 := u64HiU32 a.d1
        m4 := u64LoU32 a.d2, m5 := u64HiU32 a.d2
        m6 := u64LoU32 a.d3, m7 := u64HiU32 a.d3
        m8 := u64LoU32 b.d0, m9 := u64HiU32 b.d0
        m10 := u64LoU32 b.d1, m11 := u64HiU32 b.d1
        m12 := u64LoU32 b.d2, m13 := u64HiU32 b.d2
        m14 := u64LoU32 b.d3, m15 := u64HiU32 b.d3 } 0 64 75
    have hblk : block16ToPure
      { m0 := u64LoU32 a.d0, m1 := u64HiU32 a.d0
        m2 := u64LoU32 a.d1, m3 := u64HiU32 a.d1
        m4 := u64LoU32 a.d2, m5 := u64HiU32 a.d2
        m6 := u64LoU32 a.d3, m7 := u64HiU32 a.d3
        m8 := u64LoU32 b.d0, m9 := u64HiU32 b.d0
        m10 := u64LoU32 b.d1, m11 := u64HiU32 b.d1
        m12 := u64LoU32 b.d2, m13 := u64HiU32 b.d2
        m14 := u64LoU32 b.d3, m15 := u64HiU32 b.d3 } =
      digestBytesToCV a ++ digestBytesToCV b := rfl
    rw [hblk] at hcomp
    have hpair := IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith_pair
      (digest32ToCV v6MerkleCompressCv) IxCC.AiurBackend.Blake3KeyedSpec.flagDeriveKeyMaterial
      (digestBytesToCV a) (digestBytesToCV b)
    have ha_cv : (Blake3.Pure.cvBytes (digestBytesToCV a)).toList = digestBytesToUInt8List a := by
      have := digestBytesToP3_toBytes ha
      rw [Ix.Cert.MultiStark.digest_toBytes_eq_cvBytes] at this
      exact this
    have hb_cv : (Blake3.Pure.cvBytes (digestBytesToCV b)).toList = digestBytesToUInt8List b := by
      have := digestBytesToP3_toBytes hb
      rw [Ix.Cert.MultiStark.digest_toBytes_eq_cvBytes] at this
      exact this
    rw [ha_cv, hb_cv] at hpair
    change (Blake3.Pure.cvBytes (digest32ToCV (blake3Compress v6MerkleCompressCv _
      (0 : UInt64).toUInt32 ((0 : UInt64) >>> 32).toUInt32 64 75))).toList = _
    rw [hcomp, show (75 : UInt32) = IxCC.AiurBackend.Blake3KeyedSpec.flagDeriveKeyMaterial ||| 11 from rfl,
        ← hpair, v6MerkleCompressCv_eq_deriveKeyContextCV]
    rfl
  · rw [Ix.Cert.MultiStark.baseHasherSep_compress_eq_pure]
    change digestBytesToUInt8List (digest32ToDigestBytes _) =
      (Ix.Cert.MultiStark.digestDeriveKey "multi-stark/v6/merkle/compress"
        ((digestBytesToP3 a).toBytes ++ (digestBytesToP3 b).toBytes).data.toList).toList
    have happ : ((digestBytesToP3 a).toBytes ++ (digestBytesToP3 b).toBytes).data.toList =
        digestBytesToUInt8List a ++ digestBytesToUInt8List b := by
      simp only [ByteArray.data_append, Array.toList_append,
        digestBytesToP3_toBytes ha, digestBytesToP3_toBytes hb]
    rw [happ, ← digestDeriveKey_bridge]
    -- Reuse the first branch directly:
    have hcomp := blake3Compress_eq_pure v6MerkleCompressCv
      { m0 := u64LoU32 a.d0, m1 := u64HiU32 a.d0
        m2 := u64LoU32 a.d1, m3 := u64HiU32 a.d1
        m4 := u64LoU32 a.d2, m5 := u64HiU32 a.d2
        m6 := u64LoU32 a.d3, m7 := u64HiU32 a.d3
        m8 := u64LoU32 b.d0, m9 := u64HiU32 b.d0
        m10 := u64LoU32 b.d1, m11 := u64HiU32 b.d1
        m12 := u64LoU32 b.d2, m13 := u64HiU32 b.d2
        m14 := u64LoU32 b.d3, m15 := u64HiU32 b.d3 } 0 64 75
    have hblk : block16ToPure
      { m0 := u64LoU32 a.d0, m1 := u64HiU32 a.d0
        m2 := u64LoU32 a.d1, m3 := u64HiU32 a.d1
        m4 := u64LoU32 a.d2, m5 := u64HiU32 a.d2
        m6 := u64LoU32 a.d3, m7 := u64HiU32 a.d3
        m8 := u64LoU32 b.d0, m9 := u64HiU32 b.d0
        m10 := u64LoU32 b.d1, m11 := u64HiU32 b.d1
        m12 := u64LoU32 b.d2, m13 := u64HiU32 b.d2
        m14 := u64LoU32 b.d3, m15 := u64HiU32 b.d3 } =
      digestBytesToCV a ++ digestBytesToCV b := rfl
    rw [hblk] at hcomp
    have hpair := IxCC.AiurBackend.Blake3KeyedSpec.digestCVWith_pair
      (digest32ToCV v6MerkleCompressCv) IxCC.AiurBackend.Blake3KeyedSpec.flagDeriveKeyMaterial
      (digestBytesToCV a) (digestBytesToCV b)
    have ha_cv : (Blake3.Pure.cvBytes (digestBytesToCV a)).toList = digestBytesToUInt8List a := by
      have := digestBytesToP3_toBytes ha; rw [Ix.Cert.MultiStark.digest_toBytes_eq_cvBytes] at this; exact this
    have hb_cv : (Blake3.Pure.cvBytes (digestBytesToCV b)).toList = digestBytesToUInt8List b := by
      have := digestBytesToP3_toBytes hb; rw [Ix.Cert.MultiStark.digest_toBytes_eq_cvBytes] at this; exact this
    rw [ha_cv, hb_cv] at hpair
    unfold digestBytesToUInt8List
    rw [digest32ToDigestBytes_toUInt8List, byteListToUInt8List, List.append_nil]
    change (Blake3.Pure.cvBytes (digest32ToCV (blake3Compress v6MerkleCompressCv _
      (0 : UInt64).toUInt32 ((0 : UInt64) >>> 32).toUInt32 64 75))).toList = _
    rw [hcomp, show (75 : UInt32) = IxCC.AiurBackend.Blake3KeyedSpec.flagDeriveKeyMaterial ||| 11 from rfl,
        ← hpair, v6MerkleCompressCv_eq_deriveKeyContextCV]
    rfl

/-! ### Section 3B: Exact 84-Byte `"ix/compress-wrap/v1\0"` Statement Binding -/

theorem statementDomainOnto_validBytes {tail : ByteList} (ht : ValidBytes tail) :
    ValidBytes (statementDomainOnto tail) := by
  unfold statementDomainOnto
  simp only [ValidBytes]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ht⟩

theorem statementDomainOnto_length (tail : ByteList) :
    byteListLen (statementDomainOnto tail) = 20 + byteListLen tail := by
  unfold statementDomainOnto
  simp only [byteListLen]; omega

theorem statementDomainOnto_toUInt8List (tail : ByteList) :
    byteListToUInt8List (statementDomainOnto tail) =
      Ix.Cert.AiurCompression.compressWrapDomain ++ byteListToUInt8List tail := rfl

theorem statementPreimage_validBytes (kd cd : Digest32) :
    ValidBytes (statementPreimage kd cd) :=
  statementDomainOnto_validBytes (validBytes_digest32Onto kd (validBytes_digest32Onto cd trivial))

theorem statementPreimage_length (kd cd : Digest32) :
    byteListLen (statementPreimage kd cd) = 84 := by
  unfold statementPreimage
  rw [statementDomainOnto_length, byteListLen_digest32Onto, byteListLen_digest32Onto]
  rfl

theorem statementPreimage_eq_compressWrapPreimage (kd cd : Digest32) :
    byteListToUInt8List (statementPreimage kd cd) =
      Ix.Cert.AiurCompression.compressWrapPreimage
        (digest32ToBytes kd).toList (digest32ToBytes cd).toList := by
  unfold statementPreimage Ix.Cert.AiurCompression.compressWrapPreimage
  rw [statementDomainOnto_toUInt8List, digest32Onto_toUInt8List, digest32Onto_toUInt8List,
      byteListToUInt8List, List.append_nil, List.append_assoc]
  rfl

/-- **Exact `"ix/compress-wrap/v1\0"` Statement Digest Binding (`StarkWire.computeStatementDigest`)**:
Matches `Ix.Cert.AiurCompression.rootStatementWords` / `compressWrapStatementDigest` word-for-word,
and every output word is strictly `< 2^32`. -/
theorem computeStatementDigest_eq_pure {keyBytes claimsBytes : ByteList}
    (hvK : ValidBytes keyBytes) (hvC : ValidBytes claimsBytes)
    (hlK : byteListLen keyBytes ≤ 1024 * 2 ^ 64) (hlC : byteListLen claimsBytes ≤ 1024 * 2 ^ 64) :
    digest32WordsToList (computeStatementDigest keyBytes claimsBytes) =
      Ix.Cert.AiurCompression.rootStatementWords
        (Blake3.Pure.digest (byteListToUInt8List keyBytes))
        (byteListToUInt8List claimsBytes) ∧
    (∀ w ∈ digest32WordsToList (computeStatementDigest keyBytes claimsBytes), w < 2 ^ 32) := by
  have hmain : digest32WordsToList (computeStatementDigest keyBytes claimsBytes) =
      Ix.Cert.AiurCompression.rootStatementWords
        (Blake3.Pure.digest (byteListToUInt8List keyBytes))
        (byteListToUInt8List claimsBytes) := by
    unfold computeStatementDigest Ix.Cert.AiurCompression.rootStatementWords
      Ix.Cert.AiurCompression.rootStatementDigest Ix.Cert.AiurCompression.compressWrapStatementDigest
    dsimp only
    rw [← packBytes32ToU32Words_cvBytes]
    have hpreV := statementPreimage_validBytes (blake3HashBytes keyBytes) (blake3HashBytes claimsBytes)
    have hpreL : byteListLen (statementPreimage (blake3HashBytes keyBytes) (blake3HashBytes claimsBytes)) ≤
        1024 * 2 ^ 64 := by
      rw [statementPreimage_length]; decide
    change Ix.Cert.AiurCompression.packBytes32ToU32Words
      (digest32ToBytes (blake3HashBytes (statementPreimage _ _))).toList = _
    rw [blake3HashBytes_eq_pure hpreV hpreL, statementPreimage_eq_compressWrapPreimage,
        blake3HashBytes_eq_pure hvK hlK, blake3HashBytes_eq_pure hvC hlC]
  exact ⟨hmain, by rw [hmain]; exact Ix.Cert.AiurCompression.rootStatementWords_lt _ _⟩

/-- **Statement Digest Collision-Resistant Injectivity**:
Two valid `(keyBytes, claimsBytes)` pairs that produce the same `computeStatementDigest`
either are byte-for-byte identical OR yield a concrete BLAKE3 collision (at the 84-byte
statement preimage, key bytes, or claims bytes). -/
theorem computeStatementDigest_injective_or_collision
    {k₁ c₁ k₂ c₂ : ByteList}
    (hvk₁ : ValidBytes k₁) (hvc₁ : ValidBytes c₁)
    (hvk₂ : ValidBytes k₂) (hvc₂ : ValidBytes c₂)
    (hlk₁ : byteListLen k₁ ≤ 1024 * 2 ^ 64) (hlc₁ : byteListLen c₁ ≤ 1024 * 2 ^ 64)
    (hlk₂ : byteListLen k₂ ≤ 1024 * 2 ^ 64) (hlc₂ : byteListLen c₂ ≤ 1024 * 2 ^ 64)
    (heq : computeStatementDigest k₁ c₁ = computeStatementDigest k₂ c₂) :
    (∃ a b, Ix.Cert.AiurCompression.Blake3Collision a b) ∨ (k₁ = k₂ ∧ c₁ = c₂) := by
  have h1 := (computeStatementDigest_eq_pure hvk₁ hvc₁ hlk₁ hlc₁).1
  have h2 := (computeStatementDigest_eq_pure hvk₂ hvc₂ hlk₂ hlc₂).1
  have hwords :
      Ix.Cert.AiurCompression.rootStatementWords
        (Blake3.Pure.digest (byteListToUInt8List k₁)) (byteListToUInt8List c₁) =
      Ix.Cert.AiurCompression.rootStatementWords
        (Blake3.Pure.digest (byteListToUInt8List k₂)) (byteListToUInt8List c₂) := by
    rw [← h1, ← h2, heq]
  unfold Ix.Cert.AiurCompression.rootStatementWords Ix.Cert.AiurCompression.rootStatementDigest at hwords
  have hdigList := Ix.Cert.AiurCompression.packBytes32ToU32Words_injective (by simp) (by simp) hwords
  have hdig :
      Ix.Cert.AiurCompression.compressWrapStatementDigest
        (Blake3.Pure.digest (byteListToUInt8List k₁)).toList
        (Blake3.Pure.digest (byteListToUInt8List c₁)).toList =
      Ix.Cert.AiurCompression.compressWrapStatementDigest
        (Blake3.Pure.digest (byteListToUInt8List k₂)).toList
        (Blake3.Pure.digest (byteListToUInt8List c₂)).toList :=
    Vector.ext fun i hi => by
      have := congrArg (fun l => l[i]?) hdigList
      simpa [Vector.getElem?_toList, hi] using this
  rcases Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision (by simp) (by simp) hdig with
    hcol | ⟨hkDigList, hcDigList⟩
  · exact Or.inl ⟨_, _, hcol⟩
  · have hkDig : Blake3.Pure.digest (byteListToUInt8List k₁) = Blake3.Pure.digest (byteListToUInt8List k₂) :=
      Vector.ext fun i hi => by
        have := congrArg (fun l => l[i]?) hkDigList
        simpa [Vector.getElem?_toList, hi] using this
    have hcDig : Blake3.Pure.digest (byteListToUInt8List c₁) = Blake3.Pure.digest (byteListToUInt8List c₂) :=
      Vector.ext fun i hi => by
        have := congrArg (fun l => l[i]?) hcDigList
        simpa [Vector.getElem?_toList, hi] using this
    by_cases hk : byteListToUInt8List k₁ = byteListToUInt8List k₂
    · by_cases hc : byteListToUInt8List c₁ = byteListToUInt8List c₂
      · exact Or.inr ⟨byteList_eq_of_toUInt8List_eq hvk₁ hvk₂ hk,
          byteList_eq_of_toUInt8List_eq hvc₁ hvc₂ hc⟩
      · exact Or.inl ⟨byteListToUInt8List c₁, byteListToUInt8List c₂, hc, hcDig⟩
    · exact Or.inl ⟨byteListToUInt8List k₁, byteListToUInt8List k₂, hk, hkDig⟩

/-- Direct link between `computeStatementDigest` and `Ix.Cert.AiurCompression.StatementPolicy`:
under any `pol : StatementPolicy` (`singleLayerDirect` or `twoLayerWrap wp`), mapping
`computeStatementDigest keyBytes claimsBytes` via `pol.glStatementWords` equals
`pol.terminalStatementWords (Blake3.Pure.digest keyBytes) claimsBytes`. -/
theorem computeStatementDigest_statementPolicy_link
    (pol : Ix.Cert.AiurCompression.StatementPolicy)
    {keyBytes claimsBytes : ByteList}
    (hvK : ValidBytes keyBytes) (hvC : ValidBytes claimsBytes)
    (hlK : byteListLen keyBytes ≤ 1024 * 2 ^ 64) (hlC : byteListLen claimsBytes ≤ 1024 * 2 ^ 64) :
    pol.glStatementWords (digest32WordsToList (computeStatementDigest keyBytes claimsBytes)) =
      pol.terminalStatementWords
        (Blake3.Pure.digest (byteListToUInt8List keyBytes))
        (byteListToUInt8List claimsBytes) := by
  rw [(computeStatementDigest_eq_pure hvK hvC hlK hlC).1]
  rfl

/-! ### Section 3C: Protocol `v6` Keyed BLAKE3 Fiat–Shamir Challenger Equivalence -/

/-- Every bit in a `BitList` is `0` or `1`. -/
def ValidBits : BitList → Prop
  | .nil => True
  | .cons b rest => (b = 0 ∨ b = 1) ∧ ValidBits rest

/-- State coupling invariant between `CompressWrapPure.ChallengerState` and
`CertiFri.P3.ChallengerState`. -/
structure ChallengerRel (st : CompressWrapPure.ChallengerState)
    (s : CertiFri.P3.ChallengerState) : Prop where
  validInput : ValidBytes st.input
  validOutput : ValidBytes st.output
  inputBound : byteListLen st.input ≤ 1024 * 2 ^ 64
  outputMod8 : byteListLen st.output % 8 = 0
  inputEq : s.input = byteListToByteArray st.input
  outputEq : s.output = byteListToUInt8List st.output
  notExhausted : s.exhausted = false

private theorem pack_le_u64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ((((((((0 : UInt64) ||| (b0.toUInt64 <<< 0)) ||| (b1.toUInt64 <<< 8)) |||
      (b2.toUInt64 <<< 16)) ||| (b3.toUInt64 <<< 24)) ||| (b4.toUInt64 <<< 32)) |||
      (b5.toUInt64 <<< 40)) ||| (b6.toUInt64 <<< 48)) ||| (b7.toUInt64 <<< 56) =
    UInt64.ofNat
      ((b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) +
        4294967296 * (b4.toNat + 256 * b5.toNat + 65536 * b6.toNat + 16777216 * b7.toNat)) := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt; have h2 := b2.toNat_lt; have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt; have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  have hsum :
      (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) +
        4294967296 * (b4.toNat + 256 * b5.toNat + 65536 * b6.toNat + 16777216 * b7.toNat) < 2 ^ 64 := by
    omega
  have lor_mul_pow : ∀ (a b k : Nat), a < 2 ^ k → (a ||| (b * 2 ^ k)) = a + b * 2 ^ k := by
    intro a b k ha
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
    have hbit : (a + b * 2 ^ k).testBit i = if i < k then a.testBit i else b.testBit (i - k) := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      split_ifs with hi
      · have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        have hstep : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
          conv => lhs; rw [show k - i = (k - i - 1) + 1 by omega, Nat.pow_succ]
        rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), hstep,
            ← Nat.mul_assoc, Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod]
        have hmod : (a / 2 ^ i + b * 2 ^ (k - i - 1) * 2) % 2 = (a / 2 ^ i) % 2 := by omega
        rw [hmod]
      · have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
          rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
            Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hbit]
    by_cases hi : i < k
    · have : ¬ k ≤ i := by omega
      simp [hi, this]
    · have ha_lt : a < 2 ^ i :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
      have : a.testBit i = false := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ha_lt]; rfl
      have hge : k ≤ i := by omega
      simp [hi, hge, this]
  have hsh (x : UInt8) (k : Nat) (hk : k ≤ 56) :
      (x.toUInt64 <<< UInt64.ofNat k).toNat = x.toNat * 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
    have hmod : (UInt64.ofNat k).toNat % 64 = k := by
      rw [UInt64.toNat_ofNat']; omega
    rw [hmod, Nat.shiftLeft_eq]
    have hx := x.toNat_lt
    have hpow : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
    have hmul : x.toNat * 2 ^ k < 2 ^ 64 := by
      have : x.toNat * 2 ^ k ≤ 255 * 2 ^ 56 := Nat.mul_le_mul (by omega) hpow
      omega
    exact Nat.mod_eq_of_lt hmul
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsum]
  simp only [UInt64.toNat_or, UInt64.toNat_zero, Nat.zero_or]
  rw [show (0 : UInt64) = UInt64.ofNat 0 from rfl, hsh b0 0 (by decide),
      show (8 : UInt64) = UInt64.ofNat 8 from rfl, hsh b1 8 (by decide),
      show (16 : UInt64) = UInt64.ofNat 16 from rfl, hsh b2 16 (by decide),
      show (24 : UInt64) = UInt64.ofNat 24 from rfl, hsh b3 24 (by decide),
      show (32 : UInt64) = UInt64.ofNat 32 from rfl, hsh b4 32 (by decide),
      show (40 : UInt64) = UInt64.ofNat 40 from rfl, hsh b5 40 (by decide),
      show (48 : UInt64) = UInt64.ofNat 48 from rfl, hsh b6 48 (by decide),
      show (56 : UInt64) = UInt64.ofNat 56 from rfl, hsh b7 56 (by decide)]
  rw [Nat.pow_zero, Nat.mul_one]
  rw [lor_mul_pow b0.toNat b1.toNat 8 h0]
  rw [lor_mul_pow _ b2.toNat 16 (by omega)]
  rw [lor_mul_pow _ b3.toNat 24 (by omega)]
  rw [lor_mul_pow _ b4.toNat 32 (by omega)]
  rw [lor_mul_pow _ b5.toNat 40 (by omega)]
  rw [lor_mul_pow _ b6.toNat 48 (by omega)]
  rw [lor_mul_pow _ b7.toNat 56 (by omega)]
  omega

private theorem pop8Bytes_sound (out : ByteList) (hv : ValidBytes out) (hlen : 8 ≤ byteListLen out) :
    let p := pop8Bytes out
    ValidU64Bytes p.word ∧
    ValidBytes p.state.output ∧
    byteListLen p.state.output = byteListLen out - 8 ∧
    byteListToUInt8List out =
      [UInt8.ofNat p.word.b0, UInt8.ofNat p.word.b1, UInt8.ofNat p.word.b2, UInt8.ofNat p.word.b3,
       UInt8.ofNat p.word.b4, UInt8.ofNat p.word.b5, UInt8.ofNat p.word.b6, UInt8.ofNat p.word.b7] ++
      byteListToUInt8List p.state.output := by
  rcases out with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · simp [byteListLen] at hlen
  · rcases hv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hrest⟩
    have hr (b : Nat) (hb : b < 256) (s : ByteList) :
        readU8 (.cons b s) = { ok := 1, val := b, rest := s } := by
      unfold readU8 readLeNatAux; dsimp only
      rw [ite_eq_left hb]
      simp [readLeNatAux]
    unfold pop8Bytes
    simp only [hr b0 h0, hr b1 h1, hr b2 h2, hr b3 h3, hr b4 h4, hr b5 h5, hr b6 h6, hr b7 h7]
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, hrest, by simp [byteListLen]; omega, rfl⟩

private theorem sampleWord_of_output_cons8 (hash : ByteArray → ByteArray)
    (inp : ByteArray) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (rest : List UInt8) (exh : Bool) :
    CertiFri.P3.ChallengerState.sampleWord hash
      { input := inp, output := b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, exhausted := exh } =
    (UInt64.ofNat
      ((b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) +
        4294967296 * (b4.toNat + 256 * b5.toNat + 65536 * b6.toNat + 16777216 * b7.toNat)),
      { input := inp, output := rest, exhausted := exh }) := by
  unfold CertiFri.P3.ChallengerState.sampleWord CertiFri.P3.ChallengerState.sampleBytes
    CertiFri.P3.ChallengerState.sampleByte
  dsimp only
  exact Prod.ext (pack_le_u64 b0 b1 b2 b3 b4 b5 b6 b7) rfl

private theorem byteArray_toList_loop_eq (bs : ByteArray) :
    ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, hk => by
    have hge : ¬ i < bs.size := by omega
    have hlen : bs.data.toList.length ≤ i := by
      have : bs.data.toList.length = bs.size := Array.length_toList
      omega
    rw [ByteArray.toList.loop, ite_eq_right hge, List.drop_eq_nil_of_le hlen, List.append_nil]
  | k + 1, i, r, hk => by
    have hlt : i < bs.size := by omega
    have hltL : i < bs.data.toList.length := by
      have : bs.data.toList.length = bs.size := Array.length_toList
      omega
    rw [ByteArray.toList.loop, ite_eq_left hlt, byteArray_toList_loop_eq bs k (i + 1) _ (by omega)]
    have hget : bs.get! i = bs.data.toList[i]'hltL := by
      simp [ByteArray.get!, hlt]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, hget, List.getElem_cons_drop]

private theorem byteArray_toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop_eq bs bs.size 0 [] (by omega)

/-- **Protocol `v6` Challenger `sampleWord` Equivalence (`CompressWrapPure.chSample8`)**:
exact word-for-word and state-for-state match with
`CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch)`. -/
theorem chSample8_eq_sampleWord {st : CompressWrapPure.ChallengerState}
    {s : CertiFri.P3.ChallengerState} (hrel : ChallengerRel st s) :
    let out := chSample8 st
    let p3 := CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s
    ValidU64Bytes out.word ∧
    UInt64.ofNat (u64BytesToNat out.word) = p3.1 ∧
    ChallengerRel out.state p3.2 := by
  rcases hrel with ⟨hvI, hvO, hbdI, hmod8, hinpEq, houtEq, hexh⟩
  cases hstOut : st.output with
  | nil =>
    have hsOut : s.output = [] := by rw [houtEq, hstOut]; rfl
    set h := v6TranscriptBatchHash st.input
    set fwd := digest32Onto h .nil
    set rev := byteListRevOnto fwd .nil
    have hvfwd : ValidBytes fwd := validBytes_digest32Onto h trivial
    have hlfwd : byteListLen fwd = 32 := by
      simp [fwd, byteListLen_digest32Onto, byteListLen]
    have hvrev : ValidBytes rev := validBytes_revOnto hvfwd trivial
    have hlrev : byteListLen rev = 32 := by
      rw [← byteListToUInt8List_length, byteListRevOnto_toUInt8List, byteListToUInt8List,
          List.append_nil, List.length_reverse, byteListToUInt8List_length, hlfwd]
    have hpop := pop8Bytes_sound rev hvrev (by omega)
    have hdigEq : CertiFri.P3.blake3Transcript .v6Batch s.input = byteListToByteArray fwd := by
      rw [hinpEq]
      exact (v6TranscriptBatchHash_eq_pure hvI hbdI).2.symm
    have hrevList : (CertiFri.P3.blake3Transcript .v6Batch s.input).toList.reverse =
        byteListToUInt8List rev := by
      rw [hdigEq, byteListRevOnto_toUInt8List, byteListToUInt8List, List.append_nil,
          byteArray_toList_eq_data_toList]
      simp only [byteListToByteArray, List.toList_toArray]
    have hpopBytes := hpop.2.2.2
    have hvW := hpop.1
    have hbn (k : Nat) (hk : k < 256) : (UInt8.ofNat k).toNat = k := by
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hk]
    have hs1 : CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s =
        (UInt64.ofNat (u64BytesToNat (pop8Bytes rev).word),
         { input := byteListToByteArray fwd
           output := byteListToUInt8List (pop8Bytes rev).state.output
           exhausted := false }) := by
      unfold CertiFri.P3.ChallengerState.sampleWord CertiFri.P3.ChallengerState.sampleBytes
      have hfirst : CertiFri.P3.ChallengerState.sampleByte (CertiFri.P3.blake3Transcript .v6Batch) s =
          (UInt8.ofNat (pop8Bytes rev).word.b0,
           { input := byteListToByteArray fwd
             output := UInt8.ofNat (pop8Bytes rev).word.b1 :: UInt8.ofNat (pop8Bytes rev).word.b2 ::
               UInt8.ofNat (pop8Bytes rev).word.b3 :: UInt8.ofNat (pop8Bytes rev).word.b4 ::
               UInt8.ofNat (pop8Bytes rev).word.b5 :: UInt8.ofNat (pop8Bytes rev).word.b6 ::
               UInt8.ofNat (pop8Bytes rev).word.b7 :: byteListToUInt8List (pop8Bytes rev).state.output
             exhausted := false }) := by
        unfold CertiFri.P3.ChallengerState.sampleByte
        rw [hsOut]; dsimp only
        rw [hrevList, hpopBytes, hdigEq]
        rfl
      rw [hfirst]
      dsimp only [CertiFri.P3.ChallengerState.sampleBytes, CertiFri.P3.ChallengerState.sampleByte]
      refine Prod.ext ?_ rfl
      change ((((((((0 : UInt64) ||| ((UInt8.ofNat (pop8Bytes rev).word.b0).toUInt64 <<< 0)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b1).toUInt64 <<< 8)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b2).toUInt64 <<< 16)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b3).toUInt64 <<< 24)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b4).toUInt64 <<< 32)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b5).toUInt64 <<< 40)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b6).toUInt64 <<< 48)) |||
        ((UInt8.ofNat (pop8Bytes rev).word.b7).toUInt64 <<< 56) = _
      rw [pack_le_u64]
      rw [hbn _ hvW.1, hbn _ hvW.2.1, hbn _ hvW.2.2.1, hbn _ hvW.2.2.2.1,
          hbn _ hvW.2.2.2.2.1, hbn _ hvW.2.2.2.2.2.1, hbn _ hvW.2.2.2.2.2.2.1,
          hbn _ hvW.2.2.2.2.2.2.2]
      rfl
    unfold chSample8
    rw [hstOut]
    change ValidU64Bytes (pop8Bytes rev).word ∧ _ ∧ _
    rw [hs1]
    exact ⟨hvW, rfl, ⟨hvfwd, hpop.2.1, by rw [hlfwd]; decide, by rw [hpop.2.2.1, hlrev],
      rfl, rfl, rfl⟩⟩
  | cons b rest =>
    have hge8 : 8 ≤ byteListLen (.cons b rest) := by
      rw [hstOut] at hmod8
      have hpos : 1 ≤ byteListLen (.cons b rest) := by simp [byteListLen]
      omega
    rw [hstOut] at hvO houtEq hmod8
    have hpop := pop8Bytes_sound (.cons b rest) hvO hge8
    have hvW := hpop.1
    have hbn (k : Nat) (hk : k < 256) : (UInt8.ofNat k).toNat = k := by
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hk]
    have hsEq : s = { input := byteListToByteArray st.input
                      output := UInt8.ofNat (pop8Bytes (.cons b rest)).word.b0 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b1 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b2 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b3 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b4 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b5 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b6 ::
                        UInt8.ofNat (pop8Bytes (.cons b rest)).word.b7 ::
                        byteListToUInt8List (pop8Bytes (.cons b rest)).state.output
                      exhausted := false } := by
      cases s; simp only [CertiFri.P3.ChallengerState.mk.injEq] at hinpEq houtEq hexh ⊢
      exact ⟨hinpEq, houtEq.trans hpop.2.2.2, hexh⟩
    have hsw : CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s =
        (UInt64.ofNat (u64BytesToNat (pop8Bytes (.cons b rest)).word),
         { input := byteListToByteArray st.input
           output := byteListToUInt8List (pop8Bytes (.cons b rest)).state.output
           exhausted := false }) := by
      rw [hsEq, sampleWord_of_output_cons8]
      refine Prod.ext ?_ rfl
      rw [hbn _ hvW.1, hbn _ hvW.2.1, hbn _ hvW.2.2.1, hbn _ hvW.2.2.2.1,
          hbn _ hvW.2.2.2.2.1, hbn _ hvW.2.2.2.2.2.1, hbn _ hvW.2.2.2.2.2.2.1,
          hbn _ hvW.2.2.2.2.2.2.2]
      rfl
    unfold chSample8
    rw [hstOut]
    dsimp only
    rw [hsw]
    exact ⟨hvW, rfl, ⟨hvI, hpop.2.1, hbdI, by rw [hpop.2.2.1]; omega, rfl, rfl, rfl⟩⟩

theorem chSampleGlFuel_eq_sampleBaseStrict :
    ∀ (k fuel : Nat) {st : CompressWrapPure.ChallengerState} {s : CertiFri.P3.ChallengerState},
      k ≤ fuel →
      ChallengerRel st s →
      (chSampleGlFuel k st).ok = 1 →
      ∃ (a : CertiFri.P3.Goldilocks) (s' : CertiFri.P3.ChallengerState),
        Ix.Cert.MultiStark.sampleBaseStrict fuel s = some (a, s') ∧
        ValidU64Bytes (chSampleGlFuel k st).raw ∧
        (chSampleGlFuel k st).val = u64BytesToNat (chSampleGlFuel k st).raw ∧
        (chSampleGlFuel k st).val < glPrime ∧
        a.val.toNat = (chSampleGlFuel k st).val ∧
        ChallengerRel (chSampleGlFuel k st).state s'
  | 0, _, _, _, _, _, hok => by simp [chSampleGlFuel] at hok
  | k + 1, fuel, st, s, hle, hrel, hok => by
    obtain ⟨fuel', rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    have h8 := chSample8_eq_sampleWord hrel
    obtain ⟨hvW, hwEq, hrel'⟩ := h8
    have hlt64 : u64BytesToNat (chSample8 st).word < 2 ^ 64 := u64BytesToNat_lt _ hvW
    have hp3_toNat :
        (CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1.toNat =
          u64BytesToNat (chSample8 st).word := by
      rw [← hwEq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt64]
    unfold chSampleGlFuel at hok ⊢
    unfold Ix.Cert.MultiStark.sampleBaseStrict
    by_cases hltP : glLtPBytes (chSample8 st).word = 1
    · have hltNat : u64BytesToNat (chSample8 st).word < glPrime :=
        (glLtPBytes_eq_one_iff hvW).mp hltP
      have hltU64 : (CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1 <
          (18446744069414584321 : UInt64) := by
        rw [UInt64.lt_iff_toNat_lt, hp3_toNat]
        exact hltNat
      have hofCan :
          CertiFri.P3.Goldilocks.ofCanonical?
            (CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1 =
          some ⟨(CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1,
            hltU64⟩ := by
        unfold CertiFri.P3.Goldilocks.ofCanonical?
        rw [dite_eq_left hltU64]
      simp only [hltP, beq_self_eq_true, ↓reduceIte]
      rw [hofCan]
      obtain ⟨hgv, hglt⟩ := glValBytes_of_ltP hvW hltP
      exact ⟨_, _, rfl, hvW, hgv, hglt, by rw [hp3_toNat, hgv], hrel'⟩
    · have hbf : (glLtPBytes (chSample8 st).word == 1) = false := beq_false_of_ne hltP
      simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      have hgeP : ¬ u64BytesToNat (chSample8 st).word < glPrime :=
        fun h => hltP ((glLtPBytes_eq_one_iff hvW).mpr h)
      have hgeU64 : ¬ (CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1 <
          (18446744069414584321 : UInt64) := by
        rw [UInt64.lt_iff_toNat_lt, hp3_toNat]
        exact hgeP
      have hofCan :
          CertiFri.P3.Goldilocks.ofCanonical?
            (CertiFri.P3.ChallengerState.sampleWord (CertiFri.P3.blake3Transcript .v6Batch) s).1 =
          none := by
        unfold CertiFri.P3.Goldilocks.ofCanonical?
        rw [dite_eq_right hgeU64]
      rw [hofCan]
      exact chSampleGlFuel_eq_sampleBaseStrict k fuel' (by omega) hrel' hok

/-- **Protocol `v6` Base-Field Rejection Sampling Equivalence (`CompressWrapPure.chSampleGl`)**:
acceptance implies `Ix.Cert.MultiStark.sampleBaseStrict` succeeds with identical Goldilocks
element and coupled challenger state. -/
theorem chSampleGl_eq_sampleBaseStrict {st : CompressWrapPure.ChallengerState}
    {s : CertiFri.P3.ChallengerState} (hrel : ChallengerRel st s)
    (hok : (chSampleGl st).ok = 1) :
    ∃ (a : CertiFri.P3.Goldilocks) (s' : CertiFri.P3.ChallengerState),
      Ix.Cert.MultiStark.sampleBaseStrict CertiFri.P3.ChallengerState.rejectionFuel s = some (a, s') ∧
      ValidU64Bytes (chSampleGl st).raw ∧
      (chSampleGl st).val = u64BytesToNat (chSampleGl st).raw ∧
      (chSampleGl st).val < glPrime ∧
      a.val.toNat = (chSampleGl st).val ∧
      ChallengerRel (chSampleGl st).state s' :=
  chSampleGlFuel_eq_sampleBaseStrict 64 CertiFri.P3.ChallengerState.rejectionFuel
    (by decide) hrel hok

/-- **Protocol `v6` Cubic-Extension Sampling Equivalence (`CompressWrapPure.chSampleExt`)**:
acceptance implies `Ix.Cert.MultiStark.sampleExtStrict` succeeds with identical cubic extension
element `(c0, c1, c2)` and coupled challenger state. -/
theorem chSampleExt_eq_sampleExtStrict {st : CompressWrapPure.ChallengerState}
    {s : CertiFri.P3.ChallengerState} (hrel : ChallengerRel st s)
    (hok : (chSampleExt st).ok = 1) :
    ∃ (e : CertiFri.P3.GoldilocksExt3) (s' : CertiFri.P3.ChallengerState),
      Ix.Cert.MultiStark.sampleExtStrict s = some (e, s') ∧
      e.c0.val.toNat = (chSampleExt st).val.c0 ∧
      e.c1.val.toNat = (chSampleExt st).val.c1 ∧
      e.c2.val.toNat = (chSampleExt st).val.c2 ∧
      (chSampleExt st).val.c0 < glPrime ∧
      (chSampleExt st).val.c1 < glPrime ∧
      (chSampleExt st).val.c2 < glPrime ∧
      ChallengerRel (chSampleExt st).state s' := by
  have hgl01 : ∀ st0, (chSampleGl st0).ok = 0 ∨ (chSampleGl st0).ok = 1 := by
    intro st0
    have aux : ∀ k st1, (chSampleGlFuel k st1).ok = 0 ∨ (chSampleGlFuel k st1).ok = 1 := by
      intro k; induction k with
      | zero => intro _; exact Or.inl rfl
      | succ k ih =>
        intro st1; unfold chSampleGlFuel; dsimp only; split
        · exact Or.inr rfl
        · exact ih _
    exact aux 64 st0
  unfold chSampleExt at hok ⊢
  generalize hs0 : chSampleGl st = s0 at hok ⊢
  rcases hgl01 st with h0 | h0
  · rw [hs0] at h0; simp [h0] at hok
  · rw [hs0] at h0
    have h0ne : (s0.ok == 0) = false := by rw [h0]; rfl
    simp only [h0ne, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    generalize hs1 : chSampleGl s0.state = s1 at hok ⊢
    rcases hgl01 s0.state with h1 | h1
    · rw [hs1] at h1; simp [h1] at hok
    · rw [hs1] at h1
      have h1ne : (s1.ok == 0) = false := by rw [h1]; rfl
      simp only [h1ne, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      generalize hs2 : chSampleGl s1.state = s2 at hok ⊢
      rcases hgl01 s1.state with h2 | h2
      · rw [hs2] at h2; simp [h2] at hok
      · rw [hs2] at h2
        have h2ne : (s2.ok == 0) = false := by rw [h2]; rfl
        simp only [h2ne, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        obtain ⟨a0, st1, he0, _, _, hlt0, hv0, hrel1⟩ :=
          chSampleGl_eq_sampleBaseStrict hrel (hs0.symm ▸ h0)
        rw [hs0] at hv0 hlt0 hrel1
        obtain ⟨a1, st2, he1, _, _, hlt1, hv1, hrel2⟩ :=
          chSampleGl_eq_sampleBaseStrict hrel1 (hs1.symm ▸ h1)
        rw [hs1] at hv1 hlt1 hrel2
        obtain ⟨a2, st3, he2, _, _, hlt2, hv2, hrel3⟩ :=
          chSampleGl_eq_sampleBaseStrict hrel2 (hs2.symm ▸ h2)
        rw [hs2] at hv2 hlt2 hrel3
        refine ⟨⟨a0, a1, a2⟩, st3, ?_, hv0, hv1, hv2, hlt0, hlt1, hlt2, hrel3⟩
        unfold Ix.Cert.MultiStark.sampleExtStrict
        simp only [he0, he1, he2, Bind.bind, Option.bind, Pure.pure]

private theorem bitsToNum_byteBitsOnto {b : Nat} (hb : b < 256) (tail : BitList) :
    bitsToNum (byteBitsOnto b tail) = b + 256 * bitsToNum tail := by
  have hd := byte_bit_decomp hb
  unfold byteBitsOnto
  simp only [bitsToNum, Nat.div_div_eq_div_mul]
  generalize b % 2 = x0 at hd ⊢
  generalize (b / 2) % 2 = x1 at hd ⊢
  generalize (b / 4) % 2 = x2 at hd ⊢
  generalize (b / 8) % 2 = x3 at hd ⊢
  generalize (b / 16) % 2 = x4 at hd ⊢
  generalize (b / 32) % 2 = x5 at hd ⊢
  generalize (b / 64) % 2 = x6 at hd ⊢
  generalize (b / 128) % 2 = x7 at hd ⊢
  omega

private theorem validBits_byteBitsOnto (b : Nat) {tail : BitList} (ht : ValidBits tail) :
    ValidBits (byteBitsOnto b tail) := by
  unfold byteBitsOnto
  simp only [ValidBits]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ht⟩

private theorem bitListLen_byteBitsOnto (b : Nat) (tail : BitList) :
    bitListLen (byteBitsOnto b tail) = 8 + bitListLen tail := by
  unfold byteBitsOnto
  simp only [bitListLen]; omega

private theorem takeBits_spec :
    ∀ (n : Nat) (bits : BitList),
      ValidBits bits →
      n ≤ bitListLen bits →
      bitListLen (takeBits bits n) = n ∧
      ValidBits (takeBits bits n) ∧
      bitsToNum (takeBits bits n) = bitsToNum bits % 2 ^ n
  | 0, bits, _, _ => ⟨rfl, trivial, by simp [takeBits, bitsToNum, Nat.mod_one]⟩
  | n + 1, .nil, _, hle => by simp [bitListLen] at hle
  | n + 1, .cons b rest, ⟨hb, hrest⟩, hle => by
    have ih := takeBits_spec n rest hrest (by simp [bitListLen] at hle; omega)
    simp only [takeBits, bitListLen, ValidBits, bitsToNum]
    refine ⟨by rw [ih.1]; omega, ⟨hb, ih.2.1⟩, ?_⟩
    rw [ih.2.2, Nat.pow_succ]
    have h2 : b + bitsToNum rest % 2 ^ n + bitsToNum rest % 2 ^ n =
        b + 2 * (bitsToNum rest % 2 ^ n) := by omega
    have h3 : b + bitsToNum rest + bitsToNum rest = b + 2 * bitsToNum rest := by omega
    rw [h2, h3]
    have hdm : 2 ^ n * (bitsToNum rest / 2 ^ n) + bitsToNum rest % 2 ^ n = bitsToNum rest :=
      Nat.div_add_mod (bitsToNum rest) (2 ^ n)
    have hlt : b + 2 * (bitsToNum rest % 2 ^ n) < 2 ^ n * 2 := by
      have := Nat.mod_lt (bitsToNum rest) (Nat.two_pow_pos n)
      rcases hb with rfl | rfl <;> omega
    have hmul : b + 2 * bitsToNum rest =
        (b + 2 * (bitsToNum rest % 2 ^ n)) + (2 ^ n * 2) * (bitsToNum rest / 2 ^ n) := by
      have : 2 * bitsToNum rest =
          2 * (bitsToNum rest % 2 ^ n) + (2 ^ n * 2) * (bitsToNum rest / 2 ^ n) := by
        calc 2 * bitsToNum rest
            = 2 * (2 ^ n * (bitsToNum rest / 2 ^ n) + bitsToNum rest % 2 ^ n) := by rw [hdm]
          _ = 2 * (bitsToNum rest % 2 ^ n) + (2 ^ n * 2) * (bitsToNum rest / 2 ^ n) := by ring
      omega
    rw [hmul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **Protocol `v6` Bit-Sampling Equivalence (`CompressWrapPure.chSampleBits`)**:
for any `n ≤ 32`, `chSampleBits st n` returns `n` valid LSB-first bits whose numerical value
equals `(CertiFri.P3.ChallengerState.sampleBits (CertiFri.P3.blake3Transcript .v6Batch) s n).1`
and preserves `ChallengerRel`. -/
theorem chSampleBits_eq_sampleBits {st : CompressWrapPure.ChallengerState}
    {s : CertiFri.P3.ChallengerState} (hrel : ChallengerRel st s) {n : Nat} (hn : n ≤ 32) :
    let out := chSampleBits st n
    let p3 := CertiFri.P3.ChallengerState.sampleBits (CertiFri.P3.blake3Transcript .v6Batch) s n
    bitListLen out.bits = n ∧
    ValidBits out.bits ∧
    bitsToNum out.bits = p3.1 ∧
    ChallengerRel out.state p3.2 := by
  obtain ⟨hvW, hwEq, hrel'⟩ := chSample8_eq_sampleWord hrel
  set w := (chSample8 st).word
  set b32 := byteBitsOnto w.b0 (byteBitsOnto w.b1 (byteBitsOnto w.b2 (byteBitsOnto w.b3 .nil)))
  have hvb32 : ValidBits b32 :=
    validBits_byteBitsOnto _ (validBits_byteBitsOnto _ (validBits_byteBitsOnto _
      (validBits_byteBitsOnto _ trivial)))
  have hlb32 : bitListLen b32 = 32 := by
    simp only [b32, bitListLen_byteBitsOnto, bitListLen]
  have hnum32 : bitsToNum b32 = w.b0 + 256 * w.b1 + 65536 * w.b2 + 16777216 * w.b3 := by
    simp only [b32, bitsToNum_byteBitsOnto hvW.1, bitsToNum_byteBitsOnto hvW.2.1,
      bitsToNum_byteBitsOnto hvW.2.2.1, bitsToNum_byteBitsOnto hvW.2.2.2.1, bitsToNum]
    omega
  obtain ⟨hlen, hvb, hnum⟩ := takeBits_spec n b32 hvb32 (by omega)
  unfold chSampleBits CertiFri.P3.ChallengerState.sampleBits
  dsimp only
  refine ⟨hlen, hvb, ?_, hrel'⟩
  rw [hnum, hnum32, ← hwEq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (u64BytesToNat_lt w hvW)]
  unfold u64BytesToNat
  have hdvd : 2 ^ n ∣ 4294967296 := by
    rw [show (4294967296 : Nat) = 2 ^ 32 by decide]
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-! ## Section 4: Security Floor, Zero-PoW Canonicalization, MMCS, FRI, AIR, LogUp & MEMSEG Soundness -/

/-! ### Section 4A: In-Circuit Security Floor & Bridge to `Aiur.Parameters` -/

/-- Exact integer unique-decoding millibits per FRI query enforced by `checkSecurityFloor`. -/
def udMillibitsOf (lb : Nat) : Nat :=
  if lb == 1 then 415
  else if lb == 2 then 678
  else if lb == 3 then 830
  else 912

/-- Complete cryptographic security-floor postcondition enforced by `checkSecurityFloor`:
all 7 numerical inequalities plus the derived per-`logBlowup` minimum query counts (`211/101/66/53`). -/
structure SecurityFloorHolds (p : SysParams) : Prop where
  logBlowup_ge : 1 ≤ p.logBlowup
  logBlowup_le : p.logBlowup ≤ 4
  numQueries_pos : 1 ≤ p.numQueries
  commitPow_le : p.commitPowBits ≤ 32
  queryPow_le : p.queryPowBits ≤ 32
  conjectured_ge_220 : p.logBlowup * p.numQueries + p.queryPowBits ≥ 220
  ud_ge_80000 : udMillibitsOf p.logBlowup * p.numQueries + 1000 * p.queryPowBits ≥ 80000
  johnson_ge_128000 : (500 * p.logBlowup - 45) * p.numQueries + 1000 * p.queryPowBits ≥ 128000
  minQueries_lb1 : p.logBlowup = 1 → 211 ≤ p.numQueries
  minQueries_lb2 : p.logBlowup = 2 → 101 ≤ p.numQueries
  minQueries_lb3 : p.logBlowup = 3 → 66 ≤ p.numQueries
  minQueries_lb4 : p.logBlowup = 4 → 53 ≤ p.numQueries

/-- **Security Floor Soundness (`CompressWrapPure.checkSecurityFloor`)**:
returning `1` guarantees all cryptographic bounds AND all per-`logBlowup` minimum query floors
(`211 / 101 / 66 / 53` queries for `logBlowup ∈ {1, 2, 3, 4}`). -/
theorem checkSecurityFloor_sound {p : SysParams} (hok : checkSecurityFloor p = 1) :
    SecurityFloorHolds p := by
  unfold checkSecurityFloor at hok
  by_cases h1 : (decide (p.logBlowup < 1) || decide (p.logBlowup > 4)) = true
  · rw [ite_eq_left h1] at hok; cases hok
  · rw [ite_eq_right h1] at hok
    have hlb : 1 ≤ p.logBlowup ∧ p.logBlowup ≤ 4 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1; omega
    by_cases h2 : p.numQueries < 1
    · rw [ite_eq_left h2] at hok; cases hok
    · rw [ite_eq_right h2] at hok
      by_cases h3 : (decide (p.commitPowBits > 32) || decide (p.queryPowBits > 32)) = true
      · rw [ite_eq_left h3] at hok; cases hok
      · rw [ite_eq_right h3] at hok
        have hpow : p.commitPowBits ≤ 32 ∧ p.queryPowBits ≤ 32 := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h3; omega
        by_cases h4 : p.logBlowup * p.numQueries + p.queryPowBits < 220
        · rw [ite_eq_left h4] at hok; cases hok
        · rw [ite_eq_right h4] at hok
          change (if udMillibitsOf p.logBlowup * p.numQueries + 1000 * p.queryPowBits < 80000 then 0 else _) = 1 at hok
          by_cases h5 : udMillibitsOf p.logBlowup * p.numQueries + 1000 * p.queryPowBits < 80000
          · rw [ite_eq_left h5] at hok; cases hok
          · rw [ite_eq_right h5] at hok
            dsimp only at hok
            by_cases h6 : (500 * p.logBlowup - 45) * p.numQueries + 1000 * p.queryPowBits < 128000
            · rw [ite_eq_left h6] at hok; cases hok
            · have hud : udMillibitsOf p.logBlowup * p.numQueries + 1000 * p.queryPowBits ≥ 80000 := by omega
              have hj : (500 * p.logBlowup - 45) * p.numQueries + 1000 * p.queryPowBits ≥ 128000 := by omega
              refine ⟨hlb.1, hlb.2, by omega, hpow.1, hpow.2, by omega, hud, hj, ?_, ?_, ?_, ?_⟩
              · intro hlb1; rw [hlb1] at hj; omega
              · intro hlb2; rw [hlb2] at hj; omega
              · intro hlb3; rw [hlb3] at hj; omega
              · intro hlb4; rw [hlb4] at hud; unfold udMillibitsOf at hud; simp only [show ((4 : Nat) == 1) = false from rfl,
                  show ((4 : Nat) == 2) = false from rfl, show ((4 : Nat) == 3) = false from rfl,
                  Bool.false_eq_true, ↓reduceIte] at hud; omega

/-- **Direct Bridge to `Ix.Aiur.Parameters`**:
under canonical fixed profile parameters (`capHeight = 0`, `logFinalPolyLen = 0`,
`maxLogArity = 1`), `checkSecurityFloor p = 1` implies BOTH `Aiur.meetsSecurityFloor = true`
AND `Aiur.meetsSecurityFloor128Johnson extensionDegreeV6 protocolVersionV6 = true`. -/
theorem checkSecurityFloor_implies_meetsSecurityFloor {p : SysParams}
    (hok : checkSecurityFloor p = 1)
    (hcap : p.capHeight = 0) (hfin : p.logFinalPolyLen = 0) (har : p.maxLogArity = 1) :
    let comm : Aiur.CommitmentParameters := ⟨p.logBlowup, p.capHeight⟩
    let fri : Aiur.FriParameters :=
      ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩
    Aiur.meetsSecurityFloor comm fri = true ∧
    Aiur.meetsSecurityFloor128Johnson Aiur.extensionDegreeV6 Aiur.protocolVersionV6 comm fri = true := by
  have hs := checkSecurityFloor_sound hok
  have hlbCases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by
    have := hs.logBlowup_ge; have := hs.logBlowup_le; omega
  have hmsf :
      Aiur.meetsSecurityFloor ⟨p.logBlowup, p.capHeight⟩
        ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ = true := by
    unfold Aiur.meetsSecurityFloor Aiur.conjecturedSecurityBits Aiur.provableUdMillibits
      Aiur.johnsonMillibits Aiur.maxProofOfWorkBits Aiur.minConjecturedSecurityBits
      Aiur.minProvableUdBits Aiur.minJohnsonBits Aiur.johnsonSlackMillibitsPerQuery
    rcases hlbCases with hlb | hlb | hlb | hlb <;>
    · have hmq : (match Aiur.minQueriesForLogBlowup p.logBlowup with
          | some minQ => decide (minQ ≤ p.numQueries) | none => false) = true := by
        rw [hlb]; simp [Aiur.minQueriesForLogBlowup]
        first
        | exact hs.minQueries_lb1 hlb
        | exact hs.minQueries_lb2 hlb
        | exact hs.minQueries_lb3 hlb
        | exact hs.minQueries_lb4 hlb
      have hud : (match (Aiur.udMillibitsPerQuery p.logBlowup).map
          (fun rate => p.numQueries * rate + p.queryPowBits * 1000) with
          | some udMb => decide (80 * 1000 ≤ udMb) | none => false) = true := by
        have h := hs.ud_ge_80000
        rw [hlb] at h ⊢
        unfold udMillibitsOf at h
        simp [Aiur.udMillibitsPerQuery] at h ⊢
        omega
      have hj : 128 * 1000 ≤ (p.logBlowup * 500 - 45) * p.numQueries + p.queryPowBits * 1000 := by
        have h := hs.johnson_ge_128000
        rw [hlb] at h ⊢; omega
      simp only [hcap, hfin, har, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨hs.logBlowup_ge, hs.logBlowup_le⟩, hs.numQueries_pos⟩,
        hs.commitPow_le⟩, hs.queryPow_le⟩, hmq⟩, hs.conjectured_ge_220⟩, hud⟩, hj⟩
  refine ⟨hmsf, ?_⟩
  unfold Aiur.meetsSecurityFloor128Johnson Aiur.minProvableSecurityBits128 Aiur.johnsonMillibits
    Aiur.johnsonSlackMillibitsPerQuery
  simp only [hmsf, le_refl, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rcases hlbCases with hlb | hlb | hlb | hlb <;>
      simp [hlb, Aiur.minQueriesForLogBlowup128Johnson]
    · exact hs.minQueries_lb1 hlb
    · exact hs.minQueries_lb2 hlb
    · exact hs.minQueries_lb3 hlb
    · exact hs.minQueries_lb4 hlb
  · have h := hs.johnson_ge_128000
    rcases hlbCases with hlb | hlb | hlb | hlb <;> (rw [hlb] at h ⊢; omega)

/-! ### Section 4B: Zero-PoW Witness Canonicalization & PoW Soundness -/

/-- **Zero-PoW Witness Canonicalization (`CompressWrapPure.pcsCheckWitness`)**:
whenever `bits = 0`, `pcsCheckWitness` accepts IF AND ONLY IF `witness = u64Zero`
(eliminating unused witness malleability). -/
theorem pcsCheckWitness_zero_bits_canonical (input : ByteList) (witness : U64Bytes) :
    (pcsCheckWitness input witness 0).ok = 1 ↔ witness = u64Zero := by
  unfold pcsCheckWitness
  by_cases hlt : glLtPBytes witness = 0
  · simp only [hlt, beq_self_eq_true, ↓reduceIte]
    constructor
    · intro h; cases h
    · intro heq; subst heq; simp [glLtPBytes, u64Zero] at hlt
  · have hne : (glLtPBytes witness == 0) = false := beq_false_of_ne hlt
    simp only [hne, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
    by_cases hz : u64BytesEq witness u64Zero = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro heq; subst heq; simp [u64BytesEq, u64Zero] at hz
    · have h1 : u64BytesEq witness u64Zero = 1 :=
        (u64BytesEq_zero_or_one witness u64Zero).resolve_left hz
      have hne0 : (u64BytesEq witness u64Zero == 0) = false := beq_false_of_ne hz
      simp only [hne0, Bool.false_eq_true, ↓reduceIte, true_iff]
      exact (u64BytesEq_eq_one_iff witness u64Zero).mp h1

/-- Complete soundness of `pcsCheckWitness` for arbitrary `bits`:
enforces canonical `< p_GL` witness, exact `witness = u64Zero` when `bits = 0`, and
`bits` zero LSBs from the Protocol `v6` keyed BLAKE3 challenger when `bits > 0`. -/
theorem pcsCheckWitness_sound {input : ByteList} {witness : U64Bytes} {bits : Nat}
    (hok : (pcsCheckWitness input witness bits).ok = 1) :
    glLtPBytes witness = 1 ∧
    (bits = 0 → witness = u64Zero ∧ (pcsCheckWitness input witness 0).state = { input := input, output := .nil }) ∧
    (bits ≠ 0 →
      let s := chSampleBits { input := snocU64 input witness, output := .nil } bits
      bitsToNum s.bits = 0 ∧ (pcsCheckWitness input witness bits).state = s.state) := by
  have hlt1 : glLtPBytes witness = 1 := by
    unfold pcsCheckWitness at hok
    by_cases h0 : glLtPBytes witness = 0
    · simp [h0] at hok
    · exact (glLtPBytes_zero_or_one witness).resolve_left h0
  refine ⟨hlt1, ?_, ?_⟩
  · intro hb0; subst hb0
    have hw := (pcsCheckWitness_zero_bits_canonical input witness).mp hok
    refine ⟨hw, ?_⟩
    subst hw
    unfold pcsCheckWitness
    simp [glLtPBytes, u64BytesEq, u64Zero]
  · intro hbne
    unfold pcsCheckWitness at hok ⊢
    have hlt0 : (glLtPBytes witness == 0) = false := by rw [hlt1]; rfl
    have hb0f : (bits == 0) = false := beq_false_of_ne hbne
    simp only [hlt0, hb0f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    refine ⟨?_, trivial⟩
    by_cases hbz : bitsToNum (chSampleBits { input := snocU64 input witness, output := .nil } bits).bits = 0
    · exact hbz
    · have hbf : (bitsToNum (chSampleBits { input := snocU64 input witness, output := .nil } bits).bits == 0) = false :=
        beq_false_of_ne hbz
      simp [hbf] at hok

/-- Every witness in `U64List` satisfies `glLtPBytes w = 1` and (when `bits = 0`) equals `u64Zero`. -/
def PowWitnessesValid (bits : Nat) : U64List → Prop
  | .nil => True
  | .cons w rest => glLtPBytes w = 1 ∧ (bits = 0 → w = u64Zero) ∧ PowWitnessesValid bits rest

theorem pcsBetas_sound :
    ∀ (input : ByteList) (comms : MerkleCapList) (witnesses : U64List) (bits : Nat),
      (pcsBetas input comms witnesses bits).ok = 1 →
      u64ListLen witnesses = merkleCapListLen comms ∧
      extGlListLen (pcsBetas input comms witnesses bits).vals = merkleCapListLen comms ∧
      PowWitnessesValid bits witnesses
  | input, .nil, witnesses, bits, hok => by
    cases witnesses with
    | nil => exact ⟨rfl, rfl, trivial⟩
    | cons _ _ => simp [pcsBetas] at hok
  | input, .cons c crest, witnesses, bits, hok => by
    cases witnesses with
    | nil => simp [pcsBetas] at hok
    | cons w wrest =>
      unfold pcsBetas at hok ⊢
      dsimp only at hok ⊢
      generalize hpw : pcsCheckWitness (snocCap input c) w bits = pw at hok ⊢
      by_cases hpw0 : pw.ok = 0
      · simp [hpw0] at hok
      · have hpw01 : (pcsCheckWitness (snocCap input c) w bits).ok = 0 ∨
            (pcsCheckWitness (snocCap input c) w bits).ok = 1 := by
          unfold pcsCheckWitness; split
          · exact Or.inl rfl
          · split
            · split
              · exact Or.inl rfl
              · exact Or.inr rfl
            · dsimp only; split <;> [exact Or.inr rfl; exact Or.inl rfl]
        have hpw1 : pw.ok = 1 := (hpw ▸ hpw01).resolve_left hpw0
        have hpwf : (pw.ok == 0) = false := beq_false_of_ne hpw0
        simp only [hpwf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        generalize hsb : chSampleExt pw.state = sb at hok ⊢
        by_cases hsb0 : sb.ok = 0
        · simp [hsb0] at hok
        · have hsbf : (sb.ok == 0) = false := beq_false_of_ne hsb0
          simp only [hsbf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          have ih := pcsBetas_sound sb.state.input crest wrest bits hok
          have hpws := pcsCheckWitness_sound (hpw.symm ▸ hpw1)
          refine ⟨by simp [u64ListLen, merkleCapListLen, ih.1],
            by simp [extGlListLen, merkleCapListLen, ih.2.1],
            ⟨hpws.1, fun hb0 => (hpws.2.1 hb0).1, ih.2.2⟩⟩

/-! ### Section 4C: Batched Pruned MMCS Verification Soundness (`mmcsVerifyMulti_sound`) -/

/-- Membership in a `FrontierList`. -/
def FrontierMem (x : FrontierNode) : FrontierList → Prop
  | .nil => False
  | .cons h t => x = h ∨ FrontierMem x t

/-- Fixed-length valid LSB-first bit representation invariant on a `FrontierNode`. -/
def FrontierNodeWF (levels : Nat) (n : FrontierNode) : Prop :=
  ValidBits n.bits ∧ bitListLen n.bits = levels ∧ n.idx = bitsToNum n.bits

/-- Every node in a `FrontierList` satisfies `FrontierNodeWF levels`. -/
def FrontierAllWF (levels : Nat) : FrontierList → Prop
  | .nil => True
  | .cons h t => FrontierNodeWF levels h ∧ FrontierAllWF levels t

/-- Strict ascending sort order by `.idx` on a `FrontierList`. -/
def FrontierStrictlySorted : FrontierList → Prop
  | .nil => True
  | .cons _ .nil => True
  | .cons a (.cons b rest) => a.idx < b.idx ∧ FrontierStrictlySorted (.cons b rest)

private theorem bitsToNum_inj :
    ∀ {b1 b2 : BitList},
      ValidBits b1 → ValidBits b2 → bitListLen b1 = bitListLen b2 →
      bitsToNum b1 = bitsToNum b2 → b1 = b2
  | .nil, .nil, _, _, _, _ => rfl
  | .cons x xs, .nil, _, _, hlen, _ => by simp [bitListLen] at hlen
  | .nil, .cons y ys, _, _, hlen, _ => by simp [bitListLen] at hlen; omega
  | .cons x xs, .cons y ys, ⟨hx, hxs⟩, ⟨hy, hys⟩, hlen, hnum => by
    simp only [bitListLen] at hlen
    simp only [bitsToNum] at hnum
    have hxy : x = y := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
    subst hxy
    have hrest : bitsToNum xs = bitsToNum ys := by omega
    rw [bitsToNum_inj hxs hys (by omega) hrest]

private theorem frontierStrictlySorted_tail {a : FrontierNode} {rest : FrontierList}
    (hs : FrontierStrictlySorted (.cons a rest)) : FrontierStrictlySorted rest := by
  cases rest with
  | nil => trivial
  | cons b r => exact hs.2

private theorem frontierStrictlySorted_lt_of_mem {a x : FrontierNode} {rest : FrontierList}
    (hs : FrontierStrictlySorted (.cons a rest)) (hm : FrontierMem x rest) : a.idx < x.idx := by
  induction rest generalizing a with
  | nil => cases hm
  | cons b r ih =>
    rcases hm with rfl | hmr
    · exact hs.1
    · exact Nat.lt_trans hs.1 (ih hs.2 hmr)

private theorem frontierStrictlySorted_cons_of_lt {a : FrontierNode} {rest : FrontierList}
    (hlt : ∀ x, FrontierMem x rest → a.idx < x.idx)
    (hs : FrontierStrictlySorted rest) : FrontierStrictlySorted (.cons a rest) := by
  cases rest with
  | nil => trivial
  | cons b r => exact ⟨hlt b (Or.inl rfl), hs⟩

private theorem frontierMergeFuel_sound (levels : Nat) :
    ∀ (fuel : Nat) (xs ys : FrontierList),
      FrontierAllWF levels xs → FrontierAllWF levels ys →
      FrontierStrictlySorted xs → FrontierStrictlySorted ys →
      (frontierMergeFuel fuel xs ys).ok = 1 →
      let out := (frontierMergeFuel fuel xs ys).nodes
      FrontierAllWF levels out ∧
      FrontierStrictlySorted out ∧
      (∀ z, FrontierMem z out ↔ FrontierMem z xs ∨ FrontierMem z ys)
  | 0, _, _, _, _, _, _, hok => by simp [frontierMergeFuel] at hok
  | fuel + 1, .nil, ys, _, hwy, _, hsy, _ =>
    ⟨hwy, hsy, fun z => by simp [frontierMergeFuel, FrontierMem]⟩
  | fuel + 1, .cons x xr, .nil, hwx, _, hsx, _, _ =>
    ⟨hwx, hsx, fun z => by simp [frontierMergeFuel, FrontierMem]⟩
  | fuel + 1, .cons x xr, .cons y yr, ⟨hwx1, hwxr⟩, ⟨hwy1, hwyr⟩, hsx, hsy, hok => by
    unfold frontierMergeFuel at hok ⊢
    dsimp only at hok ⊢
    by_cases hlt : x.idx < y.idx
    · rw [ite_eq_left hlt] at hok ⊢
      have ih := frontierMergeFuel_sound levels fuel xr (.cons y yr)
        hwxr ⟨hwy1, hwyr⟩ (frontierStrictlySorted_tail hsx) hsy hok
      refine ⟨⟨hwx1, ih.1⟩, ?_, ?_⟩
      · refine frontierStrictlySorted_cons_of_lt ?_ ih.2.1
        intro z hz
        rcases (ih.2.2 z).mp hz with hzx | hzy
        · exact frontierStrictlySorted_lt_of_mem hsx hzx
        · rcases hzy with rfl | hzyr
          · exact hlt
          · exact Nat.lt_trans hlt (frontierStrictlySorted_lt_of_mem hsy hzyr)
      · intro z
        simp only [FrontierMem, ih.2.2]
        tauto
    · rw [ite_eq_right hlt] at hok ⊢
      by_cases heq : x.idx = y.idx
      · rw [ite_eq_left (beq_iff_eq.mpr heq)] at hok ⊢
        dsimp only at hok ⊢
        by_cases hde : digestBytesEq x.digest y.digest = 1 ∧ assertSameClaims x.rows y.rows = 1
        · have hrok : (frontierMergeFuel fuel xr yr).ok = 1 := by
            by_cases hr : (frontierMergeFuel fuel xr yr).ok = 1
            · exact hr
            · have hrf : ((frontierMergeFuel fuel xr yr).ok == 1) = false := beq_false_of_ne hr
              simp [hrf] at hok
          have hxy : x = y := by
            have hdig := (digestBytesEq_eq_one_iff x.digest y.digest).mp hde.1
            have hrows := (assertSameClaims_eq_one_iff x.rows y.rows).mp hde.2
            have hbits : x.bits = y.bits := bitsToNum_inj hwx1.1 hwy1.1
              (hwx1.2.1.trans hwy1.2.1.symm) (by rw [← hwx1.2.2, ← hwy1.2.2, heq])
            cases x; cases y; simp only at heq hbits hrows hdig
            subst heq; subst hbits; subst hrows; subst hdig; rfl
          have ih := frontierMergeFuel_sound levels fuel xr yr
            hwxr hwyr (frontierStrictlySorted_tail hsx) (frontierStrictlySorted_tail hsy) hrok
          refine ⟨⟨hwx1, ih.1⟩, ?_, ?_⟩
          · refine frontierStrictlySorted_cons_of_lt ?_ ih.2.1
            intro z hz
            rcases (ih.2.2 z).mp hz with hzx | hzy
            · exact frontierStrictlySorted_lt_of_mem hsx hzx
            · rw [heq]; exact frontierStrictlySorted_lt_of_mem hsy hzy
          · intro z
            simp only [FrontierMem, ih.2.2, hxy]
            tauto
        · have hfb : (digestBytesEq x.digest y.digest == 1 && assertSameClaims x.rows y.rows == 1) = false := by
            by_cases h1 : digestBytesEq x.digest y.digest = 1
            · have h2 : assertSameClaims x.rows y.rows ≠ 1 := fun h => hde ⟨h1, h⟩
              simp [h1, beq_false_of_ne h2]
            · simp [beq_false_of_ne h1]
          simp only [hfb, Bool.false_eq_true, ↓reduceIte, show ((0 : Nat) == 1) = false from rfl,
            Bool.false_and] at hok
          cases hok
      · rw [ite_eq_right (by rw [beq_iff_eq]; exact heq)] at hok ⊢
        have hgt : y.idx < x.idx := by omega
        have ih := frontierMergeFuel_sound levels fuel (.cons x xr) yr
          ⟨hwx1, hwxr⟩ hwyr hsx (frontierStrictlySorted_tail hsy) hok
        refine ⟨⟨hwy1, ih.1⟩, ?_, ?_⟩
        · refine frontierStrictlySorted_cons_of_lt ?_ ih.2.1
          intro z hz
          rcases (ih.2.2 z).mp hz with hzx | hzy
          · rcases hzx with rfl | hzxr
            · exact hgt
            · exact Nat.lt_trans hgt (frontierStrictlySorted_lt_of_mem hsx hzxr)
          · exact frontierStrictlySorted_lt_of_mem hsy hzy
        · intro z
          simp only [FrontierMem, ih.2.2]
          tauto

private theorem frontierSplit_props (levels : Nat) :
    ∀ xs : FrontierList,
      FrontierAllWF levels xs →
      let p := frontierSplit xs
      FrontierAllWF levels p.left ∧
      FrontierAllWF levels p.right ∧
      frontierLen p.left + frontierLen p.right = frontierLen xs ∧
      (2 ≤ frontierLen xs → frontierLen p.left < frontierLen xs ∧ frontierLen p.right < frontierLen xs) ∧
      (∀ z, FrontierMem z xs ↔ FrontierMem z p.left ∨ FrontierMem z p.right)
  | .nil, _ => ⟨trivial, trivial, rfl, fun h => by simp [frontierLen] at h, fun _ => by simp [frontierSplit, FrontierMem]⟩
  | .cons x .nil, ⟨hwx, _⟩ =>
    ⟨⟨hwx, trivial⟩, trivial, rfl, fun h => by simp [frontierLen] at h,
     fun _ => by simp [frontierSplit, FrontierMem]⟩
  | .cons x (.cons y rest), ⟨hwx, hwy, hwr⟩ => by
    have ih := frontierSplit_props levels rest hwr
    unfold frontierSplit
    dsimp only
    refine ⟨⟨hwx, ih.1⟩, ⟨hwy, ih.2.1⟩,
      by simp only [frontierLen]; omega,
      fun _ => by simp only [frontierLen]; omega,
      fun z => by simp only [FrontierMem, ih.2.2.2.2]; tauto⟩

private theorem frontierSortFuel_sound (levels : Nat) :
    ∀ (fuel : Nat) (xs : FrontierList),
      FrontierAllWF levels xs →
      frontierLen xs ≤ fuel →
      (frontierSortFuel fuel xs).ok = 1 →
      let out := (frontierSortFuel fuel xs).nodes
      FrontierAllWF levels out ∧
      FrontierStrictlySorted out ∧
      (∀ z, FrontierMem z out ↔ FrontierMem z xs)
  | 0, xs, hwf, hlen, _ => by
    cases xs with
    | nil => exact ⟨trivial, trivial, fun _ => Iff.rfl⟩
    | cons _ _ => simp [frontierLen] at hlen
  | fuel + 1, .nil, _, _, _ => ⟨trivial, trivial, fun _ => Iff.rfl⟩
  | fuel + 1, .cons x .nil, hwf, _, _ => ⟨hwf, trivial, fun _ => Iff.rfl⟩
  | fuel + 1, .cons x (.cons y rest), hwf, hlen, hok => by
    unfold frontierSortFuel at hok ⊢
    dsimp only at hok ⊢
    have hsp := frontierSplit_props levels (.cons x (.cons y rest)) hwf
    have hge2 : 2 ≤ frontierLen (.cons x (.cons y rest)) := by simp [frontierLen]; omega
    obtain ⟨hwL, hwR, _, hltSp, hmemSp⟩ := hsp
    obtain ⟨hlL, hlR⟩ := hltSp hge2
    generalize hpEq : frontierSplit (.cons x (.cons y rest)) = p at hwL hwR hlL hlR hmemSp hok ⊢
    generalize hslEq : frontierSortFuel fuel p.left = sl at hok ⊢
    generalize hsrEq : frontierSortFuel fuel p.right = sr at hok ⊢
    generalize hmEq : frontierMergeFuel (frontierLen sl.nodes + frontierLen sr.nodes + 1) sl.nodes sr.nodes = m at hok ⊢
    have hflags : sl.ok = 1 ∧ sr.ok = 1 ∧ m.ok = 1 := by
      by_cases h1 : sl.ok = 1
      · by_cases h2 : sr.ok = 1
        · by_cases h3 : m.ok = 1
          · exact ⟨h1, h2, h3⟩
          · have h3f : (m.ok == 1) = false := beq_false_of_ne h3; simp [h1, h2, h3f] at hok
        · have h2f : (sr.ok == 1) = false := beq_false_of_ne h2; simp [h1, h2f] at hok
      · have h1f : (sl.ok == 1) = false := beq_false_of_ne h1; simp [h1f] at hok
    have ihL := frontierSortFuel_sound levels fuel p.left hwL (by omega) (hslEq.symm ▸ hflags.1)
    have ihR := frontierSortFuel_sound levels fuel p.right hwR (by omega) (hsrEq.symm ▸ hflags.2.1)
    rw [hslEq] at ihL; rw [hsrEq] at ihR
    have ihM := frontierMergeFuel_sound levels (frontierLen sl.nodes + frontierLen sr.nodes + 1)
      sl.nodes sr.nodes ihL.1 ihR.1 ihL.2.1 ihR.2.1 (hmEq.symm ▸ hflags.2.2)
    rw [hmEq] at ihM
    refine ⟨ihM.1, ihM.2.1, fun z => ?_⟩
    rw [ihM.2.2, ihL.2.2, ihR.2.2, ← hmemSp]

/-- One authenticated upward MMCS Merkle step from `node` to `parent` at tree level `k`,
using Protocol `v6` keyed BLAKE3 compression (`compressOrdered` + `injectMaybe`). -/
def MmcsStep (lhs : NatList) (k : Nat) (node parent : FrontierNode) : Prop :=
  ∃ b restBits sib,
    node.bits = .cons b restBits ∧
    (b = 0 ∨ b = 1) ∧
    parent.idx = bitsToNum restBits ∧
    parent.bits = restBits ∧
    selectRowsLe parent.rows lhs k = selectRowsLe node.rows lhs k ∧
    let inj := injectMaybe parent.rows lhs k (compressOrdered b node.digest sib)
    inj.ok = 1 ∧ parent.digest = inj.digest

/-- Valid `levels`-step Protocol `v6` keyed-BLAKE3 MMCS authentication path from `node`
to the unique Merkle cap root `root`. -/
def MmcsPathValid : Nat → NatList → FrontierNode → DigestBytes → Prop
  | 0, _, node, root => node.idx = 0 ∧ node.digest = root
  | levels + 1, lhs, node, root =>
    ∃ parent : FrontierNode,
      MmcsStep lhs levels node parent ∧
      MmcsPathValid levels lhs parent root

private theorem frontierLevelFuel_sound (lhs : NatList) (levels : Nat) :
    ∀ (fuel : Nat) (nodes : FrontierList) (proof : DigestBytesList),
      FrontierAllWF (levels + 1) nodes →
      FrontierStrictlySorted nodes →
      (frontierLevelFuel fuel nodes proof lhs levels).ok = 1 →
      let out := (frontierLevelFuel fuel nodes proof lhs levels).nodes
      FrontierAllWF levels out ∧
      FrontierStrictlySorted out ∧
      (∀ p, FrontierMem p out → ∃ n, FrontierMem n nodes ∧ n.idx / 2 = p.idx) ∧
      (∀ n, FrontierMem n nodes → ∃ p, FrontierMem p out ∧ MmcsStep lhs levels n p)
  | 0, _, _, _, _, hok => by simp [frontierLevelFuel] at hok
  | fuel + 1, .nil, proof, _, _, _ =>
    ⟨trivial, trivial, (fun _ hm => by cases hm), (fun _ hm => by cases hm)⟩
  | fuel + 1, .cons a rest, proof, ⟨hwa, hwr⟩, hsort, hok => by
    rcases haBits : a.bits with _ | ⟨abit, aParentBits⟩
    · have := hwa.2.1; rw [haBits] at this; simp [bitListLen] at this
    have hab01 : abit = 0 ∨ abit = 1 := by
      have := hwa.1; rw [haBits] at this; exact this.1
    have haParentWF : ValidBits aParentBits ∧ bitListLen aParentBits = levels := by
      have h1 := hwa.1; have h2 := hwa.2.1
      rw [haBits] at h1 h2; simp only [ValidBits, bitListLen] at h1 h2
      exact ⟨h1.2, by omega⟩
    have haIdxDiv : a.idx / 2 = bitsToNum aParentBits := by
      have := hwa.2.2; rw [haBits] at this; simp only [bitsToNum] at this
      rcases hab01 with rfl | rfl <;> omega
    cases rest with
    | nil =>
      cases proof with
      | nil =>
        unfold frontierLevelFuel at hok; dsimp only at hok; rw [haBits] at hok; simp at hok
      | cons sib prest =>
        unfold frontierLevelFuel at hok ⊢
        dsimp only at hok ⊢
        rw [haBits] at hok ⊢
        dsimp only at hok ⊢
        refine ⟨⟨⟨haParentWF.1, haParentWF.2, rfl⟩, trivial⟩, trivial, ?_, ?_⟩
        · intro p hp
          rcases hp with rfl | hm
          · exact ⟨a, Or.inl rfl, haIdxDiv⟩
          · cases hm
        · intro n hn
          rcases hn with rfl | hm
          · exact ⟨_, Or.inl rfl, ⟨abit, aParentBits, sib, haBits, hab01, rfl, rfl, rfl, hok, rfl⟩⟩
          · cases hm
    | cons b brest =>
      rcases hwr with ⟨hwb, hwbr⟩
      rcases hbBits : b.bits with _ | ⟨bbit, bParentBits⟩
      · have := hwb.2.1; rw [hbBits] at this; simp [bitListLen] at this
      have hbb01 : bbit = 0 ∨ bbit = 1 := by
        have := hwb.1; rw [hbBits] at this; exact this.1
      have hbParentWF : ValidBits bParentBits ∧ bitListLen bParentBits = levels := by
        have h1 := hwb.1; have h2 := hwb.2.1
        rw [hbBits] at h1 h2; simp only [ValidBits, bitListLen] at h1 h2
        exact ⟨h1.2, by omega⟩
      have hbIdxDiv : b.idx / 2 = bitsToNum bParentBits := by
        have := hwb.2.2; rw [hbBits] at this; simp only [bitsToNum] at this
        rcases hbb01 with rfl | rfl <;> omega
      unfold frontierLevelFuel at hok ⊢
      dsimp only at hok ⊢
      rw [haBits, hbBits] at hok ⊢
      dsimp only at hok ⊢
      by_cases hpar : bitsToNum aParentBits = bitsToNum bParentBits
      · rw [ite_eq_left (beq_iff_eq.mpr hpar)] at hok ⊢
        dsimp only at hok ⊢
        set sameOk := assertSameClaims (selectRowsLe a.rows lhs levels) (selectRowsLe b.rows lhs levels)
        set merged := injectMaybe a.rows lhs levels (v6MerkleCompress a.digest b.digest)
        generalize htailEq : frontierLevelFuel fuel brest proof lhs levels = tail at hok ⊢
        have hfl : sameOk = 1 ∧ merged.ok = 1 ∧ tail.ok = 1 := by
          by_cases h1 : sameOk = 1
          · by_cases h2 : merged.ok = 1
            · by_cases h3 : tail.ok = 1
              · exact ⟨h1, h2, h3⟩
              · have h3f : (tail.ok == 1) = false := beq_false_of_ne h3; simp [h1, h2, h3f] at hok
            · have h2f : (merged.ok == 1) = false := beq_false_of_ne h2; simp [h1, h2f] at hok
          · have h1f : (sameOk == 1) = false := beq_false_of_ne h1; simp [h1f] at hok
        have hsameRows : selectRowsLe a.rows lhs levels = selectRowsLe b.rows lhs levels :=
          (assertSameClaims_eq_one_iff _ _).mp hfl.1
        have hab0 : abit = 0 ∧ bbit = 1 := by
          have habLt : a.idx < b.idx := hsort.1
          have hae := hwa.2.2; have hbe := hwb.2.2
          rw [haBits] at hae; rw [hbBits] at hbe
          simp only [bitsToNum] at hae hbe
          rcases hab01 with rfl | rfl <;> rcases hbb01 with rfl | rfl <;> omega
        have hparBits : aParentBits = bParentBits :=
          bitsToNum_inj haParentWF.1 hbParentWF.1 (haParentWF.2.trans hbParentWF.2.symm) hpar
        have ih := frontierLevelFuel_sound lhs levels fuel brest proof hwbr
          (frontierStrictlySorted_tail (frontierStrictlySorted_tail hsort)) (htailEq.symm ▸ hfl.2.2)
        rw [htailEq] at ih
        refine ⟨⟨⟨haParentWF.1, haParentWF.2, rfl⟩, ih.1⟩, ?_, ?_, ?_⟩
        · refine frontierStrictlySorted_cons_of_lt ?_ ih.2.1
          intro p hp
          obtain ⟨n, hnm, hndiv⟩ := ih.2.2.1 p hp
          have hbn : b.idx < n.idx := frontierStrictlySorted_lt_of_mem hsort.2 hnm
          have hbe := hwb.2.2; rw [hbBits, hab0.2] at hbe; simp only [bitsToNum] at hbe
          dsimp only
          omega
        · intro p hp
          rcases hp with rfl | hpt
          · exact ⟨a, Or.inl rfl, haIdxDiv⟩
          · obtain ⟨n, hnm, hndiv⟩ := ih.2.2.1 p hpt
            exact ⟨n, Or.inr (Or.inr hnm), hndiv⟩
        · intro n hn
          rcases hn with rfl | rfl | hnbr
          · refine ⟨_, Or.inl rfl, ⟨abit, aParentBits, b.digest, haBits, hab01, rfl, rfl, rfl, ?_, ?_⟩⟩
            · simp only [compressOrdered, hab0.1, beq_self_eq_true, ↓reduceIte]; exact hfl.2.1
            · simp only [compressOrdered, hab0.1, beq_self_eq_true, ↓reduceIte]; rfl
          · refine ⟨_, Or.inl rfl, ⟨bbit, bParentBits, a.digest, hbBits, hbb01, hpar, hparBits, hsameRows, ?_, ?_⟩⟩
            · simp only [compressOrdered, hab0.2, show ((1 : Nat) == 0) = false from rfl,
                Bool.false_eq_true, ↓reduceIte]; exact hfl.2.1
            · simp only [compressOrdered, hab0.2, show ((1 : Nat) == 0) = false from rfl,
                Bool.false_eq_true, ↓reduceIte]; rfl
          · obtain ⟨p, hpm, hstep⟩ := ih.2.2.2 n hnbr
            exact ⟨p, Or.inr hpm, hstep⟩
      · rw [ite_eq_right (by rw [beq_iff_eq]; exact hpar)] at hok ⊢
        cases proof with
        | nil => simp at hok
        | cons sib prest =>
          dsimp only at hok ⊢
          set merged := injectMaybe a.rows lhs levels (compressOrdered abit a.digest sib)
          generalize htailEq : frontierLevelFuel fuel (.cons b brest) prest lhs levels = tail at hok ⊢
          have hfl : merged.ok = 1 ∧ tail.ok = 1 := by
            by_cases h1 : merged.ok = 1
            · by_cases h2 : tail.ok = 1
              · exact ⟨h1, h2⟩
              · have h2f : (tail.ok == 1) = false := beq_false_of_ne h2; simp [h1, h2f] at hok
            · have h1f : (merged.ok == 1) = false := beq_false_of_ne h1; simp [h1f] at hok
          have ih := frontierLevelFuel_sound lhs levels fuel (.cons b brest) prest ⟨hwb, hwbr⟩
            hsort.2 (htailEq.symm ▸ hfl.2)
          rw [htailEq] at ih
          refine ⟨⟨⟨haParentWF.1, haParentWF.2, rfl⟩, ih.1⟩, ?_, ?_, ?_⟩
          · refine frontierStrictlySorted_cons_of_lt ?_ ih.2.1
            intro p hp
            obtain ⟨n, hnm, hndiv⟩ := ih.2.2.1 p hp
            have hlt_ab : bitsToNum aParentBits < bitsToNum bParentBits := by
              have : a.idx < b.idx := hsort.1; omega
            dsimp only
            rcases hnm with rfl | hnbr
            · omega
            · have hbn : b.idx < n.idx := frontierStrictlySorted_lt_of_mem hsort.2 hnbr
              omega
          · intro p hp
            rcases hp with rfl | hpt
            · exact ⟨a, Or.inl rfl, haIdxDiv⟩
            · obtain ⟨n, hnm, hndiv⟩ := ih.2.2.1 p hpt
              exact ⟨n, Or.inr hnm, hndiv⟩
          · intro n hn
            rcases hn with rfl | hrest
            · exact ⟨_, Or.inl rfl, ⟨abit, aParentBits, sib, haBits, hab01, rfl, rfl, rfl, hfl.1, rfl⟩⟩
            · obtain ⟨p, hpm, hstep⟩ := ih.2.2.2 n hrest
              exact ⟨p, Or.inr hpm, hstep⟩

private theorem frontierFold_sound (lhs : NatList) :
    ∀ (levels : Nat) (nodes : FrontierList) (proof : DigestBytesList) (root : FrontierNode),
      FrontierAllWF levels nodes →
      FrontierStrictlySorted nodes →
      (frontierFold nodes proof lhs levels).ok = 1 →
      (frontierFold nodes proof lhs levels).nodes = .cons root .nil →
      root.idx = 0 →
      ∀ n, FrontierMem n nodes → MmcsPathValid levels lhs n root.digest
  | 0, nodes, proof, root, _, _, _, hnodes, hidx0, n, hm => by
    unfold frontierFold at hnodes
    dsimp only at hnodes
    rw [hnodes] at hm
    rcases hm with rfl | hm2
    · exact ⟨hidx0, rfl⟩
    · cases hm2
  | levels + 1, nodes, proof, root, hwf, hsort, hok, hnodes, hidx0, n, hm => by
    unfold frontierFold at hok hnodes
    dsimp only at hok hnodes
    generalize hstEq : frontierLevelFuel (frontierLen nodes + 1) nodes proof lhs levels = st at hok hnodes
    by_cases hst0 : st.ok = 0
    · simp [hst0] at hok
    · have hst01 : (frontierLevelFuel (frontierLen nodes + 1) nodes proof lhs levels).ok = 0 ∨
          (frontierLevelFuel (frontierLen nodes + 1) nodes proof lhs levels).ok = 1 := by
        have aux : ∀ f ns pr,
            (frontierLevelFuel f ns pr lhs levels).ok = 0 ∨
            (frontierLevelFuel f ns pr lhs levels).ok = 1 := by
          intro f; induction f with
          | zero => intro _ _; exact Or.inl rfl
          | succ f ih =>
            intro ns pr; unfold frontierLevelFuel
            cases ns with
            | nil => exact Or.inr rfl
            | cons a rest =>
              dsimp only
              cases ha : a.bits with
              | nil => exact Or.inl rfl
              | cons abit aPB =>
                dsimp only
                cases rest with
                | nil =>
                  cases pr with
                  | nil => exact Or.inl rfl
                  | cons sib prest =>
                    dsimp only
                    unfold injectMaybe; split
                    · exact Or.inr rfl
                    · unfold leafHashAt v6MerkleLeafHashChecked; dsimp only
                      cases selectRows a.rows lhs levels with
                      | nil => exact Or.inr rfl
                      | cons r rr =>
                        unfold flattenRowsChecked; dsimp only
                        by_cases hfc : ((flattenRowChecked r (flattenRowsChecked rr).bytes).ok == 1 &&
                            (flattenRowsChecked rr).ok == 1) = true
                        · rw [ite_eq_left hfc]; exact Or.inr rfl
                        · rw [ite_eq_right hfc]; exact Or.inl rfl
                | cons b brest =>
                  dsimp only
                  cases hb : b.bits with
                  | nil => exact Or.inl rfl
                  | cons _ bPB =>
                    dsimp only
                    by_cases hp : bitsToNum aPB = bitsToNum bPB
                    · rw [ite_eq_left (beq_iff_eq.mpr hp)]; dsimp only
                      by_cases hc : (assertSameClaims (selectRowsLe a.rows lhs levels)
                          (selectRowsLe b.rows lhs levels) == 1 &&
                          (injectMaybe a.rows lhs levels (v6MerkleCompress a.digest b.digest)).ok == 1 &&
                          (frontierLevelFuel f brest pr lhs levels).ok == 1) = true
                      · rw [ite_eq_left hc]; exact Or.inr rfl
                      · rw [ite_eq_right hc]; exact Or.inl rfl
                    · rw [ite_eq_right (by rw [beq_iff_eq]; exact hp)]
                      cases pr with
                      | nil => exact Or.inl rfl
                      | cons sib prest =>
                        dsimp only
                        by_cases hc : ((injectMaybe a.rows lhs levels (compressOrdered abit a.digest sib)).ok == 1 &&
                            (frontierLevelFuel f (.cons b brest) prest lhs levels).ok == 1) = true
                        · rw [ite_eq_left hc]; exact Or.inr rfl
                        · rw [ite_eq_right hc]; exact Or.inl rfl
        exact aux _ _ _
      have hst1 : st.ok = 1 := (hstEq ▸ hst01).resolve_left hst0
      have hstf : (st.ok == 0) = false := beq_false_of_ne hst0
      simp only [hstf, Bool.false_eq_true, ↓reduceIte] at hok hnodes
      have hlev := frontierLevelFuel_sound lhs levels (frontierLen nodes + 1) nodes proof hwf hsort
        (hstEq.symm ▸ hst1)
      rw [hstEq] at hlev
      obtain ⟨p, hpm, hstep⟩ := hlev.2.2.2 n hm
      exact ⟨p, hstep, frontierFold_sound lhs levels st.nodes st.proof root hlev.1 hlev.2.1 hok hnodes hidx0 p hpm⟩

/-- All query index bitlists in `BitListList` are valid bitlists of exact length `levels`. -/
def ValidQueryIndices (levels : Nat) : BitListList → Prop
  | .nil => True
  | .cons bits rest => ValidBits bits ∧ bitListLen bits = levels ∧ ValidQueryIndices levels rest

/-- Pairwise membership of `(idxBits, rows)` in parallel `(indices, allRows)` lists. -/
def QueryPairMem (idxBits : BitList) (qRows : U64ListList) : BitListList → U64List3 → Prop
  | .nil, _ => False
  | _, .nil => False
  | .cons b br, .cons r rr => (idxBits = b ∧ qRows = r) ∨ QueryPairMem idxBits qRows br rr

private theorem frontierLeaves_sound (lhs : NatList) (logMax : Nat) :
    ∀ (indices : BitListList) (rows : U64List3),
      ValidQueryIndices logMax indices →
      (frontierLeaves indices rows lhs logMax).ok = 1 →
      let out := (frontierLeaves indices rows lhs logMax).nodes
      FrontierAllWF logMax out ∧
      (∀ idxBits qRows, QueryPairMem idxBits qRows indices rows →
        (leafHashAt qRows lhs logMax).ok = 1 ∧
        FrontierMem { idx := bitsToNum idxBits, bits := idxBits, rows := qRows,
                      digest := (leafHashAt qRows lhs logMax).digest } out)
  | .nil, .nil, _, _ => ⟨trivial, fun _ _ hm => by cases hm⟩
  | .nil, .cons _ _, _, hok => by simp [frontierLeaves] at hok
  | .cons _ _, .nil, _, hok => by simp [frontierLeaves] at hok
  | .cons bits irest, .cons r rrest, ⟨hvb, hlb, hvrest⟩, hok => by
    unfold frontierLeaves at hok ⊢
    dsimp only at hok ⊢
    set d := leafHashAt r lhs logMax
    generalize htEq : frontierLeaves irest rrest lhs logMax = tail at hok ⊢
    have hfl : d.ok = 1 ∧ tail.ok = 1 := by
      by_cases h1 : d.ok = 1
      · by_cases h2 : tail.ok = 1
        · exact ⟨h1, h2⟩
        · have h2f : (tail.ok == 1) = false := beq_false_of_ne h2; simp [h1, h2f] at hok
      · have h1f : (d.ok == 1) = false := beq_false_of_ne h1; simp [h1f] at hok
    have ih := frontierLeaves_sound lhs logMax irest rrest hvrest (htEq.symm ▸ hfl.2)
    rw [htEq] at ih
    refine ⟨⟨⟨hvb, hlb, rfl⟩, ih.1⟩, ?_⟩
    intro idxBits qRows hm
    rcases hm with ⟨rfl, rfl⟩ | hmr
    · exact ⟨hfl.1, Or.inl rfl⟩
    · obtain ⟨hd, hmem⟩ := ih.2 idxBits qRows hmr
      exact ⟨hd, Or.inr hmem⟩

private theorem frontierLeaves_ok_zero_or_one (lhs : NatList) (logMax : Nat) :
    ∀ indices rows, (frontierLeaves indices rows lhs logMax).ok = 0 ∨
      (frontierLeaves indices rows lhs logMax).ok = 1
  | .nil, .nil => Or.inr rfl
  | .nil, .cons _ _ => Or.inl rfl
  | .cons _ _, .nil => Or.inl rfl
  | .cons _ _, .cons _ _ => by unfold frontierLeaves; dsimp only; split <;> [exact Or.inr rfl; exact Or.inl rfl]

private theorem frontierSortFuel_ok_zero_or_one :
    ∀ fuel xs, (frontierSortFuel fuel xs).ok = 0 ∨ (frontierSortFuel fuel xs).ok = 1
  | 0, _ => Or.inr rfl
  | _ + 1, .nil => Or.inr rfl
  | _ + 1, .cons _ .nil => Or.inr rfl
  | _ + 1, .cons _ (.cons _ _) => by
    unfold frontierSortFuel; dsimp only; split <;> [exact Or.inr rfl; exact Or.inl rfl]

private theorem frontierFold_ok_zero_or_one (lhs : NatList) :
    ∀ levels nodes proof, (frontierFold nodes proof lhs levels).ok = 0 ∨
      (frontierFold nodes proof lhs levels).ok = 1
  | 0, _, _ => Or.inr rfl
  | levels + 1, nodes, proof => by
    unfold frontierFold; dsimp only; split
    · exact Or.inl rfl
    · exact frontierFold_ok_zero_or_one lhs levels _ _

/-- **Batched Pruned MMCS Verification Soundness (`CompressWrapPure.mmcsVerifyMulti`)**:
whenever `mmcsVerifyMulti cap rows lhs indices proof logMax = 1` on valid `logMax`-bit query
indices, the verifier enforces:
1. matching query count (`u64List3Len rows = bitListListLen indices`),
2. a unique length-1 Merkle cap `[expected]`,
3. for EVERY queried `(idxBits, qRows)`, all opened Goldilocks words at `logMax` are canonical
   (`< p_GL`) AND there exists a genuine `MmcsPathValid` keyed-BLAKE3 authentication path
   opening `(idxBits, qRows)` to `expected`,
4. **duplicate-index consistency**: any two queries at the same leaf index (`bitsToNum idx1 = bitsToNum idx2`)
   carry identical rows and identical leaf digests. -/
theorem mmcsVerifyMulti_sound {cap : DigestBytesList} {rows : U64List3} {lhs : NatList}
    {indices : BitListList} {proof : DigestBytesList} {logMax : Nat}
    (hvIdx : ValidQueryIndices logMax indices)
    (hok : mmcsVerifyMulti cap rows lhs indices proof logMax = 1) :
    u64List3Len rows = bitListListLen indices ∧
    ∃ expected : DigestBytes,
      cap = .cons expected .nil ∧
      (∀ idxBits qRows, QueryPairMem idxBits qRows indices rows →
        (leafHashAt qRows lhs logMax).ok = 1 ∧
        MmcsPathValid logMax lhs
          { idx := bitsToNum idxBits, bits := idxBits, rows := qRows,
            digest := (leafHashAt qRows lhs logMax).digest }
          expected) ∧
      (∀ idx1 r1 idx2 r2,
        QueryPairMem idx1 r1 indices rows →
        QueryPairMem idx2 r2 indices rows →
        bitsToNum idx1 = bitsToNum idx2 →
        r1 = r2 ∧ (leafHashAt r1 lhs logMax).digest = (leafHashAt r2 lhs logMax).digest) := by
  unfold mmcsVerifyMulti at hok
  by_cases hlen : u64List3Len rows ≠ bitListListLen indices
  · rw [ite_eq_left (bne_iff_ne.mpr hlen)] at hok; cases hok
  · have hlenEq : u64List3Len rows = bitListListLen indices := Classical.not_not.mp hlen
    rw [ite_eq_right (by rw [bne_iff_ne]; exact hlen)] at hok
    dsimp only at hok
    generalize hlEq : frontierLeaves indices rows lhs logMax = leavesRes at hok
    by_cases hl0 : leavesRes.ok = 0
    · simp [hl0] at hok
    · have hl1 : leavesRes.ok = 1 := (hlEq ▸ frontierLeaves_ok_zero_or_one lhs logMax indices rows).resolve_left hl0
      rw [ite_eq_right (by rw [beq_iff_eq]; exact hl0)] at hok
      generalize hsEq : frontierSortFuel (frontierLen leavesRes.nodes + 2) leavesRes.nodes = sortedRes at hok
      by_cases hs0 : sortedRes.ok = 0
      · simp [hs0] at hok
      · have hs1 : sortedRes.ok = 1 :=
          (hsEq ▸ frontierSortFuel_ok_zero_or_one _ _).resolve_left hs0
        rw [ite_eq_right (by rw [beq_iff_eq]; exact hs0)] at hok
        generalize hfEq : frontierFold sortedRes.nodes proof lhs logMax = foldRes at hok
        by_cases hf0 : foldRes.ok = 0
        · simp [hf0] at hok
        · have hf1 : foldRes.ok = 1 :=
            (hfEq ▸ frontierFold_ok_zero_or_one lhs _ _ _).resolve_left hf0
          rw [ite_eq_right (by rw [beq_iff_eq]; exact hf0)] at hok
          cases hpr : foldRes.proof with
          | cons _ _ => rw [hpr] at hok; cases hok
          | nil =>
            rw [hpr] at hok
            cases hfn : foldRes.nodes with
            | nil => rw [hfn] at hok; cases hok
            | cons root noMore =>
              rw [hfn] at hok
              cases noMore with
              | cons _ _ => cases hok
              | nil =>
                dsimp only at hok
                by_cases hidx : root.idx ≠ 0
                · rw [ite_eq_left (bne_iff_ne.mpr hidx)] at hok; cases hok
                · have hidx0 : root.idx = 0 := Classical.not_not.mp hidx
                  rw [ite_eq_right (by rw [bne_iff_ne]; exact hidx)] at hok
                  cases cap with
                  | nil => cases hok
                  | cons expected capRest =>
                    cases capRest with
                    | cons _ _ => cases hok
                    | nil =>
                      have hexp : expected = root.digest :=
                        (digestBytesEq_eq_one_iff expected root.digest).mp hok
                      have hleaves := frontierLeaves_sound lhs logMax indices rows hvIdx (hlEq.symm ▸ hl1)
                      rw [hlEq] at hleaves
                      have hsorted := frontierSortFuel_sound logMax (frontierLen leavesRes.nodes + 2)
                        leavesRes.nodes hleaves.1 (by omega) (hsEq.symm ▸ hs1)
                      rw [hsEq] at hsorted
                      have hfold := frontierFold_sound lhs logMax sortedRes.nodes proof root
                        hsorted.1 hsorted.2.1 (hfEq.symm ▸ hf1) (hfEq.symm ▸ hfn) hidx0
                      refine ⟨hlenEq, expected, rfl, ?_, ?_⟩
                      · intro idxBits qRows hm
                        obtain ⟨hlok, hmem⟩ := hleaves.2 idxBits qRows hm
                        have hmemS : FrontierMem _ sortedRes.nodes := (hsorted.2.2 _).mpr hmem
                        exact ⟨hlok, hexp ▸ hfold _ hmemS⟩
                      · intro idx1 r1 idx2 r2 hm1 hm2 hidxEq
                        obtain ⟨_, hmem1⟩ := hleaves.2 idx1 r1 hm1
                        obtain ⟨_, hmem2⟩ := hleaves.2 idx2 r2 hm2
                        have hm1S := (hsorted.2.2 _).mpr hmem1
                        have hm2S := (hsorted.2.2 _).mpr hmem2
                        -- Strict sort uniqueness on `.idx`: two members of a strictly sorted
                        -- `FrontierList` with the same `.idx` must be identical!
                        have huniq : ∀ xs : FrontierList, FrontierStrictlySorted xs →
                            ∀ a b, FrontierMem a xs → FrontierMem b xs → a.idx = b.idx → a = b := by
                          intro xs; induction xs with
                          | nil => intro _ _ _ h; cases h
                          | cons hd tl ih =>
                            intro hss a b ha hb hi
                            rcases ha with rfl | hat <;> rcases hb with rfl | hbt
                            · rfl
                            · have := frontierStrictlySorted_lt_of_mem hss hbt; omega
                            · have := frontierStrictlySorted_lt_of_mem hss hat; omega
                            · exact ih (frontierStrictlySorted_tail hss) a b hat hbt hi
                        have heqNode := huniq sortedRes.nodes hsorted.2.1 _ _ hm1S hm2S hidxEq
                        exact ⟨congrArg FrontierNode.rows heqNode, congrArg FrontierNode.digest heqNode⟩

/-! ### Section 4D: Goldilocks `ExtGl` Ring Homomorphism, FRI Folding, Horner & PCS Soundness -/

/-- Canonical embedding of `StarkWire.ExtGl` into `CompressionIntrinsicsProof.ExtGL = GLF[X]/(X^3 - X - 1)`. -/
def extGlToExtGL (e : ExtGl) : IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL :=
  ⟨(e.c0 : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF),
   (e.c1 : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF),
   (e.c2 : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF)⟩

private theorem glPrime_eq_mod : glPrime = IxCC.AiurBackend.CompressionIntrinsicsProof.glModulus := rfl

private theorem natCast_glMod (n : Nat) :
    ((n % glPrime : Nat) : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) =
      (n : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) := by
  rw [glPrime_eq_mod, ZMod.natCast_mod]

theorem glAdd_toGLF (a b : Nat) :
    ((glAdd a b : Nat) : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) = (a : _) + (b : _) := by
  unfold glAdd; rw [natCast_glMod, Nat.cast_add]

theorem glSub_toGLF (a b : Nat) :
    ((glSub a b : Nat) : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) = (a : _) - (b : _) := by
  unfold glSub
  rw [natCast_glMod]
  have hlt : b % glPrime < glPrime := Nat.mod_lt b (by decide)
  have hadd : (a + glPrime - b % glPrime) + b % glPrime = a + glPrime := by omega
  have hcast := congrArg (Nat.cast : Nat → IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) hadd
  simp only [Nat.cast_add, glPrime_eq_mod, ZMod.natCast_self, add_zero, ZMod.natCast_mod] at hcast
  exact eq_sub_of_add_eq hcast

theorem glMul_toGLF (a b : Nat) :
    ((glMul a b : Nat) : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) = (a : _) * (b : _) := by
  unfold glMul; rw [natCast_glMod, Nat.cast_mul]

theorem extGlToExtGL_add (a b : ExtGl) :
    extGlToExtGL (extAdd a b) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add (extGlToExtGL a) (extGlToExtGL b) := by
  simp [extGlToExtGL, extAdd, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add, glAdd_toGLF]

theorem extGlToExtGL_sub (a b : ExtGl) :
    extGlToExtGL (extSub a b) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.sub (extGlToExtGL a) (extGlToExtGL b) := by
  simp [extGlToExtGL, extSub, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.sub, glSub_toGLF]

theorem extGlToExtGL_scale (a : ExtGl) (k : Nat) :
    extGlToExtGL (extScale a k) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (extGlToExtGL a) ⟨(k : _), 0, 0⟩ := by
  simp [extGlToExtGL, extScale, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul, glMul_toGLF]

theorem extGlToExtGL_mul (a b : ExtGl) :
    extGlToExtGL (extMul a b) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (extGlToExtGL a) (extGlToExtGL b) := by
  rw [← IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.karatsubaMul_eq_mul]
  simp only [extGlToExtGL, extMul, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.karatsubaMul,
    glAdd_toGLF, glSub_toGLF, glMul_toGLF]

theorem extGlToExtGL_eq_iff (a b : ExtGl) :
    extEq a b = 1 ↔ extGlToExtGL a = extGlToExtGL b := by
  rw [extEq_eq_one_iff]
  simp only [extGlToExtGL, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mk.injEq,
    ZMod.natCast_eq_natCast_iff', glPrime_eq_mod]

theorem extGlToExtGL_isZero_iff (a : ExtGl) :
    extIsZero a = 1 ↔ extGlToExtGL a = IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero := by
  rw [extIsZero_eq_one_iff]
  simp only [extGlToExtGL, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero,
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mk.injEq,
    ← Nat.cast_zero (R := IxCC.AiurBackend.CompressionIntrinsicsProof.GLF),
    ZMod.natCast_eq_natCast_iff', Nat.zero_mod, glPrime_eq_mod]

/-- Direct power-series polynomial evaluation `∑ c_i · x^i` in `ExtGL`. -/
def polyEvalExtGL (coeffs : ExtGlList) (x : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF)
    (pow : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) :
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL :=
  match coeffs with
  | .nil => IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero
  | .cons c rest =>
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add
      (IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (extGlToExtGL c) ⟨pow, 0, 0⟩)
      (polyEvalExtGL rest x (pow * x))

private theorem polyEvalExtGL_scale (coeffs : ExtGlList)
    (x p : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) :
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (polyEvalExtGL coeffs x 1) ⟨p, 0, 0⟩ =
      polyEvalExtGL coeffs x p := by
  have aux : ∀ cs a b,
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (polyEvalExtGL cs x a) ⟨b, 0, 0⟩ =
        polyEvalExtGL cs x (a * b) := by
    intro cs; induction cs with
    | nil =>
      intro a b
      simp [polyEvalExtGL, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero,
        IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul]
    | cons c rest ih =>
      intro a b
      simp only [polyEvalExtGL]
      rw [IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_comm,
          IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_add,
          IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_comm ⟨b, 0, 0⟩,
          IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_comm ⟨b, 0, 0⟩,
          ih (a * x) b, IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_assoc]
      have h1 : IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul ⟨a, 0, 0⟩ ⟨b, 0, 0⟩ = ⟨a * b, 0, 0⟩ := by
        simp [IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul]
      rw [h1, show a * x * b = a * b * x by ring]
  simpa [one_mul] using aux coeffs 1 p

/-- **Horner Final-Polynomial Soundness (`CompressWrapPure.evalFinalPoly`)**:
`evalFinalPoly coeffs x` computes the exact polynomial evaluation `∑_i c_i · x^i` in `ExtGL`. -/
theorem evalFinalPoly_spec (coeffs : ExtGlList) (x : Nat) :
    extGlToExtGL (evalFinalPoly coeffs x) = polyEvalExtGL coeffs (x : _) 1 := by
  induction coeffs with
  | nil => rfl
  | cons c rest ih =>
    unfold evalFinalPoly polyEvalExtGL
    rw [extGlToExtGL_add, extGlToExtGL_scale, ih, polyEvalExtGL_scale, one_mul,
        show (⟨(1 : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF), 0, 0⟩ :
            IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL) =
          IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.one from rfl,
        IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul_one]

/-- **Degree-2 FRI Butterfly Exactness (`CompressWrapPure.friFold2Step`)**:
if `e0 = p(x) = a + b · x` and `e1 = p(-x) = a - b · x` in `ExtGL` and `inv2x = (2x)⁻¹` in `GLF`,
then `friFold2Step inv2x β e0 e1 = a + β · b` identically in `ExtGL`. -/
theorem friFold2Step_linear_poly_sound
    (a b : IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL)
    {x inv2x : Nat} {β e0 e1 : ExtGl}
    (hinv : (inv2x : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) * (2 * (x : _)) = 1)
    (he0 : extGlToExtGL e0 = IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add a
      (IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul b ⟨(x : _), 0, 0⟩))
    (he1 : extGlToExtGL e1 = IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.sub a
      (IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul b ⟨(x : _), 0, 0⟩)) :
    extGlToExtGL (friFold2Step inv2x β e0 e1) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add a
        (IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (extGlToExtGL β) b) := by
  have h2inv : ((glInv2 : Nat) : IxCC.AiurBackend.CompressionIntrinsicsProof.GLF) * 2 = 1 := by
    have hval : glInv2 = 9223372034707292161 := rfl
    rw [hval]; decide
  unfold friFold2Step
  rw [extGlToExtGL_add, extGlToExtGL_scale, extGlToExtGL_add, extGlToExtGL_mul,
      extGlToExtGL_scale, extGlToExtGL_sub, he0, he1]
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  rcases extGlToExtGL β with ⟨β0, β1, β2⟩
  simp only [IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.add,
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.sub,
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul,
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination a0 * h2inv + (β0 * b0 + β1 * b2 + β2 * b1) * hinv
  · linear_combination a1 * h2inv + (β0 * b1 + β1 * b0 + β1 * b2 + β2 * b1 + β2 * b2) * hinv
  · linear_combination a2 * h2inv + (β0 * b2 + β2 * b0 + β1 * b1 + β2 * b2) * hinv

/-- Every FRI round arity in `arities` is in `1..min 3 maxLogArity`. -/
def ValidFriArities (maxLogArity : Nat) : NatList → Prop
  | .nil => True
  | .cons la rest => 1 ≤ la ∧ la ≤ maxLogArity ∧ la ≤ 3 ∧ ValidFriArities maxLogArity rest

/-- **Multi-Arity FRI Query Loop Soundness (`CompressWrapPure.verifyQueryMulti`)**:
acceptance guarantees exact round-count match across `betas`/`openings`/`arities`, valid per-round
arities `1 ≤ la ≤ min 3 maxLogArity`, exact height sum `sumNatList arities + logFinal = logCur`,
and exact commit-phase opened row count. -/
theorem verifyQueryMulti_sound :
    ∀ (openings : ExtGlListList) (folded : ExtGl) (betas : ExtGlList) (arities : NatList)
      (domIdx : BitList) (logCur : Nat) (roRest : RollBucketList) (logFinal maxLogArity : Nat),
      (verifyQueryMulti folded betas openings arities domIdx logCur roRest logFinal maxLogArity).ok = 1 →
      extGlListLen betas = extGlListListLen openings ∧
      natListLen arities = extGlListListLen openings ∧
      ValidFriArities maxLogArity arities ∧
      sumNatList arities + logFinal = logCur ∧
      u64ListListLen (verifyQueryMulti folded betas openings arities domIdx logCur roRest logFinal maxLogArity).rows =
        extGlListListLen openings
  | .nil, folded, betas, arities, domIdx, logCur, roRest, logFinal, maxLogArity, hok => by
    cases betas <;> cases arities <;> cases roRest <;>
      simp only [verifyQueryMulti] at hok ⊢ <;> try cases hok
    by_cases hcur : logCur = logFinal
    · subst hcur; exact ⟨rfl, rfl, trivial, by simp [sumNatList], by simp [u64ListListLen, extGlListListLen]⟩
    · have hbf : (logCur == logFinal) = false := beq_false_of_ne hcur
      simp [hbf] at hok
  | .cons sibs opRest, folded, betas, arities, domIdx, logCur, roRest, logFinal, maxLogArity, hok => by
    cases betas with
    | nil => simp [verifyQueryMulti] at hok
    | cons beta betaRest =>
      cases arities with
      | nil => simp [verifyQueryMulti] at hok
      | cons la laRest =>
        unfold verifyQueryMulti at hok ⊢
        dsimp only at hok ⊢
        by_cases hbad : (la == 0 || decide (la > maxLogArity) || decide (logCur < la)) = true
        · simp [hbad] at hok
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hok ⊢
          have hlaB : 1 ≤ la ∧ la ≤ maxLogArity ∧ la ≤ logCur := by
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hbad; omega
          by_cases h1 : la = 1
          · subst h1
            simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
            cases domIdx with
            | nil => simp at hok
            | cons b0 idRest =>
              dsimp only at hok ⊢
              by_cases hev : (reconEvals2 b0 folded sibs).ok = 0
              · simp [hev] at hok
              · have hevf : ((reconEvals2 b0 folded sibs).ok == 0) = false := beq_false_of_ne hev
                simp only [hevf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                have ih := verifyQueryMulti_sound opRest _ betaRest laRest idRest (logCur - 1) _ logFinal maxLogArity hok
                refine ⟨by simp [extGlListLen, extGlListListLen, ih.1],
                  by simp [natListLen, extGlListListLen, ih.2.1],
                  ⟨hlaB.1, hlaB.2.1, by decide, ih.2.2.1⟩,
                  by simp [sumNatList]; omega,
                  by simp [u64ListListLen, extGlListListLen, ih.2.2.2.2]⟩
          · have h1f : (la == 1) = false := beq_false_of_ne h1
            simp only [h1f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
            by_cases h2 : la = 2
            · subst h2
              simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
              cases domIdx with
              | nil => simp at hok
              | cons b0 r0 =>
                cases r0 with
                | nil => simp at hok
                | cons b1 idRest =>
                  dsimp only at hok ⊢
                  by_cases hev : (reconEvals4 (b0 + b1 + b1) folded sibs).ok = 0
                  · simp [hev] at hok
                  · have hevf : ((reconEvals4 (b0 + b1 + b1) folded sibs).ok == 0) = false := beq_false_of_ne hev
                    simp only [hevf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                    have ih := verifyQueryMulti_sound opRest _ betaRest laRest idRest (logCur - 2) _ logFinal maxLogArity hok
                    refine ⟨by simp [extGlListLen, extGlListListLen, ih.1],
                      by simp [natListLen, extGlListListLen, ih.2.1],
                      ⟨hlaB.1, hlaB.2.1, by decide, ih.2.2.1⟩,
                      by simp [sumNatList]; omega,
                      by simp [u64ListListLen, extGlListListLen, ih.2.2.2.2]⟩
            · have h2f : (la == 2) = false := beq_false_of_ne h2
              simp only [h2f, Bool.false_eq_true, ↓reduceIte] at hok ⊢
              by_cases h3 : la = 3
              · subst h3
                simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
                cases domIdx with
                | nil => simp at hok
                | cons b0 r0 =>
                  cases r0 with
                  | nil => simp at hok
                  | cons b1 r1 =>
                    cases r1 with
                    | nil => simp at hok
                    | cons b2 idRest =>
                      dsimp only at hok ⊢
                      by_cases hev : (reconEvals8 (b0 + 2 * b1 + 4 * b2) folded sibs).ok = 0
                      · simp [hev] at hok
                      · have hevf : ((reconEvals8 (b0 + 2 * b1 + 4 * b2) folded sibs).ok == 0) = false := beq_false_of_ne hev
                        simp only [hevf, Bool.false_eq_true, ↓reduceIte] at hok ⊢
                        have ih := verifyQueryMulti_sound opRest _ betaRest laRest idRest (logCur - 3) _ logFinal maxLogArity hok
                        refine ⟨by simp [extGlListLen, extGlListListLen, ih.1],
                          by simp [natListLen, extGlListListLen, ih.2.1],
                          ⟨hlaB.1, hlaB.2.1, by decide, ih.2.2.1⟩,
                          by simp [sumNatList]; omega,
                          by simp [u64ListListLen, extGlListListLen, ih.2.2.2.2]⟩
              · have h3f : (la == 3) = false := beq_false_of_ne h3
                simp [h3f] at hok

/-- Per-bucket DEEP denominator non-zero & bottom-height vanishing postcondition. -/
def FinalizeBucketsValid (logBlowup : Nat) (zeta : ExtGl) :
    BucketList → HeightInfoList → BitList → Nat → RollBucketList → Prop
  | .nil, .nil, _, _, .nil => True
  | .cons b br, .cons info ir, curBits, prevH, .cons rb rbr =>
    let bitsH := bitListDrop (prevH - b.height) curBits
    let x := glMul glCosetShift (glExpByBits info.genH (bitListRevOnto bitsH .nil))
    extGlToExtGL (extSub zeta (extOfBase x)) ≠ IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero ∧
    extGlToExtGL (extSub info.zetaNext (extOfBase x)) ≠ IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero ∧
    rb.height = b.height ∧
    (b.height = logBlowup → extGlToExtGL rb.ro = IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero) ∧
    FinalizeBucketsValid logBlowup zeta br ir bitsH b.height rbr
  | _, _, _, _, _ => False

theorem finalizeBuckets_sound :
    ∀ (buckets : BucketList) (infos : HeightInfoList) (curBits : BitList)
      (prevH logBlowup : Nat) (zeta : ExtGl),
      (finalizeBuckets buckets infos curBits prevH logBlowup zeta).ok = 1 →
      FinalizeBucketsValid logBlowup zeta buckets infos curBits prevH
        (finalizeBuckets buckets infos curBits prevH logBlowup zeta).rollBuckets
  | .nil, .nil, _, _, _, _, _ => trivial
  | .nil, .cons _ _, _, _, _, _, hok => by simp [finalizeBuckets] at hok
  | .cons _ _, .nil, _, _, _, _, hok => by simp [finalizeBuckets] at hok
  | .cons b br, .cons info ir, curBits, prevH, logBlowup, zeta, hok => by
    unfold finalizeBuckets at hok ⊢
    dsimp only at hok ⊢
    set bitsH := bitListDrop (prevH - b.height) curBits
    set x := glMul glCosetShift (glExpByBits info.genH (bitListRevOnto bitsH .nil))
    by_cases hz : (extIsZero (extSub zeta (extOfBase x)) == 1 ||
        extIsZero (extSub info.zetaNext (extOfBase x)) == 1) = true
    · simp [hz] at hok
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      have hnz : extIsZero (extSub zeta (extOfBase x)) ≠ 1 ∧
          extIsZero (extSub info.zetaNext (extOfBase x)) ≠ 1 := by
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hz; exact hz
      set ro := extAdd (extMul (extInvDirect (extSub zeta (extOfBase x))) b.ro0)
        (extMul (extInvDirect (extSub info.zetaNext (extOfBase x))) b.ro1)
      set zeroOk := if b.height == logBlowup then extIsZero ro else 1
      generalize htailEq : finalizeBuckets br ir bitsH b.height logBlowup zeta = tail at hok ⊢
      have hfl : zeroOk = 1 ∧ tail.ok = 1 := by
        by_cases h1 : zeroOk = 1
        · by_cases h2 : tail.ok = 1
          · exact ⟨h1, h2⟩
          · have h2f : (tail.ok == 1) = false := beq_false_of_ne h2; simp [h1, h2f] at hok
        · have h1f : (zeroOk == 1) = false := beq_false_of_ne h1; simp [h1f] at hok
      have ih := finalizeBuckets_sound br ir bitsH b.height logBlowup zeta (htailEq.symm ▸ hfl.2)
      rw [htailEq] at ih
      refine ⟨mt (extGlToExtGL_isZero_iff _).mpr hnz.1,
        mt (extGlToExtGL_isZero_iff _).mpr hnz.2, rfl, ?_, ih⟩
      intro hbh
      have hz1 : extIsZero ro = 1 := by
        have := hfl.1; dsimp only [zeroOk] at this; rw [hbh] at this; simpa using this
      exact (extGlToExtGL_isZero_iff ro).mp hz1

private theorem heightsFit_sound (logBlowup logGmax : Nat) :
    ∀ logDegrees : NatList, heightsFit logDegrees logBlowup logGmax = 1 →
      ∀ ld, natInList logDegrees ld = 1 → ld + logBlowup ≤ logGmax
  | .nil, _, _, hm => by simp [natInList] at hm
  | .cons d rest, hok, ld, hm => by
    unfold heightsFit at hok
    by_cases hle : d + logBlowup ≤ logGmax
    · rw [ite_eq_left hle] at hok
      unfold natInList at hm
      by_cases heq : d = ld
      · subst heq; exact hle
      · rw [ite_eq_right (by rw [beq_iff_eq]; exact heq)] at hm
        exact heightsFit_sound logBlowup logGmax rest hok ld hm
    · rw [ite_eq_right hle] at hok; cases hok

theorem pow2NatExact_eq (k : Nat) : pow2NatExact k = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow2NatExact, ih, Nat.pow_succ, Nat.mul_comm]

/-- Soundness postcondition of `pcsFriVerify`: exact round counts, final polynomial length,
domain height bound `logGmax ≤ 32`, commit & query PoW (with zero-PoW canonicalization),
all input MMCS openings (`s1c`, `s2c`, `qc`, optional `prepCommit`), per-query DEEP/FRI/Horner
consistency, and commit-phase MMCS verification. -/
structure PcsFriAccepted (postZetaInput : ByteList) (stage1 stage2 qOpened : OpenedRound)
    (prepOpt : PreprocessedOpt) (opening : FriProof)
    (s1c s2c qc prepCommit : DigestBytesList) (prepIndices : OptIdxList)
    (logDegrees : NatList) (zeta : ExtGl)
    (logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits : Nat) : Prop where
  commitPow_count : u64ListLen opening.commitPowWitnesses = merkleCapListLen opening.commitPhaseCommits
  commitOpen_count : commitStepListLen opening.commitPhaseOpenings = merkleCapListLen opening.commitPhaseCommits
  finalPoly_len : extGlListLen opening.finalPoly = 2 ^ logFinalPolyLen
  logGmax_le_32 : sumNatList (extractStepArities opening.commitPhaseOpenings) + (logBlowup + logFinalPolyLen) ≤ 32
  heights_fit : ∀ ld, natInList logDegrees ld = 1 →
    ld + logBlowup ≤ sumNatList (extractStepArities opening.commitPhaseOpenings) + (logBlowup + logFinalPolyLen)
  commitPow_valid : PowWitnessesValid commitPowBits opening.commitPowWitnesses
  queryPow_canonical_ltP : glLtPBytes opening.queryPowWitness = 1
  queryPow_zero_canonical : queryPowBits = 0 → opening.queryPowWitness = u64Zero
  input_s1_cap_singleton : ∃ r, s1c = .cons r .nil
  input_s2_cap_singleton : ∃ r, s2c = .cons r .nil
  input_q_cap_singleton : ∃ r, qc = .cons r .nil
  raw_accepted : pcsFriVerify postZetaInput stage1 stage2 qOpened prepOpt opening
    s1c s2c qc prepCommit prepIndices logDegrees zeta
    logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits = 1

private theorem mmcsVerifyMulti_implies_singleton_cap {cap : DigestBytesList} {rows : U64List3}
    {lhs : NatList} {indices : BitListList} {proof : DigestBytesList} {logMax : Nat}
    (hok : mmcsVerifyMulti cap rows lhs indices proof logMax = 1) :
    ∃ r : DigestBytes, cap = .cons r .nil := by
  unfold mmcsVerifyMulti at hok
  split at hok
  · cases hok
  · dsimp only at hok; split at hok
    · cases hok
    · split at hok
      · cases hok
      · split at hok
        · cases hok
        · split at hok
          · cases hok
          · split at hok
            · cases hok
            · split at hok
              · cases hok
              · split at hok
                · cases hok
                · cases cap with
                  | nil => cases hok
                  | cons r cr =>
                    cases cr with
                    | nil => exact ⟨r, rfl⟩
                    | cons _ _ => cases hok

/-- **PCS / FRI Verification Soundness (`CompressWrapPure.pcsFriVerify`)**:
returning `1` guarantees `PcsFriAccepted`, including exact round counts, `2^logFinalPolyLen`
final polynomial length, `logGmax ≤ 32`, commit & query PoW with zero-PoW canonicalization,
and singleton verified MMCS caps for stage1, stage2, and quotient commitments. -/
theorem pcsFriVerify_sound {postZetaInput : ByteList} {stage1 stage2 qOpened : OpenedRound}
    {prepOpt : PreprocessedOpt} {opening : FriProof}
    {s1c s2c qc prepCommit : DigestBytesList} {prepIndices : OptIdxList}
    {logDegrees : NatList} {zeta : ExtGl}
    {logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits : Nat}
    (hok : pcsFriVerify postZetaInput stage1 stage2 qOpened prepOpt opening
      s1c s2c qc prepCommit prepIndices logDegrees zeta
      logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits = 1) :
    PcsFriAccepted postZetaInput stage1 stage2 qOpened prepOpt opening
      s1c s2c qc prepCommit prepIndices logDegrees zeta
      logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits := by
  have hraw := hok
  unfold pcsFriVerify at hok
  dsimp only at hok
  by_cases hc1 : u64ListLen opening.commitPowWitnesses ≠ merkleCapListLen opening.commitPhaseCommits
  · rw [ite_eq_left (bne_iff_ne.mpr hc1)] at hok; cases hok
  · have hcw : u64ListLen opening.commitPowWitnesses = merkleCapListLen opening.commitPhaseCommits :=
      Classical.not_not.mp hc1
    rw [ite_eq_right (by rw [bne_iff_ne]; exact hc1)] at hok
    have hstep2 : ∀ {c : Prop} [Decidable c] {t : Nat}, (if c then 0 else t) = 1 → t = 1 := by
      intro c _ t h
      by_cases hc : c
      · rw [ite_eq_left hc] at h; cases h
      · rw [ite_eq_right hc] at h; exact h
    have hok := hstep2 hok
    by_cases hc3 : commitStepListLen opening.commitPhaseOpenings ≠ merkleCapListLen opening.commitPhaseCommits
    · rw [ite_eq_left (bne_iff_ne.mpr hc3)] at hok; cases hok
    · have hco : commitStepListLen opening.commitPhaseOpenings = merkleCapListLen opening.commitPhaseCommits :=
        Classical.not_not.mp hc3
      rw [ite_eq_right (by rw [bne_iff_ne]; exact hc3)] at hok
      by_cases hc4 : extGlListLen opening.finalPoly ≠ pow2NatExact logFinalPolyLen
      · rw [ite_eq_left (bne_iff_ne.mpr hc4)] at hok; cases hok
      · have hfp : extGlListLen opening.finalPoly = 2 ^ logFinalPolyLen := by
          rw [← pow2NatExact_eq]; exact Classical.not_not.mp hc4
        rw [ite_eq_right (by rw [bne_iff_ne]; exact hc4)] at hok
        generalize hcolEq : sampleExtN _ _ = colRes at hok
        by_cases hcol0 : colRes.ok = 0
        · simp [hcol0] at hok
        · rw [ite_eq_right (by rw [beq_iff_eq]; exact hcol0)] at hok
          generalize hopenEq : sampleExtN colRes.state _ = openRes at hok
          by_cases hopen0 : openRes.ok = 0
          · simp [hopen0] at hok
          · rw [ite_eq_right (by rw [beq_iff_eq]; exact hopen0)] at hok
            generalize hbetaEq : pcsBetas openRes.state.input opening.commitPhaseCommits
              opening.commitPowWitnesses commitPowBits = betaRes at hok
            by_cases hbeta0 : betaRes.ok = 0
            · simp [hbeta0] at hok
            · have hbeta01 : ∀ inp cm ws b, (pcsBetas inp cm ws b).ok = 0 ∨ (pcsBetas inp cm ws b).ok = 1 := by
                intro inp cm; induction cm generalizing inp with
                | nil => intro ws b; cases ws <;> [exact Or.inr rfl; exact Or.inl rfl]
                | cons c cr ih =>
                  intro ws b; cases ws with
                  | nil => exact Or.inl rfl
                  | cons w wr =>
                    unfold pcsBetas; dsimp only; split
                    · exact Or.inl rfl
                    · split
                      · exact Or.inl rfl
                      · exact ih _ wr b
              have hbeta1 : betaRes.ok = 1 := (hbetaEq ▸ hbeta01 _ _ _ _).resolve_left hbeta0
              rw [ite_eq_right (by rw [beq_iff_eq]; exact hbeta0)] at hok
              generalize hqpwEq : pcsCheckWitness _ opening.queryPowWitness queryPowBits = qpwRes at hok
              by_cases hqpw0 : qpwRes.ok = 0
              · simp [hqpw0] at hok
              · have hqpw01 : ∀ inp w b, (pcsCheckWitness inp w b).ok = 0 ∨ (pcsCheckWitness inp w b).ok = 1 := by
                  intro inp w b; unfold pcsCheckWitness; split
                  · exact Or.inl rfl
                  · split
                    · split <;> [exact Or.inl rfl; exact Or.inr rfl]
                    · dsimp only; split <;> [exact Or.inr rfl; exact Or.inl rfl]
                have hqpw1 : qpwRes.ok = 1 := (hqpwEq ▸ hqpw01 _ _ _).resolve_left hqpw0
                rw [ite_eq_right (by rw [beq_iff_eq]; exact hqpw0)] at hok
                by_cases hgm : sumNatList (extractStepArities opening.commitPhaseOpenings) +
                    (logBlowup + logFinalPolyLen) ≥ 33
                · rw [ite_eq_left hgm] at hok; cases hok
                · rw [ite_eq_right hgm] at hok
                  by_cases hhf : heightsFit logDegrees logBlowup
                      (sumNatList (extractStepArities opening.commitPhaseOpenings) +
                        (logBlowup + logFinalPolyLen)) = 0
                  · simp [hhf] at hok
                  · have hhf01 : ∀ ds, heightsFit ds logBlowup
                        (sumNatList (extractStepArities opening.commitPhaseOpenings) +
                          (logBlowup + logFinalPolyLen)) = 0 ∨
                        heightsFit ds logBlowup
                        (sumNatList (extractStepArities opening.commitPhaseOpenings) +
                          (logBlowup + logFinalPolyLen)) = 1 := by
                      intro ds; induction ds with
                      | nil => exact Or.inr rfl
                      | cons d dr ih => unfold heightsFit; split <;> [exact ih; exact Or.inl rfl]
                    have hhf1 := (hhf01 logDegrees).resolve_left hhf
                    rw [ite_eq_right (by rw [beq_iff_eq]; exact hhf)] at hok
                    cases hio : opening.inputOpenings with
                    | nil => rw [hio] at hok; cases hok
                    | cons boS1 io1 =>
                      cases io1 with
                      | nil => rw [hio] at hok; cases hok
                      | cons boS2 io2 =>
                        cases io2 with
                        | nil => rw [hio] at hok; cases hok
                        | cons boQ io3 =>
                          rw [hio] at hok; dsimp only at hok
                          have hm01 : ∀ c r l i p m,
                              mmcsVerifyMulti c r l i p m = 0 ∨ mmcsVerifyMulti c r l i p m = 1 := by
                            intro c r l i p m; unfold mmcsVerifyMulti
                            split
                            · exact Or.inl rfl
                            · dsimp only; split
                              · exact Or.inl rfl
                              · split
                                · exact Or.inl rfl
                                · split
                                  · exact Or.inl rfl
                                  · split
                                    · exact Or.inl rfl
                                    · split
                                      · exact Or.inl rfl
                                      · split
                                        · exact Or.inl rfl
                                        · split
                                          · exact Or.inl rfl
                                          · split
                                            · exact Or.inl rfl
                                            · split
                                              · exact Or.inl rfl
                                              · unfold digestBytesEq
                                                split <;> [exact Or.inr rfl; exact Or.inl rfl]
                          set logGmax := sumNatList (extractStepArities opening.commitPhaseOpenings) +
                              (logBlowup + logFinalPolyLen)
                          set hall := heightsAll logDegrees logBlowup
                          set indices := sampleQueryIndices qpwRes.state numQueries logGmax
                          by_cases hs1 : mmcsVerifyMulti s1c boS1.openedValues hall indices boS1.openingProof logGmax = 0
                          · simp [hs1] at hok
                          · have hs1_1 := (hm01 _ _ _ _ _ _).resolve_left hs1
                            rw [ite_eq_right (by rw [beq_iff_eq]; exact hs1)] at hok
                            by_cases hs2 : mmcsVerifyMulti s2c boS2.openedValues hall indices boS2.openingProof logGmax = 0
                            · simp [hs2] at hok
                            · have hs2_1 := (hm01 _ _ _ _ _ _).resolve_left hs2
                              rw [ite_eq_right (by rw [beq_iff_eq]; exact hs2)] at hok
                              by_cases hsq : mmcsVerifyMulti qc boQ.openedValues hall indices boQ.openingProof logGmax = 0
                              · simp [hsq] at hok
                              · have hsq_1 := (hm01 _ _ _ _ _ _).resolve_left hsq
                                have hpb := pcsBetas_sound _ _ _ _ (hbetaEq.symm ▸ hbeta1)
                                have hqp := pcsCheckWitness_sound (hqpwEq.symm ▸ hqpw1)
                                exact ⟨hcw, hco, hfp, by omega,
                                  heightsFit_sound _ _ _ hhf1, hpb.2.2,
                                  hqp.1, fun hb0 => (hqp.2.1 hb0).1,
                                  mmcsVerifyMulti_implies_singleton_cap hs1_1,
                                  mmcsVerifyMulti_implies_singleton_cap hs2_1,
                                  mmcsVerifyMulti_implies_singleton_cap hsq_1, hraw⟩

/-! ### Section 4E: AIR DAG Fuel-Invariance, OOD Quotient, Row Bounds, MEMSEG, Batch & Root Soundness -/

private theorem sysNodesTopological_lookup :
    ∀ (nodes : SysNodeList) (start i : Nat),
      SysNodesTopological start nodes →
      i < sysNodeListLen nodes →
      SysNodeWellFormed (start + i) (sysNodeLookup nodes i)
  | .nil, _, _, _, hi => by simp [sysNodeListLen] at hi
  | .cons nd rest, start, 0, ⟨hnd, _⟩, _ => by simpa [sysNodeLookup] using hnd
  | .cons _ rest, start, i + 1, ⟨_, hrest⟩, hi => by
    simp only [sysNodeListLen] at hi
    have h := sysNodesTopological_lookup rest (start + 1) i hrest (by omega)
    simpa [sysNodeLookup, show start + 1 + i = start + (i + 1) by omega] using h

/-- **AIR DAG Fuel-Invariance (`CompressWrapPure.evalAtFuel`)**:
on any topologically ordered AIR expression DAG (`SysNodesTopological 0 nodes`, guaranteed
for every circuit decoded by `readSystem`), evaluating node `i < sysNodeListLen nodes` with
any two fuel values `f1 > i` and `f2 > i` produces the exact same `ExtGl` value (zero fuel
truncation at `fuel = nodeCount + 1`). -/
theorem evalAtFuel_dag_invariant (nodes : SysNodeList) (ctx : EvalCtx)
    (htopo : SysNodesTopological 0 nodes) :
    ∀ (i f1 f2 : Nat), i < sysNodeListLen nodes → i < f1 → i < f2 →
      evalAtFuel nodes ctx f1 i = evalAtFuel nodes ctx f2 i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro f1 f2 hi hf1 hf2
    obtain ⟨f1', rfl⟩ : ∃ m, f1 = m + 1 := ⟨f1 - 1, by omega⟩
    obtain ⟨f2', rfl⟩ : ∃ m, f2 = m + 1 := ⟨f2 - 1, by omega⟩
    have hwf := sysNodesTopological_lookup nodes 0 i htopo hi
    rw [Nat.zero_add] at hwf
    unfold evalAtFuel
    cases hnd : sysNodeLookup nodes i with
    | const c => rfl
    | var src off idx => rfl
    | pub idx => rfl
    | isFirstRow => rfl
    | isLastRow => rfl
    | isTransition => rfl
    | add a b =>
      rw [hnd] at hwf
      dsimp only [SysNodeWellFormed] at hwf
      dsimp only
      rw [ih a hwf.1 f1' f2' (by omega) (by omega) (by omega),
          ih b hwf.2 f1' f2' (by omega) (by omega) (by omega)]
    | sub a b =>
      rw [hnd] at hwf
      dsimp only [SysNodeWellFormed] at hwf
      dsimp only
      rw [ih a hwf.1 f1' f2' (by omega) (by omega) (by omega),
          ih b hwf.2 f1' f2' (by omega) (by omega) (by omega)]
    | mul a b =>
      rw [hnd] at hwf
      dsimp only [SysNodeWellFormed] at hwf
      dsimp only
      rw [ih a hwf.1 f1' f2' (by omega) (by omega) (by omega),
          ih b hwf.2 f1' f2' (by omega) (by omega) (by omega)]
    | neg a =>
      rw [hnd] at hwf
      dsimp only [SysNodeWellFormed] at hwf
      dsimp only
      rw [ih a hwf f1' f2' (by omega) (by omega) (by omega)]

/-- Per-circuit OOD constraint & quotient identity postcondition enforced by `oodLoop`. -/
def OodLoopValid :
    SysCircuitList → OptIdxList → NatList → ExtGlList →
    OpenedRound → OpenedRound → PreprocessedOpt → OpenedRound →
    ExtGl → ExtGl → ExtGl → ExtGl → ExtGl → Prop
  | .nil, .nil, .nil, .nil, .nil, .nil, .noPreprocessed, .nil, _, _, _, _, _ => True
  | .nil, .nil, .nil, .nil, .nil, .nil, .somePreprocessed .nil, .nil, _, _, _, _, _ => True
  | .cons circ rest, .cons pi piRest, .cons ld ldRest, .cons naccp accRest,
    .cons (.cons main (.cons mainNext .nil)) s1Rest,
    .cons (.cons s2row (.cons s2next .nil)) s2Rest,
    prepOpt,
    .cons (.cons qrow .nil) qRest, accp, lch, fch, alpha, zeta =>
    let pr := oodPrepRows prepOpt pi
    let sel := traceSelectors zeta ld
    let height := glPow2 ld
    let inorm := glInv (glMul height sel.gen)
    let ctx : EvalCtx :=
      { main := main, mainNext := mainNext, prep := pr.prep, prepNext := pr.prepNext
        s2 := s2row, s2Next := s2next, publics := buildPublics lch fch accp naccp
        isf := sel.isFirst, isl := sel.isLast, ist := sel.isTrans }
    let comp := oodComposition circ.nodes circ.nodeCount circ.zeros circ.lookups
      circ.lookupGroupSize ctx lch fch accp naccp alpha inorm
    let qd := quotientDegreeOf circ.maxDegree
    let quot := quotientEval (reconstructExtRowFuel qd qrow) sel.zetaPowN extOne
    ld < 32 ∧
    pr.ok = 1 ∧
    extGlListLen main = circ.mainWidth ∧ extGlListLen mainNext = circ.mainWidth ∧
    extGlListLen s2row = circ.stage2Width ∧ extGlListLen s2next = circ.stage2Width ∧
    extGlListLen pr.prep = circ.prepWidth ∧ extGlListLen pr.prepNext = circ.prepWidth ∧
    extGlToExtGL (extSub sel.zetaPowN extOne) ≠ IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero ∧
    (circ.prepHeight ≠ 0 → height = circ.prepHeight) ∧
    extGlListLen qrow = 3 * qd ∧
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul (extGlToExtGL comp) (extGlToExtGL sel.invVan) =
      extGlToExtGL quot ∧
    OodLoopValid rest piRest ldRest accRest s1Rest s2Rest pr.nextOpt qRest naccp lch fch alpha zeta
  | _, _, _, _, _, _, _, _, _, _, _, _, _ => False

/-- **AIR + LogUp OOD Quotient Soundness (`CompressWrapPure.oodLoop`)**:
acceptance enforces `OodLoopValid` across every active circuit (width match, `ld < 32`,
`prepHeight` match, non-zero vanishing polynomial `ζ^(2^ld) - 1 ≠ 0`, and exact
`comp · invVan = quot` in `ExtGL`). -/
theorem oodLoop_sound :
    ∀ (circuits : SysCircuitList) (prepIndices : OptIdxList) (logDegrees : NatList)
      (accs : ExtGlList) (stage1 stage2 : OpenedRound) (prepOpt : PreprocessedOpt)
      (qOpened : OpenedRound) (accp lch fch alpha zeta : ExtGl),
      oodLoop circuits prepIndices logDegrees accs stage1 stage2 prepOpt qOpened
        accp lch fch alpha zeta = 1 →
      OodLoopValid circuits prepIndices logDegrees accs stage1 stage2 prepOpt qOpened
        accp lch fch alpha zeta
  | .nil, .nil, .nil, .nil, .nil, .nil, .noPreprocessed, .nil, _, _, _, _, _, _ => trivial
  | .nil, .nil, .nil, .nil, .nil, .nil, .somePreprocessed .nil, .nil, _, _, _, _, _, _ => trivial
  | .nil, .nil, .nil, .nil, .nil, .nil, .somePreprocessed (.cons _ _), .nil, _, _, _, _, _, hok => by
    simp [oodLoop] at hok
  | .nil, prepIndices, logDegrees, accs, stage1, stage2, prepOpt, qOpened, _, _, _, _, _, hok => by
    cases prepIndices <;> cases logDegrees <;> cases accs <;> cases stage1 <;>
      cases stage2 <;> cases qOpened <;> cases prepOpt
    all_goals first
      | (simp [oodLoop] at hok; done)
      | trivial
      | (cases ‹OpenedRound› <;> [trivial; simp [oodLoop] at hok])
  | .cons circ rest, prepIndices, logDegrees, accs, stage1, stage2, prepOpt, qOpened,
    accp, lch, fch, alpha, zeta, hok => by
    cases prepIndices with | nil => simp [oodLoop] at hok | cons pi piRest =>
    cases logDegrees with | nil => simp [oodLoop] at hok | cons ld ldRest =>
    cases accs with | nil => simp [oodLoop] at hok | cons naccp accRest =>
    cases stage1 with | nil => simp [oodLoop] at hok | cons m1 s1Rest =>
    cases m1 with | nil => simp [oodLoop] at hok | cons main m1r =>
    cases m1r with | nil => simp [oodLoop] at hok | cons mainNext m1rr =>
    cases m1rr with | cons _ _ => simp [oodLoop] at hok | nil =>
    cases stage2 with | nil => simp [oodLoop] at hok | cons m2 s2Rest =>
    cases m2 with | nil => simp [oodLoop] at hok | cons s2row m2r =>
    cases m2r with | nil => simp [oodLoop] at hok | cons s2next m2rr =>
    cases m2rr with | cons _ _ => simp [oodLoop] at hok | nil =>
    cases qOpened with | nil => simp [oodLoop] at hok | cons mq qRest =>
    cases mq with | nil => simp [oodLoop] at hok | cons qrow mqr =>
    cases mqr with | cons _ _ => simp [oodLoop] at hok | nil =>
    unfold oodLoop at hok
    dsimp only at hok
    by_cases hld : ld ≥ 32
    · rw [ite_eq_left hld] at hok; cases hok
    · rw [ite_eq_right hld] at hok
      by_cases hpr0 : (oodPrepRows prepOpt pi).ok = 0
      · simp [hpr0] at hok
      · have hpr1 : (oodPrepRows prepOpt pi).ok = 1 := by
          have : (oodPrepRows prepOpt pi).ok = 0 ∨ (oodPrepRows prepOpt pi).ok = 1 := by
            unfold oodPrepRows; cases pi with
            | noIdx => exact Or.inr rfl
            | someIdx _ =>
              cases prepOpt with
              | noPreprocessed => exact Or.inl rfl
              | somePreprocessed r =>
                cases r with
                | nil => exact Or.inl rfl
                | cons m _ =>
                  cases m with
                  | nil => exact Or.inl rfl
                  | cons _ mr =>
                    cases mr with
                    | nil => exact Or.inl rfl
                    | cons _ mrr =>
                      cases mrr with
                      | nil => exact Or.inr rfl
                      | cons _ _ => exact Or.inl rfl
          exact this.resolve_left hpr0
        rw [ite_eq_right (by rw [beq_iff_eq]; exact hpr0)] at hok
        by_cases hmw : (extGlListLen main != circ.mainWidth || extGlListLen mainNext != circ.mainWidth) = true
        · simp [hmw] at hok
        · simp only [hmw, Bool.false_eq_true, ↓reduceIte] at hok
          have hmwEq : extGlListLen main = circ.mainWidth ∧ extGlListLen mainNext = circ.mainWidth := by
            simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hmw; exact hmw
          by_cases hs2w : (extGlListLen s2row != circ.stage2Width || extGlListLen s2next != circ.stage2Width) = true
          · simp [hs2w] at hok
          · simp only [hs2w, Bool.false_eq_true, ↓reduceIte] at hok
            have hs2wEq : extGlListLen s2row = circ.stage2Width ∧ extGlListLen s2next = circ.stage2Width := by
              simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hs2w; exact hs2w
            by_cases hpw : (extGlListLen (oodPrepRows prepOpt pi).prep != circ.prepWidth ||
                extGlListLen (oodPrepRows prepOpt pi).prepNext != circ.prepWidth) = true
            · simp [hpw] at hok
            · simp only [hpw, Bool.false_eq_true, ↓reduceIte] at hok
              have hpwEq : extGlListLen (oodPrepRows prepOpt pi).prep = circ.prepWidth ∧
                  extGlListLen (oodPrepRows prepOpt pi).prepNext = circ.prepWidth := by
                simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hpw; exact hpw
              by_cases hvan : extIsZero (extSub (traceSelectors zeta ld).zetaPowN extOne) = 1
              · simp [hvan] at hok
              · rw [ite_eq_right (by rw [beq_iff_eq]; exact hvan)] at hok
                by_cases hph : (circ.prepHeight != 0 && glPow2 ld != circ.prepHeight) = true
                · simp [hph] at hok
                · simp only [hph, Bool.false_eq_true, ↓reduceIte] at hok
                  have hphImp : circ.prepHeight ≠ 0 → glPow2 ld = circ.prepHeight := by
                    intro hne
                    simp only [Bool.and_eq_true, bne_iff_ne, not_and, not_not] at hph
                    exact hph hne
                  by_cases hql : extGlListLen qrow ≠ quotientDegreeOf circ.maxDegree +
                      quotientDegreeOf circ.maxDegree + quotientDegreeOf circ.maxDegree
                  · rw [ite_eq_left (bne_iff_ne.mpr hql)] at hok; cases hok
                  · have hqlEq : extGlListLen qrow = 3 * quotientDegreeOf circ.maxDegree := by
                      have := Classical.not_not.mp hql; omega
                    rw [ite_eq_right (by rw [bne_iff_ne]; exact hql)] at hok
                    set ctx : EvalCtx :=
                      { main := main, mainNext := mainNext
                        prep := (oodPrepRows prepOpt pi).prep
                        prepNext := (oodPrepRows prepOpt pi).prepNext
                        s2 := s2row, s2Next := s2next
                        publics := buildPublics lch fch accp naccp
                        isf := (traceSelectors zeta ld).isFirst
                        isl := (traceSelectors zeta ld).isLast
                        ist := (traceSelectors zeta ld).isTrans }
                    set comp := oodComposition circ.nodes circ.nodeCount circ.zeros circ.lookups
                      circ.lookupGroupSize ctx lch fch accp naccp alpha
                      (glInv (glMul (glPow2 ld) (traceSelectors zeta ld).gen))
                    set quot := quotientEval (reconstructExtRowFuel (quotientDegreeOf circ.maxDegree) qrow)
                      (traceSelectors zeta ld).zetaPowN extOne
                    by_cases heq0 : extEq (extMul comp (traceSelectors zeta ld).invVan) quot = 0
                    · simp [heq0] at hok
                    · have heq1 : extEq (extMul comp (traceSelectors zeta ld).invVan) quot = 1 := by
                        have h01 : ∀ a b, extEq a b = 0 ∨ extEq a b = 1 := by
                          intro a b; unfold extEq; split
                          · split
                            · unfold glEq; split <;> [exact Or.inr rfl; exact Or.inl rfl]
                            · exact Or.inl rfl
                          · exact Or.inl rfl
                        exact (h01 _ _).resolve_left heq0
                      rw [ite_eq_right (by rw [beq_iff_eq]; exact heq0)] at hok
                      have hqId : IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.mul
                          (extGlToExtGL comp) (extGlToExtGL (traceSelectors zeta ld).invVan) =
                          extGlToExtGL quot := by
                        rw [← extGlToExtGL_mul]
                        exact (extGlToExtGL_eq_iff _ _).mp heq1
                      exact ⟨by omega, hpr1, hmwEq.1, hmwEq.2, hs2wEq.1, hs2wEq.2, hpwEq.1, hpwEq.2,
                        mt (extGlToExtGL_isZero_iff _).mpr hvan, hphImp, hqlEq, hqId,
                        oodLoop_sound rest piRest ldRest accRest s1Rest s2Rest
                          (oodPrepRows prepOpt pi).nextOpt qRest naccp lch fch alpha zeta hok⟩

/-- Strict monotonic, non-overlapping `MEMSEG = 16` closure-pair invariant on `BatchMessageList`. -/
def MemsegPairsValid (prevW prevB : U64Bytes) (count : Nat) : BatchMessageList → Prop
  | .nil => True
  | .cons _ .nil => False
  | .cons pull (.cons push rest) =>
    count < 65536 ∧
    glAdd (glValBytes pull.multiplicity) 1 = 0 ∧
    glValBytes push.multiplicity = 1 ∧
    ∃ pc pw pa qc qw qb : U64Bytes,
      pull.args = .cons pc (.cons pw (.cons pa .nil)) ∧
      push.args = .cons qc (.cons qw (.cons qb .nil)) ∧
      glValBytes pc = 16 ∧ glValBytes qc = 16 ∧
      qw = pw ∧
      u64BytesLe qb pa = 0 ∧
      (u64BytesLe pw prevW = 0 ∨ (pw = prevW ∧ u64BytesLe prevB pa = 1)) ∧
      MemsegPairsValid pw qb (count + 1) rest

/-- **MEMSEG Closure-Pair Soundness (`CompressWrapPure.assertClosurePairs`)**:
enforces even count (`≤ 65536` pairs), `(-1, +1)` multiplicities on channel `16`, matching
widths, strict positive intervals (`a < b`), and strict monotonic disjoint `(width, [a, b))`
ordering. -/
theorem assertClosurePairs_sound :
    ∀ (ms : BatchMessageList) (prevW prevB : U64Bytes) (count : Nat),
      assertClosurePairs ms prevW prevB count = 1 →
      MemsegPairsValid prevW prevB count ms
  | .nil, _, _, _, _ => trivial
  | .cons _ .nil, _, _, count, hok => by
    unfold assertClosurePairs at hok; split at hok <;> cases hok
  | .cons pull (.cons push rest), prevW, prevB, count, hok => by
    unfold assertClosurePairs at hok
    by_cases hcnt : count ≥ 65536
    · rw [ite_eq_left hcnt] at hok; cases hok
    · rw [ite_eq_right hcnt] at hok
      dsimp only at hok
      by_cases hmult : (glAdd (glValBytes pull.multiplicity) 1 != 0 ||
          glValBytes push.multiplicity != 1) = true
      · simp [hmult] at hok
      · simp only [hmult, Bool.false_eq_true, ↓reduceIte] at hok
        have hmultEq : glAdd (glValBytes pull.multiplicity) 1 = 0 ∧
            glValBytes push.multiplicity = 1 := by
          simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hmult; exact hmult
        cases hpArgs : pull.args with
        | nil => rw [hpArgs] at hok; cases hok
        | cons pc pr1 =>
          cases pr1 with
          | nil => rw [hpArgs] at hok; cases hok
          | cons pw pr2 =>
            cases pr2 with
            | nil => rw [hpArgs] at hok; cases hok
            | cons pa pr3 =>
              cases pr3 with
              | cons _ _ => rw [hpArgs] at hok; cases hok
              | nil =>
                cases hqArgs : push.args with
                | nil => rw [hpArgs, hqArgs] at hok; cases hok
                | cons qc qr1 =>
                  cases qr1 with
                  | nil => rw [hpArgs, hqArgs] at hok; cases hok
                  | cons qw qr2 =>
                    cases qr2 with
                    | nil => rw [hpArgs, hqArgs] at hok; cases hok
                    | cons qb qr3 =>
                      cases qr3 with
                      | cons _ _ => rw [hpArgs, hqArgs] at hok; cases hok
                      | nil =>
                        rw [hpArgs, hqArgs] at hok
                        dsimp only at hok
                        by_cases hch : (glValBytes pc != 16 || glValBytes qc != 16) = true
                        · simp [hch] at hok
                        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hok
                          have hchEq : glValBytes pc = 16 ∧ glValBytes qc = 16 := by
                            simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hch; exact hch
                          by_cases hqw : u64BytesEq qw pw = 0
                          · simp [hqw] at hok
                          · have hqwEq : qw = pw :=
                              (u64BytesEq_eq_one_iff qw pw).mp ((u64BytesEq_zero_or_one qw pw).resolve_left hqw)
                            rw [ite_eq_right (by rw [beq_iff_eq]; exact hqw)] at hok
                            by_cases hab : u64BytesLe qb pa = 1
                            · simp [hab] at hok
                            · have hab0 : u64BytesLe qb pa = 0 := by
                                have h01 : ∀ x y, u64BytesLe x y = 0 ∨ u64BytesLe x y = 1 := by
                                  intro x y; unfold u64BytesLe
                                  split
                                  · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                  · split
                                    · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                    · split
                                      · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                      · split
                                        · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                        · split
                                          · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                          · split
                                            · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                            · split
                                              · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                              · split <;> [exact Or.inr rfl; exact Or.inl rfl]
                                exact (h01 qb pa).resolve_right hab
                              rw [ite_eq_right (by rw [beq_iff_eq]; exact hab)] at hok
                              by_cases hord :
                                  (if u64BytesLe pw prevW == 0 then 1 else 0) +
                                    u64BytesEq pw prevW * u64BytesLe prevB pa = 1
                              · rw [ite_eq_left (beq_iff_eq.mpr hord)] at hok
                                have hordDisj : u64BytesLe pw prevW = 0 ∨ (pw = prevW ∧ u64BytesLe prevB pa = 1) := by
                                  by_cases hwu : u64BytesLe pw prevW = 0
                                  · exact Or.inl hwu
                                  · have hwuf : (u64BytesLe pw prevW == 0) = false := beq_false_of_ne hwu
                                    simp only [hwuf, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hord
                                    have hmul1 : u64BytesEq pw prevW = 1 ∧ u64BytesLe prevB pa = 1 := by
                                      rcases u64BytesEq_zero_or_one pw prevW with h1 | h1
                                      · rw [h1] at hord; simp at hord
                                      · rw [h1, Nat.one_mul] at hord; exact ⟨h1, hord⟩
                                    exact Or.inr ⟨(u64BytesEq_eq_one_iff pw prevW).mp hmul1.1, hmul1.2⟩
                                exact ⟨by omega, hmultEq.1, hmultEq.2,
                                  pc, pw, pa, qc, qw, qb, hpArgs, hqArgs,
                                  hchEq.1, hchEq.2, hqwEq, hab0, hordDisj,
                                  assertClosurePairs_sound rest pw qb (count + 1) hok⟩
                              · rw [ite_eq_right (by rw [beq_iff_eq]; exact hord)] at hok; cases hok

/-- Every circuit in `SysCircuitList` has `< 2^24` lookups. -/
def LookupsBounded : SysCircuitList → Prop
  | .nil => True
  | .cons c rest => sysLookupListLen c.lookups < 16777216 ∧ LookupsBounded rest

theorem lookupsCountOk_sound :
    ∀ cs : SysCircuitList, lookupsCountOk cs = 1 → LookupsBounded cs
  | .nil, _ => trivial
  | .cons c rest, hok => by
    unfold lookupsCountOk at hok
    by_cases hlt : sysLookupListLen c.lookups < 16777216
    · rw [ite_eq_left hlt] at hok
      exact ⟨hlt, lookupsCountOk_sound rest hok⟩
    · rw [ite_eq_right hlt] at hok; cases hok

/-- Exact total ROM-lane-weighted row count across all shards in `ShardHeaderList`. -/
def totalBatchWeightedRows (weights : NatList) : ShardHeaderList → Nat
  | .nil => 0
  | .cons h rest => (shardRowsCheck weights h.active h.logDegrees).snd + totalBatchWeightedRows weights rest

theorem batchRowsOk_sound (weights : NatList) :
    ∀ (headers : ShardHeaderList) (acc : Nat),
      acc ≤ maxBatchRows →
      batchRowsOk weights headers acc = 1 →
      acc + totalBatchWeightedRows weights headers ≤ maxBatchRows
  | .nil, acc, hacc, _ => by
    simpa [totalBatchWeightedRows] using hacc
  | .cons h rest, acc, _, hok => by
    unfold batchRowsOk at hok
    dsimp only at hok
    generalize hsr : shardRowsCheck weights h.active h.logDegrees = sr at hok
    by_cases hc : (sr.fst == 1 && decide (acc + sr.snd ≤ maxBatchRows)) = true
    · rw [ite_eq_left hc] at hok
      have hc' := hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
      have ih := batchRowsOk_sound weights rest (acc + sr.snd) hc'.2 hok
      simpa [totalBatchWeightedRows, hsr, Nat.add_assoc] using ih
    · rw [ite_eq_right hc] at hok; cases hok

/-- `target` appears in `NatList`. -/
def NatListMem (target : Nat) : NatList → Prop
  | .nil => False
  | .cons x rest => x = target ∨ NatListMem target rest

theorem natInList_eq_one_iff (xs : NatList) (target : Nat) :
    natInList xs target = 1 ↔ NatListMem target xs := by
  induction xs with
  | nil => simp [natInList, NatListMem]
  | cons x rest ih =>
    unfold natInList NatListMem
    by_cases hx : x = target
    · subst hx; simp
    · have hbf : (x == target) = false := beq_false_of_ne hx
      simp [hbf, hx, ih]

/-- Every closure pair `(pull, push)` in `ms` has `pull.args = [pc, pw, pa]` with
`glValBytes pw ∈ romWidths`. -/
def ClosureWidthsValid (romWidths : NatList) : BatchMessageList → Prop
  | .nil => True
  | .cons pull (.cons _ rest) =>
    ∃ pc pw pa, pull.args = .cons pc (.cons pw (.cons pa .nil)) ∧
      NatListMem (glValBytes pw) romWidths ∧
      ClosureWidthsValid romWidths rest
  | .cons _ .nil => False

/-- Number of `(pull, push)` pairs in a `BatchMessageList`. -/
def batchMessagePairCount : BatchMessageList → Nat
  | .nil => 0
  | .cons _ (.cons _ rest) => 1 + batchMessagePairCount rest
  | .cons _ .nil => 0

theorem assertClosureWidthsLoop_sound (romWidths : NatList) :
    ∀ (ms : BatchMessageList) (pairs : Nat),
      (assertClosureWidthsLoop ms romWidths pairs).fst = 1 →
      ClosureWidthsValid romWidths ms ∧
      (assertClosureWidthsLoop ms romWidths pairs).snd = pairs + batchMessagePairCount ms
  | .nil, pairs, _ => ⟨trivial, by simp [assertClosureWidthsLoop, batchMessagePairCount]⟩
  | .cons _ .nil, _, hok => by simp [assertClosureWidthsLoop] at hok
  | .cons pull (.cons push rest), pairs, hok => by
    unfold assertClosureWidthsLoop at hok ⊢
    dsimp only at hok ⊢
    cases hargs : pull.args with
    | nil => rw [hargs] at hok; cases hok
    | cons pc r1 =>
      cases r1 with
      | nil => rw [hargs] at hok; cases hok
      | cons pw r2 =>
        cases r2 with
        | nil => rw [hargs] at hok; cases hok
        | cons pa r3 =>
          cases r3 with
          | cons _ _ => rw [hargs] at hok; cases hok
          | nil =>
            rw [hargs] at hok
            dsimp only at hok ⊢
            by_cases hmem : natInList romWidths (glValBytes pw) = 1
            · rw [ite_eq_left (beq_iff_eq.mpr hmem)] at hok ⊢
              obtain ⟨hv, hcnt⟩ := assertClosureWidthsLoop_sound romWidths rest (pairs + 1) hok
              refine ⟨⟨pc, pw, pa, hargs, (natInList_eq_one_iff romWidths (glValBytes pw)).mp hmem, hv⟩, ?_⟩
              simp only [batchMessagePairCount, hcnt]
              omega
            · rw [ite_eq_right (by rw [beq_iff_eq]; exact hmem)] at hok; cases hok

private theorem ite_proj_zero_or_one {α : Type} (c : Prop) [Decidable c]
    (f : α → Nat) (a b : α) (ha : f a = 0 ∨ f a = 1) (hb : f b = 0 ∨ f b = 1) :
    f (if c then a else b) = 0 ∨ f (if c then a else b) = 1 := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha
  · rw [ite_eq_right h]; exact hb

private theorem ite_nat_zero_or_one (c : Prop) [Decidable c] (a b : Nat)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (if c then a else b) = 0 ∨ (if c then a else b) = 1 :=
  ite_proj_zero_or_one c id a b ha hb

private theorem ite_verifyShard_ok {c : Prop} [Decidable c] {t : VerifyShardOut}
    (h : (if c then ({ ok := 0, lastAcc := extZero } : VerifyShardOut) else t).ok = 1) :
    ¬ c ∧ t.ok = 1 := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

private theorem ite_verifyBatch_ok {c : Prop} [Decidable c] {t : VerifyBatchOut}
    (h : (if c then ({ ok := 0, claims := .nil } : VerifyBatchOut) else t).ok = 1) :
    ¬ c ∧ t.ok = 1 := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

private theorem ite_nat_zero_eq_one {c : Prop} [Decidable c] {t : Nat}
    (h : (if c then 0 else t) = 1) :
    ¬ c ∧ t = 1 := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; cases h
  · rw [ite_eq_right hc] at h; exact ⟨hc, h⟩

private theorem extIsZero_zero_or_one (a : ExtGl) :
    extIsZero a = 0 ∨ extIsZero a = 1 := by
  unfold extIsZero glIsZero
  apply ite_nat_zero_or_one _ _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ _ (Or.inl rfl)
  exact ite_nat_zero_or_one _ _ _ (Or.inr rfl) (Or.inl rfl)

/-- Every entry in `NatList` is a bit (`0` or `1`). -/
def AllBits : NatList → Prop
  | .nil => True
  | .cons b rest => (b = 0 ∨ b = 1) ∧ AllBits rest

theorem assertBits_zero_or_one : ∀ xs : NatList, assertBits xs = 0 ∨ assertBits xs = 1
  | .nil => Or.inr rfl
  | .cons b rest => by
    unfold assertBits
    exact ite_nat_zero_or_one _ _ _ (assertBits_zero_or_one rest) (Or.inl rfl)

theorem assertBits_sound : ∀ xs : NatList, assertBits xs = 1 → AllBits xs
  | .nil, _ => trivial
  | .cons b rest, hok => by
    unfold assertBits at hok
    by_cases hb : (b == 0 || b == 1) = true
    · rw [ite_eq_left hb] at hok
      have hb' : b = 0 ∨ b = 1 := by simpa [Bool.or_eq_true, beq_iff_eq] using hb
      exact ⟨hb', assertBits_sound rest hok⟩
    · rw [ite_eq_right hb] at hok; cases hok

/-- Every log-degree in `NatList` is `≤ 32`. -/
def AllLogDegreesLe32 : NatList → Prop
  | .nil => True
  | .cons ld rest => ld ≤ 32 ∧ AllLogDegreesLe32 rest

theorem assertLogDegreesOk_zero_or_one :
    ∀ xs : NatList, assertLogDegreesOk xs = 0 ∨ assertLogDegreesOk xs = 1
  | .nil => Or.inr rfl
  | .cons ld rest => by
    unfold assertLogDegreesOk
    exact ite_nat_zero_or_one _ _ _ (assertLogDegreesOk_zero_or_one rest) (Or.inl rfl)

theorem assertLogDegreesOk_sound :
    ∀ xs : NatList, assertLogDegreesOk xs = 1 → AllLogDegreesLe32 xs
  | .nil, _ => trivial
  | .cons ld rest, hok => by
    unfold assertLogDegreesOk at hok
    by_cases hle : ld ≤ 32
    · rw [ite_eq_left hle] at hok
      exact ⟨hle, assertLogDegreesOk_sound rest hok⟩
    · rw [ite_eq_right hle] at hok; cases hok

theorem assertSameNatList_zero_or_one :
    ∀ a b : NatList, assertSameNatList a b = 0 ∨ assertSameNatList a b = 1
  | .nil, .nil => Or.inr rfl
  | .nil, .cons _ _ => Or.inl rfl
  | .cons _ _, .nil => Or.inl rfl
  | .cons x ra, .cons y rb => by
    unfold assertSameNatList; dsimp only
    exact ite_nat_zero_or_one _ _ _ (assertSameNatList_zero_or_one ra rb) (Or.inl rfl)

theorem assertSameCap_zero_or_one :
    ∀ a b : DigestBytesList, assertSameCap a b = 0 ∨ assertSameCap a b = 1
  | .nil, .nil => Or.inr rfl
  | .nil, .cons _ _ => Or.inl rfl
  | .cons _ _, .nil => Or.inl rfl
  | .cons x ra, .cons y rb => by
    unfold assertSameCap; dsimp only
    exact ite_nat_zero_or_one _ _ _ (assertSameCap_zero_or_one ra rb) (Or.inl rfl)

theorem checkSecurityFloor_zero_or_one (p : SysParams) :
    checkSecurityFloor p = 0 ∨ checkSecurityFloor p = 1 := by
  unfold checkSecurityFloor
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  exact ite_nat_zero_or_one _ _ _ (Or.inl rfl) (Or.inr rfl)

theorem shardFiatShamir_ok_zero_or_one (input : ByteList) (shard : Nat) (s2 q : DigestBytesList)
    (accs : ExtGlList) :
    (shardFiatShamir input shard s2 q accs).ok = 0 ∨
    (shardFiatShamir input shard s2 q accs).ok = 1 := by
  unfold shardFiatShamir
  apply ite_proj_zero_or_one _ ShardFsOut.ok _ _ (Or.inl rfl)
  exact ite_proj_zero_or_one _ ShardFsOut.ok _ _ (Or.inl rfl) (Or.inr rfl)

theorem batchFiatShamir_ok_zero_or_one (tLimbs : U64List) (prepCap : DigestBytesList)
    (headers : ShardHeaderList) (messages : BatchMessageList) :
    (batchFiatShamir tLimbs prepCap headers messages).ok = 0 ∨
    (batchFiatShamir tLimbs prepCap headers messages).ok = 1 := by
  unfold batchFiatShamir
  apply ite_proj_zero_or_one _ BatchFsOut.ok _ _ (Or.inl rfl)
  exact ite_proj_zero_or_one _ BatchFsOut.ok _ _ (Or.inl rfl) (Or.inr rfl)

theorem claimsAcc_ok_zero_or_one :
    ∀ (acc : ExtGl) (claims : U64ListList) (lch fch : ExtGl),
      (claimsAcc acc claims lch fch).ok = 0 ∨ (claimsAcc acc claims lch fch).ok = 1
  | _, .nil, _, _ => Or.inr rfl
  | acc, .cons c rest, lch, fch => by
    unfold claimsAcc
    apply ite_proj_zero_or_one _ VerifyShardOut.ok _ _ (Or.inl rfl)
    exact ite_proj_zero_or_one _ VerifyShardOut.ok _ _ (Or.inl rfl)
      (claimsAcc_ok_zero_or_one _ rest lch fch)

theorem messagesAcc_ok_zero_or_one :
    ∀ (acc : ExtGl) (ms : BatchMessageList) (lch fch : ExtGl),
      (messagesAcc acc ms lch fch).ok = 0 ∨ (messagesAcc acc ms lch fch).ok = 1
  | _, .nil, _, _ => Or.inr rfl
  | acc, .cons m rest, lch, fch => by
    unfold messagesAcc
    exact ite_proj_zero_or_one _ VerifyShardOut.ok _ _ (Or.inl rfl)
      (messagesAcc_ok_zero_or_one _ rest lch fch)

theorem oodLoop_zero_or_one :
    ∀ (circuits : SysCircuitList) (prepIndices : OptIdxList) (logDegrees : NatList) (accs : ExtGlList)
      (stage1 stage2 : OpenedRound) (prepOpt : PreprocessedOpt) (qOpened : OpenedRound)
      (accp lch fch alpha zeta : ExtGl),
      oodLoop circuits prepIndices logDegrees accs stage1 stage2 prepOpt qOpened
        accp lch fch alpha zeta = 0 ∨
      oodLoop circuits prepIndices logDegrees accs stage1 stage2 prepOpt qOpened
        accp lch fch alpha zeta = 1
  | .nil, .nil, .nil, .nil, .nil, .nil, .noPreprocessed, .nil, _, _, _, _, _ => Or.inr rfl
  | .nil, .nil, .nil, .nil, .nil, .nil, .somePreprocessed .nil, .nil, _, _, _, _, _ => Or.inr rfl
  | .nil, .nil, .nil, .nil, .nil, .nil, .somePreprocessed (.cons _ _), .nil, _, _, _, _, _ => Or.inl rfl
  | .nil, pi, ld, accs, s1, s2, prepOpt, qO, _, _, _, _, _ => by
    cases pi <;> cases ld <;> cases accs <;> cases s1 <;> cases s2 <;> cases qO <;> cases prepOpt
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | (cases ‹OpenedRound› <;> [exact Or.inr rfl; exact Or.inl rfl])
  | .cons circ rest, pi, ld, accs, s1, s2, prepOpt, qO, accp, lch, fch, alpha, zeta => by
    cases pi with | nil => exact Or.inl rfl | cons pi1 piR =>
    cases ld with | nil => exact Or.inl rfl | cons ld1 ldR =>
    cases accs with | nil => exact Or.inl rfl | cons a1 aR =>
    cases s1 with | nil => exact Or.inl rfl | cons m1 s1R =>
    cases m1 with | nil => exact Or.inl rfl | cons mn m1r =>
    cases m1r with | nil => exact Or.inl rfl | cons mnN m1rr =>
    cases m1rr with | cons _ _ => exact Or.inl rfl | nil =>
    cases s2 with | nil => exact Or.inl rfl | cons m2 s2R =>
    cases m2 with | nil => exact Or.inl rfl | cons s2r m2r =>
    cases m2r with | nil => exact Or.inl rfl | cons s2n m2rr =>
    cases m2rr with | cons _ _ => exact Or.inl rfl | nil =>
    cases qO with | nil => exact Or.inl rfl | cons mq qR =>
    cases mq with | nil => exact Or.inl rfl | cons qr mqr =>
    cases mqr with | cons _ _ => exact Or.inl rfl | nil =>
    unfold oodLoop; dsimp only
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    exact ite_nat_zero_or_one _ _ _ (Or.inl rfl)
      (oodLoop_zero_or_one rest piR ldR aR s1R s2R _ qR a1 lch fch alpha zeta)

private theorem verifyCommitMulti_zero_or_one :
    ∀ (steps : CommitPhaseMultiStepList) (comms : MerkleCapList) (allRows : U64List3)
      (indices : BitListList) (logCur maxLogArity : Nat),
      verifyCommitMulti steps comms allRows indices logCur maxLogArity = 0 ∨
      verifyCommitMulti steps comms allRows indices logCur maxLogArity = 1
  | .nil, .nil, _, _, _, _ => Or.inr rfl
  | .nil, .cons _ _, _, _, _, _ => Or.inl rfl
  | .cons _ _, .nil, _, _, _, _ => Or.inl rfl
  | .cons st srest, .cons c crest, allRows, indices, logCur, maxLogArity => by
    unfold verifyCommitMulti; dsimp only
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    exact verifyCommitMulti_zero_or_one srest crest _ _ _ maxLogArity

theorem pcsFriVerify_zero_or_one (postZetaInput : ByteList)
    (stage1 stage2 qOpened : OpenedRound) (prepOpt : PreprocessedOpt)
    (opening : FriProof) (s1c s2c qc prepCommit : DigestBytesList)
    (prepIndices : OptIdxList) (logDegrees : NatList) (zeta : ExtGl)
    (logBlowup logFinalPolyLen maxLogArity numQueries commitPowBits queryPowBits : Nat) :
    pcsFriVerify postZetaInput stage1 stage2 qOpened prepOpt opening s1c s2c qc prepCommit
      prepIndices logDegrees zeta logBlowup logFinalPolyLen maxLogArity numQueries
      commitPowBits queryPowBits = 0 ∨
    pcsFriVerify postZetaInput stage1 stage2 qOpened prepOpt opening s1c s2c qc prepCommit
      prepIndices logDegrees zeta logBlowup logFinalPolyLen maxLogArity numQueries
      commitPowBits queryPowBits = 1 := by
  unfold pcsFriVerify
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
  cases opening.inputOpenings with
  | nil => exact Or.inl rfl
  | cons boS1 r1 =>
    cases r1 with
    | nil => exact Or.inl rfl
    | cons boS2 r2 =>
      cases r2 with
      | nil => exact Or.inl rfl
      | cons boQ io3 =>
        dsimp only
        apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
        apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
        apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
        apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
        apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
        exact verifyCommitMulti_zero_or_one _ _ _ _ _ _

theorem lookupsCountOk_zero_or_one :
    ∀ cs : SysCircuitList, lookupsCountOk cs = 0 ∨ lookupsCountOk cs = 1
  | .nil => Or.inr rfl
  | .cons c rest => by
    unfold lookupsCountOk
    exact ite_nat_zero_or_one _ _ _ (lookupsCountOk_zero_or_one rest) (Or.inl rfl)

theorem batchRowsOk_zero_or_one (weights : NatList) :
    ∀ (headers : ShardHeaderList) (acc : Nat),
      batchRowsOk weights headers acc = 0 ∨ batchRowsOk weights headers acc = 1
  | .nil, _ => Or.inr rfl
  | .cons h rest, acc => by
    unfold batchRowsOk
    exact ite_nat_zero_or_one _ _ _ (batchRowsOk_zero_or_one weights rest _) (Or.inl rfl)

theorem assertClosurePairs_zero_or_one :
    ∀ (ms : BatchMessageList) (prevW prevB : U64Bytes) (count : Nat),
      assertClosurePairs ms prevW prevB count = 0 ∨ assertClosurePairs ms prevW prevB count = 1
  | .nil, _, _, _ => Or.inr rfl
  | .cons pull rest1, prevW, prevB, count => by
    unfold assertClosurePairs
    apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
    cases rest1 with
    | nil => exact Or.inl rfl
    | cons push rest =>
      dsimp only
      apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
      cases pull.args with | nil => exact Or.inl rfl | cons pc r1 =>
      cases r1 with | nil => exact Or.inl rfl | cons pw r2 =>
      cases r2 with | nil => exact Or.inl rfl | cons pa r3 =>
      cases r3 with | cons _ _ => exact Or.inl rfl | nil =>
      cases push.args with | nil => exact Or.inl rfl | cons qc q1 =>
      cases q1 with | nil => exact Or.inl rfl | cons qw q2 =>
      cases q2 with | nil => exact Or.inl rfl | cons qb q3 =>
      cases q3 with | cons _ _ => exact Or.inl rfl | nil =>
      dsimp only
      apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
      apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
      apply ite_nat_zero_or_one _ _ _ (Or.inl rfl)
      exact ite_nat_zero_or_one _ _ _ (assertClosurePairs_zero_or_one rest pw qb (count + 1)) (Or.inl rfl)

theorem assertClosureWidthsLoop_fst_zero_or_one (romWidths : NatList) :
    ∀ (ms : BatchMessageList) (pairs : Nat),
      (assertClosureWidthsLoop ms romWidths pairs).fst = 0 ∨
      (assertClosureWidthsLoop ms romWidths pairs).fst = 1
  | .nil, _ => Or.inr rfl
  | .cons _ .nil, _ => Or.inl rfl
  | .cons pull (.cons _ rest), pairs => by
    unfold assertClosureWidthsLoop; dsimp only
    cases pull.args with | nil => exact Or.inl rfl | cons _ r1 =>
    cases r1 with | nil => exact Or.inl rfl | cons pw r2 =>
    cases r2 with | nil => exact Or.inl rfl | cons _ r3 =>
    cases r3 with | cons _ _ => exact Or.inl rfl | nil =>
    dsimp only
    exact ite_proj_zero_or_one _ NatPair.fst _ _
      (assertClosureWidthsLoop_fst_zero_or_one romWidths rest (pairs + 1)) (Or.inl rfl)

theorem verifyShardWithFloor_ok_zero_or_one (ef : Nat) (sys : SysKey) (header : ShardHeader)
    (shard : Nat) (proof : ShardProof) (input : ByteList) (lch fch : ExtGl) :
    (verifyShardWithFloor ef sys header shard proof input lch fch).ok = 0 ∨
    (verifyShardWithFloor ef sys header shard proof input lch fch).ok = 1 := by
  unfold verifyShardWithFloor
  repeat apply ite_proj_zero_or_one _ VerifyShardOut.ok _ _ (Or.inl rfl)
  exact Or.inr rfl

theorem verifyShardsWithFloor_ok_zero_or_one (ef : Nat) (sys : SysKey) :
    ∀ (headers : ShardHeaderList) (proofs : ShardProofList) (shard : Nat)
      (input : ByteList) (lch fch acc : ExtGl),
      (verifyShardsWithFloor ef sys headers proofs shard input lch fch acc).ok = 0 ∨
      (verifyShardsWithFloor ef sys headers proofs shard input lch fch acc).ok = 1
  | .nil, .nil, _, _, _, _, _ => Or.inr rfl
  | .nil, .cons _ _, _, _, _, _, _ => Or.inl rfl
  | .cons _ _, .nil, _, _, _, _, _ => Or.inl rfl
  | .cons h hrest, .cons p prest, shard, input, lch, fch, acc => by
    unfold verifyShardsWithFloor; dsimp only
    exact ite_proj_zero_or_one _ VerifyShardOut.ok _ _ (Or.inl rfl)
      (verifyShardsWithFloor_ok_zero_or_one ef sys hrest prest (shard + 1) input lch fch _)

theorem readSystem_ok_zero_or_one (s : ByteList) :
    (readSystem s).ok = 0 ∨ (readSystem s).ok = 1 := by
  unfold readSystem
  apply ite_proj_zero_or_one _ ParseSysKey.ok _ _ (Or.inl rfl)
  apply ite_proj_zero_or_one _ ParseSysKey.ok _ _ (Or.inl rfl)
  cases (readOptIdxN _ _ _ _).rest with
  | cons _ _ => exact Or.inl rfl
  | nil => exact Or.inr rfl

theorem readClaims_ok_zero_or_one (s : ByteList) :
    (readClaims s).ok = 0 ∨ (readClaims s).ok = 1 := by
  unfold readClaims
  apply ite_proj_zero_or_one _ ParseU64ListList.ok _ _ (Or.inl rfl)
  apply ite_proj_zero_or_one _ ParseU64ListList.ok _ _ (Or.inl rfl)
  cases (readClaimsN (readCount s).rest (readCount s).val).rest with
  | nil => exact readClaimsN_ok_zero_or_one _ _
  | cons _ _ => exact Or.inl rfl

theorem readBatchProof_ok_zero_or_one (s : ByteList) :
    (readBatchProof s).ok = 0 ∨ (readBatchProof s).ok = 1 := by
  unfold readBatchProof
  apply ite_proj_zero_or_one _ ParseBatchProof.ok _ _ (Or.inl rfl)
  apply ite_proj_zero_or_one _ ParseBatchProof.ok _ _ (Or.inl rfl)
  apply ite_proj_zero_or_one _ ParseBatchProof.ok _ _ (Or.inl rfl)
  cases (readShardProofVec (readBatchMessageVec (readShardHeaderVec s).rest).rest).rest with
  | cons _ _ => exact Or.inl rfl
  | nil => exact Or.inr rfl

theorem verifyBatchWithFloor_ok_zero_or_one (ef : Nat) (sys : SysKey) (batch : BatchProof) :
    (verifyBatchWithFloor ef sys batch).ok = 0 ∨ (verifyBatchWithFloor ef sys batch).ok = 1 := by
  unfold verifyBatchWithFloor
  repeat apply ite_proj_zero_or_one _ VerifyBatchOut.ok _ _ (Or.inl rfl)
  exact Or.inr rfl

/-! ### Complete Production `verifyShard`, `verifyBatch` & `verifyRootBytes` Soundness -/

/-- Complete verification postcondition for a single production shard (`verifyShard`). -/
structure ShardAccepted (sys : SysKey) (header : ShardHeader) (shard : Nat) (proof : ShardProof)
    (input : ByteList) (lch fch : ExtGl) : Prop where
  capHeight_zero : sys.params.capHeight = 0
  maxLogArity_bounds : 1 ≤ sys.params.maxLogArity ∧ sys.params.maxLogArity ≤ 3
  securityFloor : SecurityFloorHolds sys.params
  numCircuits_pos : extGlListLen proof.intermediateAccs ≠ 0
  active_bits : AllBits proof.active
  logDegrees_ok : AllLogDegreesLe32 proof.logDegrees
  active_match : header.active = proof.active
  stage1_match : header.stage1 = proof.commitments.stage1
  logDegrees_match : header.logDegrees = proof.logDegrees
  active_len : natListLen proof.active = sysCircuitListLen sys.circuits
  countOnes_match : countOnes proof.active = natListLen proof.logDegrees
  prep_presence_match :
    (sys.prepCommit = .noCommit ∧ proof.preprocessedOpened = .noPreprocessed) ∨
    (∃ c p, sys.prepCommit = .someCommit c ∧ proof.preprocessedOpened = .somePreprocessed p)
  fs_ok : (shardFiatShamir input shard proof.commitments.stage2 proof.commitments.quotient
            proof.intermediateAccs).ok = 1
  zeta_nonzero : extGlToExtGL (shardFiatShamir input shard proof.commitments.stage2
    proof.commitments.quotient proof.intermediateAccs).zeta ≠
    IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero
  claimsAcc_ok : (claimsAcc extZero header.claims lch fch).ok = 1
  ood_valid :
    let ac := selectActiveCircuits sys.circuits proof.active
    let ap := selectActivePrep sys.prepIndices proof.active
    let fs := shardFiatShamir input shard proof.commitments.stage2 proof.commitments.quotient
      proof.intermediateAccs
    let acc0Res := claimsAcc extZero header.claims lch fch
    OodLoopValid ac.circuits ap.prepIndices proof.logDegrees proof.intermediateAccs
      proof.stage1Opened proof.stage2Opened proof.preprocessedOpened proof.quotientOpened
      acc0Res.lastAcc lch fch fs.alpha fs.zeta
  pcs_accepted :
    let ap := selectActivePrep sys.prepIndices proof.active
    let fs := shardFiatShamir input shard proof.commitments.stage2 proof.commitments.quotient
      proof.intermediateAccs
    PcsFriAccepted fs.postZetaInput proof.stage1Opened proof.stage2Opened
      proof.quotientOpened proof.preprocessedOpened proof.openingProof
      proof.commitments.stage1 proof.commitments.stage2 proof.commitments.quotient
      (optCommitCap sys.prepCommit) ap.prepIndices proof.logDegrees fs.zeta
      sys.params.logBlowup sys.params.logFinalPolyLen sys.params.maxLogArity
      sys.params.numQueries sys.params.commitPowBits sys.params.queryPowBits
  lastAcc_eq : (verifyShard sys header shard proof input lch fch).lastAcc = lastAcc proof.intermediateAccs

/-- **Headline Production Single-Shard Soundness (`verifyShard`)**:
acceptance (`ok = 1`) implies all in-circuit security-floor assertions, active-circuit /
preprocessed-commitment consistency, non-zero OOD challenge `zeta`, per-circuit AIR OOD
quotient & LogUp checks (`OodLoopValid`), full batched MMCS + multi-arity FRI + zero-PoW
canonicalized PCS acceptance (`PcsFriAccepted`), and exact `lastAcc` return value. -/
theorem verifyShard_sound {sys : SysKey} {header : ShardHeader} {shard : Nat}
    {proof : ShardProof} {input : ByteList} {lch fch : ExtGl}
    (hok : (verifyShard sys header shard proof input lch fch).ok = 1) :
    ShardAccepted sys header shard proof input lch fch := by
  unfold verifyShard verifyShardWithFloor at hok
  obtain ⟨hcap, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨har, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hpar, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hfl, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hnc, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hs1l, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hs2l, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hql, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hbits, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨halen, hok⟩ := ite_verifyShard_ok hok
  generalize hac : selectActiveCircuits sys.circuits proof.active = ac at hok
  generalize hap : selectActivePrep sys.prepIndices proof.active = ap at hok
  obtain ⟨hacp, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hacl, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hactEq, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hs1Eq, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hldEq, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hldOk, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hco, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hpm, hok⟩ := ite_verifyShard_ok hok
  generalize hfs : shardFiatShamir input shard proof.commitments.stage2
    proof.commitments.quotient proof.intermediateAccs = fs at hok
  obtain ⟨hfsRaw, hok⟩ := ite_verifyShard_ok hok
  generalize hacc0 : claimsAcc extZero header.claims lch fch = acc0Res at hok
  obtain ⟨hacc0Ok, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hood, hok⟩ := ite_verifyShard_ok hok
  obtain ⟨hpcs, _⟩ := ite_verifyShard_ok hok
  have hcap0 : sys.params.capHeight = 0 := by simpa [bne_iff_ne] using hcap
  have har' : 1 ≤ sys.params.maxLogArity ∧ sys.params.maxLogArity ≤ 3 := by
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at har; omega
  have hfl1 : checkSecurityFloor sys.params = 1 := by
    have hfl' := hfl
    simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true, not_and] at hfl'
    exact (checkSecurityFloor_zero_or_one sys.params).resolve_left (hfl' (by decide))
  have hnc0 : extGlListLen proof.intermediateAccs ≠ 0 := by simpa [beq_iff_eq] using hnc
  have hbits1 : assertBits proof.active = 1 :=
    (assertBits_zero_or_one proof.active).resolve_left (by simpa [beq_iff_eq] using hbits)
  have halenEq : natListLen proof.active = sysCircuitListLen sys.circuits := by
    simpa [bne_iff_ne] using halen
  have hactMatch : header.active = proof.active :=
    (assertSameNatList_eq_one_iff _ _).mp
      ((assertSameNatList_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hactEq))
  have hs1Match : header.stage1 = proof.commitments.stage1 :=
    (assertSameCap_eq_one_iff _ _).mp
      ((assertSameCap_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hs1Eq))
  have hldMatch : header.logDegrees = proof.logDegrees :=
    (assertSameNatList_eq_one_iff _ _).mp
      ((assertSameNatList_zero_or_one _ _).resolve_left (by simpa [beq_iff_eq] using hldEq))
  have hldOk1 : assertLogDegreesOk proof.logDegrees = 1 :=
    (assertLogDegreesOk_zero_or_one _).resolve_left (by simpa [beq_iff_eq] using hldOk)
  have hcoEq : countOnes proof.active = natListLen proof.logDegrees := by
    simpa [bne_iff_ne] using hco
  have hprepMatch :
      (sys.prepCommit = .noCommit ∧ proof.preprocessedOpened = .noPreprocessed) ∨
      (∃ c p, sys.prepCommit = .someCommit c ∧ proof.preprocessedOpened = .somePreprocessed p) := by
    cases hpc : sys.prepCommit <;> cases hpo : proof.preprocessedOpened
    · exact Or.inl ⟨rfl, rfl⟩
    · simp [hpc, hpo] at hpm
    · simp [hpc, hpo] at hpm
    · exact Or.inr ⟨_, _, rfl, rfl⟩
  have hfsOk : fs.ok ≠ 0 ∧ extIsZero fs.zeta ≠ 1 := by
    simpa [Bool.or_eq_true, beq_iff_eq, not_or] using hfsRaw
  have hfs1 : fs.ok = 1 := by
    have h01 := shardFiatShamir_ok_zero_or_one input shard
      proof.commitments.stage2 proof.commitments.quotient proof.intermediateAccs
    rw [hfs] at h01
    exact h01.resolve_left hfsOk.1
  have hzetaNe : extGlToExtGL fs.zeta ≠
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero := fun hz =>
    hfsOk.2 ((extGlToExtGL_isZero_iff fs.zeta).mpr hz)
  have hacc0_1 : acc0Res.ok = 1 := by
    have h01 := claimsAcc_ok_zero_or_one extZero header.claims lch fch
    rw [hacc0] at h01
    exact h01.resolve_left (by simpa [beq_iff_eq] using hacc0Ok)
  have hood1 : oodLoop ac.circuits ap.prepIndices proof.logDegrees
      proof.intermediateAccs proof.stage1Opened proof.stage2Opened
      proof.preprocessedOpened proof.quotientOpened
      acc0Res.lastAcc lch fch fs.alpha fs.zeta = 1 :=
    (oodLoop_zero_or_one _ _ _ _ _ _ _ _ _ _ _ _ _).resolve_left
      (by simpa [beq_iff_eq] using hood)
  have hpcs1 : pcsFriVerify fs.postZetaInput proof.stage1Opened
      proof.stage2Opened proof.quotientOpened proof.preprocessedOpened
      proof.openingProof proof.commitments.stage1 proof.commitments.stage2
      proof.commitments.quotient (optCommitCap sys.prepCommit)
      ap.prepIndices proof.logDegrees fs.zeta sys.params.logBlowup
      sys.params.logFinalPolyLen sys.params.maxLogArity
      sys.params.numQueries sys.params.commitPowBits
      sys.params.queryPowBits = 1 :=
    (pcsFriVerify_zero_or_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).resolve_left
      (by simpa [beq_iff_eq] using hpcs)
  have hlastEq : (verifyShard sys header shard proof input lch fch).lastAcc =
      lastAcc proof.intermediateAccs := by
    unfold verifyShard verifyShardWithFloor
    rw [ite_eq_right hcap, ite_eq_right har, ite_eq_right hpar, ite_eq_right hfl,
        ite_eq_right hnc, ite_eq_right hs1l, ite_eq_right hs2l, ite_eq_right hql,
        ite_eq_right hbits, ite_eq_right halen, hac, hap,
        ite_eq_right hacp, ite_eq_right hacl, ite_eq_right hactEq, ite_eq_right hs1Eq,
        ite_eq_right hldEq, ite_eq_right hldOk, ite_eq_right hco, ite_eq_right hpm,
        hfs, ite_eq_right hfsRaw, hacc0, ite_eq_right hacc0Ok,
        ite_eq_right hood, ite_eq_right hpcs]
  exact
    { capHeight_zero := hcap0
      maxLogArity_bounds := har'
      securityFloor := checkSecurityFloor_sound hfl1
      numCircuits_pos := hnc0
      active_bits := assertBits_sound proof.active hbits1
      logDegrees_ok := assertLogDegreesOk_sound proof.logDegrees hldOk1
      active_match := hactMatch
      stage1_match := hs1Match
      logDegrees_match := hldMatch
      active_len := halenEq
      countOnes_match := hcoEq
      prep_presence_match := hprepMatch
      fs_ok := by rw [hfs]; exact hfs1
      zeta_nonzero := by rw [hfs]; exact hzetaNe
      claimsAcc_ok := by rw [hacc0]; exact hacc0_1
      ood_valid := by
        dsimp only
        rw [hac, hap, hfs, hacc0]
        exact oodLoop_sound _ _ _ _ _ _ _ _ _ _ _ _ _ hood1
      pcs_accepted := by
        dsimp only
        rw [hap, hfs]
        exact pcsFriVerify_sound hpcs1
      lastAcc_eq := hlastEq }

/-- Exact running LogUp accumulator sum over a sequence of shard proofs starting at `acc`. -/
def foldShardAccs (acc : ExtGl) : ShardProofList → ExtGl
  | .nil => acc
  | .cons p prest => foldShardAccs (extAdd acc (lastAcc p.intermediateAccs)) prest

/-- Every `(header, proof)` pair in `(headers, proofs)` passes full production `ShardAccepted`. -/
def ShardsAllAccepted (sys : SysKey) :
    ShardHeaderList → ShardProofList → Nat → ByteList → ExtGl → ExtGl → Prop
  | .nil, .nil, _, _, _, _ => True
  | .cons h hrest, .cons p prest, shard, input, lch, fch =>
    ShardAccepted sys h shard p input lch fch ∧
    ShardsAllAccepted sys hrest prest (shard + 1) input lch fch
  | _, _, _, _, _, _ => False

theorem verifyShards_sound (sys : SysKey) :
    ∀ (headers : ShardHeaderList) (proofs : ShardProofList) (shard : Nat)
      (input : ByteList) (lch fch acc : ExtGl),
      (verifyShards sys headers proofs shard input lch fch acc).ok = 1 →
      ShardsAllAccepted sys headers proofs shard input lch fch ∧
      (verifyShards sys headers proofs shard input lch fch acc).lastAcc =
        foldShardAccs acc proofs
  | .nil, .nil, _, _, _, _, acc, _ =>
    ⟨trivial, rfl⟩
  | .nil, .cons _ _, _, _, _, _, _, hok => by simp [verifyShards, verifyShardsWithFloor] at hok
  | .cons _ _, .nil, _, _, _, _, _, hok => by simp [verifyShards, verifyShardsWithFloor] at hok
  | .cons h hrest, .cons p prest, shard, input, lch, fch, acc, hok => by
    unfold verifyShards verifyShardsWithFloor at hok ⊢
    dsimp only at hok ⊢
    by_cases hr0 : (verifyShardWithFloor 1 sys h shard p input lch fch).ok = 0
    · rw [ite_eq_left (beq_iff_eq.mpr hr0)] at hok; cases hok
    · have hr1 : (verifyShard sys h shard p input lch fch).ok = 1 :=
        (verifyShardWithFloor_ok_zero_or_one 1 sys h shard p input lch fch).resolve_left hr0
      rw [ite_eq_right (by rw [beq_iff_eq]; exact hr0)] at hok ⊢
      have hsa := verifyShard_sound hr1
      obtain ⟨hrestAcc, hrestLast⟩ := verifyShards_sound sys hrest prest (shard + 1) input lch fch
        (extAdd acc (verifyShardWithFloor 1 sys h shard p input lch fch).lastAcc) hok
      refine ⟨⟨hsa, hrestAcc⟩, ?_⟩
      unfold verifyShards at hrestLast
      rw [hrestLast]
      have hl : (verifyShardWithFloor 1 sys h shard p input lch fch).lastAcc = lastAcc p.intermediateAccs :=
        hsa.lastAcc_eq
      rw [hl]; rfl

/-- Complete verification postcondition for a production multi-shard batch (`verifyBatch`). -/
structure BatchAccepted (sys : SysKey) (batch : BatchProof) : Prop where
  numShards_bounds : 1 ≤ shardHeaderListLen batch.headers ∧ shardHeaderListLen batch.headers ≤ 65536
  proofs_len_match : shardProofListLen batch.proofs = shardHeaderListLen batch.headers
  capHeight_zero : sys.params.capHeight = 0
  maxLogArity_bounds : 1 ≤ sys.params.maxLogArity ∧ sys.params.maxLogArity ≤ 3
  securityFloor : SecurityFloorHolds sys.params
  lookups_bounded : LookupsBounded sys.circuits
  batchRows_bounded :
    totalBatchWeightedRows (circuitRowWeights sys.circuits) batch.headers ≤ maxBatchRows
  memseg_pairs_valid : MemsegPairsValid u64Zero u64Zero 0 batch.messages
  closure_widths_valid : ClosureWidthsValid (systemRomWidths sys.circuits) batch.messages
  closure_pairs_bounded :
    batchMessagePairCount batch.messages ≤
      shardHeaderListLen batch.headers * natListLen (systemRomWidths sys.circuits)
  batchFs_ok :
    (batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit)
      batch.headers batch.messages).ok = 1
  messagesAcc_ok :
    let bfs := batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit)
      batch.headers batch.messages
    (messagesAcc extZero batch.messages bfs.lch bfs.fch).ok = 1
  shards_accepted :
    let bfs := batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit)
      batch.headers batch.messages
    ShardsAllAccepted sys batch.headers batch.proofs 0 bfs.input bfs.lch bfs.fch
  logup_global_closure :
    let bfs := batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit)
      batch.headers batch.messages
    let mAcc := messagesAcc extZero batch.messages bfs.lch bfs.fch
    extGlToExtGL (foldShardAccs mAcc.lastAcc batch.proofs) =
      IxCC.AiurBackend.CompressionIntrinsicsProof.ExtGL.zero
  claims_eq : (verifyBatch sys batch).claims = batchClaims batch.headers

/-- **Headline Production Multi-Shard Batch Soundness (`verifyBatch`)**:
acceptance (`ok = 1`) implies non-empty bounded shard count (`1 ≤ numShards ≤ 65536`),
all production security-floor assertions (via the verified first shard), `< 2^24` lookups
per circuit, ROM-lane-weighted total batch row count `≤ 2^39`, strict monotonic disjoint
`MEMSEG = 16` closure pairs over declared ROM widths, valid batch Fiat–Shamir transcript,
full `ShardAccepted` on every shard, global LogUp running-sum closure (`= 0 ∈ GF(p_GL^3)`),
and exact extracted `batchClaims`. -/
theorem verifyBatch_sound {sys : SysKey} {batch : BatchProof}
    (hok : (verifyBatch sys batch).ok = 1) :
    BatchAccepted sys batch := by
  unfold verifyBatch verifyBatchWithFloor at hok
  dsimp only at hok
  obtain ⟨hns, hok⟩ := ite_verifyBatch_ok hok
  obtain ⟨hplen, hok⟩ := ite_verifyBatch_ok hok
  obtain ⟨hlk, hok⟩ := ite_verifyBatch_ok hok
  obtain ⟨hbr, hok⟩ := ite_verifyBatch_ok hok
  obtain ⟨hcp, hok⟩ := ite_verifyBatch_ok hok
  generalize hcw : assertClosureWidthsLoop batch.messages (systemRomWidths sys.circuits) 0 = cw at hok
  obtain ⟨hcwRaw, hok⟩ := ite_verifyBatch_ok hok
  generalize hbfs : batchFiatShamir sys.transcriptLimbs (optCommitCap sys.prepCommit)
    batch.headers batch.messages = bfs at hok
  obtain ⟨hbfsOk, hok⟩ := ite_verifyBatch_ok hok
  generalize hmAcc : messagesAcc extZero batch.messages bfs.lch bfs.fch = mAcc at hok
  obtain ⟨hmAccOk, hok⟩ := ite_verifyBatch_ok hok
  generalize htot : verifyShardsWithFloor 1 sys batch.headers batch.proofs 0
    bfs.input bfs.lch bfs.fch mAcc.lastAcc = total at hok
  obtain ⟨htotRaw, _⟩ := ite_verifyBatch_ok hok
  have hnsB : 1 ≤ shardHeaderListLen batch.headers ∧ shardHeaderListLen batch.headers ≤ 65536 := by
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hns; omega
  have hplenEq : shardProofListLen batch.proofs = shardHeaderListLen batch.headers := by
    simpa [bne_iff_ne] using hplen
  have hlk1 : lookupsCountOk sys.circuits = 1 :=
    (lookupsCountOk_zero_or_one sys.circuits).resolve_left (by simpa [beq_iff_eq] using hlk)
  have hbr1 : batchRowsOk (circuitRowWeights sys.circuits) batch.headers 0 = 1 :=
    (batchRowsOk_zero_or_one _ _ _).resolve_left (by simpa [beq_iff_eq] using hbr)
  have hcp1 : assertClosurePairs batch.messages u64Zero u64Zero 0 = 1 :=
    (assertClosurePairs_zero_or_one _ _ _ _).resolve_left (by simpa [beq_iff_eq] using hcp)
  have hcwOk : cw.fst ≠ 0 ∧ ¬ cw.snd > shardHeaderListLen batch.headers * natListLen (systemRomWidths sys.circuits) := by
    simpa [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] using hcwRaw
  have hcw1 : cw.fst = 1 := by
    have h01 := assertClosureWidthsLoop_fst_zero_or_one (systemRomWidths sys.circuits) batch.messages 0
    rw [hcw] at h01
    exact h01.resolve_left hcwOk.1
  have hcwSnd : cw.snd ≤ shardHeaderListLen batch.headers * natListLen (systemRomWidths sys.circuits) := by
    omega
  obtain ⟨hcwValid, hcwCnt⟩ := assertClosureWidthsLoop_sound (systemRomWidths sys.circuits)
    batch.messages 0 (by rw [hcw]; exact hcw1)
  rw [hcw, Nat.zero_add] at hcwCnt
  have hbfs1 : bfs.ok = 1 := by
    have h01 := batchFiatShamir_ok_zero_or_one sys.transcriptLimbs (optCommitCap sys.prepCommit)
      batch.headers batch.messages
    rw [hbfs] at h01
    exact h01.resolve_left (by simpa [beq_iff_eq] using hbfsOk)
  have hmAcc1 : mAcc.ok = 1 := by
    have h01 := messagesAcc_ok_zero_or_one extZero batch.messages bfs.lch bfs.fch
    rw [hmAcc] at h01
    exact h01.resolve_left (by simpa [beq_iff_eq] using hmAccOk)
  have htotOk : total.ok ≠ 0 ∧ extIsZero total.lastAcc ≠ 0 := by
    simpa [Bool.or_eq_true, beq_iff_eq, not_or] using htotRaw
  have htot1 : total.ok = 1 := by
    have h01 := verifyShardsWithFloor_ok_zero_or_one 1 sys batch.headers batch.proofs 0
      bfs.input bfs.lch bfs.fch mAcc.lastAcc
    rw [htot] at h01
    exact h01.resolve_left htotOk.1
  have hzero1 : extIsZero total.lastAcc = 1 :=
    (extIsZero_zero_or_one total.lastAcc).resolve_left htotOk.2
  obtain ⟨hShards, hLastEq⟩ := verifyShards_sound sys batch.headers batch.proofs 0
    bfs.input bfs.lch bfs.fch mAcc.lastAcc (by change (verifyShardsWithFloor 1 _ _ _ _ _ _ _ _).ok = 1; rw [htot]; exact htot1)
  have htotLast : total.lastAcc = foldShardAccs mAcc.lastAcc batch.proofs := by
    rw [← htot]; exact hLastEq
  have hfirst : sys.params.capHeight = 0 ∧
      (1 ≤ sys.params.maxLogArity ∧ sys.params.maxLogArity ≤ 3) ∧
      SecurityFloorHolds sys.params := by
    cases hh : batch.headers with
    | nil => simp [hh, shardHeaderListLen] at hnsB
    | cons h0 hrest =>
      cases hp : batch.proofs with
      | nil => simp [hh, hp, shardHeaderListLen, shardProofListLen] at hplenEq; omega
      | cons p0 prest =>
        rw [hh, hp] at hShards
        exact ⟨hShards.1.capHeight_zero, hShards.1.maxLogArity_bounds, hShards.1.securityFloor⟩
  have hclaimsEq : (verifyBatch sys batch).claims = batchClaims batch.headers := by
    unfold verifyBatch verifyBatchWithFloor
    dsimp only
    rw [ite_eq_right hns, ite_eq_right hplen, ite_eq_right hlk, ite_eq_right hbr,
        ite_eq_right hcp, hcw, ite_eq_right hcwRaw, hbfs, ite_eq_right hbfsOk,
        hmAcc, ite_eq_right hmAccOk, htot, ite_eq_right htotRaw]
  exact
    { numShards_bounds := hnsB
      proofs_len_match := hplenEq
      capHeight_zero := hfirst.1
      maxLogArity_bounds := hfirst.2.1
      securityFloor := hfirst.2.2
      lookups_bounded := lookupsCountOk_sound sys.circuits hlk1
      batchRows_bounded := by
        simpa using batchRowsOk_sound (circuitRowWeights sys.circuits) batch.headers 0 (Nat.zero_le _) hbr1
      memseg_pairs_valid := assertClosurePairs_sound batch.messages u64Zero u64Zero 0 hcp1
      closure_widths_valid := hcwValid
      closure_pairs_bounded := by rw [← hcwCnt]; exact hcwSnd
      batchFs_ok := by rw [hbfs]; exact hbfs1
      messagesAcc_ok := by dsimp only; rw [hbfs, hmAcc]; exact hmAcc1
      shards_accepted := by dsimp only; rw [hbfs]; exact hShards
      logup_global_closure := by
        dsimp only
        rw [hbfs, hmAcc, ← htotLast]
        exact (extGlToExtGL_isZero_iff total.lastAcc).mp hzero1
      claims_eq := hclaimsEq }

/-- **Master Pure Mathematical Postcondition of `CompressWrap::verify_root`**
(`verifyRootBytes r0..r7 s0..s7 keyBytes claimsBytes proofBytes = 1`):
bundles all 8 zero reserved words, exact `"ix/compress-wrap/v1\0"` 84-byte BLAKE3 statement
binding (`Ix.Cert.AiurCompression.rootStatementWords`), canonical trailing-byte-free wire
decoding (`readSystem`, `readClaims`, `readBatchProof`), structural VK invariants
(`SysKeyWellFormed`), full production batch verification (`BatchAccepted`: all 8+ security-floor
assertions, zero-PoW canonicalization, MMCS, multi-arity FRI, DEEP quotient, Horner final poly,
AIR OOD quotient, global LogUp closure, ROM-lane-weighted `≤ 2^39` row bound, MEMSEG closure),
and word-for-word equality of verified batch claims with the bound public claims stream. -/
structure CompressWrapAccepted
    (r0 r1 r2 r3 r4 r5 r6 r7 : Nat)
    (s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (keyBytes claimsBytes proofBytes : ByteList) : Prop where
  reserved_zero : r0 = 0 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 0 ∧ r5 = 0 ∧ r6 = 0 ∧ r7 = 0
  valid_keyBytes : ValidBytes keyBytes
  valid_claimsBytes : ValidBytes claimsBytes
  valid_proofBytes : ValidBytes proofBytes
  keyBytes_len_le : byteListLen keyBytes ≤ 1024 * 2 ^ 64
  claimsBytes_len_le : byteListLen claimsBytes ≤ 1024 * 2 ^ 64
  statement_digest_eq :
    computeStatementDigest keyBytes claimsBytes =
      { w0 := s0, w1 := s1, w2 := s2, w3 := s3, w4 := s4, w5 := s5, w6 := s6, w7 := s7 }
  statement_words_eq_pure :
    [s0, s1, s2, s3, s4, s5, s6, s7] =
      Ix.Cert.AiurCompression.rootStatementWords
        (Blake3.Pure.digest (byteListToUInt8List keyBytes))
        (byteListToUInt8List claimsBytes)
  statement_words_lt : ∀ w ∈ [s0, s1, s2, s3, s4, s5, s6, s7], w < 2 ^ 32
  sys_ok : (readSystem keyBytes).ok = 1
  sys_rest_nil : (readSystem keyBytes).rest = .nil
  sys_header_pin :
    (readU16LE keyBytes).val = 6 ∧
    (readU16LE (readU16LE keyBytes).rest).val = 3 ∧
    (readU16LE (readU16LE (readU16LE keyBytes).rest).rest).val = 1
  sys_wf : SysKeyWellFormed (readSystem keyBytes).val
  sys_no_trailing :
    ∀ extra : ByteList, extra ≠ .nil → (readSystem (byteListAppend keyBytes extra)).ok = 0
  claims_ok : (readClaims claimsBytes).ok = 1
  claims_rest_nil : (readClaims claimsBytes).rest = .nil
  claims_canonical : CanonicalClaims (readClaims claimsBytes).val
  claims_no_trailing :
    ∀ extra : ByteList, extra ≠ .nil → (readClaims (byteListAppend claimsBytes extra)).ok = 0
  batch_ok : (readBatchProof proofBytes).ok = 1
  batch_rest_nil : (readBatchProof proofBytes).rest = .nil
  batch_wf : BatchProofDecodedWellFormed (readBatchProof proofBytes).val
  batch_no_trailing :
    ∀ extra : ByteList, extra ≠ .nil → (readBatchProof (byteListAppend proofBytes extra)).ok = 0
  batch_accepted : BatchAccepted (readSystem keyBytes).val (readBatchProof proofBytes).val
  claims_match : batchClaims (readBatchProof proofBytes).val.headers = (readClaims claimsBytes).val

/-- **Headline Pure-Lean Functional Correctness of `CompressWrapPure.verifyRootBytes`**
(zero side hypotheses — byte validity and BLAKE3 counter ceiling are proved automatically from
canonical wire decoding!):
any input tuple for which `verifyRootBytes` returns `1` satisfies the complete mathematical
postcondition `CompressWrapAccepted`. -/
theorem verifyRootBytes_sound
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    {keyBytes claimsBytes proofBytes : ByteList}
    (hok : verifyRootBytes r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
      keyBytes claimsBytes proofBytes = 1) :
    CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
      keyBytes claimsBytes proofBytes := by
  unfold verifyRootBytes verifyRootBytesWithFloor at hok
  obtain ⟨hres, hok⟩ := ite_nat_zero_eq_one hok
  generalize hstmt : computeStatementDigest keyBytes claimsBytes = stmt at hok
  obtain ⟨hs, hok⟩ := ite_nat_zero_eq_one hok
  generalize hpSys : readSystem keyBytes = pSys at hok
  obtain ⟨hsys0, hok⟩ := ite_nat_zero_eq_one hok
  generalize hpClaims : readClaims claimsBytes = pClaims at hok
  obtain ⟨hcl0, hok⟩ := ite_nat_zero_eq_one hok
  generalize hpBatch : readBatchProof proofBytes = pBatch at hok
  obtain ⟨hba0, hok⟩ := ite_nat_zero_eq_one hok
  generalize hvb : verifyBatchWithFloor 1 pSys.val pBatch.val = vb at hok
  obtain ⟨hvb0, hok⟩ := ite_nat_zero_eq_one hok
  simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hres hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hr0, hr1⟩, hr2⟩, hr3⟩, hr4⟩, hr5⟩, hr6⟩, hr7⟩ := hres
  obtain ⟨⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩, hs7⟩ := hs
  have hstmtEq : stmt = { w0 := s0, w1 := s1, w2 := s2, w3 := s3, w4 := s4, w5 := s5, w6 := s6, w7 := s7 } := by
    cases stmt; dsimp only at hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7; subst hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7; rfl
  have hsys1 : (readSystem keyBytes).ok = 1 := by
    have h01 := readSystem_ok_zero_or_one keyBytes
    rw [hpSys] at h01
    rw [hpSys]
    exact h01.resolve_left (by simpa [beq_iff_eq] using hsys0)
  have hcl1 : (readClaims claimsBytes).ok = 1 := by
    have h01 := readClaims_ok_zero_or_one claimsBytes
    rw [hpClaims] at h01
    rw [hpClaims]
    exact h01.resolve_left (by simpa [beq_iff_eq] using hcl0)
  have hba1 : (readBatchProof proofBytes).ok = 1 := by
    have h01 := readBatchProof_ok_zero_or_one proofBytes
    rw [hpBatch] at h01
    rw [hpBatch]
    exact h01.resolve_left (by simpa [beq_iff_eq] using hba0)
  have hvb1 : (verifyBatch pSys.val pBatch.val).ok = 1 := by
    have h01 := verifyBatchWithFloor_ok_zero_or_one 1 pSys.val pBatch.val
    rw [hvb] at h01
    change (verifyBatchWithFloor 1 pSys.val pBatch.val).ok = 1
    rw [hvb]
    exact h01.resolve_left (by simpa [beq_iff_eq] using hvb0)
  have hsameClaims : vb.claims = pClaims.val :=
    (assertSameClaims_eq_one_iff vb.claims pClaims.val).mp hok
  obtain ⟨hsysRest, hsysV, hsys6, hsys3, hsys1v, hsysWf, hsysLen, hsysNoTr⟩ :=
    readSystem_sound keyBytes hsys1
  obtain ⟨hclRest, hclV, hclCan, hclLen, hclNoTr⟩ :=
    readClaims_sound claimsBytes hcl1
  obtain ⟨hbaRest, hbaV, hbaWf, hbaNoTr⟩ :=
    readBatchProof_sound proofBytes hba1
  obtain ⟨hstmtPure, hstmtLt⟩ := computeStatementDigest_eq_pure hsysV hclV hsysLen hclLen
  have hwordsEq : digest32WordsToList (computeStatementDigest keyBytes claimsBytes) =
      [s0, s1, s2, s3, s4, s5, s6, s7] := by
    rw [hstmt, hstmtEq]; rfl
  have hbatchAcc := verifyBatch_sound hvb1
  have hclaimsMatch : batchClaims pBatch.val.headers = pClaims.val := by
    have hce := hbatchAcc.claims_eq
    change (verifyBatchWithFloor 1 pSys.val pBatch.val).claims = _ at hce
    rw [hvb] at hce
    rw [← hce, hsameClaims]
  exact
    { reserved_zero := ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩
      valid_keyBytes := hsysV
      valid_claimsBytes := hclV
      valid_proofBytes := hbaV
      keyBytes_len_le := hsysLen
      claimsBytes_len_le := hclLen
      statement_digest_eq := by rw [hstmt, hstmtEq]
      statement_words_eq_pure := by rw [← hwordsEq]; exact hstmtPure
      statement_words_lt := by rw [← hwordsEq]; exact hstmtLt
      sys_ok := hsys1
      sys_rest_nil := hsysRest
      sys_header_pin := ⟨hsys6, hsys3, hsys1v⟩
      sys_wf := hsysWf
      sys_no_trailing := hsysNoTr
      claims_ok := hcl1
      claims_rest_nil := hclRest
      claims_canonical := hclCan
      claims_no_trailing := hclNoTr
      batch_ok := hba1
      batch_rest_nil := hbaRest
      batch_wf := hbaWf
      batch_no_trailing := hbaNoTr
      batch_accepted := by rw [hpSys, hpBatch]; exact hbatchAcc
      claims_match := by rw [hpBatch, hpClaims]; exact hclaimsMatch }

/-- **Collision-Resistant Statement Uniqueness for `CompressWrapAccepted`**:
Any two accepted `CompressWrap` executions sharing the same 8 public statement words
`s0..s7` must have byte-for-byte identical `(keyBytes, claimsBytes)` (and therefore identical
decoded verifying key `SysKey` and public `Claims`) — or else exhibit an explicit BLAKE3
collision! -/
theorem compressWrapAccepted_statement_unique_or_collision
    {r0 r1 r2 r3 r4 r5 r6 r7 r0' r1' r2' r3' r4' r5' r6' r7' s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    {k₁ c₁ p₁ k₂ c₂ p₂ : ByteList}
    (h₁ : CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 k₁ c₁ p₁)
    (h₂ : CompressWrapAccepted r0' r1' r2' r3' r4' r5' r6' r7' s0 s1 s2 s3 s4 s5 s6 s7 k₂ c₂ p₂) :
    (∃ a b, Ix.Cert.AiurCompression.Blake3Collision a b) ∨
    (k₁ = k₂ ∧ c₁ = c₂ ∧
      (readSystem k₁).val = (readSystem k₂).val ∧
      (readClaims c₁).val = (readClaims c₂).val) := by
  have heq : computeStatementDigest k₁ c₁ = computeStatementDigest k₂ c₂ := by
    rw [h₁.statement_digest_eq, h₂.statement_digest_eq]
  rcases computeStatementDigest_injective_or_collision
      h₁.valid_keyBytes h₁.valid_claimsBytes h₂.valid_keyBytes h₂.valid_claimsBytes
      h₁.keyBytes_len_le h₁.claimsBytes_len_le h₂.keyBytes_len_le h₂.claimsBytes_len_le heq with
    hcol | ⟨hk, hc⟩
  · exact Or.inl hcol
  · subst hk hc; exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 5: End-to-End Composition with `CompressionIntrinsicsProof.CompressionCert`

Connects the pure functional soundness theorem `verifyRootBytes_sound` (`CompressWrapAccepted`)
directly to `IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert`:
any weighted execution trace accepted by `cert.plan.checkMemo` on an `IxCCAiur`-compiled
`CompressWrap::verify_root` circuit (with `--assert-ok` and 3 witness byte-stream channels
`keyBytes`, `claimsBytes`, `proofBytes`, over arbitrary prime fields `[Field F] [DecidableEq F]`
or concretely over Goldilocks `p_G`, BN254 `Fr`, or BLS12-381 `Fr`) yields finite canonical
witness byte streams satisfying the full pure mathematical `CompressWrapAccepted` postcondition
and exact `"ix/compress-wrap/v1\0"` 84-byte BLAKE3 statement digest binding. -/

section EndToEndComposition

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
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

/-- Canonical 16-word public input vector `[r0..r7, s0..s7]` for `CompressWrap::verify_root`,
embedded into an arbitrary field `F` via `Value.field (n : F)`. -/
def compressWrapPubVals (F : Type) [Field F]
    (r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat) :
    List (SourceValue F) :=
  [r0, r1, r2, r3, r4, r5, r6, r7, s0, s1, s2, s3, s4, s5, s6, s7].map (fun n => .field (n : F))

/-- Pre-intrinsic functional refinement contract linking the lowered verifier function
`checkFnName` in `wOrig` to `CompressWrapPure.verifyRootBytes`: whenever `checkFnName`
evaluates to `.field 1` on the 16 public words `(r0..r7, s0..s7)` and 3 `ByteStreamRel`-linked
witness byte streams `[keyBytes, claimsBytes, proofBytes]`, pure `verifyRootBytes` returns `1`. -/
def VerifyRootEvalSound {F : Type} [Field F] [DecidableEq F]
    (wOrig : World F) (checkFnName : String)
    (r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : Prop :=
  ∀ (h1 h2 : Heap F)
    (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
    ws.length = 3 →
    List.Forall₂ (ByteStreamRel h1) ws wPtrs →
    EvalFn wOrig checkFnName
      (compressWrapPubVals F r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 ++ wPtrs)
      h1 (.field 1) h2 →
    match ws with
    | [keyBytes, claimsBytes, proofBytes] =>
      verifyRootBytes r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes) = 1
    | _ => False

/-- Witness-wrapper postcondition predicate passed to `CompressionCert.accepted_witness_assertOk_sound`. -/
def CompressWrapWitnessSpec {F : Type} [Field F]
    (r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (pub : List (SourceValue F)) (ws : List (List UInt8)) : Prop :=
  pub = compressWrapPubVals F r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 →
  ws.length = 3 →
  ∃ keyBytes claimsBytes proofBytes : List UInt8,
    ws = [keyBytes, claimsBytes, proofBytes] ∧
    CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
      (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes)

private theorem verifyRootEvalSound_to_witnessSpec {F : Type} [Field F] [DecidableEq F]
    {wOrig : World F} {checkFnName : String}
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    (href : VerifyRootEvalSound wOrig checkFnName
      r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7) :
    ∀ (pubArgs : List (SourceValue F))
      (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      CompressWrapWitnessSpec r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 pubArgs ws := by
  intro pubArgs h1 h2 wPtrs ws hRel ev hpub hlen3
  subst hpub
  have hok := href h1 h2 wPtrs ws hlen3 hRel ev
  rcases ws with _ | ⟨k, _ | ⟨c, _ | ⟨p, _ | _⟩⟩⟩
  · simp at hlen3
  · simp at hlen3
  · simp at hlen3
  · exact ⟨k, c, p, rfl, verifyRootBytes_sound hok⟩
  · simp at hlen3

/-- **Headline End-to-End Composition with `CompressionCert` (Arbitrary Prime Field `F`)**:
any accepted trace (`cert.plan.checkMemo (rawROM rom) root rows = .ok ()`) of a compiled
`--assert-ok` `CompressWrap::verify_root` circuit over `[Field F] [DecidableEq F]` with
3 witness channels yields finite byte streams `(keyBytes, claimsBytes, proofBytes)` satisfying:
1. Full `CompressWrapAccepted` (canonical wire decoding, structural VK invariants, all 8+
   production security-floor assertions, zero-PoW canonicalization, batched MMCS, multi-arity
   FRI, DEEP/Horner, AIR OOD quotient, global LogUp closure, `≤ 2^39` rows, MEMSEG closure),
2. All 8 reserved public words equal to `0`, and
3. Exact `"ix/compress-wrap/v1\0"` 84-byte BLAKE3 statement digest binding
   `[s0..s7] = Ix.Cert.AiurCompression.rootStatementWords (Blake3.Pure.digest keyBytes) claimsBytes`. -/
theorem compressionCert_compressWrap_accepted {F : Type} [Field F] [DecidableEq F]
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
    (hchLen : channels.length = 3)
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName false)))
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    (href : VerifyRootEvalSound wOrig checkFnName
      r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)
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
      (Aiur.entryValues (compressWrapPubVals F r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ keyBytes claimsBytes proofBytes : List UInt8,
      CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes) ∧
      [s0, s1, s2, s3, s4, s5, s6, s7] =
        Ix.Cert.AiurCompression.rootStatementWords (Blake3.Pure.digest keyBytes) claimsBytes := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    cert.accepted_witness_assertOk_sound characteristic hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyRootEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  obtain ⟨k, c, p, _, hacc⟩ := hspec rfl (hwsLen.trans hchLen)
  have hstmt := hacc.statement_words_eq_pure
  rw [byteListToUInt8List_ofUInt8List, byteListToUInt8List_ofUInt8List] at hstmt
  exact ⟨k, c, p, hacc, hstmt⟩

/-- **Goldilocks (`p_G`) End-to-End `CompressWrap` Theorem**
(characteristic condition discharged automatically via `compressionCert_witness_goldilocks`). -/
theorem compressionCert_compressWrap_goldilocks
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
    (hchLen : channels.length = 3)
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF GLF (witnessWrapperBody pubParams channels checkFnName false)))
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    (href : VerifyRootEvalSound wOrig checkFnName
      r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)
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
      (Aiur.entryValues (compressWrapPubVals GLF r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ keyBytes claimsBytes proofBytes : List UInt8,
      CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes) ∧
      [s0, s1, s2, s3, s4, s5, s6, s7] =
        Ix.Cert.AiurCompression.rootStatementWords (Blake3.Pure.digest keyBytes) claimsBytes := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_goldilocks cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyRootEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  obtain ⟨k, c, p, _, hacc⟩ := hspec rfl (hwsLen.trans hchLen)
  have hstmt := hacc.statement_words_eq_pure
  rw [byteListToUInt8List_ofUInt8List, byteListToUInt8List_ofUInt8List] at hstmt
  exact ⟨k, c, p, hacc, hstmt⟩

/-- **BN254 (`Fr`) End-to-End `CompressWrap` Theorem**
(characteristic condition discharged automatically via `compressionCert_witness_bn254`). -/
theorem compressionCert_compressWrap_bn254
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
    (hchLen : channels.length = 3)
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BN254.F (witnessWrapperBody pubParams channels checkFnName false)))
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    (href : VerifyRootEvalSound wOrig checkFnName
      r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)
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
      (Aiur.entryValues (compressWrapPubVals Aiur.Library.Field.BN254.F
        r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ keyBytes claimsBytes proofBytes : List UInt8,
      CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes) ∧
      [s0, s1, s2, s3, s4, s5, s6, s7] =
        Ix.Cert.AiurCompression.rootStatementWords (Blake3.Pure.digest keyBytes) claimsBytes := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_bn254 cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyRootEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  obtain ⟨k, c, p, _, hacc⟩ := hspec rfl (hwsLen.trans hchLen)
  have hstmt := hacc.statement_words_eq_pure
  rw [byteListToUInt8List_ofUInt8List, byteListToUInt8List_ofUInt8List] at hstmt
  exact ⟨k, c, p, hacc, hstmt⟩

/-- **BLS12-381 (`Fr`) End-to-End `CompressWrap` Theorem**
(characteristic condition discharged automatically via `compressionCert_witness_bls12381`). -/
theorem compressionCert_compressWrap_bls12381
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
    (hchLen : channels.length = 3)
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BLS12381.F (witnessWrapperBody pubParams channels checkFnName false)))
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    (href : VerifyRootEvalSound wOrig checkFnName
      r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)
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
      (Aiur.entryValues (compressWrapPubVals Aiur.Library.Field.BLS12381.F
        r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ keyBytes claimsBytes proofBytes : List UInt8,
      CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        (ofUInt8List keyBytes) (ofUInt8List claimsBytes) (ofUInt8List proofBytes) ∧
      [s0, s1, s2, s3, s4, s5, s6, s7] =
        Ix.Cert.AiurCompression.rootStatementWords (Blake3.Pure.digest keyBytes) claimsBytes := by
  obtain ⟨ws, hwsLen, _, hspec⟩ :=
    compressionCert_witness_bls12381 cert hAssert hsio hkio bridge
      hchkQual hnd hwrap (verifyRootEvalSound_to_witnessSpec href)
      valid signed rooted outside bound checked arguments decoded
  obtain ⟨k, c, p, _, hacc⟩ := hspec rfl (hwsLen.trans hchLen)
  have hstmt := hacc.statement_words_eq_pure
  rw [byteListToUInt8List_ofUInt8List, byteListToUInt8List_ofUInt8List] at hstmt
  exact ⟨k, c, p, hacc, hstmt⟩

/-- **Source-Level `Recheck.FrontFir` Composition (`CompressionCert.accepted_assertOk_source`)**:
for any prime field `ZMod p` where the checked Lean/Ix source evaluator at export `i` refines
`CompressWrapPure.verifyRootBytes`, an accepted trace (`cert.plan.checkMemo = .ok ()`) yields
both the escape-free source evaluation `obs v = some (.nat 1)` AND the complete mathematical
`CompressWrapAccepted` postcondition! -/
theorem compressionCert_compressWrap_source_accepted {p : Nat} [Fact (Nat.Prime p)]
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
    {r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7 : Nat}
    {keyBytes claimsBytes proofBytes : ByteList}
    (hSrcRefine :
      (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1)) →
      verifyRootBytes r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
        keyBytes claimsBytes proofBytes = 1) :
    CompressWrapAccepted r0 r1 r2 r3 r4 r5 r6 r7 s0 s1 s2 s3 s4 s5 s6 s7
      keyBytes claimsBytes proofBytes :=
  verifyRootBytes_sound <| hSrcRefine <|
    cert.accepted_assertOk_source fc characteristic hnat hf hAssert hexp hret hfn
      hwOrig bridge valid signed rooted outside bound checked arguments decoded hcov hshape

end EndToEndComposition

/-! ## Section 6: Kernel-Checked Axiom Fences (`⊆ [propext, Classical.choice, Quot.sound]`) -/

section AxiomFences

-- Section 2: Wire Decoders & Structural VK Validation
/-- info: 'CompressWrapSpec.readU32LE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readU32LE_sound

/-- info: 'CompressWrapSpec.readU64LE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readU64LE_sound

/-- info: 'CompressWrapSpec.readGlCanonical_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readGlCanonical_sound

/-- info: 'CompressWrapSpec.readExtGl_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readExtGl_sound

/-- info: 'CompressWrapSpec.readDigest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readDigest_sound

/-- info: 'CompressWrapSpec.readClaims_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readClaims_sound

/-- info: 'CompressWrapSpec.readSystem_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readSystem_sound

/-- info: 'CompressWrapSpec.readBatchProof_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.readBatchProof_sound

-- Section 3: Pure BLAKE3 Parity, Statement Binding & Protocol v6 Challenger
/-- info: 'CompressWrapSpec.blake3Compress_eq_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.blake3Compress_eq_pure

/-- info: 'CompressWrapSpec.blake3HashBytesWithCv_eq_digestCVWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.blake3HashBytesWithCv_eq_digestCVWith

/-- info: 'CompressWrapSpec.blake3HashBytes_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.blake3HashBytes_eq_pure

/-- info: 'CompressWrapSpec.v6TranscriptBatchHash_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.v6TranscriptBatchHash_eq_pure

/-- info: 'CompressWrapSpec.v6MerkleLeafHashChecked_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.v6MerkleLeafHashChecked_eq_pure

/-- info: 'CompressWrapSpec.v6MerkleCompress_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.v6MerkleCompress_eq_pure

/-- info: 'CompressWrapSpec.computeStatementDigest_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.computeStatementDigest_eq_pure

/-- info: 'CompressWrapSpec.computeStatementDigest_injective_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.computeStatementDigest_injective_or_collision

/-- info: 'CompressWrapSpec.computeStatementDigest_statementPolicy_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.computeStatementDigest_statementPolicy_link

/-- info: 'CompressWrapSpec.chSample8_eq_sampleWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.chSample8_eq_sampleWord

/-- info: 'CompressWrapSpec.chSampleGl_eq_sampleBaseStrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.chSampleGl_eq_sampleBaseStrict

/-- info: 'CompressWrapSpec.chSampleExt_eq_sampleExtStrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.chSampleExt_eq_sampleExtStrict

/-- info: 'CompressWrapSpec.chSampleBits_eq_sampleBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.chSampleBits_eq_sampleBits

-- Section 4: Security Floor, Zero-PoW, MMCS, FRI, AIR, LogUp, MEMSEG & Verifier Soundness
/-- info: 'CompressWrapSpec.checkSecurityFloor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.checkSecurityFloor_sound

/-- info: 'CompressWrapSpec.checkSecurityFloor_implies_meetsSecurityFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.checkSecurityFloor_implies_meetsSecurityFloor

/-- info: 'CompressWrapSpec.pcsCheckWitness_zero_bits_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.pcsCheckWitness_zero_bits_canonical

/-- info: 'CompressWrapSpec.pcsCheckWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.pcsCheckWitness_sound

/-- info: 'CompressWrapSpec.pcsBetas_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.pcsBetas_sound

/-- info: 'CompressWrapSpec.mmcsVerifyMulti_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.mmcsVerifyMulti_sound

/-- info: 'CompressWrapSpec.evalFinalPoly_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.evalFinalPoly_spec

/-- info: 'CompressWrapSpec.friFold2Step_linear_poly_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.friFold2Step_linear_poly_sound

/-- info: 'CompressWrapSpec.finalizeBuckets_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.finalizeBuckets_sound

/-- info: 'CompressWrapSpec.verifyQueryMulti_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.verifyQueryMulti_sound

/-- info: 'CompressWrapSpec.pcsFriVerify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.pcsFriVerify_sound

/-- info: 'CompressWrapSpec.evalAtFuel_dag_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.evalAtFuel_dag_invariant

/-- info: 'CompressWrapSpec.oodLoop_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.oodLoop_sound

/-- info: 'CompressWrapSpec.assertClosurePairs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.assertClosurePairs_sound

/-- info: 'CompressWrapSpec.verifyShard_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.verifyShard_sound

/-- info: 'CompressWrapSpec.verifyBatch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.verifyBatch_sound

/-- info: 'CompressWrapSpec.verifyRootBytes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.verifyRootBytes_sound

/-- info: 'CompressWrapSpec.compressWrapAccepted_statement_unique_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressWrapAccepted_statement_unique_or_collision

-- Section 5: End-to-End Composition with CompressionIntrinsicsProof.CompressionCert
/-- info: 'CompressWrapSpec.compressionCert_compressWrap_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressionCert_compressWrap_accepted

/-- info: 'CompressWrapSpec.compressionCert_compressWrap_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressionCert_compressWrap_goldilocks

/-- info: 'CompressWrapSpec.compressionCert_compressWrap_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressionCert_compressWrap_bn254

/-- info: 'CompressWrapSpec.compressionCert_compressWrap_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressionCert_compressWrap_bls12381

/-- info: 'CompressWrapSpec.compressionCert_compressWrap_source_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressWrapSpec.compressionCert_compressWrap_source_accepted

end AxiomFences

end CompressWrapSpec

