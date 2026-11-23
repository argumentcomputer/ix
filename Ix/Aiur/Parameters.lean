module

/-!
The STARK parameters every Aiur proof uses. They mirror Rust's
`aiur::trace::stark::Parameters::DEFAULT` and `stark_key::security`; the Rust
test `lean_mirror_matches` reads the values from this file, so keep one
`name := value` per field. `docs/stark-parameters.md` explains them, and
`lake exe fri-security` computes their security.
-/

public section

namespace Aiur

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

def defaultCommitmentParameters : CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }

def defaultFriParameters : FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 128
  commitProofOfWorkBits := 0
  queryProofOfWorkBits := 20
}

/-- The floor on `logBlowup · numQueries + queryProofOfWorkBits` (the
ethSTARK conjecture's query-phase bits) that every key must meet. -/
def minConjecturedSecurityBits : Nat := 220

/-- Minimum provable unique-decoding (`CertiFRI`) query-phase soundness in bits.
Blocks high-blowup / low-query configurations such as `(4, 55, 0)` (50.2 bits UD)
that pass the conjectured floor while falling below provable unique-decoding soundness. -/
def minProvableUdBits : Nat := 80

/-- Minimum Johnson (list-decoding) query-phase soundness in bits (Protocol v6 Fp^3 128-bit floor). -/
def minJohnsonBits : Nat := 128

/-- The most proof-of-work bits either FRI grinding phase may require. -/
def maxProofOfWorkBits : Nat := 32

/-- Conservative integer per-query finite-`m` Johnson slack (`m = 16`):
`ceil(1000 · log2(1 + 1/(2m))) = ceil(1000 · log2(33/32)) = 45` milli-bits/query. -/
def johnsonSlackMillibitsPerQuery : Nat := 45

/-- Conservative integer lower bound on `-1000 · log2((1 + 2^{-logBlowup}) / 2)`
(milli-bits of unique-decoding query soundness per FRI query). -/
def udMillibitsPerQuery : Nat → Option Nat
  | 1 => some 415
  | 2 => some 678
  | 3 => some 830
  | 4 => some 912
  | _ => none

/-- Explicit per-`logBlowup` minimum FRI query count guaranteeing that both
`minJohnsonBits` (128) and `minProvableUdBits` (80) are attainable with at most
`maxProofOfWorkBits` (32) query grinding bits. -/
def minQueriesForLogBlowup : Nat → Option Nat
  | 1 => some 211
  | 2 => some 101
  | 3 => some 66
  | 4 => some 53
  | _ => none

/-- Provable unique-decoding query-phase soundness in milli-bits:
`udMillibitsPerQuery(logBlowup) · numQueries + 1000 · queryProofOfWorkBits`. -/
def provableUdMillibits (commitment : CommitmentParameters) (fri : FriParameters) : Option Nat :=
  (udMillibitsPerQuery commitment.logBlowup).map fun rate =>
    fri.numQueries * rate + fri.queryProofOfWorkBits * 1000

/-- Finite-`m` (`m = 16`) Johnson-bound query-phase soundness in milli-bits:
`(500 · logBlowup - johnsonSlackMillibitsPerQuery) · numQueries + 1000 · queryProofOfWorkBits`. -/
def johnsonMillibits (commitment : CommitmentParameters) (fri : FriParameters) : Nat :=
  (commitment.logBlowup * 500 - johnsonSlackMillibitsPerQuery) * fri.numQueries +
    fri.queryProofOfWorkBits * 1000

/-- The conjectured query-phase bits of `commitment` and `fri`. -/
def conjecturedSecurityBits (commitment : CommitmentParameters) (fri : FriParameters) : Nat :=
  commitment.logBlowup * fri.numQueries + fri.queryProofOfWorkBits

/-- Whether `commitment` and `fri` meet the structural and cryptographic floor Rust enforces
(`stark_key::security::check`): fixed structural parameters (`capHeight = 0`,
`logFinalPolyLen = 0`, `maxLogArity = 1`), `1 ≤ logBlowup ≤ 4`, per-`logBlowup` query floor,
proof-of-work ceiling, conjectured floor (`220` bits), provable UD floor (`80` bits),
and finite-`m` Johnson floor (`128` bits). -/
def meetsSecurityFloor (commitment : CommitmentParameters) (fri : FriParameters) : Bool :=
  commitment.capHeight == 0 &&
    fri.logFinalPolyLen == 0 &&
    fri.maxLogArity == 1 &&
    1 ≤ commitment.logBlowup && commitment.logBlowup ≤ 4 &&
    0 < fri.numQueries &&
    fri.commitProofOfWorkBits ≤ maxProofOfWorkBits &&
    fri.queryProofOfWorkBits ≤ maxProofOfWorkBits &&
    (match minQueriesForLogBlowup commitment.logBlowup with
      | some minQ => minQ ≤ fri.numQueries
      | none => false) &&
    minConjecturedSecurityBits ≤ conjecturedSecurityBits commitment fri &&
    (match provableUdMillibits commitment fri with
      | some udMb => minProvableUdBits * 1000 ≤ udMb
      | none => false) &&
    minJohnsonBits * 1000 ≤ johnsonMillibits commitment fri

theorem default_meets_security_floor :
    meetsSecurityFloor defaultCommitmentParameters defaultFriParameters = true := by
  decide

theorem rejects_high_blowup_low_ud :
    meetsSecurityFloor ⟨4, 0⟩ ⟨0, 1, 55, 0, 0⟩ = false := by
  decide

theorem rejects_below_query_floor :
    meetsSecurityFloor ⟨4, 0⟩ ⟨0, 1, 52, 0, 32⟩ = false := by
  decide

theorem rejects_blowup2_low_ud :
    meetsSecurityFloor ⟨2, 0⟩ ⟨0, 1, 110, 0, 0⟩ = false := by
  decide

theorem rejects_blowup3_low_ud :
    meetsSecurityFloor ⟨3, 0⟩ ⟨0, 1, 67, 0, 20⟩ = false := by
  decide

theorem rejects_nonzero_cap_height :
    meetsSecurityFloor ⟨2, 1⟩ defaultFriParameters = false := by
  decide

/-! ## `v6` 128-bit Security Profile (`Fp^3`, BLAKE3 `derive_key` / 48B XOF)

Mirrors `stark_key::security::{EXTENSION_DEGREE_V6, PROTOCOL_VERSION_V6,
MIN_PROVABLE_SECURITY_BITS_128, DIGEST_BYTES_XOF48, check_128_ud,
check_128_johnson}` alongside the live Protocol `v6` (`Fp^3`) defaults above. -/

/-- Extension field degree for the `v6` 128-bit profile (`Fp^3`, `p^3 > 2^191`). -/
def extensionDegreeV6 : Nat := 3

/-- Protocol version tag for the `v6` `Fp^3` + BLAKE3 `derive_key` profile. -/
def protocolVersionV6 : Nat := 6

/-- Target provable security floor (in bits) for the `v6` 128-bit profile. -/
def minProvableSecurityBits128 : Nat := 128

/-- Digest width in bytes for the 48-byte (384-bit) BLAKE3 XOF profile
(`>= 190.5` classical BCS collision bits and exact `128.0` BHT quantum bits). -/
def digestBytesXof48 : Nat := 48

/-- Explicit per-`logBlowup` minimum FRI query count guaranteeing that
`minProvableSecurityBits128` UD query soundness is attainable with at most
`maxProofOfWorkBits` query grinding bits. -/
def minQueriesForLogBlowup128Ud : Nat → Option Nat
  | 1 => some 232
  | 2 => some 142
  | 3 => some 116
  | 4 => some 106
  | _ => none

/-- Explicit per-`logBlowup` minimum FRI query count guaranteeing that both
`minProvableSecurityBits128` finite-`m` (`m = 16`) Johnson soundness and
`minProvableUdBits` UD soundness are attainable with at most `maxProofOfWorkBits`
query grinding bits. -/
def minQueriesForLogBlowup128Johnson : Nat → Option Nat
  | 1 => some 211
  | 2 => some 101
  | 3 => some 66
  | 4 => some 53
  | _ => none

/-- Canonical `v6` 128-bit commitment parameters (`logBlowup = 2, capHeight = 0`). -/
def defaultV6CommitmentParameters : CommitmentParameters := ⟨2, 0⟩

/-- Canonical `v6` unconditional 128-bit unique-decoding FRI parameters
(`logBlowup = 2, numQueries = 160, queryPow = 20`: `128.48` UD bits). -/
def defaultV6UdFriParameters : FriParameters := ⟨0, 1, 160, 0, 20⟩

/-- Canonical `v6` 128-bit Johnson FRI parameters
(`logBlowup = 2, numQueries = 128, queryPow = 20`: `142.24` Johnson bits). -/
def defaultV6JohnsonFriParameters : FriParameters := ⟨0, 1, 128, 0, 20⟩

/-- Whether `(extensionDegree, protocolVersion, commitment, fri)` meets the
`v6` 128-bit provable unique-decoding security floor (`stark_key::security::check_128_ud`). -/
def meetsSecurityFloor128Ud (extensionDegree protocolVersion : Nat)
    (commitment : CommitmentParameters) (fri : FriParameters) : Bool :=
  extensionDegreeV6 ≤ extensionDegree &&
    protocolVersionV6 ≤ protocolVersion &&
    meetsSecurityFloor commitment fri &&
    (match minQueriesForLogBlowup128Ud commitment.logBlowup with
      | some minQ => minQ ≤ fri.numQueries
      | none => false) &&
    (match provableUdMillibits commitment fri with
      | some udMb => minProvableSecurityBits128 * 1000 ≤ udMb
      | none => false)

/-- Whether `(extensionDegree, protocolVersion, commitment, fri)` meets the
`v6` 128-bit finite-`m` Johnson list-decoding security floor
(`stark_key::security::check_128_johnson`). -/
def meetsSecurityFloor128Johnson (extensionDegree protocolVersion : Nat)
    (commitment : CommitmentParameters) (fri : FriParameters) : Bool :=
  extensionDegreeV6 ≤ extensionDegree &&
    protocolVersionV6 ≤ protocolVersion &&
    meetsSecurityFloor commitment fri &&
    (match minQueriesForLogBlowup128Johnson commitment.logBlowup with
      | some minQ => minQ ≤ fri.numQueries
      | none => false) &&
    minProvableSecurityBits128 * 1000 ≤ johnsonMillibits commitment fri

theorem v6_ud_160_meets_128_ud :
    meetsSecurityFloor128Ud extensionDegreeV6 protocolVersionV6
      defaultV6CommitmentParameters defaultV6UdFriParameters = true := by
  decide

theorem v6_johnson_118_meets_128_johnson :
    meetsSecurityFloor128Johnson extensionDegreeV6 protocolVersionV6
      defaultV6CommitmentParameters ⟨0, 1, 118, 0, 20⟩ = true := by
  decide

theorem v6_johnson_128_meets_128_johnson :
    meetsSecurityFloor128Johnson extensionDegreeV6 protocolVersionV6
      defaultV6CommitmentParameters defaultV6JohnsonFriParameters = true := by
  decide

theorem v6_128_rejects_fp2 :
    meetsSecurityFloor128Ud 2 protocolVersionV6
      defaultV6CommitmentParameters defaultV6UdFriParameters = false ∧
    meetsSecurityFloor128Johnson 2 protocolVersionV6
      defaultV6CommitmentParameters defaultV6JohnsonFriParameters = false := by
  decide

theorem v6_128_rejects_v5_protocol :
    meetsSecurityFloor128Ud extensionDegreeV6 5
      defaultV6CommitmentParameters defaultV6UdFriParameters = false ∧
    meetsSecurityFloor128Johnson extensionDegreeV6 5
      defaultV6CommitmentParameters defaultV6JohnsonFriParameters = false := by
  decide

theorem v6_128_rejects_v5_default_100_20 :
    meetsSecurityFloor128Ud extensionDegreeV6 protocolVersionV6
      ⟨2, 0⟩ ⟨0, 1, 100, 0, 20⟩ = false ∧
    meetsSecurityFloor128Johnson extensionDegreeV6 protocolVersionV6
      ⟨2, 0⟩ ⟨0, 1, 100, 0, 20⟩ = false := by
  decide

theorem v6_128_rejects_high_blowup_4_55_0 :
    meetsSecurityFloor128Ud extensionDegreeV6 protocolVersionV6
      ⟨4, 0⟩ ⟨0, 1, 55, 0, 0⟩ = false ∧
    meetsSecurityFloor128Johnson extensionDegreeV6 protocolVersionV6
      ⟨4, 0⟩ ⟨0, 1, 55, 0, 0⟩ = false := by
  decide

end Aiur

end
