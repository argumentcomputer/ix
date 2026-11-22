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
  numQueries := 100
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

/-- Minimum Johnson (list-decoding) query-phase soundness in bits. -/
def minJohnsonBits : Nat := 100

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

/-- Explicit per-`logBlowup` minimum FRI query count guaranteeing that
`minProvableUdBits` is attainable with at most `maxProofOfWorkBits` query grinding bits. -/
def minQueriesForLogBlowup : Nat → Option Nat
  | 1 => some 116
  | 2 => some 71
  | 3 => some 58
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
and finite-`m` Johnson floor (`100` bits). -/
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

end Aiur

end
