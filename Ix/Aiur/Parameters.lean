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

/-- The most proof-of-work bits either FRI grinding phase may require. -/
def maxProofOfWorkBits : Nat := 32

/-- The conjectured query-phase bits of `commitment` and `fri`. -/
def conjecturedSecurityBits (commitment : CommitmentParameters) (fri : FriParameters) : Nat :=
  commitment.logBlowup * fri.numQueries + fri.queryProofOfWorkBits

/-- Whether `commitment` and `fri` meet the floor Rust enforces
(`stark_key::security::check`). -/
def meetsSecurityFloor (commitment : CommitmentParameters) (fri : FriParameters) : Bool :=
  1 ≤ commitment.logBlowup && commitment.logBlowup ≤ 4 && 0 < fri.numQueries &&
    fri.commitProofOfWorkBits ≤ maxProofOfWorkBits &&
    fri.queryProofOfWorkBits ≤ maxProofOfWorkBits &&
    minConjecturedSecurityBits ≤ conjecturedSecurityBits commitment fri

theorem default_meets_security_floor :
    meetsSecurityFloor defaultCommitmentParameters defaultFriParameters = true := by
  decide

end Aiur

end
