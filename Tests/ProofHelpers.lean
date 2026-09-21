module
public import LSpec
public import Ix.Aiur.Protocol

public section
namespace Tests.ProofHelpers
open LSpec

/-- A passing test iff `e` is `.ok`; on `.error` the message is surfaced. -/
def expectOk [ToString ε] (descr : String) (e : Except ε α) : TestSeq :=
  match e with
  | .ok _ => test descr true
  | .error msg => test s!"{descr} — unexpected error: {msg}" false

/-- A passing test iff the verifier rejected the input. -/
def expectErr (descr : String) (e : Except ε α) : TestSeq :=
  match e with
  | .error _ => test descr true
  | .ok _ => test s!"{descr} — expected a rejection but it was accepted" false

/-- Inner-proof commitment/FRI parameters. A tractable subset of production
(`numQueries := 3`, standard PoW regime: commit 0 / query 20); the verifier
code itself is blowup/query-count agnostic, and `pcs_check_witness` is shared
by both PoW phases, so the query-phase grinding exercises the commit-phase
code path too. -/
def recCommitParams : Aiur.CommitmentParameters :=
  { logBlowup := 2, capHeight := 0 }
def innerFri : Aiur.FriParameters :=
  { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 3,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 20 }

/-- 8 little-endian bytes of a `Nat` (taken mod 2^64). -/
def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))


end Tests.ProofHelpers
end
