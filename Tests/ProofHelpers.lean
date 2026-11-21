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

/-- Inner-proof commitment/FRI parameters. -/
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
