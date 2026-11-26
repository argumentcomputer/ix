module
public import LSpec
public import Ix.Aiur.Protocol

public section
namespace Tests.ProofHelpers
open LSpec

/-- A passing test iff `e` is `.ok`; on `.error` the message is surfaced. -/
def checkOk [ToString ε] (descr : String) (e : Except ε α) : Spec :=
  it descr do
    let _ ← LSpec.expectOk e

/-- A passing test iff the verifier rejected the input. -/
def checkErr [Repr α] (descr : String) (e : Except ε α) : Spec :=
  it descr do
    let _ ← LSpec.expectErr e

/-- A passing test iff `e` is `.error` (no `Repr` needed on `α`). -/
def checkErrAny (descr : String) (e : Except ε α) : Spec :=
  it descr do
    match e with
    | .error _ => pure ()
    | .ok _ => fail s!"{descr} — expected a rejection but it was accepted"

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
