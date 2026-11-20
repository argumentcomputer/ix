import IxAICommon.Hash
import IxAICommon.Paths

/-!
# External verifiers

The Rust verifiers this package calls, and how to run them. Each tool's path is its environment
variable when set; otherwise the first three are the release examples of the `ix-aiurexec` fork's
checkout (`IXAI_AIUREXEC`, default `/home/sam/repos/forks/ix-aiurexec`), and `aiur_join_check`,
`ixw` and the store are this project's (`IxAI.projectDir`). The output names each tool's BLAKE3, which is part of what a
consumer trusts.

* `verify_claim PACKAGE.ixa PROOF ARGS OUTPUT` (`IXAI_VERIFY_CLAIM`): verifies one Aiur STARK
  proof of `entry(args) = output`, against the key recompiled from the package's program.
* `aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED COUNT` (`IXAI_AIUR_EXEC_CHECK`):
  checks what an `aiurExec` root claims against the specification. It does not verify the root's
  proof; that is bound by the compression certificate.
* `aiur_plonk_verify KEY KEY_BLAKE3 PROOF STATEMENT` (`IXAI_PLONK_VERIFY`): verifies a terminal
  PLONK certificate of the compression pipeline with gnark, against a verifying key it checks by
  BLAKE3 and whose KZG anchors must be Ix's release Ignition parameters, and a statement the
  caller computed (`IxAIVerify.Compression`).
* `aiur_join_check IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 ENV.ixe MANIFEST.ixes ROOT_DIR RUN_AGGR.ixa
  PROGRAM.ixa RUN_ROOT SPEC_ARGS EXPECTED COUNT STEPS THEOREM BINDING` (`IXAI_AIUR_JOIN_CHECK`,
  default `ix/toolchain-cert/bin/aiur_join_check`, built from the `ix-cert` fork): checks what a
  joined environment-and-training root claims against keys it recompiles from pinned artifacts, the
  environment's `CheckEnv` claim it rebuilds, and the run's endpoints and data computed from
  `SPEC_ARGS` and `EXPECTED`. Like `aiur_exec_check`, it does not verify the root's proof.
* `ixw verify PROOF` (`IXAI_IXW`): verifies an Ix (IxVM) proof from the local store
  (`IXAI_IX_STORE`), which the verifier also reads to compare the proof's claim with the expected
  one.
-/

namespace IxAIVerify

def projectDir : System.FilePath := IxAI.projectDir

/-- The checkout of the `ix-aiurexec` fork whose release examples are the default tools. -/
def defaultAiurExecFork : System.FilePath := "/home/sam/repos/forks/ix-aiurexec"

structure Tools where
  verifyClaim : String
  aiurExecCheck : String
  plonkVerify : String
  aiurJoinCheck : String
  ixw : String
  /-- The content-addressed Ix store `ixw` reads proofs from (`$HOME/.ix/store` of `ixw`). -/
  ixStore : System.FilePath

def Tools.fromEnv : IO Tools := do
  let get := fun (var dflt : String) => do return (← IO.getEnv var).getD dflt
  let examples := System.FilePath.mk (← get "IXAI_AIUREXEC" defaultAiurExecFork.toString) / "target" / "release" / "examples"
  return { verifyClaim := ← get "IXAI_VERIFY_CLAIM" (examples / "verify_claim").toString
           aiurExecCheck := ← get "IXAI_AIUR_EXEC_CHECK" (examples / "aiur_exec_check").toString
           plonkVerify := ← get "IXAI_PLONK_VERIFY" (examples / "aiur_plonk_verify").toString
           aiurJoinCheck := ← get "IXAI_AIUR_JOIN_CHECK" (projectDir / "ix" / "toolchain-cert" / "bin" / "aiur_join_check").toString
           ixw := ← get "IXAI_IXW" (projectDir / "ix" / "ixw").toString
           ixStore := ← get "IXAI_IX_STORE" (projectDir / ".truthmines" / ".ix" / "store").toString }

/-- The last `n` characters of `s`, without trailing whitespace. -/
def lastChars (s : String) (n : Nat) : String :=
  let cs := (s.toList.reverse.dropWhile Char.isWhitespace).reverse
  String.ofList (cs.drop (cs.length - n))

def fileDigest? (path : System.FilePath) : IO (Option IxAI.Digest) := do
  if ← path.pathExists then return some (IxAI.blake3 (← IO.FS.readBinFile path)) else return none

def fileDigestStr (path : System.FilePath) : IO String := do
  match ← fileDigest? path with
  | some d => return d.hex
  | none => return "missing"

/-- Run a command; `none` if it cannot be started. -/
def run? (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO (Option IO.Process.Output) := do
  try return some (← IO.Process.output { cmd, args, cwd })
  catch _ => return none

/-- Run `jobs` on `width` worker tasks, each taking the next job as soon as it finishes one;
results in the order of the list. -/
def runPool {α : Type} (width : Nat) (jobs : List (IO α)) : IO (List α) := do
  let queue := jobs.toArray
  let next ← IO.mkRef 0
  let worker : IO (List (Nat × α)) := do
    let mut out := []
    repeat
      let i ← next.modifyGet fun k => (k, k + 1)
      match queue[i]? with
      | some job => out := (i, ← job) :: out
      | none => break
    return out
  let tasks ← (List.range (max 1 (min width queue.size))).mapM fun _ => IO.asTask worker .dedicated
  let mut results : Array (Option α) := Array.replicate queue.size none
  for t in tasks do
    match ← IO.wait t with
    | .ok rs => for (i, a) in rs do results := results.set! i (some a)
    | .error e => throw e
  results.toList.mapM fun
    | some a => pure a
    | none => throw (IO.userError "runPool: a job has no result")

end IxAIVerify
