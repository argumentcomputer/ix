import Ix.Aiur.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Compiler
import Ix.Aiur.Statistics
import Ix.MultiStark
import Ix.Keccak

open Aiur

/-!
# Recursive-verifier cost benchmark (Keccak baseline port)

A/B baseline for the Blake3 branch's `Benchmarks/RecursiveVerifier.lean`,
against this commit's Keccak-based multi-stark: proves `factorial(5)`,
executes `verify_multi_stark_proof` over the proof, then proves and verifies
that execution. Same parameters as the Blake3 side (`logBlowup := 2`,
`numQueries := 3`, `commitProofOfWorkBits := 20`).
-/

def factorialProgram : Source.Toplevel := ⟦
  pub fn factorial(n: G) -> G {
    match n {
      0 => 1,
      _ => n * factorial(n - 1),
    }
  }
⟧

/-- The most trivial provable statement (`--trivial`): one non-recursive
function, no memory — the floor of the verifier's per-statement cost. -/
def squareProgram : Source.Toplevel := ⟦
  pub fn square(n: G) -> G {
    n * n
  }
⟧

/-- `--queries N`-style overrides for the parameter sweep; defaults mirror the
Blake3 branch's bench (logBlowup 2, 3 queries, 20 commit-PoW bits). -/
def argNat (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => v.toNat?.getD dflt
  | _ => dflt

def recCommitParams (args : List String) : Aiur.CommitmentParameters :=
  { logBlowup := argNat args "--blowup" 2, capHeight := 0 }
def innerFri (args : List String) : Aiur.FriParameters :=
  { logFinalPolyLen := argNat args "--final-poly" 0, maxLogArity := 1,
    numQueries := argNat args "--queries" 3,
    commitProofOfWorkBits := argNat args "--pow" 20, queryProofOfWorkBits := 0 }

def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Serialize the public claims for the verifier's IO channel (matches the
in-circuit `read_claims` wire format). -/
def serializeClaims (claims : Array (Array Aiur.G)) : ByteArray := Id.run do
  let mut out : Array UInt8 := u64le claims.size
  for c in claims do
    out := out ++ u64le c.size
    for g in c do
      out := out ++ u64le g.val.toNat
  return ⟨out⟩

def main (args : List String) : IO Unit := do
  let doProve := !args.contains "--execute-only"
  let recCommitParams := recCommitParams args
  let innerFri := innerFri args
  IO.println s!"params: logBlowup={recCommitParams.logBlowup} \
    numQueries={innerFri.numQueries} finalPoly={innerFri.logFinalPolyLen} \
    pow={innerFri.commitProofOfWorkBits}"
  let trivial := args.contains "--trivial"
  let (program, entry) :=
    if trivial then (squareProgram, `square) else (factorialProgram, `factorial)
  let facCompiled ← match program.compile with
    | .ok c => pure c | .error e => IO.eprintln s!"inner compile failed: {e}"; return
  let facSystem := AiurSystem.build facCompiled.bytecode recCommitParams
  let facIdx := facCompiled.getFuncIdx entry |>.get!
  IO.println s!"proving inner {entry} (5)…"
  let it0 ← IO.monoNanosNow
  let (claim, proof, _) := facSystem.prove innerFri facIdx #[Aiur.G.ofNat 5] default
  let proofBytes := proof.toBytes
  let it1 ← IO.monoNanosNow
  let innerOk := facSystem.verify innerFri claim proof matches .ok _
  let it2 ← IO.monoNanosNow
  IO.println s!"inner PROVE: {(Float.ofNat (it1 - it0)) / 1e9} s, \
    proof {proofBytes.size} bytes; inner VERIFY: \
    {(Float.ofNat (it2 - it1)) / 1e9} s ({if innerOk then "ok" else "FAILED"})"
  -- Proof (advice, channel 0), vk (channel 1), claims (channel 2), plus the
  -- Keccak-bound vk/claims digests and FRI params as public input.
  let proofGs : Array Aiur.G := proofBytes.data.map .ofUInt8
  let vkBytes := facSystem.vkBytes
  let sysDigestInput : Array Aiur.G := (Keccak.hash vkBytes).data.map .ofUInt8
  let vkGs : Array Aiur.G := vkBytes.data.map .ofUInt8
  let claimBytes := serializeClaims #[claim]
  let claimsDigestInput : Array Aiur.G := (Keccak.hash claimBytes).data.map .ofUInt8
  let claimGs : Array Aiur.G := claimBytes.data.map .ofUInt8
  let friParamInput : Array Aiur.G :=
    #[Aiur.G.ofNat innerFri.numQueries, Aiur.G.ofNat innerFri.commitProofOfWorkBits,
      Aiur.G.ofNat recCommitParams.logBlowup]
  let pubInput : Array Aiur.G := sysDigestInput ++ claimsDigestInput ++ friParamInput
  let io := (((default : IOBuffer).extend 0 #[Aiur.G.ofNat 0] proofGs).extend
      1 #[Aiur.G.ofNat 0] vkGs).extend 2 #[Aiur.G.ofNat 0] claimGs
  -- Compile the verifier toplevel and run it over the proof.
  let vTop ← match MultiStark.multiStark with
    | .ok t => pure t | .error e => IO.eprintln s!"verifier merge failed: {e}"; return
  let vCompiled ← match vTop.compile with
    | .ok c => pure c | .error e => IO.eprintln s!"verifier compile failed: {e}"; return
  let vIdx := vCompiled.getFuncIdx `verify_multi_stark_proof |>.get!
  IO.println "executing verify_multi_stark_proof…"
  let e0 ← IO.monoNanosNow
  match vCompiled.bytecode.execute vIdx pubInput io with
  | .error e => IO.eprintln s!"verifier execution failed: {e}"
  | .ok (out, _, qc) =>
    let e1 ← IO.monoNanosNow
    let stats := Aiur.computeStats vCompiled qc
    IO.println s!"verifier output (accept): {out}, \
      execute {(Float.ofNat (e1 - e0)) / 1e9} s"
    IO.println s!"\n=== recursive verifier in-circuit cost ==="
    IO.println s!"totalFftCost = {stats.totalFftCost}"
    IO.println "\n=== per-circuit breakdown (top FFT contributors) ==="
    Aiur.printStats stats
    if doProve then
      IO.println "\n=== PROVING the verifier (multi-stark) ==="
      let vSystem := AiurSystem.build vCompiled.bytecode recCommitParams
      let t0 ← IO.monoNanosNow
      let (vclaim, vproof, _) := vSystem.prove innerFri vIdx pubInput io
      let nbytes := vproof.toBytes.size  -- force the (lazy, pure) prove to run
      let t1 ← IO.monoNanosNow
      let outerOk := vSystem.verify innerFri vclaim vproof matches .ok _
      let t2 ← IO.monoNanosNow
      IO.println s!"verifier PROVE time: {(Float.ofNat (t1 - t0)) / 1e9} s, proof {nbytes} bytes"
      IO.println s!"verifier proof VERIFY time: \
        {(Float.ofNat (t2 - t1)) / 1e9} s ({if outerOk then "ok" else "FAILED"})"
