module
public import Tests.Ixby.Common
public import Tests.Aiur.Common
public import Ix.Ixby.Aiur

/-! Shared fixtures for the experimental IxBy adapters. These tests deliberately
use System.prove/verify/verifyBytes, including statement binding and malformed
requests; the generic Aiur harness does not exercise that public boundary. -/

public section

namespace Tests.Ixby.Aiur

open Ix.Ixby Ix.Ixby.AiurBackend

/-- Keep the builder opaque to closed-term extraction: each IO invocation
must construct a fresh native system for the independent-verifier tests. -/
@[noinline] def buildFresh
    (build : Aiur.CommitmentParameters → Aiur.FriParameters → Except String System) :
    IO (Except String System) := do
  return build commitmentParameters friParameters

structure Fixture where
  code : Codec.Bytes
  input : Codec.Bytes
  output : Codec.Bytes
  statement : Commitment.Statement

/-- Callers retain their backend-specific admission and expected-value checks. -/
def Fixture.encode (profile : Profile) (program : Program) (input : Array Value) :
    Except String Fixture := do
  let code ← Codec.encodeProgram profile program |>.mapError (fun e => s!"code: {repr e}")
  let input ← Codec.encodeInput profile program input |>.mapError (fun e => s!"input: {repr e}")
  let execution ← Codec.execute profile code input profile.maxSteps
    |>.mapError (fun e => s!"reference execution: {repr e}")
  let statement ← Commitment.ofExecution execution |>.mapError (fun e => s!"statement: {repr e}")
  return ⟨code, input, execution.outputBytes, statement⟩

/-- Bypass host admission and execution. Matching raw commitments ensure a
hash mismatch cannot substitute for the circuit's parser/runtime rejection. -/
def Fixture.raw (profile : Profile) (code input output : Codec.Bytes) : Except String Fixture := do
  let p ← Codec.encodeProfile profile |>.mapError (fun e => s!"{repr e}")
  return ⟨code, input, output, Commitment.Internal.bind p code input output⟩

def encodeRawProgram (profile : Profile) (program : Program) : Except String Codec.Bytes :=
  Codec.Internal.encode 65536 0 (Codec.Internal.writeProgram profile program)
    |>.mapError (fun e => s!"raw program: {repr e}")

def replaceU32 (bytes : Codec.Bytes) (offset value : Nat) : Codec.Bytes :=
  bytes.extract 0 offset ++ bytesLE 4 value ++ bytes.extract (offset + 4) bytes.size

def executeFixture (backend : System) (f : Fixture) : Except String Unit := do
  let (output, _, _) ← backend.execute f.statement f.code f.input
  unless output.isEmpty do throw "unexpected public output"

def interpretFixture (backend : System) (source : Except String Aiur.Source.Toplevel)
    (entry : Lean.Name) (f : Fixture) : Except String Unit := do
  let source ← source
  let decls ← source.mkDecls.mapError toString
  let s := f.statement
  let args := [s.profile, s.program, s.input, s.output].map fun d =>
    Aiur.Value.array ((digestFields d).map Aiur.Value.field)
  match Aiur.runFunction decls ⟨entry⟩ args (artifactAdvice f.code f.input) with
  | (.error error, _) => throw s!"source interpreter: {error}"
  | (.ok value, _) =>
    let indices (g : Aiur.Global) := backend.compiled.getFuncIdx g.toName
    unless (Aiur.flattenValue decls indices value).isEmpty do throw "unexpected interpreter output"

def printStats (backend : System) (label : String) (f : Fixture) : IO Unit := do
  let .ok (_, _, counts) := backend.execute f.statement f.code f.input
    | IO.eprintln s!"statistics execution failed: {label}"; return
  let stats := Aiur.computeStats backend.compiled counts backend.system.circuitShapes
    commitmentParameters.logBlowup
  IO.println s!"{label}: {f.code.size} code bytes, {f.input.size} input bytes, {f.output.size} output bytes"
  IO.println "table | raw rows | padded rows | committed width | cache hits"
  for c in stats.circuits do
    let padded := if c.height ≤ 1 then c.height else 2 ^ ((c.height - 1).log2 + 1)
    IO.println s!"{c.name} | {c.height} | {padded} | {c.width} | {c.cacheHits}"
  IO.println s!"FFT-work surrogate (not measured proving time): {stats.totalFftCost}"

/-- Check field-valued advice before conversion to bytes, and the public
prover's malformed-request preflight. -/
def preflightChecks (backend : System) (base : Fixture) : List Check :=
  let original := artifactAdvice base.code base.input
  let badData := (base.input.map Aiur.G.ofUInt8).set! 14 256
  let badByte := { original with data := original.data.insert 1 badData }
  let badInfo : Aiur.IOKeyInfo := { idx := 0, len := 2 ^ 32 }
  let badLength := { original with map := original.map.insert (0, #[0]) badInfo }
  [( "advice byte 256 rejected",
      !(backend.compiled.bytecode.execute backend.entry (statementFields base.statement) badByte).isOk),
   ( "non-u32 advice length rejected",
      !(backend.compiled.bytecode.execute backend.entry (statementFields base.statement) badLength).isOk),
   ( "malformed prove request returns an error",
      !(backend.prove base.statement (base.code.push 0) base.input).isOk)]

/-- A separately built verifier has no prover execution record and receives no
artifact advice. Keep every statement mismatch and checked-decoder mutation at
the IxBy adapter boundary. The IO builder also avoids module-initialization work. -/
def proofChecks (backend : System) (buildVerifier : IO (Except String System))
    (cases : List (String × Except String Fixture)) (negative : Except String Fixture) :
    IO (List Check) := do
  let .ok verifier ← buildVerifier
    | return [("fresh verifier build failed", false)]
  let vk := backend.system.vkBytes
  let mut checks := [("fresh verifier has the same key", verifier.system.vkBytes == vk)]
  for (label, result) in cases do
    IO.println s!"  proving {label}"
    let start ← IO.monoMsNow
    let result := do
      let f ← result
      let proof ← backend.prove f.statement f.code f.input
      let bytes := proof.toBytes
      verifier.verifyBytes f.statement bytes
      return bytes.size
    checks := checks ++ [succeeds (s!"prove/round-trip/verify {label}") result]
    if let .ok size := result then
      IO.println s!"  {label}: {size} bytes, {(← IO.monoMsNow) - start} ms prove/round-trip/verify"
  let proof := do
    let f ← negative
    let proof ← backend.prove f.statement f.code f.input
    return (f.statement, proof)
  match proof with
  | .error error => checks := checks ++ [(s!"negative-test proof: {error}", false)]
  | .ok (s, proof) =>
    for (label, expected) in [
        ("profile", { s with profile := Commitment.hash .profile #[] }),
        ("program", { s with program := Commitment.hash .program #[] }),
        ("input", { s with input := Commitment.hash .input #[] }),
        ("output", { s with output := Commitment.hash .output #[] })] do
      checks := checks ++ [(s!"proof rejects changed {label}", !(verifier.verify expected proof).isOk)]
    let bytes := proof.toBytes
    -- Mutate the first activation Boolean, not a length that could request allocation.
    for (label, corrupted) in [
        ("empty", ByteArray.empty), ("truncated", bytes.extract 0 (bytes.size - 1)),
        ("trailing", bytes.push 0), ("invalid Boolean", bytes.set! 8 2),
        ("changed activation", bytes.set! 8 (bytes[8]! ^^^ 1))] do
      checks := checks ++ [(s!"{label} proof rejected", !(verifier.verifyBytes s corrupted).isOk)]
  return checks ++ [("guest changes preserve the interpreter key", backend.system.vkBytes == vk)]

end Tests.Ixby.Aiur
