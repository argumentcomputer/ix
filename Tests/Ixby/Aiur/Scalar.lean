module
import Ix.Ixby.Aiur
import Ix.Aiur.Statistics
import Ix.Aiur.Interpret

namespace Tests.Ixby.Aiur.Scalar

open Ix.Ixby Ix.Ixby.AiurBackend

private def w (n : UInt32) : Value := .scalar (.word32 n)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def ext (a b : Nat) : Value :=
  .scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)

private def identity : Program := { functions := #[{
  arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }] }

private def primitiveProgram (op : Primitive) : Program := { functions := #[{
  arity := op.arity, blocks := #[
    ⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }] }

private def copyChain (blocks : Nat) (arity : Nat := 1) : Program := { functions := #[{
  arity, blocks := (Array.range blocks).map fun i =>
    ⟨arity + i, if i + 1 == blocks then .ret (.local (arity + i - 1))
      else .letOp (.copy (.local 0)) (i + 1)⟩ }] }

private def argsFor : Primitive → Array Value
  | .word32ToField => #[w 0xffffffff]
  | .word32Add | .word32And | .word32Or | .word32Xor | .word32Eq | .word32Lt =>
    #[w 0xfffffff0, w 0x21]
  | .fieldInverse => #[g 7]
  | .extInverse | .extFst | .extSnd => #[ext 7 11]
  | .extAdd | .extSub | .extMul | .extEq => #[ext 7 11, ext 13 17]
  | _ => #[g (goldilocksModulus - 1), g 2]

private structure Fixture where
  code : Codec.Bytes
  input : Codec.Bytes
  output : Codec.Bytes
  statement : Commitment.Statement

private def fixture (program : Program) (input : Array Value) : Except String Fixture := do
  validateFragment program
  unless input.all valueSupported do throw "unsupported fixture value"
  let code ← Codec.encodeProgram profile program |>.mapError (fun e => s!"code: {repr e}")
  let input ← Codec.encodeInput profile program input |>.mapError (fun e => s!"input: {repr e}")
  let execution ← Codec.execute profile code input profile.maxSteps
    |>.mapError (fun e => s!"reference execution: {repr e}")
  let statement ← Commitment.ofExecution execution |>.mapError (fun e => s!"statement: {repr e}")
  return ⟨code, input, execution.outputBytes, statement⟩

private def cp : Aiur.CommitmentParameters := { logBlowup := 2, capHeight := 0 }
/-- Test-only parameters, never a deployment security recommendation. -/
private def fri : Aiur.FriParameters := {
  logFinalPolyLen := 0, maxLogArity := 1, numQueries := 64,
  commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }

private def executeFixture (backend : ScalarSystem) (f : Fixture) : Except String Unit := do
  let (output, _, _) ← backend.execute f.statement f.code f.input
  unless output.isEmpty do throw "unexpected public output"

private def interpretFixture (backend : ScalarSystem) (f : Fixture) : Except String Unit := do
  let source ← scalarToplevel
  let decls ← source.mkDecls.mapError toString
  let s := f.statement
  let args := [s.profile, s.program, s.input, s.output].map fun d =>
    Aiur.Value.array ((digestFields d).map Aiur.Value.field)
  match Aiur.runFunction decls ⟨`ixby_scalar_exec⟩ args (artifactAdvice f.code f.input) with
  | (.error error, _) => throw s!"source interpreter: {error}"
  | (.ok value, _) =>
    let indices (g : Aiur.Global) := backend.compiled.getFuncIdx g.toName
    unless (Aiur.flattenValue decls indices value).isEmpty do throw "unexpected interpreter output"

private def printStats (backend : ScalarSystem) (label : String) (f : Fixture) : IO Unit := do
  let .ok (_, _, counts) := backend.execute f.statement f.code f.input
    | IO.eprintln s!"statistics execution failed: {label}"; return
  let stats := Aiur.computeStats backend.compiled counts backend.system.circuitShapes cp.logBlowup
  IO.println s!"{label}: {f.code.size} code bytes, {f.input.size} input bytes, {f.output.size} output bytes"
  IO.println "table | raw rows | padded rows | committed width | cache hits"
  for c in stats.circuits do
    let padded := if c.height ≤ 1 then c.height else 2 ^ ((c.height - 1).log2 + 1)
    IO.println s!"{c.name} | {c.height} | {padded} | {c.width} | {c.cacheHits}"
  IO.println s!"FFT-work surrogate (not measured proving time): {stats.totalFftCost}"

/-- Intentionally bypass BOTH host program admission and host execution.
Malformed bytes get matching commitments so a hash mismatch cannot stand in
for the circuit's parser/admission checks. -/
private def rawFixture (code input output : Codec.Bytes) : Except String Fixture := do
  let p ← Codec.encodeProfile profile |>.mapError (fun e => s!"{repr e}")
  return ⟨code, input, output, Commitment.Internal.bind p code input output⟩

private def rawProgram (program : Program) : Except String Codec.Bytes :=
  Codec.Internal.encode 65536 0 (Codec.Internal.writeProgram profile program)
    |>.mapError (fun e => s!"raw program: {repr e}")

private def replaceU32 (bytes : Codec.Bytes) (offset value : Nat) : Codec.Bytes :=
  bytes.extract 0 offset ++ bytesLE 4 value ++ bytes.extract (offset + 4) bytes.size

private def rawInput (body : Codec.Bytes) : Codec.Bytes :=
  "IXBI".toUTF8.data ++ bytesLE 4 0 ++ bytesLE 4 1 ++ body

private def negativeCases (base : Fixture) : List (String × Except String Fixture) :=
  let code (bytes : Codec.Bytes) := rawFixture bytes base.input base.output
  let input (bytes : Codec.Bytes) := rawFixture base.code bytes base.output
  let program (p : Program) := rawProgram p >>= code
  [ ("program magic", code (base.code.set! 0 0)),
    ("program wire revision", code (replaceU32 base.code 4 1)),
    ("program trailing bytes", code (base.code.push 0)),
    ("input magic", input (base.input.set! 0 0)),
    ("input wire revision", input (replaceU32 base.input 4 1)),
    ("input trailing bytes", input (base.input.push 0)),
    ("program byte limit", code (base.code ++ Array.replicate profile.programBytes 0)),
    ("input byte limit", input (base.input ++ Array.replicate profile.valueBytes 0)),
    ("nonzero program entry", code (replaceU32 base.code 8 1)),
    ("constructor table excluded", code (replaceU32 base.code 12 1)),
    ("multiple functions excluded", program { identity with functions := identity.functions ++ identity.functions }),
    ("hostile function count", code (replaceU32 base.code 16 0xffffffff)),
    ("nonzero function entry", code (replaceU32 base.code 24 1)),
    ("empty function", code (replaceU32 base.code 28 0)),
    ("hostile block count", code (replaceU32 base.code 28 0xffffffff)),
    ("block capacity", program (copyChain 65)),
    ("local capacity", do
      let c ← rawProgram (copyChain 64 2)
      let i := "IXBI".toUTF8.data ++ bytesLE 4 0 ++ bytesLE 4 2 ++
        #[0, 1] ++ bytesLE 4 7 ++ #[0, 1] ++ bytesLE 4 9
      rawFixture c i base.output),
    ("incoming frame mismatch", code (replaceU32 base.code 32 0)),
    ("out-of-bounds local", code (replaceU32 base.code 38 1)),
    ("unknown instruction", code (base.code.set! 36 255)),
    ("unknown operand", code (base.code.set! 37 255)),
    ("input arity mismatch", input (replaceU32 base.input 8 0)),
    ("hostile input count", input (replaceU32 base.input 8 0xffffffff)),
    ("Boolean 2", input (rawInput #[0, 0, 2])),
    ("noncanonical field modulus", input (rawInput (#[0, 2] ++ bytesLE 8 goldilocksModulus))),
    ("noncanonical maximum u64", input (rawInput (#[0, 2] ++ bytesLE 8 (2 ^ 64 - 1)))),
    ("noncanonical extension coefficient", input (rawInput
      (#[0, 3] ++ bytesLE 8 0 ++ bytesLE 8 goldilocksModulus))),
    ("unknown scalar tag", input (rawInput #[0, 255])),
    ("byte scalar outside slice", input (rawInput (#[0, 4] ++ bytesLE 4 0))),
    ("constructor value outside slice", input (rawInput #[1])),
    ("PAP outside slice", input (rawInput (#[2] ++ bytesLE 4 0 ++ bytesLE 4 0))),
    ("unknown value tag", input (rawInput #[255])),
    ("nonterminal final let", program { functions := #[{
      arity := 1, blocks := #[⟨1, .letOp (.copy (.local 0)) 0⟩] }] }),
    ("premature return with unused block", program { functions := #[{
      arity := 1, blocks := #[⟨1, .ret (.local 0)⟩, ⟨1, .ret (.local 0)⟩] }] }),
    ("nonsequential successor", program { functions := #[{
      arity := 1, blocks := #[⟨1, .letOp (.copy (.local 0)) 0⟩, ⟨2, .ret (.local 1)⟩] }] }),
    ("unsupported branching", program { functions := #[{
      arity := 1, blocks := #[⟨1, .branch (.local 0) 0 0⟩] }] }),
    ("unsupported tail call", program { functions := #[{
      arity := 1, blocks := #[⟨1, .tailCallSelf [.local 0]⟩] }] }),
    ("unsupported direct call", program { functions := #[{
      arity := 1, blocks := #[⟨1, .letOp (.callSelf [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩] }] }),
    ("primitive type mismatch", do
      let c ← rawProgram (primitiveProgram .fieldInverse)
      rawFixture c base.input base.output),
    ("well-formed wrong output", rawFixture base.code base.input
      ("IXBO".toUTF8.data ++ bytesLE 4 0 ++ #[0, 1] ++ bytesLE 4 9)) ]

private def successfulCases : List (String × Program × Array Value) :=
  [ ("identity Word32", identity, #[w 0x12345678]),
    ("identity false", identity, #[.scalar (.bool false)]),
    ("identity true", identity, #[.scalar (.bool true)]),
    ("identity maximum field", identity, #[g (goldilocksModulus - 1)]),
    ("identity extension", identity, #[ext (goldilocksModulus - 1) 11]),
    ("identity erased", identity, #[.erased]),
    ("word add without carry", primitiveProgram .word32Add, #[w 7, w 11]),
    ("word add wraps to zero", primitiveProgram .word32Add, #[w 0xffffffff, w 1]),
    ("word equality true", primitiveProgram .word32Eq, #[w 7, w 7]),
    ("word ordering true", primitiveProgram .word32Lt, #[w 7, w 11]),
    ("field equality true", primitiveProgram .fieldEq, #[g 7, g 7]),
    ("extension equality true", primitiveProgram .extEq, #[ext 7 11, ext 7 11]),
    ("local/block/step boundary with multi-chunk commitment", copyChain 64, #[w 7]),
    ("maximum input arity", { functions := #[{
      arity := 16, blocks := #[⟨16, .ret (.local 0)⟩] }] }, (Array.range 16).map (w ∘ Nat.toUInt32)),
    ("field inverse zero", primitiveProgram .fieldInverse, #[g 0]),
    ("extension inverse zero", primitiveProgram .extInverse, #[ext 0 0]),
    ("literal with no inputs", { functions := #[{
      arity := 0, blocks := #[⟨0, .ret (.literal (.word32 0xffffffff))⟩] }] }, #[]),
    ("erased operand", { functions := #[{
      arity := 0, blocks := #[⟨0, .ret .erased⟩] }] }, #[]),
    ("copy preserves absolute local", { functions := #[{
      arity := 2, blocks := #[
        ⟨2, .letOp (.primitive .word32Add [.local 0, .local 1]) 1⟩,
        ⟨3, .letOp (.copy (.local 0)) 2⟩,
        ⟨4, .ret (.local 3)⟩] }] }, #[w 0xffffffff, w 1]) ] ++
  ((cryptoPrimitives.toList.filter primitiveSupported).map fun op =>
    (s!"primitive {repr op}", primitiveProgram op, argsFor op))

public def suite (withProofs := true) (withStats := false) : IO UInt32 := do
  IO.println "ixby-aiur (experimental constrained scalar slice)"
  let built := ScalarSystem.build cp fri
  let .ok backend := built
    | IO.eprintln (match built with | .error e => e | _ => "scalar interpreter build failed"); return 1
  IO.println s!"{backend.compiled.bytecode.circuits.size} function circuits; one system for all guest programs"
  let programs := successfulCases.foldl (init := (#[] : Array Program)) fun acc (_, p, _) =>
    if acc.contains p then acc else acc.push p
  IO.println s!"{successfulCases.length} success cases over {programs.size} distinct guest programs"
  let mut passed := 0
  let mut failed := 0
  for (label, program, input) in successfulCases do
    match fixture program input >>= executeFixture backend with
    | .ok _ => passed := passed + 1; IO.println s!"  ✓ {label}"
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ {label}: {error}"
  let .ok base := fixture identity #[w 0x12345678]
    | IO.eprintln "base fixture failed"; return 1
  for (label, program, input) in [
      ("source interpreter identity", identity, #[w 0x12345678]),
      ("source interpreter local transport", primitiveProgram .word32Add, #[w 7, w 11])] do
    match fixture program input >>= interpretFixture backend with
    | .ok _ => passed := passed + 1; IO.println s!"  ✓ {label}"
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ {label}: {error}"
  let negatives := negativeCases base ++
    ((List.range base.code.size).map fun n =>
      (s!"program strict prefix {n}", rawFixture (base.code.extract 0 n) base.input base.output)) ++
    ((List.range base.input.size).map fun n =>
      (s!"input strict prefix {n}", rawFixture base.code (base.input.extract 0 n) base.output)) ++
    ((cryptoPrimitives.toList.filter (!primitiveSupported ·)).map fun op =>
      (s!"excluded primitive {repr op}", do
        let c ← rawProgram (primitiveProgram op)
        -- Match arity with scalar arguments so admission reaches the opcode.
        let args := Array.replicate op.arity (w 7)
        let i ← Codec.encodeInput profile (primitiveProgram op) args
          |>.mapError (fun e => s!"{repr e}")
        rawFixture c i base.output))
  for (label, result) in negatives do
    match result with
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ negative fixture {label}: {error}"
    | .ok f =>
      match backend.execute f.statement f.code f.input with
      | .error _ => passed := passed + 1
      | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ accepted {label}"
  IO.println s!"  tested {negatives.length} malformed/excluded artifacts with matching raw commitments"
  -- Also exercise malformed *field-valued* advice, before conversion to U8.
  let original := artifactAdvice base.code base.input
  let badData := (base.input.map Aiur.G.ofUInt8).set! 14 256
  let badByte := { original with data := original.data.insert 1 badData }
  let badInfo : Aiur.IOKeyInfo := { idx := 0, len := 2 ^ 32 }
  let badLength := { original with map := original.map.insert (0, #[0]) badInfo }
  for (label, advice) in [("advice byte 256", badByte), ("non-u32 advice length", badLength)] do
    match backend.compiled.bytecode.execute backend.entry (statementFields base.statement) advice with
    | .error _ => passed := passed + 1; IO.println s!"  ✓ {label} rejected"
    | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ accepted {label}"
  if (backend.prove base.statement (base.code.push 0) base.input).isOk then
    failed := failed + 1; IO.eprintln "  ✗ malformed prove request accepted"
  else
    passed := passed + 1; IO.println "  ✓ malformed prove request returns an error"
  if withStats then
    printStats backend "identity" base
    match fixture (copyChain 64) #[w 7] with
    | .ok f => printStats backend "64-block copy chain" f
    | .error e => IO.eprintln e
  if withProofs then
    -- A fresh verifier has no prover execution record and receives no program,
    -- input, or output advice. Its verifying key must be identical.
    let .ok verifier := ScalarSystem.build cp fri
      | IO.eprintln "fresh verifier build failed"; return 1
    let vk := backend.system.vkBytes
    if verifier.system.vkBytes == vk then
      passed := passed + 1; IO.println "  ✓ fresh verifier has the same key"
    else
      failed := failed + 1; IO.eprintln "  ✗ nondeterministic verifier key"
    for (label, program, input) in successfulCases do
      IO.println s!"  proving {label}"
      let start ← IO.monoMsNow
      let result := do
        let f ← fixture program input
        let proof ← backend.prove f.statement f.code f.input
        let bytes := proof.toBytes
        verifier.verifyBytes f.statement bytes
        return bytes.size
      match result with
      | .ok size =>
        passed := passed + 1
        let elapsed := (← IO.monoMsNow) - start
        IO.println s!"  ✓ {label}: {size} bytes, {elapsed} ms prove/round-trip/verify"
      | .error error => failed := failed + 1; IO.eprintln s!"  ✗ {label}: {error}"
    match backend.prove base.statement base.code base.input with
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ negative-test proof: {error}"
    | .ok proof =>
      let bytes := proof.toBytes
      let s := base.statement
      let mismatches := [
        ("profile", { s with profile := Commitment.hash .profile #[] }),
        ("program", { s with program := Commitment.hash .program #[] }),
        ("input", { s with input := Commitment.hash .input #[] }),
        ("output", { s with output := Commitment.hash .output #[] })]
      for (label, expected) in mismatches do
        match verifier.verify expected proof with
        | .error _ => passed := passed + 1; IO.println s!"  ✓ proof rejects changed {label}"
        | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ proof accepted changed {label}"
      -- The first encoded vector is the circuit activation Boolean vector:
      -- mutate a Boolean, not an arbitrary length that could request allocation.
      for (label, corrupted) in [
          ("empty", ByteArray.empty), ("truncated", bytes.extract 0 (bytes.size - 1)),
          ("trailing", bytes.push 0), ("invalid Boolean", bytes.set! 8 2),
          ("changed activation", bytes.set! 8 (bytes[8]! ^^^ 1))] do
        match verifier.verifyBytes base.statement corrupted with
        | .error _ => passed := passed + 1; IO.println s!"  ✓ {label} proof rejected"
        | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ {label} proof accepted"
    if backend.system.vkBytes == vk then
      passed := passed + 1; IO.println "  ✓ guest changes preserve the interpreter key"
    else
      failed := failed + 1; IO.eprintln "  ✗ guest-dependent key mutation"
  IO.println s!"{passed}/{passed + failed} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Aiur.Scalar
