module
import Ix.Ixby.Aiur
import Ix.Ixby.Aiur.Refinement
import Ix.Aiur.Statistics
import Ix.Aiur.Interpret

namespace Tests.Ixby.Aiur.Control

open Ix.Ixby Ix.Ixby.AiurBackend

private def w (n : UInt32) : Value := .scalar (.word32 n)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def ext (a b : Nat) : Value :=
  .scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)

private def identityFn : Function := { arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }
private def identity : Program := { functions := #[identityFn] }

private def primitiveFn (op : Primitive) : Function := {
  arity := op.arity, blocks := #[
    ⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }

private def branchCall : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .branch (.local 0) 2 1⟩,
    ⟨2, .letOp (.call 1 [.local 1, .literal (.word32 3)]) 3⟩,
    ⟨2, .letOp (.call 2 [.local 1, .literal (.word32 7)]) 3⟩,
    ⟨3, .letOp (.primitive .word32Add [.local 1, .local 2]) 4⟩,
    ⟨4, .ret (.local 3)⟩] }, primitiveFn .word32Add, primitiveFn .word32Xor] }

-- Both callers use their pre-call locals after returning. Subtraction makes
-- argument reversal visible; two nested returns test LIFO restoration.
private def nested : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .letOp (.call 1 [.local 1, .local 0]) 1⟩,
    ⟨3, .letOp (.primitive .fieldSub [.local 0, .local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }, {
  arity := 2, blocks := #[
    ⟨2, .letOp (.call 2 [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .fieldSub [.local 1, .local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }, primitiveFn .fieldSub] }

private def sumFn (tail : Bool) (callee : Option Nat := none) : Function := {
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive .word32Eq [.local 0, .literal (.word32 0)]) 1⟩,
    ⟨3, .branch (.local 2) 4 2⟩,
    ⟨3, .letOp (.primitive .word32Add [.local 0, .literal (.word32 0xffffffff)]) 3⟩,
    ⟨4, .letOp (.primitive .word32Add [.local 1, .local 0]) 5⟩,
    ⟨3, .ret (.local 1)⟩,
    ⟨5, if tail then match callee with
        | none => .tailCallSelf [.local 3, .local 4]
        | some f => .tailCall f [.local 3, .local 4]
      else .letOp (match callee with
        | none => .callSelf [.local 3, .local 4]
        | some f => .call f [.local 3, .local 4]) 6⟩] ++
    (if tail then #[] else #[⟨6, .ret (.local 5)⟩]) }

private def sumProgram (tail : Bool) : Program := { functions := #[sumFn tail] }

private def fuelWrapper (copies : Nat) : Program := { functions := #[{
  arity := 2, blocks := (Array.range (copies + 1)).map fun i =>
    ⟨2 + i, if i == copies then .tailCall 1 [.local 0, .local 1]
      else .letOp (.copy .erased) (i + 1)⟩ }, sumFn true] }

private def callChain (functions : Nat) (tail : Bool) : Program := {
  functions := (Array.range functions).map fun i =>
    if i + 1 == functions then identityFn
    else { arity := 1, blocks := if tail then #[⟨1, .tailCall (i + 1) [.local 0]⟩]
      else #[⟨1, .letOp (.call (i + 1) [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩] } }

private def fullStackTail : Program := { functions := #[
  { sumFn false with blocks := (sumFn false).blocks.set! 4 ⟨3, .tailCall 1 [.local 1]⟩ },
  identityFn] }

private def tailWithinCall : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .letOp (.call 1 [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .fieldSub [.local 0, .local 2]) 2⟩,
    ⟨4, .ret (.local 3)⟩] }, {
  arity := 2, blocks := #[⟨2, .tailCall 2 [.local 1, .local 0]⟩] }, primitiveFn .fieldSub] }

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
  validateControlFragment program
  unless input.all valueSupported do throw "unsupported fixture value"
  let code ← Codec.encodeProgram controlProfile program |>.mapError (fun e => s!"code: {repr e}")
  let input ← Codec.encodeInput controlProfile program input |>.mapError (fun e => s!"input: {repr e}")
  let execution ← Codec.execute controlProfile code input controlProfile.maxSteps
    |>.mapError (fun e => s!"reference execution: {repr e}")
  let statement ← Commitment.ofExecution execution |>.mapError (fun e => s!"statement: {repr e}")
  return ⟨code, input, execution.outputBytes, statement⟩

private def cp : Aiur.CommitmentParameters := { logBlowup := 2, capHeight := 0 }
/-- Test-only parameters, not a deployment security recommendation. -/
private def fri : Aiur.FriParameters := {
  logFinalPolyLen := 0, maxLogArity := 1, numQueries := 64,
  commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }

private def executeFixture (backend : ScalarSystem) (f : Fixture) : Except String Unit := do
  let (output, _, _) ← backend.execute f.statement f.code f.input
  unless output.isEmpty do throw "unexpected public output"

private def interpretFixture (f : Fixture) : Except String Unit := do
  let source ← controlToplevel
  let decls ← source.mkDecls.mapError toString
  let s := f.statement
  let args := [s.profile, s.program, s.input, s.output].map fun d =>
    Aiur.Value.array ((digestFields d).map Aiur.Value.field)
  match Aiur.runFunction decls ⟨`ixby_control_exec⟩ args (artifactAdvice f.code f.input) with
  | (.error error, _) => throw s!"source interpreter: {error}"
  | (.ok _, _) => pure ()

private def rawFixture (code input output : Codec.Bytes) : Except String Fixture := do
  let p ← Codec.encodeProfile controlProfile |>.mapError (fun e => s!"{repr e}")
  return ⟨code, input, output, Commitment.Internal.bind p code input output⟩

private def rawProgram (program : Program) : Except String Codec.Bytes :=
  Codec.Internal.encode 65536 0 (Codec.Internal.writeProgram controlProfile program)
    |>.mapError (fun e => s!"raw program: {repr e}")

private def replaceU32 (bytes : Codec.Bytes) (offset value : Nat) : Codec.Bytes :=
  bytes.extract 0 offset ++ bytesLE 4 value ++ bytes.extract (offset + 4) bytes.size

private def rawInput (values : Array Value) : Except String Codec.Bytes :=
  (Codec.Internal.encode 65536 65536 do
    Codec.Internal.writeHeader "IXBI"
    Codec.Internal.writeVector (Codec.Internal.writeValue controlProfile controlProfile.valueDepth) values)
  |>.mapError (fun e => s!"raw input: {repr e}")

private def successfulCases : List (String × Program × Array Value) :=
  [ ("identity word", identity, #[w 7]),
    ("identity false", identity, #[.scalar (.bool false)]),
    ("identity true", identity, #[.scalar (.bool true)]),
    ("identity field", identity, #[g (goldilocksModulus - 1)]),
    ("identity extension", identity, #[ext 7 11]),
    ("identity erased", identity, #[.erased]),
    ("branch/call/resume false", branchCall, #[.scalar (.bool false), w 17]),
    ("branch/call/resume true", branchCall, #[.scalar (.bool true), w 17]),
    ("nested calls restore locals and argument order", nested, #[g 17, g 5]),
    ("tail sum zero", sumProgram true, #[w 0, w 7]),
    ("tail sum one", sumProgram true, #[w 1, w 7]),
    ("50 tail calls do not grow the stack", sumProgram true, #[w 50, w 0]),
    ("self call zero", sumProgram false, #[w 0, w 7]),
    ("self call one", sumProgram false, #[w 1, w 7]),
    ("exact continuation capacity", sumProgram false, #[w 16, w 0]),
    ("tail call at full continuation capacity", fullStackTail, #[w 16, w 0]),
    ("tail call preserves an outer caller", tailWithinCall, #[g 17, g 5]),
    ("mutual tail calls", { functions := #[sumFn true (some 1), sumFn true (some 0)] }, #[w 25, w 0]),
    ("mutual non-tail calls", { functions := #[sumFn false (some 1), sumFn false (some 0)] }, #[w 8, w 0]),
    ("exact 256-transition budget", fuelWrapper 1, #[w 50, w 0]),
    ("eight-function direct chain", callChain 8 false, #[w 19]),
    ("eight-function tail chain", callChain 8 true, #[w 19]),
    ("nonzero program entry", { functions := #[identityFn, identityFn], entry := 1 }, #[w 11]),
    ("self call uses nonzero function identity", {
      functions := #[identityFn, sumFn false], entry := 1 }, #[w 3, w 0]),
    ("nonzero block entry and unused code", { functions := #[{
      arity := 1, entry := 1, blocks := #[⟨1, .ret (.literal (.word32 99))⟩,
        ⟨1, .letOp (.copy (.local 0)) 2⟩, ⟨2, .ret (.local 1)⟩] }] }, #[w 13]),
    ("backward successor after direct call", { functions := #[{
      arity := 1, entry := 2, blocks := #[⟨2, .ret (.local 1)⟩,
        ⟨0, .ret .erased⟩, ⟨1, .letOp (.call 1 [.local 0]) 0⟩] }, identityFn] }, #[w 13]),
    ("unused code may have dynamic type errors", {
      functions := #[identityFn, { arity := 0, blocks := #[
        ⟨0, .letOp (.primitive .fieldInverse [.literal (.word32 7)]) 1⟩,
        ⟨1, .ret (.local 0)⟩] }] }, #[w 13]),
    ("maximum local frame after call", { functions := #[{
      arity := 1, blocks := (Array.range 64).map fun i =>
        ⟨1 + i, if i == 63 then .ret (.local 63)
          else if i == 62 then .letOp (.call 1 [.local 0]) 63
          else .letOp (.copy .erased) (i + 1)⟩ }, identityFn] }, #[w 13]),
    ("zero-argument call and erased result", { functions := #[{
      arity := 0, blocks := #[⟨0, .letOp (.call 1 []) 1⟩, ⟨1, .ret (.local 0)⟩] },
      { arity := 0, blocks := #[⟨0, .ret .erased⟩] }] }, #[]),
    ("maximum argument arity", { functions := #[{
      arity := 16, blocks := #[⟨16, .tailCall 1 ((List.range 16).reverse.map Operand.local)⟩] },
      { arity := 16, blocks := #[⟨16, .ret (.local 0)⟩] }] },
      (Array.range 16).map (w ∘ Nat.toUInt32)) ] ++
  ((cryptoPrimitives.toList.filter primitiveSupported).map fun op =>
    (s!"primitive {repr op}", { functions := #[primitiveFn op] }, argsFor op))

-- These artifacts bypass both host admission and reference execution and have
-- matching raw commitments. A hash mismatch cannot substitute for rejection.
private def negativeCases (base : Fixture) : List (String × Except String Fixture) :=
  let code (bytes : Codec.Bytes) := rawFixture bytes base.input base.output
  let input (bytes : Codec.Bytes) := rawFixture base.code bytes base.output
  let program (p : Program) := rawProgram p >>= code
  let dead (blocks : Array Block) := program { functions := #[identityFn, { arity := 1, blocks }] }
  let run (p : Program) (values : Array Value) := do
    rawFixture (← rawProgram p) (← rawInput values) base.output
  [ ("program magic", code (base.code.set! 0 0)),
    ("program revision", code (replaceU32 base.code 4 1)),
    ("trailing program bytes", code (base.code.push 0)),
    ("program byte cap", code (base.code ++ Array.replicate controlProfile.programBytes 0)),
    ("program entry out of bounds", code (replaceU32 base.code 8 1)),
    ("constructor table excluded", code (replaceU32 base.code 12 1)),
    ("empty program", code (replaceU32 base.code 16 0)),
    ("hostile function count", code (replaceU32 base.code 16 0xffffffff)),
    ("ninth function", program (callChain 9 true)),
    ("hostile arity", code (replaceU32 base.code 20 0xffffffff)),
    ("function entry out of bounds", code (replaceU32 base.code 24 1)),
    ("empty function", code (replaceU32 base.code 28 0)),
    ("hostile block count", code (replaceU32 base.code 28 0xffffffff)),
    ("65 blocks", program { functions := #[{ identityFn with blocks := Array.replicate 65 ⟨1, .ret (.local 0)⟩ }] }),
    ("local capacity", code (replaceU32 base.code 32 65)),
    ("incoming frame mismatch", code (replaceU32 base.code 32 0)),
    ("local out of bounds", code (replaceU32 base.code 38 1)),
    ("unknown instruction", code (base.code.set! 36 255)),
    ("unknown operand", code (base.code.set! 37 255)),
    ("dead forward local", dead #[⟨1, .ret (.local 1)⟩]),
    ("dead invalid entry frame", dead #[⟨0, .ret .erased⟩]),
    ("dead missing call", dead #[⟨1, .letOp (.call 8 [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead call arity", dead #[⟨1, .letOp (.call 0 []) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead self-call arity", dead #[⟨1, .letOp (.callSelf []) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead tail-call arity", dead #[⟨1, .tailCallSelf []⟩]),
    ("dead tail-call target", dead #[⟨1, .tailCall 99 [.local 0]⟩]),
    ("dead branch target", dead #[⟨1, .branch (.local 0) 0 1⟩]),
    ("dead branch frame", dead #[⟨1, .branch (.local 0) 0 1⟩, ⟨2, .ret (.local 0)⟩]),
    ("dead return-resume frame", dead #[⟨1, .letOp (.call 0 [.local 0]) 1⟩, ⟨1, .ret (.local 0)⟩]),
    ("dead primitive arity", dead #[⟨1, .letOp (.primitive .word32Add [.local 0]) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead excluded primitive", dead (primitiveFn .word32Sub).blocks),
    ("dead closure", dead #[⟨1, .letOp (.closure 0 []) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead application", dead #[⟨1, .letOp (.apply .erased []) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead tail application", dead #[⟨1, .tailApply .erased []⟩]),
    ("dead construction", dead #[⟨1, .letOp (.construct 0 []) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead projection", dead #[⟨1, .letOp (.project .erased 0) 1⟩, ⟨2, .ret (.local 1)⟩]),
    ("dead constructor case", dead #[⟨1, .caseCtor .erased []⟩]),
    ("input magic", input (base.input.set! 0 0)),
    ("input revision", input (replaceU32 base.input 4 1)),
    ("trailing input", input (base.input.push 0)),
    ("input byte cap", input (base.input ++ Array.replicate controlProfile.valueBytes 0)),
    ("input arity", input (replaceU32 base.input 8 0)),
    ("noncanonical Bool", input (base.input.extract 0 12 ++ #[0, 0, 2])),
    ("noncanonical field", input (base.input.extract 0 12 ++ #[0, 2] ++ bytesLE 8 goldilocksModulus)),
    ("bytes excluded", run identity #[.scalar (.bytes #[])]),
    ("PAP excluded", input (base.input.extract 0 12 ++ #[2] ++ bytesLE 4 0 ++ bytesLE 4 0)),
    ("non-Boolean branch", run branchCall #[w 1, w 17]),
    ("primitive dynamic type", run { functions := #[primitiveFn .fieldInverse] } #[w 7]),
    ("continuation overflow", run (sumProgram false) #[w 17, w 0]),
    ("one step over budget", run (fuelWrapper 2) #[w 50, w 0]),
    ("nonterminating tail call", run { functions := #[{
      arity := 1, blocks := #[⟨1, .tailCallSelf [.local 0]⟩] }] } #[w 7]),
    ("nonterminating branch", run { functions := #[{
      arity := 1, blocks := #[⟨1, .branch (.local 0) 0 0⟩] }] } #[.scalar (.bool true)]),
    ("callee result cannot replace caller result", do
      let f ← fixture branchCall #[.scalar (.bool true), w 17]
      rawFixture f.code f.input ("IXBO".toUTF8.data ++ bytesLE 4 0 ++ #[0, 1] ++ bytesLE 4 (17 ^^^ 7))),
    ("wrong branch result", do
      let yes ← fixture branchCall #[.scalar (.bool true), w 17]
      let no ← fixture branchCall #[.scalar (.bool false), w 17]
      rawFixture yes.code yes.input no.output),
    ("wrong output", rawFixture base.code base.input
      ("IXBO".toUTF8.data ++ bytesLE 4 0 ++ #[0, 1] ++ bytesLE 4 9)) ]

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

public def suite (withProofs := true) (withStats := false) : IO UInt32 := do
  IO.println "ixby-control (experimental constrained scalar CEK slice)"
  let built := ScalarSystem.buildControl cp fri
  let .ok backend := built
    | IO.eprintln (match built with | .error e => e | _ => "control interpreter build failed"); return 1
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
  let .ok base := fixture identity #[w 7]
    | IO.eprintln "base fixture failed"; return 1
  for (label, program, input) in [
      ("source interpreter branch/call/resume", branchCall, #[.scalar (.bool true), w 17]),
      ("source interpreter nested restoration", nested, #[g 17, g 5]),
      ("source interpreter self call", sumProgram false, #[w 2, w 0])] do
    match fixture program input >>= interpretFixture with
    | .ok _ => passed := passed + 1; IO.println s!"  ✓ {label}"
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ {label}: {error}"
  let negatives := negativeCases base ++
    ((List.range base.code.size).map fun n =>
      (s!"program strict prefix {n}", rawFixture (base.code.extract 0 n) base.input base.output)) ++
    ((List.range base.input.size).map fun n =>
      (s!"input strict prefix {n}", rawFixture base.code (base.input.extract 0 n) base.output))
  for (label, result) in negatives do
    match result with
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ negative fixture {label}: {error}"
    | .ok f =>
      match backend.execute f.statement f.code f.input with
      | .error _ => passed := passed + 1
      | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ accepted {label}"
  IO.println s!"  tested {negatives.length} malformed/excluded/nonterminal artifacts with matching commitments"
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
    for (label, program, input) in [
        ("branch/call/resume", branchCall, #[.scalar (.bool true), w 17]),
        ("16 saved frames", sumProgram false, #[w 16, w 0]),
        ("50 tail calls", sumProgram true, #[w 50, w 0])] do
      match fixture program input with
      | .ok f => printStats backend label f
      | .error e => IO.eprintln e
  if withProofs then
    let .ok verifier := ScalarSystem.buildControl cp fri
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
        IO.println s!"  ✓ {label}: {size} bytes, {(← IO.monoMsNow) - start} ms prove/round-trip/verify"
      | .error error => failed := failed + 1; IO.eprintln s!"  ✗ {label}: {error}"
    let .ok branch := fixture branchCall #[.scalar (.bool true), w 17]
      | IO.eprintln "branch proof fixture failed"; return 1
    match backend.prove branch.statement branch.code branch.input with
    | .error error => failed := failed + 1; IO.eprintln s!"  ✗ negative-test proof: {error}"
    | .ok proof =>
      let s := branch.statement
      for (label, expected) in [
          ("profile", { s with profile := Commitment.hash .profile #[] }),
          ("program", { s with program := Commitment.hash .program #[] }),
          ("input", { s with input := Commitment.hash .input #[] }),
          ("output", { s with output := Commitment.hash .output #[] })] do
        match verifier.verify expected proof with
        | .error _ => passed := passed + 1; IO.println s!"  ✓ proof rejects changed {label}"
        | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ proof accepted changed {label}"
      let bytes := proof.toBytes
      for (label, corrupted) in [
          ("empty", ByteArray.empty), ("truncated", bytes.extract 0 (bytes.size - 1)),
          ("trailing", bytes.push 0), ("invalid Boolean", bytes.set! 8 2),
          ("changed activation", bytes.set! 8 (bytes[8]! ^^^ 1))] do
        match verifier.verifyBytes s corrupted with
        | .error _ => passed := passed + 1; IO.println s!"  ✓ {label} proof rejected"
        | .ok _ => failed := failed + 1; IO.eprintln s!"  ✗ {label} proof accepted"
    if backend.system.vkBytes == vk then
      passed := passed + 1; IO.println "  ✓ control-flow and guest changes preserve the interpreter key"
    else
      failed := failed + 1; IO.eprintln "  ✗ guest-dependent key mutation"
  IO.println s!"{passed}/{passed + failed} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Aiur.Control
