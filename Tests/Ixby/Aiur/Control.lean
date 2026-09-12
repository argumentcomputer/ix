module
import Tests.Ixby.Aiur.Common
import Ix.Ixby.Aiur.Refinement

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

private def fixture (program : Program) (input : Array Value) : Except String Fixture := do
  validateControlFragment program
  unless input.all valueSupported do throw "unsupported fixture value"
  Fixture.encode controlProfile program input

private def rawFixture := Fixture.raw controlProfile

private def rawProgram := encodeRawProgram controlProfile

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

private def buildBackend : IO (Except String System) := buildFresh System.buildControl

public def suite (withProofs := true) (withStats := false) : IO UInt32 :=
    runChecks "ixby-control" do
  IO.println "ixby-control (experimental constrained scalar CEK slice)"
  let built ← buildBackend
  let .ok backend := built
    | return [succeeds "interpreter build" built]
  IO.println s!"{backend.compiled.bytecode.circuits.size} function circuits; one system for all guest programs"
  let programs := successfulCases.foldl (init := (#[] : Array Program)) fun acc (_, p, _) =>
    if acc.contains p then acc else acc.push p
  IO.println s!"{successfulCases.length} success cases over {programs.size} distinct guest programs"
  let mut checks : List Check := []
  for (label, program, input) in successfulCases do
    checks := checks ++ [succeeds label (fixture program input >>= executeFixture backend)]
  let .ok base := fixture identity #[w 7]
    | return checks ++ [("base fixture failed", false)]
  for (label, program, input) in [
      ("source interpreter branch/call/resume", branchCall, #[.scalar (.bool true), w 17]),
      ("source interpreter nested restoration", nested, #[g 17, g 5]),
      ("source interpreter self call", sumProgram false, #[w 2, w 0])] do
    checks := checks ++ [succeeds label (fixture program input >>= interpretFixture backend controlToplevel `ixby_control_exec)]
  let negatives := negativeCases base ++
    ((List.range base.code.size).map fun n =>
      (s!"program strict prefix {n}", rawFixture (base.code.extract 0 n) base.input base.output)) ++
    ((List.range base.input.size).map fun n =>
      (s!"input strict prefix {n}", rawFixture base.code (base.input.extract 0 n) base.output))
  for (label, result) in negatives do
    match result with
    | .error error => checks := checks ++ [(s!"negative fixture {label}: {error}", false)]
    | .ok f =>
      match backend.execute f.statement f.code f.input with
      | .error _ => checks := checks ++ [(s!"rejects {label}", true)]
      | .ok _ => checks := checks ++ [(s!"rejects {label}", false)]
  IO.println s!"  tested {negatives.length} malformed/excluded/nonterminal artifacts with matching commitments"
  checks := checks ++ preflightChecks backend base
  if withStats then
    for (label, program, input) in [
        ("branch/call/resume", branchCall, #[.scalar (.bool true), w 17]),
        ("16 saved frames", sumProgram false, #[w 16, w 0]),
        ("50 tail calls", sumProgram true, #[w 50, w 0])] do
      match fixture program input with
      | .ok f => printStats backend label f
      | .error e => IO.eprintln e
  if withProofs then
    checks := checks ++ (← proofChecks backend buildBackend
      (successfulCases.map (fun (label, program, input) => (label, fixture program input))) (fixture branchCall #[.scalar (.bool true), w 17]))
  return checks

end Tests.Ixby.Aiur.Control
