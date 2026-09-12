module
import Tests.Ixby.Aiur.Common

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

private def fixture (program : Program) (input : Array Value) : Except String Fixture := do
  validateFragment program
  unless input.all valueSupported do throw "unsupported fixture value"
  Fixture.encode profile program input

/-- Intentionally bypass BOTH host program admission and host execution.
Malformed bytes get matching commitments so a hash mismatch cannot stand in
for the circuit's parser/admission checks. -/
private def rawFixture := Fixture.raw profile

private def rawProgram := encodeRawProgram profile

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

private def buildBackend : IO (Except String System) := buildFresh System.buildScalar

public def suite (withProofs := true) (withStats := false) : IO UInt32 :=
    runChecks "ixby-aiur" do
  IO.println "ixby-aiur (experimental constrained scalar slice)"
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
  let .ok base := fixture identity #[w 0x12345678]
    | return checks ++ [("base fixture failed", false)]
  for (label, program, input) in [
      ("source interpreter identity", identity, #[w 0x12345678]),
      ("source interpreter local transport", primitiveProgram .word32Add, #[w 7, w 11])] do
    checks := checks ++ [succeeds label (fixture program input >>= interpretFixture backend scalarToplevel `ixby_scalar_exec)]
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
    | .error error => checks := checks ++ [(s!"negative fixture {label}: {error}", false)]
    | .ok f =>
      match backend.execute f.statement f.code f.input with
      | .error _ => checks := checks ++ [(s!"rejects {label}", true)]
      | .ok _ => checks := checks ++ [(s!"rejects {label}", false)]
  IO.println s!"  tested {negatives.length} malformed/excluded artifacts with matching raw commitments"
  checks := checks ++ preflightChecks backend base
  if withStats then
    printStats backend "identity" base
    match fixture (copyChain 64) #[w 7] with
    | .ok f => printStats backend "64-block copy chain" f
    | .error e => IO.eprintln e
  if withProofs then
    checks := checks ++ (← proofChecks backend buildBackend
      (successfulCases.map (fun (label, program, input) => (label, fixture program input))) (.ok base))
  return checks

end Tests.Ixby.Aiur.Scalar
