import Ix.Compiler.X86.ELFValidate
import Ix.Compiler.X86.EvalExamples
import Ix.Compiler.X86.Select
import Ix.Compiler.X86.ValidatedScalar

/-! Operational fixture generator for the external ELF/binutils gate. -/

open Ix.Compiler
open Ix.Compiler.X86
open Ix.Compiler.Ixon

private def usage : String :=
  "usage: lake exe compiler-x86-object-fixture (arithmetic|direct-call|runtime|selected-scalar|validated-scalar) <output.o> [natural for validated-scalar]"

/-- Default provenance for the hand-written target and IxIR₂ fixtures.
The validated Ixon fixture replaces it with its actual addressed IxIR₁ root. -/
private def fixtureProvenance : X86.ELF.Provenance :=
  .ixir1Policy (Address.replicate 0x42) 1 1

private structure Fixture where
  program : Program
  runtime : Runtime
  sourceResult : Option Word := none
  sourceRoot : Option Address := none
  provenance : X86.ELF.Provenance := fixtureProvenance

private def selectedScalarFixture : Except String Fixture := do
  let source := X86.Select.scalarMoveProgram 42
  let selected ← match X86.Select.select source with
    | .ok output => pure output
    | .error error => throw s!"IxIR₂ selection failed: {repr error}"
  let sourceRun ←
    match IxIR2.Eval.runMain (X86.Select.sourceContext 42) .physical source 3 0 with
    | .ok result => pure result
    | .error error => throw s!"IxIR₂ execution failed: {repr error}"
  let sourceWord ← match sourceRun.value with
    | .lit (.nat number) =>
        let word := UInt64.ofNat number
        if word.toNat == number then pure word
        else throw "IxIR₂ result exceeded the selected 64-bit scalar range"
    | _ => throw "IxIR₂ scalar fixture returned a non-Nat value"
  if sourceWord != selected.word then
    throw "IxIR₂ and selected target observations disagree"
  else
    pure { program := selected.target.program
           runtime := Runtime.rejecting
           sourceResult := some sourceWord }

private def validatedScalarFixture (number : Nat) : Except String Fixture := do
  let compiled ← match X86.ValidatedScalar.compile number with
    | .ok compiled => pure compiled
    | .error error => throw s!"validated source compilation failed: {repr error}"
  let sourceWord ← compiled.observe
  return { program := compiled.selected.target.program
           runtime := Runtime.rejecting
           sourceResult := some sourceWord
           sourceRoot := some compiled.sourceRoot
           provenance := compiled.provenance }

private def fixture? (number : Nat) : String → Except String Fixture
  | "arithmetic" =>
      pure { program := X86.Examples.arithmeticProgram
             runtime := Runtime.rejecting }
  | "direct-call" =>
      pure { program := X86.Examples.callProgram
             runtime := Runtime.rejecting }
  | "runtime" =>
      pure { program := X86.Examples.runtimeProgram
             runtime := X86.Examples.fixtureRuntime }
  | "selected-scalar" => selectedScalarFixture
  | "validated-scalar" => validatedScalarFixture number
  | _ => .error usage

def main (args : List String) : IO UInt32 := do
  let some (fixture, outputPath, number) :=
      (match args with
       | [fixture, outputPath] => some (fixture, outputPath, 42)
       | ["validated-scalar", outputPath, number] =>
           number.toNat?.map fun number => ("validated-scalar", outputPath, number)
       | _ => none)
    | IO.eprintln usage
      return 2
  let selectedFixture ← match fixture? number fixture with
    | .ok selected => pure selected
    | .error error =>
        IO.eprintln error
        return 2
  let program := selectedFixture.program
  let runtime := selectedFixture.runtime
  let checked ← match program.check with
    | .ok checked => pure checked
    | .error error =>
        IO.eprintln s!"x86-object-fixture: validation failed: {repr error}"
        return 1
  let localResult ←
    match (runFrom runtime checked 64 (Core.empty 0x1008)).status with
    | .halted result => pure result
    | status =>
        IO.eprintln s!"x86-object-fixture: local execution failed: {repr status}"
        return 1
  let encoded ← match X86.Stream.encode checked with
    | .ok stream => pure stream.output
    | .error error =>
        IO.eprintln s!"x86-object-fixture: encode failed: {repr error}"
        return 1
  let object ← match X86.ELF.writeChecked
      { encoded
        entryBlock := program.entry
        provenance := selectedFixture.provenance } with
    | .ok object => pure object.bytes
    | .error error =>
        IO.eprintln s!"x86-object-fixture: ELF write failed: {repr error}"
        return 1
  IO.FS.writeBinFile outputPath object
  let sourceResult := match selectedFixture.sourceResult with
    | none => "-"
    | some result => toString result
  let sourceRoot := match selectedFixture.sourceRoot with
    | none => "-"
    | some address => address.toHex
  IO.println
    s!"fixture={fixture} source={sourceResult} local={localResult} bytes={object.size} ixon={sourceRoot} ir1={selectedFixture.provenance.root.toHex}"
  return 0
