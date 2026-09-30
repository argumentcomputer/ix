import Compilatrix.X86.ELFValidate
import Compilatrix.X86.EvalExamples

/-! Operational fixture generator for the external ELF/binutils gate. -/

open Compilatrix
open Compilatrix.X86
open Compilatrix.Ixon

private def usage : String :=
  "usage: lake exe x86-object-fixture (arithmetic|direct-call|runtime|unwind|exports) <output.o>"

/-- Provenance for the hand-written target fixtures. -/
private def fixtureProvenance : X86.ELF.Provenance :=
  .ixir1Policy (Address.replicate 0x42) 1 1

private structure Fixture where
  program : Program
  runtime : Runtime
  sourceResult : Option Word := none
  sourceRoot : Option Address := none
  provenance : X86.ELF.Provenance := fixtureProvenance
  /-- The typed run's initial core (its `rsp` is 0x1008). -/
  core : Core := Core.empty 0x1008
  /-- Further exported symbols (name and block). -/
  exports : List (String × BlockId) := []

private def fixture? : String → Except String Fixture
  | "arithmetic" =>
      pure { program := X86.Examples.arithmeticProgram
             runtime := Runtime.rejecting }
  | "direct-call" =>
      pure { program := X86.Examples.callProgram
             runtime := Runtime.rejecting }
  | "runtime" =>
      pure { program := X86.Examples.runtimeProgram
             runtime := X86.Examples.fixtureRuntime }
  | "unwind" =>
      pure { program := X86.Examples.unwindProgram
             runtime := Runtime.rejecting
             core := X86.Examples.unwindCore 3 1 }
  -- The direct-call program with its callee (returning 40) exported too.
  | "exports" =>
      pure { program := X86.Examples.callProgram
             runtime := Runtime.rejecting
             exports := [("compilatrix_forty", 1)] }
  | _ => .error usage

def main (args : List String) : IO UInt32 := do
  let [fixture, outputPath] := args
    | IO.eprintln usage
      return 2
  let selectedFixture ← match fixture? fixture with
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
    match (runFrom runtime checked 64 selectedFixture.core).status with
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
        exports := selectedFixture.exports
        provenance := selectedFixture.provenance } with
    | .ok object => pure object.bytes
    | .error error =>
        IO.eprintln s!"x86-object-fixture: ELF write failed: {repr error}"
        return 1
  -- Each further export resolves, by name, to its block's offset.
  for (name, block) in selectedFixture.exports do
    unless X86.ELF.symbol? object name == encoded.blockOffsets[block.toNat]? do
      IO.eprintln s!"x86-object-fixture: export {name} does not resolve to block {block}"
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
