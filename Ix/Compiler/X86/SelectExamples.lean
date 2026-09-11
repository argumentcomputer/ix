import Ix.Compiler.X86.Select
import Ix.Compiler.X86.Encode

/-! Executable and proof-facing checks for the first IxIR₂ selector slice. -/

namespace Ix.Compiler.X86.Select.Examples

open Ix.Compiler

def fixtureWord : X86.Word := 42

def fixtureSource : IxIR2.Program := scalarMoveProgram fixtureWord

def fixtureStats : IxIR2.Validate.Stats :=
  { functions := 1
    blocks := 1
    instructions := 2
    flowWork := 8 }

def fixtureValidationAccepted : Bool :=
  match IxIR2.Validate.validate validationContext fixtureSource with
  | .ok stats => stats == fixtureStats
  | .error _ => false

#guard fixtureValidationAccepted

def selectionAccepted : Bool :=
  match select fixtureSource with
  | .error _ => false
  | .ok output =>
      output.word == fixtureWord &&
        output.target.program == targetProgram fixtureWord

#guard selectionAccepted

def invalidRegisterSource : IxIR2.Program :=
  { declarations := []
    main :=
      { signature := scalarSignature
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .move (.lit (.nat fixtureWord.toNat)),
              .move (.reg 9)]
            terminator := .ret (.reg 1) }] } }

#guard match select invalidRegisterSource with
  | .error (.invalidSource _) => true
  | _ => false

def overflowingLiteralSource : IxIR2.Program :=
  { declarations := []
    main :=
      { signature := scalarSignature
        blocks := #[
          { valueParams := #[]
            creditParams := #[]
            instructions := #[
              .move (.lit (.nat UInt64.size)),
              .move (.reg 0)]
            terminator := .ret (.reg 1) }] } }

#guard match IxIR2.Validate.validate validationContext overflowingLiteralSource,
    select overflowingLiteralSource with
  | .ok _, .error .unsupportedScalarShape => true
  | _, _ => false

def selectedBytesAccepted : Bool :=
  match select fixtureSource with
  | .error _ => false
  | .ok output =>
      match X86.Encode.encode output.target with
      | .error _ => false
      | .ok encoded =>
          encoded.text == ByteArray.mk #[
            0x48, 0xb8, 0x2a, 0, 0, 0, 0, 0, 0, 0,
            0xc3] &&
          encoded.blockOffsets == #[0] && encoded.relocations.isEmpty

#guard selectedBytesAccepted

def workerAddress : Ixon.Address := Ixon.Address.replicate 0x53
def entryAddress : Ixon.Address := Ixon.Address.replicate 0x54

def closedApplyAccepted (word : X86.Word) : Bool :=
  match select (ScalarApply.program word workerAddress entryAddress) with
  | .error _ => false
  | .ok output => output.word == word && output.target.program == targetProgram word

#guard closedApplyAccepted 0
#guard closedApplyAccepted fixtureWord
#guard closedApplyAccepted (UInt64.ofNat (UInt64.size - 1))

/-- Reading only the worker's literal would silently miscompile this valid
graph: its entry returns seven without calling the worker. -/
def changedEntrySource : IxIR2.Program :=
  { ScalarApply.program fixtureWord workerAddress entryAddress with
    declarations :=
      [(workerAddress, .fn (ScalarApply.worker fixtureWord)),
       (entryAddress, .fn
         { ScalarApply.entry workerAddress with
           blocks := #[{ valueParams := #[], creditParams := #[]
                         instructions := #[.move (.lit (.nat 7))]
                         terminator := .ret (.reg 0) }] })] }

#guard match IxIR2.Validate.validate validationContext changedEntrySource,
    select changedEntrySource with
  | .ok _, .error .unsupportedScalarShape => true
  | _, _ => false

theorem fixtureRefines :
    IxIR2.Eval.runMain (sourceContext fixtureWord) .physical fixtureSource 3 0 =
      .ok
        { store := {}
          value := .lit (.nat fixtureWord.toNat)
          controlRemaining := 0
          heapRemaining := 0 } ∧
    (X86.runFrom X86.Runtime.rejecting (targetChecked fixtureWord) 2
      (X86.Core.empty 0x1008)).status = .halted fixtureWord :=
  scalarMoveRefines fixtureWord

end Ix.Compiler.X86.Select.Examples
