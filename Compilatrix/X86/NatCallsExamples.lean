import Compilatrix.X86.NatCallsCheck
import Compilatrix.X86.Select

namespace Compilatrix.X86.NatCalls.Examples
open Compilatrix

def schema : Schema := {
  zero := ⟨Ixon.Address.replicate 0x71, 0, 0⟩
  succ := ⟨Ixon.Address.replicate 0x71, 0, 1⟩ }
def address := Ixon.Address.replicate 0x72
def source : IxIR2.Program := { Select.scalarMoveProgram 7 with main.signature.result := .shared }

def errorIs {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with
  | .error error => error == expected
  | _ => false

#guard match select source Select.validationContext schema with
  | .ok output => output.word == 7 && output.reclaimed.heap.live == 0
  | _ => false

def changed (instructions : Array IxIR2.Instr) (terminator : IxIR2.Terminator := .ret (.reg 0)) : IxIR2.Program :=
  { source with main.blocks := #[{ valueParams := #[], creditParams := #[], instructions, terminator }] }

#guard errorIs (lower { source with main.signature.params := #[⟨.shared, .owned⟩] } schema) .openMain
#guard errorIs (lower { source with main.blocks := #[] } schema) .controlFlow
#guard errorIs (lower { source with main.signature.result := .unique } schema) .ownership
#guard errorIs (lower (changed #[.move (.reg 3)]) schema) .unknownRegister
#guard errorIs (lower (changed #[.move (.lit (.nat UInt64.size))]) schema) .wordOverflow
#guard errorIs (lower (changed #[.papp address #[.lit (.nat 0)]]) schema) .capturedPap
#guard errorIs (lower (changed #[.apply (.lit (.nat 0)) #[]]) schema) .unknownClosure
#guard errorIs (lower (changed #[.call address #[]]) schema) .unknownFunction
#guard errorIs (lower (changed #[.call address #[.lit (.nat 0), .lit (.nat 1)]]) schema) .multipleNatArguments
#guard errorIs (lower (changed #[] (.tailCallSelf #[])) schema) .controlFlow
#guard errorIs (evaluate #[] 10 (.successor (.constant (UInt64.size - 1).toUInt64)) 0) .wordOverflow

-- Validation precedes selection, including registers ignored by native
-- representation lowering. A dead malformed release still rejects.
#guard match select (changed #[.releaseShared (.reg 9), .move (.lit (.nat 7))]) Select.validationContext schema with
  | .error (.source _) => true
  | _ => false

end Compilatrix.X86.NatCalls.Examples
