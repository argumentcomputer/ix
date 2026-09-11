import Ix.Compiler.X86.NatCallsCheck
import Ix.Compiler.X86.Select

namespace Ix.Compiler.X86.NatCalls.Examples
open Ix.Compiler

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

def capturedBody : IxIR2.Function := {
  signature := { params := #[⟨.shared, .owned⟩, ⟨.shared, .owned⟩], result := .shared, papSafe := true }
  blocks := #[{
    valueParams := #[.owned .shared, .owned .shared], creditParams := #[],
    instructions := #[.releaseShared (.reg 1)], terminator := .ret (.reg 0) }] }

def capturedProgram (first second : Nat) : IxIR2.Program := {
  declarations := [(address, .fn capturedBody)]
  main := { source.main with blocks := #[{
    valueParams := #[], creditParams := #[], instructions := #[
      .papp address #[.lit (.nat first)], .apply (.reg 0) #[.lit (.nat 11)], .releaseShared (.reg 1),
      .papp address #[.lit (.nat second)], .apply (.reg 2) #[.lit (.nat 13)]],
    terminator := .ret (.reg 3) }] } }

-- Both captures use the same declaration. Their expressions must remain in
-- the specialization key, and each saturated application consumes its PAP.
#guard match select (capturedProgram 0 7) Select.validationContext schema {} .staticNat with
  | .ok output => output.word == 7 && output.residual.functions.size == 3 &&
      output.residual.functions[0]!.parameters == #[.staticNat (.constant 0), .nat] &&
      output.residual.functions[1]!.parameters == #[.staticNat (.constant 7), .nat] &&
      output.reclaimed.heap.allocs == 2 && output.reclaimed.heap.frees == 2 && output.reclaimed.heap.live == 0
  | _ => false
#guard match select (capturedProgram 0 (UInt64.size - 1)) Select.validationContext schema {} .staticNat with
  | .ok output => output.word.toNat == UInt64.size - 1 && output.reclaimed.heap.live == 0
  | _ => false
#guard errorIs (lower (capturedProgram 0 UInt64.size) schema {} .staticNat) .wordOverflow
#guard errorIs (lower (capturedProgram 0 7) schema { captureFuel := 0 } .staticNat) .budget
#guard errorIs (lower (capturedProgram 0 7) schema) .capturedPap

#guard errorIs (checkCapture #[] .argument 10) .dynamicCapture
#guard errorIs (checkCapture #[] (.successor (.constant (UInt64.size - 1).toUInt64)) 10) .wordOverflow
#guard errorIs (lower (changed #[.papp address #[.erased]]) schema {} .staticNat) .notNat
#guard errorIs (lower (changed #[.papp address #[.lit (.nat 0), .lit (.nat 1)]]) schema {} .staticNat) .capturedPap
#guard errorIs (lower (changed #[.papp address #[], .papp address #[.reg 0]]) schema {} .staticNat) .notNat

def dynamicBody : IxIR2.Function := {
  signature := { params := #[⟨.shared, .owned⟩], result := .shared, papSafe := true }
  blocks := #[{
    valueParams := #[.owned .shared], creditParams := #[],
    instructions := #[.papp address #[.reg 0]], terminator := .ret (.reg 1) }] }
#guard errorIs (lowerFunction (capturedProgram 0 7) schema {} .staticNat 10 #[] none dynamicBody #[.nat]) .dynamicCapture

-- Capture-free callees may use their own argument when the initializer's
-- call input is closed. The original call/successor syntax is retained.
def initializerFunctions : Array Function := #[{ origin := none, parameters := #[.nat], body := .successor .argument }]
#guard match checkCapture initializerFunctions (.call 0 (.constant 6)) 10 with
  | .ok capture => capture.word == 7
  | _ => false
#guard errorIs (checkCapture initializerFunctions (.call 0 .argument) 10) .dynamicCapture

-- Validation rejects unsafe or unsaturated targets before capture selection.
#guard match select { capturedProgram 0 7 with declarations := [] } Select.validationContext schema {} .staticNat with
  | .error (.source _) => true
  | _ => false
#guard match select { capturedProgram 0 7 with declarations := [(address,
    .fn { capturedBody with signature.papSafe := false })] } Select.validationContext schema {} .staticNat with
  | .error (.source _) => true
  | _ => false
#guard match select { capturedProgram 0 7 with declarations := [(address,
    .fn { capturedBody with signature.params := #[⟨.shared, .owned⟩] })] } Select.validationContext schema {} .staticNat with
  | .error (.source _) => true
  | _ => false

end Ix.Compiler.X86.NatCalls.Examples
