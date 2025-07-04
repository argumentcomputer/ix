import Ix.Archon.Circuit

namespace Aiur

open Archon Binius

structure GadgetEntry where
  input : Array UInt64
  output : Array UInt64
  multiplicity : UInt64

structure Gadget where
  name : Lean.Name
  inputSize : Nat
  outputSize : Nat
  execute : Array UInt64 → Array UInt64
  synthesize : ChannelId → CircuitModule → CircuitModule × Array OracleIdx
  populate : Array GadgetEntry → Array OracleIdx → WitnessModule → WitnessModule × ModuleMode

instance : Inhabited Gadget where
  default :=
    let synthesize := fun _ circuitModule => (circuitModule, #[])
    let populate := fun _ _ witnessModule => (witnessModule, .inactive)
    ⟨.anonymous, 0, 0, id, synthesize, populate⟩

instance : Repr Gadget where
  reprPrec g _ := s!"[{g.inputSize}] → [{g.outputSize}]"

def Gadget.provide (circuitModule: CircuitModule) (channelId : ChannelId) (multiplicity: OracleIdx)
    (args : Array OracleOrConst) : CircuitModule :=
  let circuitModule := circuitModule.flush .push channelId CircuitModule.selector
    (args.push (.const 1 .b1)) 1
  circuitModule.flush .pull channelId CircuitModule.selector (args.push (.oracle multiplicity)) 1

end Aiur
