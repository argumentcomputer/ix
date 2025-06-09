import Ix.Aiur.Trace
import Ix.Aiur.Synthesis
import Ix.Archon.Circuit

namespace Aiur.Circuit

def populateWitness (circuits : AiurCircuits) (trace : AiurTrace) : Id Archon.Witness := do
  let mut witnessModules := #[]
  let mut heights := #[]
  for ((mod, _), funcTrace) in circuits.funcs.zip trace.functions do
    heights := heights.push funcTrace.size.toUInt64
    witnessModules := witnessModules.push mod.initWitnessModule
  for ((_, (mod, _)), (_, memTrace)) in circuits.mem.pairs.zip trace.mem do
    heights := heights.push memTrace.size.toUInt64
    witnessModules := witnessModules.push mod.initWitnessModule
  pure $ Archon.compileWitnessModules witnessModules heights

end Aiur.Circuit
