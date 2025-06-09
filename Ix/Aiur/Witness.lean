import Ix.Aiur.Trace
import Ix.Aiur.Synthesis
import Ix.Archon.Circuit

namespace Aiur.Circuit

open Archon

def packBools (bits : Array Bool) : Array UInt8 :=
  let n := (bits.size + 7) / 8
  Array.range n |>.map fun i => Id.run do
    let mut byte : UInt8 := 0
    for j in [:8] do
      let idx := i * 8 + j
      if h : idx < bits.size then
        if bits[idx] then
          byte := byte ||| (1 <<< j).toUInt8
    byte

def populateWitness (circuits : AiurCircuits) (trace : AiurTrace) : Id Witness := do
  let mut witnessModules := #[]
  let mut heights := #[]

  -- Functions
  for ((mod, cols), funcTrace) in circuits.funcs.zip trace.functions do
    heights := heights.push funcTrace.numQueries.toUInt64
    let mut witnessModule := mod.initWitnessModule
    -- Inputs
    for (data, oracle) in funcTrace.inputs.zip cols.inputs do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b64
      witnessModule := witnessModule.pushUInt64sTo data entry

    -- Outputs
    for (data, oracle) in funcTrace.outputs.zip cols.outputs do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b64
      witnessModule := witnessModule.pushUInt64sTo data entry

    -- u1Auxiliaries
    for (data, oracle) in funcTrace.u1Auxiliaries.zip cols.u1Auxiliaries do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b1
      witnessModule := witnessModule.pushUInt8sTo (packBools data) entry

    -- u8Auxiliaries
    for (data, oracle) in funcTrace.u8Auxiliaries.zip cols.u8Auxiliaries do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b8
      witnessModule := witnessModule.pushUInt8sTo data entry

    -- u64Auxiliaries
    for (data, oracle) in funcTrace.u64Auxiliaries.zip cols.u64Auxiliaries do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b64
      witnessModule := witnessModule.pushUInt64sTo data entry

    -- u1Auxiliaries
    for (data, oracle) in funcTrace.selectors.zip cols.selectors do
      let (entry, witnessModule') := witnessModule.addEntry
      witnessModule := witnessModule'
      witnessModule := witnessModule.bindOracleTo oracle entry .b1
      witnessModule := witnessModule.pushUInt8sTo (packBools data) entry

    -- multiplicity
    let (entry, witnessModule') := witnessModule.addEntry
    witnessModule := witnessModule'
    witnessModule := witnessModule.bindOracleTo cols.multiplicity entry .b64
    witnessModule := witnessModule.pushUInt64sTo funcTrace.multiplicity entry

    -- collect the witness module
    witnessModules := witnessModules.push witnessModule

  -- Add
  let (xins, yins) := trace.add
  heights := heights.push xins.size.toUInt64
  let mut zouts := Array.mkEmpty xins.size
  let mut couts := Array.mkEmpty xins.size
  for (xin, yin) in xins.zip yins do
    let zout := xin + yin
    let carry := (decide (zout < xin)).toUInt64
    let cin := xin ^^^ yin ^^^ zout
    zouts := zouts.push zout
    couts := couts.push $ (carry <<< 63) ||| (cin >>> 1)
  let (circuitModule, cols) := circuits.add
  let mut witnessModule := circuitModule.initWitnessModule
  -- xin
  let (entry, witnessModule') := witnessModule.addEntry
  witnessModule := witnessModule'
  witnessModule := witnessModule.bindOracleTo cols.xin entry .b64
  witnessModule := witnessModule.pushUInt64sTo xins entry
  -- yin
  let (entry, witnessModule') := witnessModule.addEntry
  witnessModule := witnessModule'
  witnessModule := witnessModule.bindOracleTo cols.yin entry .b64
  witnessModule := witnessModule.pushUInt64sTo yins entry
  -- zout
  let (entry, witnessModule') := witnessModule.addEntry
  witnessModule := witnessModule'
  witnessModule := witnessModule.bindOracleTo cols.zout entry .b64
  witnessModule := witnessModule.pushUInt64sTo zouts entry
  -- cout
  let (entry, witnessModule') := witnessModule.addEntry
  witnessModule := witnessModule'
  witnessModule := witnessModule.bindOracleTo cols.cout entry .b64
  witnessModule := witnessModule.pushUInt64sTo couts entry
  -- Collect witnessModule
  witnessModules := witnessModules.push witnessModule

  -- Mul
  -- TODO

  -- Mem
  for ((mod, cols), memTrace) in circuits.mem.zip trace.mem do
    heights := heights.push memTrace.numQueries.toUInt64
    let mut memWitnessModule := mod.initWitnessModule
    for (oracle, data) in cols.values.zip memTrace.values do
      let (entry, witnessModule') := witnessModule.addEntry
      memWitnessModule := witnessModule'
      memWitnessModule := memWitnessModule.bindOracleTo oracle entry .b64
      memWitnessModule := memWitnessModule.pushUInt64sTo data entry

    -- multiplicity
    let (entry, witnessModule') := witnessModule.addEntry
    memWitnessModule := witnessModule'
    memWitnessModule := memWitnessModule.bindOracleTo cols.multiplicity entry .b64
    memWitnessModule := memWitnessModule.pushUInt64sTo memTrace.multiplicity entry

    -- Collect the witness module
    witnessModules := witnessModules.push memWitnessModule

  -- Populate in parallel
  witnessModules := WitnessModule.parPopulate witnessModules heights

  pure $ Archon.compileWitnessModules witnessModules heights

end Aiur.Circuit
