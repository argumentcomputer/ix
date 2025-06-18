import Ix.Aiur.Trace
import Ix.Aiur.Synthesis
import Ix.Archon.Circuit
import Ix.Binius.Boundary

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

def pushData (witnessModule : WitnessModule)
    (pushFn : WitnessModule → Array α → EntryId → WitnessModule)
    (data : Array α) (oracle : OracleIdx) (tf : TowerField) : WitnessModule :=
  let (entry, witnessModule) := witnessModule.addEntry
  let witnessModule := witnessModule.bindOracleTo oracle entry tf
  pushFn witnessModule data entry

def populateWitness (circuits : AiurCircuits) (trace : AiurTrace) : Id Witness := do
  let mut witnessModules := #[]
  let mut heights := #[]
  let mut modes := #[]

  -- Functions
  for ((mod, cols), funcTrace) in circuits.funcs.zip trace.functions do
    heights := heights.push funcTrace.numQueries.toUInt64
    let mut witnessModule := mod.initWitnessModule
    -- Inputs
    for (data, oracle) in funcTrace.inputs.zip cols.inputs do
      witnessModule := pushData witnessModule .pushUInt64sTo data oracle .b64
    -- Outputs
    for (data, oracle) in funcTrace.outputs.zip cols.outputs do
      witnessModule := pushData witnessModule .pushUInt64sTo data oracle .b64
    -- u1Auxiliaries
    for (data, oracle) in funcTrace.u1Auxiliaries.zip cols.u1Auxiliaries do
      witnessModule := pushData witnessModule .pushUInt8sTo (packBools data) oracle .b1
    -- u8Auxiliaries
    for (data, oracle) in funcTrace.u8Auxiliaries.zip cols.u8Auxiliaries do
      witnessModule := pushData witnessModule .pushUInt8sTo data oracle .b8
    -- u64Auxiliaries
    for (data, oracle) in funcTrace.u64Auxiliaries.zip cols.u64Auxiliaries do
      witnessModule := pushData witnessModule .pushUInt64sTo data oracle .b64
    -- selectors
    for (data, oracle) in funcTrace.selectors.zip cols.selectors do
      witnessModule := pushData witnessModule .pushUInt8sTo (packBools data) oracle .b1
    -- multiplicity
    witnessModule := pushData witnessModule .pushUInt64sTo funcTrace.multiplicity
      cols.multiplicity .b64
    -- Collect the witness module
    witnessModules := witnessModules.push witnessModule

  -- Add
  let (xins, yins) := trace.add
  heights := heights.push xins.size.toUInt64
  let mut addZout := Array.mkEmpty xins.size
  let mut addCout := Array.mkEmpty xins.size
  for (xin, yin) in xins.zip yins do
    let zout := xin + yin
    let carry := (decide (zout < xin)).toUInt64
    let cin := xin ^^^ yin ^^^ zout
    addZout := addZout.push zout
    addCout := addCout.push $ (carry <<< 63) ||| (cin >>> 1)
  let (circuitModule, cols) := circuits.add
  let mut addWitnessModule := circuitModule.initWitnessModule
  -- xin
  addWitnessModule := pushData addWitnessModule .pushUInt64sTo xins cols.xin .b1
  -- yin
  addWitnessModule := pushData addWitnessModule .pushUInt64sTo yins cols.yin .b1
  -- zout
  addWitnessModule := pushData addWitnessModule .pushUInt64sTo addZout cols.zout .b1
  -- cout
  addWitnessModule := pushData addWitnessModule .pushUInt64sTo addCout cols.cout .b1
  -- Collect addWitnessModule
  witnessModules := witnessModules.push addWitnessModule

  -- Mul
  let (xins, yins) := trace.mul
  heights := heights.push xins.size.toUInt64
  let mut mulZout := Array.mkEmpty xins.size
  for (xin, yin) in xins.zip yins do
    let zout := xin * yin
    mulZout := mulZout.push zout
  let (circuitModule, cols) := circuits.mul
  let mut mulWitnessModule := circuitModule.initWitnessModule
  -- xin
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo xins cols.xin .b64
  -- yin
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo yins cols.yin .b64
  -- zout
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo mulZout cols.zout .b64
  -- xinBits
  for oracle in cols.xinBits do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools #[]) oracle .b1
  -- yinBits
  for oracle in cols.yinBits do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools #[]) oracle .b1
  -- zoutBits
  for oracle in cols.zoutBits do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools #[]) oracle .b1
  -- xinExpResult
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo #[] cols.xinExpResult .b128
  -- yinExpResult
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo #[] cols.yinExpResult .b128
  -- zoutLowExpResult
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo #[] cols.zoutLowExpResult .b128
  -- zoutHighExpResult
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo #[] cols.zoutHighExpResult .b128
  -- Collect mulWitnessModule
  witnessModules := witnessModules.push mulWitnessModule

  -- Memory
  for ((mod, cols), memTrace) in circuits.mem.zip trace.mem do
    heights := heights.push memTrace.numQueries.toUInt64
    let mut witnessModule := mod.initWitnessModule
    for (oracle, data) in cols.values.zip memTrace.values do
      witnessModule := pushData witnessModule .pushUInt64sTo data oracle .b64
    -- multiplicity
    witnessModule := pushData witnessModule .pushUInt64sTo memTrace.multiplicity
      cols.multiplicity .b64
    -- Collect the witness module
    witnessModules := witnessModules.push witnessModule

  -- Populate in parallel
  witnessModules := WitnessModule.parPopulate witnessModules modes

  pure $ Archon.compileWitnessModules witnessModules modes

open Binius in
def mkBoundaries (input output : Array UInt64) (funcIdx : FuncIdx)
    (funcChannel : ChannelId) : Array Boundary :=
  let io := input ++ output ++ #[funcIdx] |>.map (.ofLoHi · 0)
  let pushBoundary := ⟨io.push B64_MULT_GEN, funcChannel, .push, 1⟩
  let pullBoundary := ⟨io.push 1, funcChannel, .pull, 1⟩
  #[pushBoundary, pullBoundary]

end Aiur.Circuit
