import Ix.Aiur.Trace
import Ix.Aiur.Synthesis
import Ix.Archon.Circuit
import Ix.Archon.TowerField
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

def extractBits (nums : Array UInt64) : Id (Array (Array Bool)) := do
  let numBits := 64
  let mut bitVectors := Array.mkArray numBits #[]
  for num in nums do
    for i in [0:numBits] do
      let bit := num.toNat.testBit i
      bitVectors := bitVectors.modify i (fun lst => lst.push bit)
  bitVectors

def extractBits128 (nums : Array UInt128) : Id (Array (Array Bool)) := do
  let numBits := 128
  let mut bitVectors := Array.mkArray numBits #[]
  for num in nums do
    for i in [0:numBits] do
      let bit := num.toNat.testBit i
      bitVectors := bitVectors.modify i (fun lst => lst.push bit)
  bitVectors

def pushData (witnessModule : WitnessModule)
    (pushFn : WitnessModule → Array α → EntryId → WitnessModule)
    (data : Array α) (oracle : OracleIdx) (tf : TowerField) : WitnessModule :=
  let (entry, witnessModule) := witnessModule.addEntry
  let witnessModule := witnessModule.bindOracleTo oracle entry tf
  pushFn witnessModule data entry

def populateWitness (circuits : AiurCircuits) (trace : AiurTrace) : Id Witness := do
  let mut witnessModules := #[]
  let mut modes := #[]

  -- Functions
  for ((mod, cols), funcTrace) in circuits.funcs.zip trace.functions do
    modes := modes.push funcTrace.mode
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
  let xins := trace.add.xs
  let yins := trace.add.ys
  modes := modes.push trace.add.mode
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
  let xins := trace.mul.xs
  let yins := trace.mul.ys
  modes := modes.push trace.mul.mode
  let mut zouts := Array.mkEmpty xins.size
  let mut zoutsLow := Array.mkEmpty xins.size
  let mut zoutsHigh := Array.mkEmpty xins.size
  for (xin, yin) in xins.zip yins do
    let zout := UInt128.exteriorMul xin yin
    zouts := zouts.push zout
    let (zoutLow, zoutHigh) := UInt128.toLoHi zout
    zoutsLow := zoutsLow.push zoutLow
    zoutsHigh := zoutsHigh.push zoutHigh
  let (circuitModule, cols) := circuits.mul
  let mut mulWitnessModule := circuitModule.initWitnessModule
  -- xin
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo xins cols.xin .b64
  -- yin
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo yins cols.yin .b64
  -- zout
  mulWitnessModule := pushData mulWitnessModule .pushUInt64sTo zoutsLow cols.zout .b64
  -- xinBits
  for (oracle, xinBits) in cols.xinBits.zip (extractBits xins) do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools xinBits) oracle .b1
  -- yinBits
  for (oracle, yinBits) in cols.yinBits.zip (extractBits yins) do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools yinBits) oracle .b1
  -- zoutBits
  for (oracle, zoutBits) in cols.zoutBits.zip (extractBits128 zouts) do
    mulWitnessModule := pushData mulWitnessModule .pushUInt8sTo (packBools zoutBits) oracle .b1
  -- TODO: exponentials require manual padding. For some reason, Binius' exponential constraints are not working properly
  -- xinExpResult
  let xinExpResult := xins.map fun xin => Archon.powUInt128InBinaryField B128_MULT_GEN xin
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo xinExpResult cols.xinExpResult .b128
  -- yinExpResult
  let yinExpResult := (yins.zip xinExpResult).map fun (yin, xinExp) => Archon.powUInt128InBinaryField xinExp yin
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo yinExpResult cols.yinExpResult .b128
  -- zoutLowExpResult
  let zoutLowExpResult := zoutsLow.map fun zoutLow => Archon.powUInt128InBinaryField B128_MULT_GEN zoutLow
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo zoutLowExpResult cols.zoutLowExpResult .b128
  -- zoutHighExpResult
  let zoutHighExpResult := zoutsHigh.map fun zoutHigh => Archon.powUInt128InBinaryField B128GenPow2To64 zoutHigh
  mulWitnessModule := pushData mulWitnessModule .pushUInt128sTo zoutHighExpResult cols.zoutHighExpResult .b128
  -- Collect mulWitnessModule
  witnessModules := witnessModules.push mulWitnessModule

  -- Memory
  for ((mod, cols), memTrace) in circuits.mem.zip trace.mem do
    modes := modes.push memTrace.mode
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
