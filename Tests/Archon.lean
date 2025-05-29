import LSpec
import Ix.Archon.Circuit
import Ix.Archon.Protocol
import Ix.ByteArray

open LSpec Archon

def populateAndValidate (circuitModule : CircuitModule)
    (witnessModule : WitnessModule) height msg :=
  let witnessModule := witnessModule.populate height
  let witness := compileWitnessModules #[witnessModule] #[height]
  withExceptOk msg (validateWitness #[circuitModule] #[] witness) fun _ => .done

def transparent : TestSeq :=
  let circuitModule := CircuitModule.new 0
  let (_, circuitModule) := circuitModule.addTransparent "constant" (.const 300)
  let (_, circuitModule) := circuitModule.addTransparent "incremental" .incremental
  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  populateAndValidate circuitModule witnessModule 91 "Archon transparents work"

def linearCombination : TestSeq := Id.run do
  let circuitModule := CircuitModule.new 0
  let (b1, circuitModule) := circuitModule.addCommitted "b1" .b1
  let (b2, circuitModule) := circuitModule.addCommitted "b2" .b2
  let (b4, circuitModule) := circuitModule.addCommitted "b4" .b4
  let (b8, circuitModule) := circuitModule.addCommitted "b8" .b8
  let (b16, circuitModule) := circuitModule.addCommitted "b16" .b16
  let (b32, circuitModule) := circuitModule.addCommitted "b32" .b32
  let (b64, circuitModule) := circuitModule.addCommitted "b64" .b64
  let (b128, circuitModule) := circuitModule.addCommitted "b128" .b128

  let (_, circuitModule) := circuitModule.addLinearCombination "lcb128" 3
    #[(b1, 3), (b2, 4), (b4, 5), (b8, 6), (b16, 7), (b32, 8), (b64, 9), (b128, 10)]
  let (_, circuitModule) := circuitModule.addLinearCombination "lcb64" 907898
    #[(b1, 500), (b2, 2000), (b4, 5), (b8, 4), (b16, 7), (b32, 8), (b64, 9879)]

  let circuitModule := circuitModule.freezeOracles
  let mut witnessModule := circuitModule.initWitnessModule

  let oracles := [b1, b2, b4, b8, b16, b32, b64, b128].mergeSort
    fun a b => (a.toUSize.toNat ^ 7) % 3 < (b.toUSize.toNat ^ 7) % 3
  for (oracleId, i) in oracles.zipIdx do
    let (entryId, newWitnessModule) := witnessModule.addEntry
    witnessModule := newWitnessModule
    for j in [0 : 1 <<< i ] do
      let u128 := UInt128.ofNatWrap (j * j + 17)
      witnessModule := witnessModule.pushUInt128sTo #[u128] entryId
    match i with
    | 0 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b1
    | 1 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b2
    | 2 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b4
    | 3 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b8
    | 4 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b16
    | 5 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b32
    | 6 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b64
    | 7 => witnessModule := witnessModule.bindOracleTo oracleId entryId .b128
    | _ => unreachable!

  populateAndValidate circuitModule witnessModule 128 "Archon linear combination works"

def packed : TestSeq :=
  let circuitModule := CircuitModule.new 0
  let (x, circuitModule) := circuitModule.addCommitted "x" .b1
  let (_, circuitModule) := circuitModule.addPacked "packed" x 2
  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  let (entryId, witnessModule) := witnessModule.addEntryWithCapacity 7
  let witnessModule := witnessModule.pushUInt128sTo #[2347928368726] entryId
  let witnessModule := witnessModule.bindOracleTo x entryId .b1
  populateAndValidate circuitModule witnessModule 128 "Archon packed works"

def shifted : TestSeq :=
  let circuitModule := CircuitModule.new 0
  let (x, circuitModule) := circuitModule.addCommitted "x" .b1
  let (_, circuitModule) := circuitModule.addShifted "shifted" x 2 4 .logicalLeft
  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  let (entryId, witnessModule) := witnessModule.addEntryWithCapacity 7
  let witnessModule := witnessModule.pushUInt128sTo #[2347928368726] entryId
  let witnessModule := witnessModule.bindOracleTo x entryId .b1
  populateAndValidate circuitModule witnessModule 128 "Archon shifted works"

def pushData : TestSeq :=
  let circuitModule := CircuitModule.new 0
  let (u8s, circuitModule) := circuitModule.addCommitted "u8s" .b1
  let (u16s, circuitModule) := circuitModule.addCommitted "u16s" .b1
  let (u32s, circuitModule) := circuitModule.addCommitted "u32s" .b1
  let (u64s, circuitModule) := circuitModule.addCommitted "u64s" .b1
  let (u128s, circuitModule) := circuitModule.addCommitted "u128s" .b1
  let circuitModule := circuitModule.assertZero "u8s xor u16s" #[] $ .add (.oracle u8s) (.oracle u16s)
  let circuitModule := circuitModule.assertZero "u16s xor u32s" #[] $ .add (.oracle u16s) (.oracle u32s)
  let circuitModule := circuitModule.assertZero "u32s xor u64s" #[] $ .add (.oracle u32s) (.oracle u64s)
  let circuitModule := circuitModule.assertZero "u64s xor u128s" #[] $ .add (.oracle u64s) (.oracle u128s)
  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  let (u8sEntry, witnessModule) := witnessModule.addEntryWithCapacity 7
  let (u16sEntry, witnessModule) := witnessModule.addEntryWithCapacity 7
  let (u32sEntry, witnessModule) := witnessModule.addEntryWithCapacity 7
  let (u64sEntry, witnessModule) := witnessModule.addEntryWithCapacity 7
  let (u128sEntry, witnessModule) := witnessModule.addEntryWithCapacity 7
  let witnessModule := witnessModule.pushUInt8sTo (.mkArray 16 0) u8sEntry
  let witnessModule := witnessModule.pushUInt16sTo (.mkArray 8 0) u16sEntry
  let witnessModule := witnessModule.pushUInt32sTo #[0, 0, 0, 0] u32sEntry
  let witnessModule := witnessModule.pushUInt64sTo #[0, 0] u64sEntry
  let witnessModule := witnessModule.pushUInt128sTo #[0] u128sEntry
  let witnessModule := witnessModule.bindOracleTo u8s u8sEntry .b1
  let witnessModule := witnessModule.bindOracleTo u16s u16sEntry .b1
  let witnessModule := witnessModule.bindOracleTo u32s u32sEntry .b1
  let witnessModule := witnessModule.bindOracleTo u64s u64sEntry .b1
  let witnessModule := witnessModule.bindOracleTo u128s u128sEntry .b1
  populateAndValidate circuitModule witnessModule 128 "Archon witness data pushes work"

def proveAndVerify : TestSeq :=
  let circuitModule := CircuitModule.new 0
  let (x, circuitModule) := circuitModule.addCommitted "x" .b1
  let (y, circuitModule) := circuitModule.addCommitted "y" .b1
  let circuitModule := circuitModule.assertZero "x xor y" #[] $ .add (.oracle x) (.oracle y)
  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  let (entryId, witnessModule) := witnessModule.addEntryWithCapacity 7
  let witnessModule := witnessModule.pushUInt128sTo #[(.ofNatCore $ UInt128.size - 1)] entryId
  let witnessModule := witnessModule.bindOracleTo x entryId .b1
  let witnessModule := witnessModule.bindOracleTo y entryId .b1
  let height := 128
  let witnessModule := witnessModule.populate height
  let witness := compileWitnessModules #[witnessModule] #[height]
  let proof := prove #[circuitModule] #[] 1 100 witness
  let proofBytes := proof.toBytes
  withExceptOk "Archon proof serde works" (Proof.ofBytes proofBytes) fun proof =>
    withExceptOk "Archon prove and verify work"
      (verify #[circuitModule] #[] 1 100 proof) fun _ => .done

def versionCircuitModules : TestSeq :=
  let c₁ := CircuitModule.new 0
  let (_, c₁) := c₁.addCommitted "a" .b1
  let c₂ := CircuitModule.new 0
  let (_, c₂) := c₂.addCommitted "b" .b1
  let v₁ := version #[c₁]
  let v₂ := version #[c₂]
  test "Circuit module versioning is name-irrelevant" (v₁.val == v₂.val)

def Tests.Archon.suite := [
    transparent,
    linearCombination,
    packed,
    shifted,
    pushData,
    proveAndVerify,
    versionCircuitModules,
  ]
