import LSpec
import Ix.Binius.ConstraintSystemBuilder
import Ix.Binius.WitnessBuilder

open LSpec Binius

def Tests.Binius.bindingsSuite :=
  let nVars := 3
  let builder := ConstraintSystemBuilder.new ()
  let (oracleId0, builder) := builder.addCommitted "a" nVars 5
  let (oracleId1, builder) := builder.addCommitted "b" nVars 4
  let (oracleId2, builder) := builder.addLinearCombination "c" nVars
    #[(oracleId0, .ofNat 3), (oracleId1, .ofNat 7)]
  let (oracleId3, builder) := builder.addLinearCombinationWithOffset "d" nVars
    (.ofNat 5) #[(oracleId0, .ofNat 3), (oracleId1, .ofNat 7)]
  let (oracleId4, builder) := builder.addPacked "e" oracleId3 2
  let builder := builder.pushNamespace "x"
  let builder := builder.popNamespace
  let builder := builder.assertZero "y" #[oracleId0, oracleId1] $
    .add (.pow (.var oracleId1) 2) (.mul (.var oracleId2) (.const (.ofNat 10)))
  let builder := builder.assertNotZero oracleId0
  let logRows := builder.logRows #[oracleId0, oracleId1]
  let (channelId0, builder) := builder.addChannel
  let (channelId1, builder) := builder.addChannel
  let builder := builder.flushWithMultiplicity .push channelId0 6 #[oracleId0, oracleId1] 1
  let builder := builder.flushWithMultiplicity .pull channelId0 7 #[oracleId0, oracleId1] 1
  let builder := builder.flushCustom .push channelId0 oracleId0 #[oracleId0, oracleId1] 1
  let builder := builder.flushCustom .pull channelId0 oracleId0 #[oracleId0, oracleId1] 1
  [
    test "Binius oracles grow by increments of 1"
      (#[oracleId0.toUSize, oracleId1.toUSize, oracleId2.toUSize,
         oracleId3.toUSize, oracleId4.toUSize] = #[0, 1, 2, 3, 4]),
    test "Binius channels grow by increments of 1"
      (channelId0.toUSize = 0 ∧ channelId1.toUSize = 1),
    test "logRows is correct" (logRows = nVars),
  ]

def Tests.Binius.witnessSuite :=
  let builder := ConstraintSystemBuilder.new ()
  let (a, builder) := builder.addCommitted "a" 4 0
  let (b, builder) := builder.addCommitted "b" 4 0
  let builder := builder.assertZero "a + b" #[a, b] (.add (.var a) (.var b))
  let cs := builder.build

  let mkWitness := fun aData bData =>
    let builder := WitnessBuilder.new cs
    let builder := builder.withColumn a aData
    let builder := builder.withColumn b bData
    builder.build

  let raw : ByteArray := ⟨#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]⟩

  -- Building a valid witness
  let witnessFromRaw := mkWitness raw raw

  -- Building an invalid witness
  let invalidWitnessFromRaw := mkWitness raw (raw.set 0 1)

  -- Building witness from UInt8s
  let u8s : Array UInt8 := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  let witnessFromUInt8s := mkWitness u8s u8s

  -- Building witness from UInt16s
  let u16s : Array UInt16 := #[0, 1, 2, 3, 4, 5, 6, 7]
  let witnessFromUInt16s := mkWitness u16s u16s

  -- Building witness from UInt32s
  let u32s : Array UInt32 := #[0, 1, 2, 3]
  let witnessFromUInt32s := mkWitness u32s u32s

  -- Building witness from UInt64s
  let u64s : Array UInt64 := #[0, 1]
  let witnessFromUInt64s := mkWitness u64s u64s

  -- Building witness from UInt128s
  let u128s : Array UInt128 := #[.ofNat 0]
  let witnessFromUInt128s := mkWitness u128s u128s

  let mkExpectOkTest := fun innerTypes witness =>
    withExceptOk s!"Constraint system accepts a valid witness from {innerTypes}"
      (cs.validateWitness #[] witness) fun _ => .done

  [
    withExceptOk "Constraint system accepts a valid witness"
      (cs.validateWitness #[] witnessFromRaw) fun _ => .done,
    withExceptError "Constraint system doesn't accept an invalid witness"
      (cs.validateWitness #[] invalidWitnessFromRaw) fun _ => .done,
    mkExpectOkTest "UInt8s" witnessFromUInt8s,
    mkExpectOkTest "UInt16s" witnessFromUInt16s,
    mkExpectOkTest "UInt32s" witnessFromUInt32s,
    mkExpectOkTest "UInt64s" witnessFromUInt64s,
    mkExpectOkTest "UInt128s" witnessFromUInt128s,
  ]
