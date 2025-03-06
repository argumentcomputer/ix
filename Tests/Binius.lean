import LSpec
import Ix.Binius.ConstraintSystemBuilder

open LSpec Binius in

def Tests.Binius.suite :=
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
    .add (.pow (.var 3) 2) (.mul (.var 5) (.const (.ofNat 10)))
  let builder := builder.assertNotZero oracleId0
  let logRows := builder.logRows #[oracleId0, oracleId1]
  let (channelId0, builder) := builder.addChannel
  let (channelId1, builder) := builder.addChannel
  let builder := builder.flushWithMultiplicity .push channelId0 6 #[oracleId0, oracleId1] 1
  let builder := builder.flushWithMultiplicity .pull channelId0 7 #[oracleId0, oracleId1] 1
  let builder := builder.flushCustom .push channelId0 oracleId0 #[oracleId0, oracleId1] 1
  let builder := builder.flushCustom .pull channelId0 oracleId0 #[oracleId0, oracleId1] 1
  let _cs := builder.build
  [
    test "Binius oracles grow by increments of 1"
      (#[oracleId0.toUSize, oracleId1.toUSize, oracleId2.toUSize,
         oracleId3.toUSize, oracleId4.toUSize] = #[0, 1, 2, 3, 4]),
    test "Binius channels grow by increments of 1"
      (channelId0.toUSize = 0 ∧ channelId1.toUSize = 1),
    test "logRows is correct" (logRows = nVars),
  ]
