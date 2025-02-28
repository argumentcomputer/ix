import LSpec
import Ix.Binius.ConstraintSystemBuilder

open LSpec Binius in
def Tests.Binius.suite :=
  let nVars := 3
  let builder := ConstraintSystemBuilder.init ()
  let (oracleId, builder) := builder.addCommitted "foo" nVars 5
  let (oracleId', builder) := builder.addCommitted "bar" nVars 4
  let builder := builder.pushNamespace "hi"
  let builder := builder.popNamespace
  let builder := builder.assertZero "zzz" #[oracleId, oracleId'] $
    .add (.pow (.var 3) 2) (.mul (.var 5) (.const (.ofNat 10)))
  let builder := builder.assertNotZero oracleId
  let logRows := builder.logRows #[oracleId, oracleId']
  let (channelId, builder) := builder.addChannel
  let (channelId', builder) := builder.addChannel
  let builder := builder.flushCustom .push channelId oracleId #[oracleId, oracleId'] 1
  let builder := builder.flushCustom .pull channelId oracleId #[oracleId, oracleId'] 1
  let _cs := builder.build
  [
    test "Binius oracles grow by increments of 1"
      (oracleId.toUSize = 0 ∧ oracleId'.toUSize = 1),
    test "Binius channels grow by increments of 1"
      (channelId.toUSize = 0 ∧ channelId'.toUSize = 1),
    test "logRows is correct" (logRows = nVars),
  ]
