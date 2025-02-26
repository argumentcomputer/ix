import LSpec
import Ix.Binius.ConstraintSystemBuilder

open Binius

open LSpec in
def main :=
  let nVars := 3
  let builder := ConstraintSystemBuilder.init ()
  let (oracleId, builder) := builder.addCommitted "foo" nVars 5
  let (oracleId', builder) := builder.addCommitted "bar" nVars 4
  let builder := builder.pushNamespace "hi"
  let builder := builder.popNamespace
  let builder := builder.assertNotZero oracleId
  let logRows := builder.logRows #[oracleId, oracleId']
  let (channelId, builder) := builder.addChannel
  let (channelId', builder) := builder.addChannel
  let builder := builder.flushCustom .push channelId oracleId #[oracleId, oracleId'] 1
  let builder := builder.flushCustom .pull channelId oracleId #[oracleId, oracleId'] 1
  let _cs := builder.build
  lspecIO $
    test "Binius oracles grow by increments of 1" (oracleId = 0 ∧ oracleId' = 1) $
    test "Binius channels grow by increments of 1" (channelId = 0 ∧ channelId' = 1) $
    test "logRows is correct" (logRows = nVars)
