import LSpec
import Ix.Binius.ConstraintSystemBuilder

open Binius

open LSpec in
def main :=
  let builder := ConstraintSystemBuilder.init ()
  let (a, builder) := builder.addChannel
  let (b, builder) := builder.addChannel
  let (c, builder) := builder.addChannel
  let _cs := builder.build
  lspecIO $
    test "Binius channels grow by increments of 1" (a = 0 ∧ b = 1 ∧ c = 2)
