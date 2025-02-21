import LSpec
import Ix.Binius

open Binius

open LSpec in
def main :=
  let builder := ConstraintSystemBuilder.init ()
  let a ≪ add_channel builder
  let b ≪ add_channel builder
  let c ≪ add_channel builder.
  lspecIO $
    test "Binius channels grow by increments of 1" (a = 0 ∧ b = 1 ∧ c = 2)
