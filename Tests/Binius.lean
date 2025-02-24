import LSpec
import Ix.Binius

open Binius

def add3Channels : CSBuildM (ChannelId × ChannelId × ChannelId) := do
  let a ← addChannel
  let b ← addChannel
  let c ← addChannel
  pure (a, b, c)

open LSpec in
def main :=
  let builder := ConstraintSystemBuilder.init ()
  let ((a, b, c), _builder) := CSBuildM.run add3Channels builder
  lspecIO $
    test "Binius channels grow by increments of 1" (a = 0 ∧ b = 1 ∧ c = 2)
