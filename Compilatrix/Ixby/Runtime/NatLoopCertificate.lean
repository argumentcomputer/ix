import Compilatrix.Ixby.Runtime.NatLoopCode
import Compilatrix.Ixby.Runtime.NatArithmetic

namespace Compilatrix.Ixby.Runtime.NatLoops

open Ix.Ixby ScalarFunction

structure Links where
  arithmetic : NatArithmetic.Links
  shiftRightLoop : FunctionId
  log2Loop : FunctionId
  powLoop : FunctionId
  shiftRight : FunctionId
  log2 : FunctionId
  pow : FunctionId

/-- Complete loop and wrapper code, including exact multiplication, every
conversion callee, and the three number layouts. -/
structure Certificate (program : Program) (links : Links) : Type where
  arithmetic : NatArithmetic.Certificate program links.arithmetic
  shiftRightLoop : Checked program links.shiftRightLoop (NatLoops.shiftRightLoop
    links.shiftRightLoop links.arithmetic.conversions.fromRaw links.arithmetic.conversions.cachedCtor)
  log2Loop : Checked program links.log2Loop (NatLoops.log2Loop
    links.log2Loop links.arithmetic.conversions.fromRaw)
  powLoop : Checked program links.powLoop (NatLoops.powLoop links.powLoop links.arithmetic.mul)
  shiftRight : Checked program links.shiftRight (NatLoops.shiftRight
    links.arithmetic.conversions.natural links.shiftRightLoop)
  log2 : Checked program links.log2 (NatLoops.log2 links.arithmetic.conversions.natural links.log2Loop)
  pow : Checked program links.pow (NatLoops.pow links.arithmetic.conversions.natural
    links.powLoop links.arithmetic.conversions.cachedCtor)

def certify (program : Program) (links : Links) : Except String (Certificate program links) := do
  let arithmetic ← NatArithmetic.certify program links.arithmetic
  let shiftRightLoop ← check program links.shiftRightLoop (NatLoops.shiftRightLoop
    links.shiftRightLoop links.arithmetic.conversions.fromRaw links.arithmetic.conversions.cachedCtor)
  let log2Loop ← check program links.log2Loop (NatLoops.log2Loop
    links.log2Loop links.arithmetic.conversions.fromRaw)
  let powLoop ← check program links.powLoop (NatLoops.powLoop links.powLoop links.arithmetic.mul)
  let shiftRight ← check program links.shiftRight (NatLoops.shiftRight
    links.arithmetic.conversions.natural links.shiftRightLoop)
  let log2 ← check program links.log2 (NatLoops.log2 links.arithmetic.conversions.natural links.log2Loop)
  let pow ← check program links.pow (NatLoops.pow links.arithmetic.conversions.natural
    links.powLoop links.arithmetic.conversions.cachedCtor)
  return { arithmetic, shiftRightLoop, log2Loop, powLoop, shiftRight, log2, pow }

end Compilatrix.Ixby.Runtime.NatLoops
