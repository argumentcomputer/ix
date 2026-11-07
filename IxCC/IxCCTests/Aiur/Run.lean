import IxCCTests.Aiur.Fixtures

namespace IxCCTests.Aiur

open IxCC.Aiur
open _root_.IxCC.Vendor.Aiur (G gSize)

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Aiur regression failed: {label}")

private def rejected (trace : Trace) (expected : Trace.Error) (limits : Trace.Limits := {}) : Bool :=
  match trace.validate limits with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def run : IO Unit := do
  for (name, trace) in [
      ("leaf", leaf), ("shared demand", shared), ("negative field weights", negativeWeights),
      ("inactive junk", inactiveJunk), ("witness pointer seven", witnessMemory),
      ("separate memory buckets", separateBuckets), ("self pointer is not a call cycle", selfPointer),
      ("mixed counter/order/rank", mixed)] do
    need name trace.validate.isOk
  need "missing provider" (rejected missingProvider .unbalanced)
  need "inactive nonzero provider" (rejected inactiveProvider .inactiveProvider)
  need "output is part of exact message" (rejected wrongOutput .unbalanced)
  need "unused provider still participates in balance" (rejected unusedProvider .unbalanced)
  let wrongChannel : Trace :=
    ⟨[provider (call 0) [.gadget 1 [9]], provider (call 1)], [call 0]⟩
  need "function and gadget channels cannot alias" (rejected wrongChannel .unbalanced)
  need "conflicting memory passes message balance" inconsistentMemory.checkBalance
  need "conflicting witness heap" (rejected inconsistentMemory .inconsistentMemory)
  need "one heap observes arbitrary pointer seven"
    (decide (Memory.heap (Memory.cells witnessMemory) 1 7 = some [42]))
  need "balanced self-call still needs acyclicity" selfCall.validate.isOk
  need "balanced mutual calls still need acyclicity" mutualCall.validate.isOk
  need "self edge exists" (decide (selfCall.Requires ⟨0, by decide⟩ ⟨0, by decide⟩))
  need "mutual edges exist" (decide (mutualCall.Requires ⟨1, by decide⟩ ⟨0, by decide⟩ ∧
    mutualCall.Requires ⟨0, by decide⟩ ⟨1, by decide⟩))
  need "row limit" (rejected leaf .resourceLimit { maxRows := 0 })
  need "slot limit" (rejected leaf .resourceLimit { maxUnitSlots := 1 })
  need "message width limit" (rejected leaf .resourceLimit { maxMessageFields := 0 })
  let hiddenDemands : Trace :=
    ⟨[provider (call 0), provider (call 1) (List.replicate 1024 (call 77)) 0 false], [call 0]⟩
  need "inactive demands still count toward resource limits" (rejected hiddenDemands .resourceLimit)
  need "nonempty count can vanish at the characteristic" (decide (G.ofNat gSize.toNat = (0 : G)))
  IO.println "aiur-tests-ok: 25 trace, memory, cycle, and resource regressions"

end IxCCTests.Aiur
