import IxCC.Aiur.Static.Sound

namespace IxCC.Aiur.Wire

/-- Reuse the exact addressed program's component-check evidence. Trace
budgets cannot replace the program's already checked component limits. -/
def Ingress.validateTrace {wireLimits : Limits} {componentLimits : CheckLimits}
    {bytes : ByteArray} {root : IxCC.Ixon.Address}
    (ingress : Ingress wireLimits componentLimits bytes root)
    (oracle : OracleEval.AdviceOracle) (trace : Trace) (limits : Static.TraceLimits)
    (ranks : Array Nat) (replies : Array (List OracleEval.Values)) :
    Except Static.Error (Static.CheckedTrace ingress.value oracle trace) := do
  let program ← match Static.prepareChecked componentLimits ingress.value ingress.checked with
    | .ok checked => pure checked
    | .error error => throw (.program error)
  Static.validatePrepared program oracle trace limits ranks replies

end IxCC.Aiur.Wire
