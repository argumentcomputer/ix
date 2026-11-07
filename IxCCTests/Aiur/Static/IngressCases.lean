import IxCCTests.Aiur.Static.Fixtures

namespace IxCCTests.Aiur.Static

open IxCC.Aiur

def runIngress (count : IO.Ref Nat) : IO Unit := do
  let bytes := WireFixtures.counterExpected
  let root := Wire.address Execution.counterProgram
  match Wire.ingest {} {} bytes root with
  | .error reason => throw (IO.userError s!"frozen counter ingress rejected: {reason}")
  | .ok ingress =>
      need count "frozen addressed bytecode reaches checked execution"
        (ingress.validateTrace OracleEval.unrestrictedAdvice Execution.counterTrace {}
          #[0, 0, 0] inputReplies).isOk
      need count "addressed path checks rank count"
        (failed (ingress.validateTrace OracleEval.unrestrictedAdvice Execution.counterTrace {}
          #[] inputReplies) (.assignment .rankCount))
      need count "addressed path preserves replay budget"
        (failed (ingress.validateTrace OracleEval.unrestrictedAdvice Execution.counterTrace
          { replay.maxSteps := 0 } #[0, 0, 0] inputReplies) (.replay .rowsRejected))
  let changed := inputProgram true
  need count "changed direction cannot use prior bytecode root"
    (!(Wire.ingest {} {} (Wire.preimage changed) (Wire.address (inputProgram false))).isOk)
  match Wire.ingest {} {} (Wire.preimage changed) (Wire.address changed) with
  | .error reason => throw (IO.userError s!"changed program's own ingress rejected: {reason}")
  | .ok ingress =>
      need count "changed code cannot reuse prior trace certificate"
        (failed (ingress.validateTrace OracleEval.unrestrictedAdvice Execution.counterTrace {}
          #[0, 0, 0] inputReplies) (.assignment .dependencies))
  -- Empty metadata is admitted by the earlier wire checker even at this
  -- function-count setting. Static plan allocation adds its own guard.
  match Wire.ingest {} { maxFunctions := 0 } (Wire.preimage fallbackProgram) (Wire.address fallbackProgram) with
  | .error reason => throw (IO.userError s!"fallback ingress unexpectedly rejected: {reason}")
  | .ok ingress =>
      need count "addressed path retains its component limits"
        (failed (ingress.validateTrace OracleEval.unrestrictedAdvice Execution.counterTrace {}
          #[0, 1, 2] inputReplies) (.program .functionLimit))

end IxCCTests.Aiur.Static
