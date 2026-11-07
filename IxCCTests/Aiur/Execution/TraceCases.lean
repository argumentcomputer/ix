import IxCCTests.Aiur.Execution.TraceFixtures

namespace IxCCTests.Aiur.Execution

open IxCC.Aiur
open IxCC.Aiur.OracleEval

def runTraces (count : IO.Ref Nat) : IO Unit := do
  for (name, toplevel, trace, replies) in [
      ("unit-counter recursion", counterProgram, counterTrace, counterReplies),
      ("ranked mutual recursion", rankedProgram, rankedTrace, counterReplies),
      ("store at pointer seven", storeProgram, storeTrace, #[[[7]], []]),
      ("load without preceding store", loadProgram, loadTrace, #[[[42]], []]),
      ("coherent self pointer", loadProgram, selfPointerTrace, #[[[7]], []]),
      ("equal content at different pointers", doubleStoreProgram, doubleStoreTrace, #[[[7], [9]], [], []]),
      ("correct gadget provider", xorProgram, xorTrace, #[[[3]], []]),
      ("callee executes its body", callProgram, callTrace 42, #[[[42]], []]),
      ("unconstrained callee is advice", hintCallProgram, hintCallTrace, #[[[99]]]),
      ("different answers to identical advice requests", repeatedAdvice, repeatedAdviceTrace, #[[[7], [9]]])] do
    need count (name ++ " trace") trace.validate.isOk
    need count (name ++ " rows") (checkRows toplevel unrestrictedAdvice trace {} replies)
    need count (name ++ " retained proof") (validateRows toplevel unrestrictedAdvice trace {} replies).isOk
  need count "false arithmetic claim is balanced" falseClaimTrace.validate.isOk
  need count "false arithmetic claim fails body replay"
    (!(checkRows constantProgram unrestrictedAdvice falseClaimTrace {} #[[]]))
  need count "false gadget is balanced" falseGadgetTrace.validate.isOk
  need count "false gadget fails primitive semantics"
    (!(checkRows xorProgram unrestrictedAdvice falseGadgetTrace {} #[[[9]], []]))
  need count "wrong callee result is balanced" (callTrace 99).validate.isOk
  need count "wrong callee result fails its own bytecode"
    (!(checkRows callProgram unrestrictedAdvice (callTrace 99) {} #[[[99]], []]))
  need count "denied advice rejects row"
    (!(checkRows repeatedAdvice (fun _ _ => false) repeatedAdviceTrace {} #[[[7], [9]]]))
  need count "advice policy sees complete answer"
    (!(checkRows repeatedAdvice (fun _ answer => decide (answer = [7])) repeatedAdviceTrace {} #[[[7], [9]]]))
  need count "row witness count checked" (failed
    (validateRows counterProgram unrestrictedAdvice counterTrace {} #[]) .rowWitnessCount)
  need count "extra row witness checked" (failed
    (validateRows constantProgram unrestrictedAdvice falseClaimTrace {} #[[], []]) .rowWitnessCount)
  need count "failed rows have explicit rejection" (failed
    (validateRows constantProgram unrestrictedAdvice falseClaimTrace {} #[[]]) .rowsRejected)
  need count "replay fuel applies to checked rows"
    (!(checkRows counterProgram unrestrictedAdvice counterTrace { maxSteps := 1 } counterReplies))
  let noDemand : Trace := ⟨[provider (.function 0 [1, 2] [3])], [.function 0 [1, 2] [3]]⟩
  need count "omitted gadget demand cannot pass replay"
    (!(checkRows xorProgram unrestrictedAdvice noDemand {} #[[[3]]]))
  let wrongMemory := provider (.memory 2 7 [42])
  need count "memory width is semantic" (!(checkRow loadProgram unrestrictedAdvice {} [] wrongMemory))
  need count "memory leaf cannot hide demands" (!(checkRow loadProgram unrestrictedAdvice {} []
    (provider (.memory 1 7 [42]) [.function 0 [] []])))
  need count "gadget leaf cannot hide demands" (!(checkRow xorProgram unrestrictedAdvice {} []
    (provider (.gadget 3 [1, 2, 3]) [.function 0 [] []])))
  need count "memory leaf has no answer tape" (!(checkRow loadProgram unrestrictedAdvice {} [[42]]
    (provider (.memory 1 7 [42]))))
  need count "gadget leaf has no answer tape" (!(checkRow xorProgram unrestrictedAdvice {} [[]]
    (provider (.gadget 3 [1, 2, 3]))))
  need count "zero-weight junk is not an execution premise" (checkRow constantProgram unrestrictedAdvice {} []
    (provider (.function 999 [] [99]) [] 0))
  need count "inactive junk is not an execution premise" (checkRow constantProgram unrestrictedAdvice {} []
    (provider (.function 999 [] [99]) [] 0 false))
  need count "balanced self loop passes local rows"
    (selfLoopTrace.validate.isOk && checkRows selfLoopProgram unrestrictedAdvice selfLoopTrace {} #[[[99]]])
  need count "balanced mutual loop passes local rows"
    (mutualLoopTrace.validate.isOk &&
      checkRows mutualLoopProgram unrestrictedAdvice mutualLoopTrace {} #[[[99]], [[99]]])

end IxCCTests.Aiur.Execution
