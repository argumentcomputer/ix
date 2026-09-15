import CompilatrixTests.Aiur.Static.Fixtures

namespace CompilatrixTests.Aiur.Static

open Compilatrix.Aiur

def runPositive (count : IO.Ref Nat) : IO Unit := do
  for increasing in [false, true] do
    need count s!"input counter checked execution {increasing}"
      (certify (inputProgram increasing) (inputTrace increasing) #[0, 0, 0] inputReplies).isOk
    need count s!"output counter checked execution {increasing}"
      (certify (outputProgram increasing) (outputTrace increasing) #[0, 0, 0] (outputReplies increasing)).isOk
  for (name, toplevel, trace, ranks, replies) in [
      ("frozen counter program", Execution.counterProgram, Execution.counterTrace, #[0, 0, 0], inputReplies),
      ("ranked mutual recursion", Execution.rankedProgram, Execution.rankedTrace, #[0, 1, 2], inputReplies),
      ("ranked fallback", fallbackProgram, Execution.counterTrace, #[0, 1, 2], inputReplies),
      ("static component order", orderedProgram, Execution.callTrace 42, #[0, 0], #[[[42]], []]),
      ("mixed flags and interleaved rows", mixedProgram, mixedTrace, mixedRanks, mixedReplies),
      ("duplicate counter providers", inputProgram false, duplicateTrace, #[0, 0, 0, 0], duplicateReplies),
      ("duplicate ranked providers", fallbackProgram, duplicateTrace, #[0, 1, 1, 2], duplicateReplies),
      ("zero-weight parent", inputProgram false, zeroJunkTrace, #[0, 0, 0, 0], zeroJunkReplies),
      ("store pointer seven", Execution.storeProgram, Execution.storeTrace, #[0, 0], #[[[7]], []]),
      ("load without prior store", Execution.loadProgram, Execution.loadTrace, #[0, 0], #[[[42]], []]),
      ("self pointer", Execution.loadProgram, Execution.selfPointerTrace, #[0, 0], #[[[7]], []]),
      ("equal contents distinct pointers", Execution.doubleStoreProgram, Execution.doubleStoreTrace,
        #[0, 0, 0], #[[[7], [9]], [], []]),
      ("concrete gadget", Execution.xorProgram, Execution.xorTrace, #[0, 0], #[[[3]], []]),
      ("unconstrained call advice", Execution.hintCallProgram, Execution.hintCallTrace, #[0], #[[[99]]]),
      ("repeated advice", Execution.repeatedAdvice, Execution.repeatedAdviceTrace, #[0], #[[[7], [9]]])] do
    need count (name ++ " independent balance") trace.validate.isOk
    need count (name ++ " certificate and replay") (certify toplevel trace ranks replies).isOk
  let continuationTrace : Trace :=
    ⟨[Execution.provider (.function 0 [0, 10] [17])], [.function 0 [0, 10] [17]]⟩
  need count "nonrecursive unranked continuation needs no counter"
    (certify { Execution.continuationScope with callComponents := #[⟨0, false⟩] }
      continuationTrace #[0] #[[]]).isOk
  let rootYieldTrace : Trace := ⟨[Execution.provider (.function 0 [7] [7])], [.function 0 [7] [7]]⟩
  need count "root yield still executes" (certify Execution.rootYield rootYieldTrace #[0] #[[]]).isOk
  need count "empty trace and program" (certify WireFixtures.empty zeroTrace #[] #[]).isOk
  need count "zero matrix budget admits empty trace"
    (certify WireFixtures.empty zeroTrace #[] #[] { assignment.maxPairs := 0 }).isOk
  need count "exact matrix budget"
    (certify fallbackProgram Execution.counterTrace #[0, 1, 2] inputReplies { assignment.maxPairs := 9 }).isOk
  need count "exact rank budget"
    (certify fallbackProgram Execution.counterTrace #[0, 1, 2] inputReplies { assignment.maxRank := 2 }).isOk
  need count "counter recursion needs no rank budget"
    (certify (inputProgram false) Execution.counterTrace #[0, 0, 0] inputReplies { assignment.maxRank := 0 }).isOk
  need count "exact trace budget"
    (certify (inputProgram false) Execution.counterTrace #[0, 0, 0] inputReplies
      { trace := { maxRows := 3, maxUnitSlots := 6, maxMessageFields := 2 } }).isOk

end CompilatrixTests.Aiur.Static
