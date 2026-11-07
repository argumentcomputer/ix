import IxCCTests.Aiur.Execution.ControlFixtures
import IxCCTests.Aiur.Execution.OpCases

namespace IxCCTests.Aiur.Execution

open IxCC.Aiur
open IxCC.Aiur.OracleEval

def runControls (count : IO.Ref Nat) : IO Unit := do
  need count "function return preserves its outcome"
    (exactResult (replay emptyReturn) ⟨.returned 7 [], [], []⟩)
  need count "root yield preserves its outcome"
    (exactResult (replay rootYield [42]) ⟨.yielded 3 [42], [], []⟩)
  need count "selected match" (succeeded (replay matched [0]) [11])
  need count "default match" (succeeded (replay matched [1]) [22])
  need count "first repeated label wins" (succeeded (replay duplicateCases [0]) [11])
  need count "absent match arm" (failed (replay missingCase [1]) .noMatch)
  need count "continuation restores pre-branch registers" (succeeded (replay continuationScope [0, 10]) [17])
  need count "return skips continuation" (succeeded (replay earlyReturn [0]) [7])
  need count "return skips all pending continuations" (succeeded (replay nestedEarlyReturn [0]) [7, 8])
  need count "yield targets closest continuation" (succeeded (replay nestedYield [0]) [15])
  need count "ordinary match forwards yield" (succeeded (replay matchInsideContinuation [0]) [10])
  need count "yield arity checked" (failed (replay wrongYieldSize [0]) (.yieldArity 1 2))
  need count "continuation preserves demand order"
    (exactResult (replay continuationMemory [0, 7] [[42], [9]])
      ⟨.returned 2 [9], [.memory 1 7 [42], .memory 1 9 [42]], []⟩)
  need count "constrained assertion accepts checked inverse" (succeeded (replay inverseChecked [1] [[1]]) [1])
  need count "constrained assertion rejects bogus inverse" (failed (replay inverseChecked [1] [[9]]) .assertionFailed)
  need count "identical requests may have different advice" (succeeded (replay repeatedAdvice [0] [[7], [9]]) [7, 9])
  need count "u32 carry is a field expression, not an implicit bit" (succeeded
    (replay virtualCarry [255, 255, 255, 255, 1, 0, 0, 0] [[1, 0, 0, 0]]) [1, 0, 0, 0, 4294967296])
  need count "virtual carry cannot be supplied as fifth advice field" (failed
    (replay virtualCarry [255, 255, 255, 255, 1, 0, 0, 0] [[0, 0, 0, 0, 9]]) (.replyArity 4 5))
  need count "missing hint answer" (failed (replay repeatedAdvice [0]) .missingReply)
  need count "extra answer rejected after return" (failed (replay emptyReturn [] [[9]]) .unusedReplies)
  need count "unused continuation answer rejected on early return"
    (failed (replay earlyReturn [0] [[9]]) .unusedReplies)
  need count "invalid public function" (failed (runFunction emptyReturn {} 9 [] []) (.invalidFunction 9))
  need count "entry input arity" (failed (replay rootYield []) (.inputArity 0 1 0))
  need count "invalid return value" (failed
    (replay (opsProgram 0 #[] #[999])) (.invalidIndex 999))
  need count "zero local fuel" (failed (replay emptyReturn [] [] { maxSteps := 0 }) .fuelExhausted)
  need count "one transition insufficient for empty body" (failed
    (replay emptyReturn [] [] { maxSteps := 1 }) .fuelExhausted)
  need count "exact local fuel boundary" (succeeded (replay emptyReturn [] [] { maxSteps := 2 }) [])
  need count "larger local fuel preserves result" (sameResults
    (replay continuationScope [0, 10] [] { maxSteps := 64 })
    (replay continuationScope [0, 10] [] { maxSteps := 128 }))
  need count "initial register capacity" (failed
    (replay rootYield [42] [] { maxValues := 0 }) .valueLimit)
  need count "register growth capacity" (failed
    (replay (opsProgram 0 #[.const 1] #[0]) [] [] { maxValues := 0 }) .valueLimit)
  need count "return operand capacity" (failed
    (replay (opsProgram 1 #[] #[0, 0]) [42] [] { maxValues := 1 }) .valueLimit)
  need count "answer count capacity" (failed
    (replay repeatedAdvice [0] [[7], [9]] { maxReplies := 1 }) .answerLimit)
  need count "answer field capacity" (failed
    (replay repeatedAdvice [0] [[7], [9]] { maxReplyFields := 1 }) .answerLimit)
  need count "advice observation capacity" (failed
    (replay repeatedAdvice [0] [[7], [9]] { maxObservationFields := 5 }) .observationLimit)
  need count "exact advice observation capacity" (succeeded
    (replay repeatedAdvice [0] [[7], [9]] { maxObservationFields := 6 }) [7, 9])
  need count "lookup observation capacity" (failed
    (replay (opsProgram 1 #[.load 1 0] #[1]) [7] [[42]] { maxObservationFields := 3 }) .observationLimit)
  need count "exact lookup observation capacity" (succeeded
    (replay (opsProgram 1 #[.load 1 0] #[1]) [7] [[42]] { maxObservationFields := 4 }) [42])
  let state : State := { values := #[20, 22], replies := [[42]] }
  need count "callee index checked" (failed
    (evalOp callTarget 128 (.call 9 #[0, 1] 1 false) state) (.invalidFunction 9))
  need count "unconstrained callee index checked" (failed
    (evalOp callTarget 128 (.call 9 #[0, 1] 1 true) state) (.invalidFunction 9))
  need count "callee input arity checked" (failed
    (evalOp callTarget 128 (.call 1 #[0] 1 false) state) (.inputArity 1 2 1))
  need count "call result arity checked" (failed
    (evalOp callTarget 128 (.call 1 #[0, 1] 2 false) state) (.replyArity 2 1))
  need count "missing register never defaults to zero" (failed
    (evalOp callTarget 128 (.add 0 99) state) (.invalidIndex 99))
  need count "unequal assertion arities reject" (failed
    (evalOp callTarget 128 (.assertEq #[0] #[0, 0] none) state) .assertionFailed)
  need count "word packing requires four operands" (failed
    (evalOp callTarget 128 (.u32ToField #[0, 1, 0]) state) (.operandArity 4 3))
  need count "word addition requires four operands" (failed
    (evalOp callTarget 128 (.unconstrainedU32Add #[0] #[1]) state) (.operandArity 4 1))
  need count "word operand indices do not default to zero" (failed
    (evalOp callTarget 128 (.u32ToField #[0, 1, 99, 0]) state) (.invalidIndex 99))
  need count "zero-width load has an exact empty reply"
    (exactResult (replay (opsProgram 1 #[.load 0 0] #[]) [7] [[]])
      ⟨.returned 0 [], [.memory 0 7 []], []⟩)
  need count "huge output count does not allocate" (failed
    (replay (opsProgram 1 #[.ioRead 0 0 (2 ^ 64)] #[]) [0] [[]]) (.replyArity (2 ^ 64) 0))
  need count "zero-output gadget still needs its reply record" (failed
    (evalOp callTarget 128 (.u8RangeCheck 0 1) { values := #[0, 255], replies := [] }) .missingReply)

end IxCCTests.Aiur.Execution
