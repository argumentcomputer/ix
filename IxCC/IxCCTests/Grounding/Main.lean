import IxCCTests.Grounding.Run
import IxCCTests.Grounding.NoCanon
import IxCCTests.Grounding.Zeta
import IxCCTests.Grounding.GradedHead
import IxCCTests.Grounding.CaseEmpty
import IxCCTests.Grounding.LetClo
import IxCCTests.Grounding.LetWit
import IxCCTests.Grounding.Words

/-- `tests-grounding` runs the grounding check on the committed closures, with its negative
controls (`IxCCTests.Grounding.Run`), the canonicity-free family's decided fact on the
accepted corpus closures (`IxCCTests.Grounding.NoCanon`), step C's `let` cases on the corpus
closures the check still refuses and planted on `fib` (`IxCCTests.Grounding.Zeta`), and step 1b's
per-spine decision on every committed closure the measurements load, with its planted controls
(`IxCCTests.Grounding.GradedHead`), and step E0's `case` entry of kind `empty` on `resource`, with
its controls (`IxCCTests.Grounding.CaseEmpty`), and step C's closure-capture `let` on `arity` and
`closures` (`IxCCTests.Grounding.LetClo`), and the witness shape of a deep `let` (the minor-premise
shape) on the corpus, `closures` and `src-words`, with its controls
(`IxCCTests.Grounding.LetWit`), and the word family (step W) on `grounding/words` and `src-words`,
with its controls (`IxCCTests.Grounding.Words`). -/
def main : IO UInt32 := do
  let ok1 ← IxCCTests.Grounding.run
  let ok2 ← IxCCTests.Grounding.NoCanon.run
  let ok3 ← IxCCTests.Grounding.Zeta.run
  let ok4 ← IxCCTests.Grounding.GradedHead.run
  let ok5 ← IxCCTests.Grounding.CaseEmpty.run
  let ok6 ← IxCCTests.Grounding.LetClo.run
  let ok7 ← IxCCTests.Grounding.LetWit.run
  let ok8 ← IxCCTests.Grounding.Words.run
  return if ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 then 0 else 1
