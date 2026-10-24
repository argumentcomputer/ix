import Tests.Ix.Cert.SourceGraphLiteral

open Ix.Compile.SourceGraph
open Tests.Ix.Cert.SourceGraphLiteral

-- Keep both real code paths distinct: there is no csimp replacement of literalUse.
private def tagScore : LiteralUse → Nat | .none => 0 | .nat => 1 | .string => 2
private def nodeScore (node : Node) : Nat :=
  tagScore node.literals + node.direct.size + match node.grouping with
    | .plain => 0 | .induct all | .recursor all => all.size
@[noinline] private def treeEval (ci : Ix.ConstantInfo) := tagScore (literalUse ci)
@[noinline] private def sharedEval (ci : Ix.ConstantInfo) := tagScore (literalUseShared ci)
@[noinline] private def oldCaptureEval (ci : Ix.ConstantInfo) := nodeScore (captureUsing ci {})
@[noinline] private def captureEval (ci : Ix.ConstantInfo) := nodeScore (captureUsingShared ci {})
@[noinline] private def rowEval (ci : Ix.ConstantInfo) : Nat :=
  let row := rowUsingShared ci.getCnst.name ci {}
  nodeScore row.node + (if row.name == ci.getCnst.name then 0 else 1) + (if row.kept.isSome then 1 else 0)

private def timeLiteral (f : Ix.ConstantInfo → Nat) (ci : Ix.ConstantInfo) (repeats : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:repeats] do
    let result ← IO.lazyPure fun _ => f ci
    unless result == 0 do throw (IO.userError "literal-free measurement changed its result or fields")
  return (← IO.monoNanosNow) - start

private def runCase (label : String) (body : Ix.Expr) (expectedNodes : Nat) : IO Unit := do
  let ci := sample body
  let observed ← IO.lazyPure fun _ => (Literal.scanTerms Literal.empty (terms ci)).memo.entries.size
  unless observed == expectedNodes do throw (IO.userError s!"{label}: memo has {observed}, expected {expectedNodes}")
  let repeats := 3
  let treeNs ← timeLiteral treeEval ci repeats
  let sharedNs ← timeLiteral sharedEval ci repeats
  let oldCaptureNs ← timeLiteral oldCaptureEval ci repeats
  let captureNs ← timeLiteral captureEval ci repeats
  let rowNs ← timeLiteral rowEval ci repeats
  let us := fun n => n / (1000 * repeats)
  IO.println s!"{label}\tnodes={observed}\trepeats={repeats}\ttree_us={us treeNs}\tshared_us={us sharedNs}\told_capture_us={us oldCaptureNs}\tcapture_us={us captureNs}\trow_us={us rowNs}"

def main : IO Unit := do
  IO.println "literal/capture/row extraction; all output fields consumed; synthetic shapes, proper hashes; times per call, no ratio threshold"
  for depth in [12, 16, 20] do
    runCase s!"shared-depth-{depth}" (dag depth) (depth + 2)
  runCase "unshared-depth-10" (unshared 10 0) 2048
