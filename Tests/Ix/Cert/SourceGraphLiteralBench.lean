import Tests.Ix.Cert.SourceGraphLiteral

open Ix.Compile.SourceGraph
open Tests.Ix.Cert.SourceGraphLiteral

-- Keep both real code paths distinct: there is no csimp replacement of literalUse.
@[noinline] private def treeEval (ci : Ix.ConstantInfo) := literalUse ci
@[noinline] private def sharedEval (ci : Ix.ConstantInfo) := literalUseShared ci

private def timeLiteral (f : Ix.ConstantInfo → LiteralUse) (ci : Ix.ConstantInfo) (repeats : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  for _ in [:repeats] do
    let result ← IO.lazyPure fun _ => f ci
    unless result == .none do throw (IO.userError "literal-free measurement changed its result")
  return (← IO.monoNanosNow) - start

private def runCase (label : String) (body : Ix.Expr) (expectedNodes : Nat) : IO Unit := do
  let ci := sample body
  let observed ← IO.lazyPure fun _ => (Literal.scanTerms Literal.empty (terms ci)).memo.entries.size
  unless observed == expectedNodes do throw (IO.userError s!"{label}: memo has {observed}, expected {expectedNodes}")
  let repeats := 3
  let treeNs ← timeLiteral treeEval ci repeats
  let sharedNs ← timeLiteral sharedEval ci repeats
  IO.println s!"{label}\tnodes={observed}\trepeats={repeats}\ttree_us={treeNs / (1000 * repeats)}\tshared_us={sharedNs / (1000 * repeats)}"

def main : IO Unit := do
  IO.println "literal extraction only; synthetic shapes, proper hashes; times per call, no ratio threshold"
  for depth in [12, 16, 20] do
    runCase s!"shared-depth-{depth}" (dag depth) (depth + 2)
  runCase "unshared-depth-10" (unshared 10 0) 2048
