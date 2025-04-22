import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CompileM
import Ix.Meta
import Lean
import Tests.Ix.Fixtures
import Lean

open LSpec
open Ix.Compile

--def testCompileExpr (env: Lean.Environment)
--  (msg: String) (commit: Bool) (input: Lean.Expr) (expected: Ix.Expr)
--  : IO TestSeq := do
--  let (out, _) <- 
--  CompileM.runIO' env (compileExpr commit input)
--  return test msg (out == expected)
--
--def threeIO : IO TestSeq := do
--  return test "one isn't two" (1 == 2)
--
--def foo : IO Lean.Expr := do
--  runMeta (Lean.Meta.whnf (Lean.toExpr 3)) (<- get_env!)
--
--def bar : IO Ix.Expr := do
--  let env <- get_env!
--  let .defnInfo defn ← runCore (Lean.getConstInfo ``id) env
--    | unreachable!
--  let input <- runMeta (Lean.Meta.whnf defn.value) env
--  --let (out, _) <- CompileM.runIO' env (compileExpr false input)
--  return out

--#eval bar

def test1 : IO TestSeq := do
  let env <- get_env!
  let input <- runMeta (Lean.Meta.whnf (Lean.toExpr 3)) env
  let expected := Lean.Expr.lit (Lean.Literal.natVal 3)
  return test "expected 3" (input == expected)

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
  test1
]
