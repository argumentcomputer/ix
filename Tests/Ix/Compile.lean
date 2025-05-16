import LSpec

import Ix.Ixon
import Ix.Address
import Ix.Common
import Ix.CompileM
import Ix.DecompileM
import Ix.Meta
import Lean
import Tests.Ix.Fixtures
import Lean

open LSpec
open Ix.Compile

--def testCompileEnv (env: Lean.Environment) : Except DecompileError Bool := do
--  let delta := env.getDelta
--  let stt <- match (compileDelta delta).run (.init 200000) (.init env 0) with
--  | .ok _ s => pure s
--  | .error e s => throw <| .compileError e s
--  let stt2 <- match decompileEnv.run (.init 200000) (.init stt.names stt.store) with
--    | .ok _ s => pure s
--    | .error e _ => throw e
--  let mut res := true
--  for (n, c) in delta do
--    match stt2.env.find? n with
--    | .some c2 => res := res && c == c2
--    | .none => throw <| .unknownName n
--  return res

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

--def testRoundtripGetEnv : IO TestSeq := do
--  let env <- get_env!
--  let delta := env.getDelta
--  let (_, cstt) <- (compileDelta delta).runIO env (seed := .some 0)
--  IO.println s!"compiled env"
--  let mut dstt := DecompileState.init cstt.names cstt.store
--  for (n, (anon, meta)) in dstt.names do
--    IO.println s!"decompiling {n} {anon}:{meta}"
--    match (ensureConst n anon meta).run (.init 200000) dstt with
--    | .ok _ s => do
--      IO.println s!"✓ {n} @ {anon}:{meta}"
--      dstt := s
--    | .error e _ => do
--      IO.println s!"{repr <| cstt.env.constants.find! n}"
--      e.pretty >>= fun e => throw (IO.userError e)
--  let mut res := true
--  for (n, c) in delta do
--    match dstt.env.find? n with
--    | .some c2 => res := (res && c == c2)
--    | .none => do
--      let e' <- (DecompileError.unknownName n).pretty
--      throw (IO.userError e')
--  return test "env compile roundtrip" (res == true)

def Tests.Ix.Compile.suiteIO: List (IO TestSeq) := [
  test1,
--  testRoundtripGetEnv
]
