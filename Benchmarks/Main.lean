--import Ix.Claim
--import Ix.Address
--import Ix.Meta
--import Ix.CompileM
--import Batteries
--import Ix.Store
--import Ix.Ixon.Expr
--import Ix.Ixon.Serialize
--import Ix.Cronos
import Ix.Benchmark

--open Batteries (RBMap)

def fibBench :=
  benchmark [
    ("fib 1", fib, 1),
    ("fib 2", fib, 2),
    ("fib 30", fib, 30)
  ]

--def storeBench :=
--  benchmark []
--
--def proveBench :=
--  benchmark []

--def cron := RBMap.ofList [("hey", 1)] compare

def main (_args: List String) : IO Unit := do
  let _result ← fibBench

  -- TODO: Use Ix.Compile.compileConst
  --let mut env : Lean.Environment := ← get_env!
  --let myExpr := cron.toList
  --let (lvls, typ, val) ← runMeta (metaMakeDef myExpr) env
  --let ((addr1, _), _) ← (Ix.Compile.commitDef lvls typ val).runIO env
  --IO.println val
  --let exprPretty <- runMeta (Lean.Meta.ppExpr val) env
  --IO.println exprPretty
  --IO.println s!"Expr: {repr myExpr}, commitment: {addr1}"
  --let const ← StoreIO.toIO $ readConst addr1
  ----IO.println $ repr const
  --let data ← Ixon.Serialize.get const
  --let result ←
  --  if args.contains "fib" then fibBench
