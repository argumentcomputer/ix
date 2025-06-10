import Ix.Benchmark

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n' + 2 => fib (n' + 1) + fib (n')

def fibBench := (bgroup "fib" [
  bench "fib 1" fib 1,
  bench "fib 2" fib 2,
  bench "fib 30" fib 30
] { numRuns := 100 } )

def addBench := (bgroup "add" [
  bench "add 1 2" (Nat.add 1) 2
])
--def storeBench :=
--  benchmark []
--
--def proveBench :=
--  benchmark []

def main : IO Unit := do
  let _result ← fibBench
