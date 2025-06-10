import Ix.Benchmark

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n' + 2 => fib (n' + 1) + fib (n')


def fibBench := benchmark [
  ("fib 1", fib, 1),
  ("fib 2", fib, 2),
  ("fib 40", fib, 40)
]

--def storeBench :=
--  benchmark []
--
--def proveBench :=
--  benchmark []

def main : IO Unit := do
  let _result ← fibBench
