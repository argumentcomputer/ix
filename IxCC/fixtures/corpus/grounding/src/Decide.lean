/-! The `grounding` family's subject (`docs/corpus.md`): the evaluation-axiom shape
`decide (fib 10 = 55)`, whose run fires `Decidable.casesOn` on a major built at another
proposition (`Nat.decEq`), passes a proof field it never builds, and reads back `Bool.true`.
`K1.fib` is verbatim from `benchmarks/fixtures/fib/Fib.lean`. -/

namespace K1

/-- Structural recursion with a `match` on 0 / 1 / n+2. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

end K1

namespace Grounding

/-- `decide (fib 10 = 55)`. -/
def decideFib10 : Bool := decide (K1.fib 10 = 55)

end Grounding

/-- The oracle driver: each stdin line `ROOT` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | ["Grounding.decideFib10"] => IO.println (toString Grounding.decideFib10)
    | [] => pure ()
    | _ => IO.println "unknown root"
