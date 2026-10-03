import Compilatrix.Ixon.V3.Validate
import Compilatrix.Tools.Check

/-! The K1 fixture packs: ordinary Lean scalar programs and the unfolding
theorems of every recursive definition in their closures, produced by
`ix compile --equations`. `k1/` holds the five programs in one closure (see
`fixtures/ixon-v3/k1/README.md`); `bench-k1/` holds one closure per K1
benchmark fixture's `entry` (see `fixtures/ixon-v3/bench-k1/README.md`). -/

namespace CompilatrixTests.IxonV3.K1

open Compilatrix.Ixon Compilatrix.Ixon.V3 Compilatrix.Tools.Check

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError s!"v3 K1: {message}")

private def address (text : String) : IO Compilatrix.Ixon.Address := do
  match Address.ofBytes? (← IO.ofExcept (unhex text)) with
  | some address => return address
  | none => throw (IO.userError s!"v3 K1: invalid address {text}")

/-- Strict ingress, every recorded root/definition/equation address present,
the expected equation count, no realization failures, and erased typing of
the complete closure. -/
def checkPack (closure equations : System.FilePath) (expectedEquations : Nat) : IO Nat := do
  let env ← IO.ofExcept (decodeAnonymousEnv (← IO.FS.readBinFile closure))
  let pack ← readJson equations
  let mut assertions := 0
  for entry in ← arrField pack "roots" do
    require (env.consts.contains (← address (← strField entry "address")))
      s!"{closure}: missing root {← strField entry "name"}"
    assertions := assertions + 1
  let recorded ← arrField pack "equations"
  require (recorded.size == expectedEquations) s!"{closure}: equation count changed"
  for entry in recorded do
    for key in ["definition_address", "equation_address"] do
      require (env.consts.contains (← address (← strField entry key)))
        s!"{closure}: missing {key} of {← strField entry "definition"}"
      assertions := assertions + 1
  require (← arrField pack "failures").isEmpty s!"{closure}: equation realization failures recorded"
  match Tc.checkEnv env with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"v3 K1: erased typing rejected {closure}: {error}")
  return assertions + 3

/-- The benchmark closures and their equation counts. -/
def benchFixtures : List (String × Nat) :=
  [("fib", 2), ("sum-loop", 34), ("ackermann", 34), ("tak", 5), ("gcd", 7)]

def run (root : System.FilePath) : IO Nat := do
  let mut assertions ← checkPack (root / "k1/k1.ixe") (root / "k1/equations.json") 40
  for (name, count) in benchFixtures do
    assertions := assertions +
      (← checkPack (root / "bench-k1" / s!"{name}.ixe") (root / "bench-k1" / s!"{name}.equations.json") count)
  return assertions

end CompilatrixTests.IxonV3.K1
