import IxCC.Ixon.V3.Validate
import IxCC.Src.KernelFront.Accept
import IxCC.Tools.Check

/-! The K1 fixture packs: ordinary Lean scalar programs and the unfolding
theorems of every recursive definition in their closures, produced by
`ix compile --equations`. `k1/` holds the five programs in one closure (see
`fixtures/ixon-v4/k1/README.md`); `bench-k1/` holds one closure per K1
benchmark fixture's `entry` (see `fixtures/ixon-v4/bench-k1/README.md`). -/

namespace IxCCTests.IxonV3.K1

open IxCC.Ixon IxCC.Ixon.V3 IxCC.Tools.Check

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError s!"v3 K1: {message}")

private def address (text : String) : IO IxCC.Ixon.Address := do
  match Address.ofBytes? (← IO.ofExcept (unhex text)) with
  | some address => return address
  | none => throw (IO.userError s!"v3 K1: invalid address {text}")

/-- Strict ingress, every recorded root/definition/equation address present,
the expected equation count, no realization failures, and the certified
kernel's acceptance of the complete closure (`Src.KernelFront.accept`). -/
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
  match IxCC.Src.KernelFront.accept env with
  | .ok _ => pure ()
  | .error refusal => throw (IO.userError s!"v3 K1: the kernel refused {closure}: {refusal.render}")
  return assertions + 3

/-- The benchmark closures and their equation counts. -/
def benchFixtures : List (String × Nat) :=
  [("fib", 3), ("sum-loop", 40), ("ackermann", 40), ("tak", 7), ("gcd", 10)]

def run (root : System.FilePath) : IO Nat := do
  let mut assertions ← checkPack (root / "k1/k1.ixe") (root / "k1/equations.json") 46
  for (name, count) in benchFixtures do
    assertions := assertions +
      (← checkPack (root / "bench-k1" / s!"{name}.ixe") (root / "bench-k1" / s!"{name}.equations.json") count)
  return assertions

end IxCCTests.IxonV3.K1
