import Compilatrix.Ixon.V3.Validate
import Compilatrix.Tools.Check

/-! The K1 fixture pack: ordinary Lean scalar programs and the unfolding
theorems of every recursive definition in their closure, produced by
`ix compile --equations` (see `fixtures/ixon-v3/k1/README.md`). -/

namespace CompilatrixTests.IxonV3.K1

open Compilatrix.Ixon Compilatrix.Ixon.V3 Compilatrix.Tools.Check

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError s!"v3 K1: {message}")

private def address (text : String) : IO Address := do
  match Address.ofBytes? (← IO.ofExcept (unhex text)) with
  | some address => return address
  | none => throw (IO.userError s!"v3 K1: invalid address {text}")

/-- Strict ingress, every recorded root/definition/equation address present,
and erased typing of the complete closure. -/
def run (root : System.FilePath) : IO Nat := do
  let env ← IO.ofExcept (decodeAnonymousEnv (← IO.FS.readBinFile (root / "k1/k1.ixe")))
  let pack ← readJson (root / "k1/equations.json")
  let mut assertions := 0
  for entry in ← arrField pack "roots" do
    require (env.consts.contains (← address (← strField entry "address")))
      s!"missing root {← strField entry "name"}"
    assertions := assertions + 1
  let equations ← arrField pack "equations"
  require (equations.size == 40) "equation count changed"
  for entry in equations do
    for key in ["definition_address", "equation_address"] do
      require (env.consts.contains (← address (← strField entry key)))
        s!"missing {key} of {← strField entry "definition"}"
      assertions := assertions + 1
  require (← arrField pack "failures").isEmpty "equation realization failures recorded"
  match Tc.checkEnv env with
  | .ok () => pure ()
  | .error error => throw (IO.userError s!"v3 K1: erased typing rejected the closure: {error}")
  return assertions + 3

end CompilatrixTests.IxonV3.K1
