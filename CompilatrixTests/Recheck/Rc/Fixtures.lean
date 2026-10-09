import Compilatrix.Recheck.Produce
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson

set_option autoImplicit false
namespace CompilatrixTests.Recheck.Rc.Fixtures
open Compilatrix Lean System

def fixtureRoot : FilePath := "fixtures/rc/real-source"
def roots : List String := ["reverseList", "reverseRepeated", "sharedReverse"]

def verify : IO Unit := do
  let result ← IO.Process.output {
    cmd := "sha256sum", args := #["--status", "--check", (fixtureRoot / "manifest.sha256").toString] }
  unless result.exitCode == 0 do throw (IO.userError "RC input/oracle fixture identity changed")

def source (root : String) : IO Recheck.Input := do
  let bytes ← IO.FS.readBinFile (fixtureRoot / "anonymous.ixe")
  let equations ← IO.ofExcept (Json.parse (← IO.FS.readFile (fixtureRoot / "consumer.equations.json")))
  IO.ofExcept ((Recheck.ingress bytes equations ["CompilatrixTests.Own.H0." ++ root]).mapError (·.message))

end CompilatrixTests.Recheck.Rc.Fixtures
