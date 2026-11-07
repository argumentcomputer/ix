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

/-- The frozen input stays byte-identical until an intentional refreeze
(`fixtures/rc/real-source/README.md`), so it keeps the names it was produced
with: the closure serializes its roots under `frozenRootPrefix`, and the
sidecar declares the k1-equations format under `frozenEquationsFormat`. These
are the only spellings this loader reads that a project rename leaves alone. -/
def frozenRootPrefix : String := "CompilatrixTests.Own.H0."
def frozenEquationsFormat : String := "compilatrix/k1-equations/1"

def source (root : String) : IO Recheck.Input := do
  let bytes ← IO.FS.readBinFile (fixtureRoot / "anonymous.ixe")
  let equations ← IO.ofExcept (Json.parse (← IO.FS.readFile (fixtureRoot / "consumer.equations.json")))
  unless (equations.getObjValAs? String "format").toOption == some frozenEquationsFormat do
    throw (IO.userError "RC real-source sidecar format changed")
  -- The same sidecar format under the name the reader expects.
  let equations := equations.setObjVal! "format" (.str "compilatrix/k1-equations/1")
  IO.ofExcept ((Recheck.ingress bytes equations [frozenRootPrefix ++ root]).mapError (·.message))

end CompilatrixTests.Recheck.Rc.Fixtures
