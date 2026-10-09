import Compilatrix.Tools.BuildGraph

/-! Registration controls for nested exact-axiom fence modules. -/

namespace CompilatrixTests.Tools.BuildGraph

open System Compilatrix.Tools.Check Compilatrix.Tools.BuildGraph

private def rejectsRegistration (proofs : List String) (root : FilePath) : IO Unit := do
  let error ← try
    let _ ← fenceAssertions root proofs
    pure none
  catch error => pure (some error.toString)
  let some error := error | throw (IO.userError "unregistered nested fence was accepted")
  need (error.contains "unregistered axiom-fence module CompilatrixTests.Fences.Nested.Flat")
    s!"nested fence failed for an unrelated reason: {error}"

def run : IO Unit := IO.FS.withTempDir fun root => do
  let directory := root / "CompilatrixTests/Fences"
  IO.FS.createDirAll (directory / "Nested")
  let flat := "/-- info: 'True.intro' does not depend on any axioms -/\n" ++
    "#guard_msgs in #print axioms True.intro\n"
  let nested := "/-- info: 'Eq.refl' does not depend on any axioms -/\n" ++
    "#guard_msgs in #print axioms Eq.refl\n"
  IO.FS.writeFile (directory / "Flat.lean") flat
  IO.FS.writeFile (directory / "Nested/Flat.lean") nested
  IO.FS.writeFile (directory / "Nested/ignored.txt") "unguarded non-Lean file"
  let assertions ← fenceAssertions root
    ["CompilatrixTests.Fences.Flat", "CompilatrixTests.Fences.Nested.Flat"]
  need (assertions.length == 2 && assertions.contains flat && assertions.contains nested)
    "nested/flat fence inventory lost or changed an exact assertion"
  rejectsRegistration ["CompilatrixTests.Fences.Flat"] root
  rejectsRegistration ["CompilatrixTests.Fences.Flat", "CompilatrixTests.Fences.Wrong.Flat"] root
  IO.println "build-graph nested fence registration: positive and two refusal controls passed"

end CompilatrixTests.Tools.BuildGraph
