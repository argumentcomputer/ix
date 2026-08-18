/-
  `getFileEnv` module-header tests: the header's actual `module` mode
  must be honored (`Environment.header.isModule` reflects the mode
  `processHeaderCore` was given), and a classic file stays classic.
  Loading a new-style module as a classic private script re-exposes
  private transitive imports and destroys qualified-package isolation
  downstream.
-/
module

public import LSpec
public import Ix.Meta

public section

open LSpec

namespace Tests.Ix.MetaEnv

private def runFixture (name source : String) (expectModule : Bool)
    (marker : Lean.Name) : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := dir / name
  IO.FS.writeFile path source
  try
    let env ← getFileEnv path
    let isModule := env.header.isModule
    let hasMarker := env.contains marker
    if isModule != expectModule then
      return (false, 0, 0,
        some s!"header.isModule = {isModule}, expected {expectModule}")
    if !hasMarker then
      return (false, 0, 0, some s!"marker {marker} missing from env")
    return (true, 0, 0, none)
  catch e =>
    return (false, 0, 0, some s!"getFileEnv failed: {e}")
  finally
    IO.FS.removeDirAll dir

def moduleFileTest : TestSeq :=
  .individualIO "getFileEnv honors a `module` header" none
    (runFixture "ModFixture.lean"
      "module\n\npublic def TestsMetaEnv.modMarker : Nat := 7\n"
      (expectModule := true) `TestsMetaEnv.modMarker) .done

def classicFileTest : TestSeq :=
  .individualIO "getFileEnv keeps a classic file classic" none
    (runFixture "ClassicFixture.lean"
      "def TestsMetaEnv.classicMarker : Nat := 3\n"
      (expectModule := false) `TestsMetaEnv.classicMarker) .done

def suite : List TestSeq := [moduleFileTest, classicFileTest]

end Tests.Ix.MetaEnv
