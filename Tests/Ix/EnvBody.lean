/-
Regression guard: `getFileEnv` must load a file's own definitions (its body),
not only its imports.

`getFileEnv` previously ran only `processHeaderCore`, so the environment it
returned held the file's imports but none of its own constants — meaning
`ix compile`/`validate`/`ingress` emitted an env missing the file's definitions.
This loads an existing fixture (`Export.lean`, which defines `inductive MyNat`)
and asserts that body definition is present, alongside an imported constant.
-/

module

public import Ix.Meta
public import LSpec
public import Lean

open LSpec

namespace Tests.Ix.EnvBody

/-- Path is relative to the repository root, which is the working directory when
`lake test` runs the `IxTests` executable. -/
def fixturePath : System.FilePath := "Tests/Ix/Fixtures/Export.lean"

public def suite : IO LSpec.TestSeq := do
  let env ← getFileEnv fixturePath
  pure $
    LSpec.test "getFileEnv includes the file body (not just imports)"
      ((env.constants.find? `MyNat).isSome)
    ++ LSpec.test "getFileEnv still includes imports"
      ((env.constants.find? `Nat).isSome)

end Tests.Ix.EnvBody
