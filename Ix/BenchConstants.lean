/-
  The shared benchmark constant set: the single source of truth for which
  constants every benchmark backend with constant rows (ixvm, ixvm-ooc) runs. Every
  such backend runs this same set, so their numbers stay comparable per
  constant.

  `env` names the registry env (`Ix.Cli.BenchCmd.envSpecs` /
  `<env>.ixe`) the constant resolves in.
-/
module

public section

namespace Ix.BenchConstants

/-- One benchmark constant: a fully-qualified Lean name and the registry
    env it resolves in. -/
structure BenchConstant where
  name : String
  env : String

def benchConstants : Array BenchConstant := #[
  { name := "Nat.add_comm",         env := "InitStd" },
  { name := "Array.extract_append", env := "InitStd" },
  { name := "ByteArray.utf8DecodeChar?_utf8EncodeChar_append", env := "InitStd" },
  { name := "Std.HashMap",          env := "InitStd" },
  { name := "Lean.Json",            env := "ISLB" }
]

end Ix.BenchConstants
