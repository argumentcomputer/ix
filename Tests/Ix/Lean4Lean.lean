import LSpec
import Benchmarks.Lean4Lean

/-!
Smoke tests for the lean4lean dependency (ignored runner `lean4lean`):
the reference Lean4-in-Lean4 kernel accepts a real closure replayed from
the test env and rejects an ill-typed declaration. Guards the pinned
require (toolchain drift or an API change in `Lean4Lean.addDecl` surfaces
here and in `bench-lean4lean`, which shares the replay machinery).
-/

namespace Tests.Ix.Lean4Lean

open LSpec

def run (env : Lean.Environment) : IO UInt32 := do
  IO.println "lean4lean"
  let newConstants := env.constants.fold
    (init := ({} : Std.HashMap Lean.Name Lean.ConstantInfo)) fun m n ci => m.insert n ci
  -- Accept: replay a real constant's whole closure into a fresh kernel env
  -- (the `bench-lean4lean --consts` path).
  let closRes ← (BenchLean4Lean.replayClosure env newConstants `Nat.add_comm false).toBaseIO
  -- Reject: an axiom whose type is a Nat literal (not a sort) must fail
  -- `checkConstantVal`.
  let bogus : Lean.AxiomVal :=
    { name := `l4lTestBogusAxiom, levelParams := [], type := Lean.mkRawNatLit 0
      isUnsafe := false }
  let rejected := !(Lean4Lean.addAxiom env.toKernelEnv bogus).isOk
  let seq : TestSeq :=
    (match closRes with
     | .ok n => test s!"Nat.add_comm closure replays through lean4lean ({n} declarations)"
         (n > 0)
     | .error e => test s!"Nat.add_comm closure replay failed: {e}" false)
    ++ test "ill-typed axiom (type = Nat literal) is rejected" rejected
  lspecIO (.ofList [("lean4lean", [seq])]) []

end Tests.Ix.Lean4Lean
