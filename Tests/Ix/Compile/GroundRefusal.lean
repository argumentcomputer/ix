/-
  The compile's record of ungrounded input (part of `ground-unit`; the
  adversarial matrix's row 11): a constant whose value dependency is left
  out of the input is refused by name in both compilers, with the named
  refusal `UNGROUNDED-INPUT: …` (`Ix.GroundError.refusal`, Rust
  `ground::refusal`, the same text), and never dropped silently; the closed
  input compiles with no failure. `ix compile-lean` exits nonzero on any
  recorded failure unless `--allow-partial` (`Ix.Cli.CompileLeanCmd`), so it
  is fail-closed on ungrounded input.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import LSpec

open Lean LSpec

namespace Tests.Ix.Compile.GroundRefusal

namespace Src

/-- A definition whose value reaches `Nat.add` through `instAddNat`. -/
def double (n : Nat) : Nat := n + n

end Src

def target : Name := ``Src.double

/-- The closure of `double`, without the constants `drop` selects. -/
def closure (env : Environment) (drop : Name → Bool) : List (Name × ConstantInfo) :=
  (Ix.EnvScope.collectDeps env [target]).filter fun (n, _) => !drop n

/-- The Lean IO pipeline's failures `(name, reason)`, sorted by name. -/
def leanFailures (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Array (String × String)) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env cs).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := 1) with
  | .error e => throw (IO.userError s!"compileLeanInput: {e}")
  | .ok out =>
    let failures := out.cenv.ungrounded.toArray.map fun (n, m) => (n.pretty, m)
    return failures.qsort fun a b => a.1 < b.1

/-- The Rust compiler's failures `(name, reason)` (fail-closed `ix compile`),
    sorted by name. -/
def rustFailures (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Array (String × String)) := do
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env cs)
  let dir ← IO.FS.createTempDir
  try
    let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared (dir / "rust.ixe").toString false
    return status.ungrounded.qsort fun a b => a.1 < b.1
  finally IO.FS.removeDirAll dir

/-- `instAddNat` references the omitted `Nat.add` (an immediate refusal,
naming it); `double` references `instAddNat` (a transitive one). -/
def expected : Array (String × String) :=
  #[(``instAddNat |>.toString, "UNGROUNDED-INPUT: references Nat.add, which is not in the input"),
    (target.toString, "UNGROUNDED-INPUT: references a constant that is itself ungrounded")]
  |>.qsort fun a b => a.1 < b.1

def suite : List TestSeq := [
  .individualIO "ground refusal: the closed input compiles with no failure, Lean and Rust" none (do
    let env ← get_env!
    let cs := closure env fun _ => false
    let lean ← leanFailures env cs
    let rust ← rustFailures env cs
    let ok := lean.isEmpty && rust.isEmpty
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"lean {lean.toList.take 4}; rust {rust.toList.take 4}")) .done,
  .individualIO "ground refusal: an omitted dependency is refused by name, Lean and Rust" none (do
    let env ← get_env!
    let cs := closure env (· == ``Nat.add)
    let lean ← leanFailures env cs
    let rust ← rustFailures env cs
    let ok := lean == expected && rust == expected
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"lean {lean}; rust {rust}; expected {expected}")) .done]

end Tests.Ix.Compile.GroundRefusal
