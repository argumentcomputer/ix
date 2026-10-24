/-
  The compile's record of ungrounded input (part of `ground-unit`; the
  adversarial matrix's row 11): a constant whose value dependency is left
  out of the input is refused by name in both compilers and in the pure
  compile (`Ix.Cert.compileReport`), with the named refusal
  `UNGROUNDED-INPUT: …` (`Ix.GroundError.refusal`, Rust `ground::refusal`,
  the same text), and never dropped silently; the closed input compiles with
  no failure. `ix compile-lean` exits nonzero on any recorded failure unless
  `--allow-partial` (`Ix.Cli.CompileLeanCmd`), and `Ix.Cert.compileComplete`
  fails on any, so both are fail-closed on ungrounded input.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.Cert.Compile
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

/-- The pure compile's report on the prepared constants (`Ix.Cert.compileReport`). -/
def pureReport (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Ixon.Env × Ix.Cert.Failures) := do
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env cs)
  let consts := (Ix.CanonM.canonChunk prepared.toArray).foldl (fun m (n, c) => m.insert n c) {}
  let ixEnv : Ix.Environment := { consts }
  IO.ofExcept (Ix.Cert.compileReport ixEnv)

/-- `Ix.Cert.compileReport`'s failures `(name, reason)`, sorted by name. -/
def pureFailures (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Array (String × String)) := do
  let (_, failures) ← pureReport env cs
  let all := failures.toMap.toArray.map fun (n, m) => (n.pretty, m)
  return all.qsort fun a b => a.1 < b.1

/-- `Ix.Cert.compileComplete` on the prepared constants: the error, if any. -/
def completeError? (env : Environment) (cs : List (Name × ConstantInfo)) : IO (Option String) := do
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env cs)
  let consts := (Ix.CanonM.canonChunk prepared.toArray).foldl (fun m (n, c) => m.insert n c) {}
  let ixEnv : Ix.Environment := { consts }
  return match Ix.Cert.compileComplete ixEnv with
    | .ok _ => none
    | .error e => some e

/-- `instAddNat` references the omitted `Nat.add` (an immediate refusal,
naming it); `double` references `instAddNat` (a transitive one). -/
def expected : Array (String × String) :=
  #[(``instAddNat |>.toString, "UNGROUNDED-INPUT: references Nat.add, which is not in the input"),
    (target.toString, "UNGROUNDED-INPUT: references a constant that is itself ungrounded")]
  |>.qsort fun a b => a.1 < b.1

def suite : List TestSeq := [
  .individualIO "ground refusal: the closed input compiles with no failure, Lean, Rust and the pure compile" none (do
    let env ← get_env!
    let cs := closure env fun _ => false
    let lean ← leanFailures env cs
    let rust ← rustFailures env cs
    let pure ← pureFailures env cs
    let complete ← completeError? env cs
    let ok := lean.isEmpty && rust.isEmpty && pure.isEmpty && complete.isNone
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"lean {lean.toList.take 4}; rust {rust.toList.take 4}; \
        pure {pure.toList.take 4}; compileComplete {complete}")) .done,
  .individualIO "ground refusal: an omitted dependency is refused by name, Lean, Rust and the pure compile" none (do
    let env ← get_env!
    let cs := closure env (· == ``Nat.add)
    let lean ← leanFailures env cs
    let rust ← rustFailures env cs
    let pure ← pureFailures env cs
    let ok := lean == expected && rust == expected && pure == expected
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"lean {lean}; rust {rust}; pure {pure}; expected {expected}")) .done,
  .individualIO "ground refusal: the pure compile's report keeps the grounded rest, and compileComplete refuses" none (do
    let env ← get_env!
    let cs := closure env (· == ``Nat.add)
    let (ixe, failures) ← pureReport env cs
    let complete ← completeError? env cs
    -- the failures are the ground filter's, none a block's; the rest is published
    let published := cs.filter fun (n, _) =>
      n != ``Nat.add && !(expected.any (·.1 == n.toString))
    let missing := published.filter fun (n, _) => !ixe.named.contains (Ix.Name.fromLeanName n)
    let least := expected.foldl (init := expected[0]!) fun k f =>
      if Ix.nameCompare (Ix.Name.fromLeanName f.1.toName) (Ix.Name.fromLeanName k.1.toName) == .lt
      then f else k
    let ok := failures.blocks.isEmpty && failures.ungrounded.size == 2 && missing.isEmpty &&
      complete == some s!"2 constant(s) failed to compile; {least.1}: {least.2}"
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"blocks {failures.blocks.toList.take 4}; \
        unpublished {(missing.map (·.1)).take 4}; compileComplete {complete}")) .done]

end Tests.Ix.Compile.GroundRefusal
