import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Ix.CompileCertified
import Ix.CompileM
import Ix.Cert.Compile
import Ix.Ixon
import LSpec

/-!
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

/-- The certified IO pipeline's failures `(name, reason)`, sorted by name.
Without binder data: the closures here are the raw ones, without recursors, on
which the annotator's install refuses the compile; grounding is the subject.
Worker-count independence is formally proved (`compileEnvFold_width`), so one
certified run suffices alongside the pure compile. -/
def certifiedFailures (env : Environment) (cs : List (Name × ConstantInfo)) :
    IO (Array (String × String)) := do
  let out ← IO.ofExcept (← Ix.CompileM.compileCertified env cs (binderData := false))
  let failures := out.failures.toMap.toArray.map fun (n, m) => (n.pretty, m)
  return failures.qsort fun a b => a.1 < b.1

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

/-- Structured-status compilation tests (moved from `Tests.FFI.CompileStatus`
    since they exercise pure-Lean certified compilation and atomic writes rather
    than Rust FFI): fail-closed writes nothing when a constant is ungrounded,
    while allow-partial serializes the grounded subset as a reloadable artifact. -/
private def statusGoodName : Lean.Name := `TestsCompileStatus.good
private def statusBadName : Lean.Name := `TestsCompileStatus.bad

private def statusGoodAx : Lean.ConstantInfo := .axiomInfo {
  name := statusGoodName, levelParams := [], type := .sort .zero
  isUnsafe := false }

private def statusBadAx : Lean.ConstantInfo := .axiomInfo {
  name := statusBadName, levelParams := []
  type := .const `TestsCompileStatus.doesNotExist []
  isUnsafe := false }

private def statusConsts : List (Lean.Name × Lean.ConstantInfo) :=
  [(statusGoodName, statusGoodAx), (statusBadName, statusBadAx)]

private def compileEnvBytes (cs : List (Lean.Name × Lean.ConstantInfo))
    (path : String) (allowPartial : Bool) : IO Ix.CompileM.CompileEnvStatus := do
  let out ← IO.ofExcept (← Ix.CompileM.compileCertifiedPrepared cs false)
  let status := { Ix.Cli.statusOf out.env out.failures.toMap with
    named := out.env.named.size.toUInt64
    uniqueAnon := out.env.consts.size.toUInt64 }
  if !allowPartial && !status.ungrounded.isEmpty then
    return status
  let bytes ← IO.ofExcept (Ixon.serEnv out.env)
  Ix.RoleBinding.Compile.writeAtomic (System.FilePath.mk path) bytes
  return { status with bytes := bytes.size.toUInt64 }

def failClosedStatusTest : TestSeq :=
  .individualIO "compileEnvBytes fail-closed: ungrounded ⇒ no artifact" none (do
    let dir ← IO.FS.createTempDir
    let out := dir / "fail-closed.ixe"
    let status ← compileEnvBytes statusConsts out.toString false
    let outExists ← out.pathExists
    let tmpExists ← (dir / "fail-closed.ixe.tmp").pathExists
    IO.FS.removeDirAll dir
    let checks : List (String × Bool) :=
      [ ("no output file", !outExists)
      , ("no .tmp left behind", !tmpExists)
      , ("bytes == 0", status.bytes == 0)
      , ("one ungrounded entry", status.ungrounded.size == 1)
      , ("ungrounded names the bad axiom",
          status.ungrounded[0]?.map (·.1) == some statusBadName.toString)
      , ("root is 64 hex chars", status.root.length == 64) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  ) .done

def allowPartialStatusTest : TestSeq :=
  .individualIO "compileEnvBytes allow-partial: grounded subset reloads" none (do
    let dir ← IO.FS.createTempDir
    let out := dir / "partial.ixe"
    let status ← compileEnvBytes statusConsts out.toString true
    let bytes ← IO.FS.readBinFile out
    IO.FS.removeDirAll dir
    let env ← match Ixon.deEnv bytes with
      | .ok env => pure env
      | .error e => return (false, 0, 0, some s!"reload failed: {e}")
    let checks : List (String × Bool) :=
      [ ("bytes matches file size", status.bytes.toNat == bytes.size)
      , ("one ungrounded entry", status.ungrounded.size == 1)
      , ("grounded axiom is named in the reloaded env",
          env.named.size == status.named.toNat && status.named ≥ 1)
      , ("bad axiom is absent from the reloaded env",
          env.named.size < statusConsts.length + 1) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)
  ) .done

def suite : List TestSeq := [
  .individualIO "ground refusal: the closed input compiles with no failure, certified IO and pure compile" none (do
    let env ← get_env!
    let cs := closure env fun _ => false
    let cert ← certifiedFailures env cs
    let pure ← pureFailures env cs
    let complete ← completeError? env cs
    let ok := cert.isEmpty && pure.isEmpty && complete.isNone
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"certified {cert.toList.take 4}; \
        pure {pure.toList.take 4}; compileComplete {complete}")) .done,
  .individualIO "ground refusal: an omitted dependency is refused by name, certified IO and pure compile" none (do
    let env ← get_env!
    let cs := closure env (· == ``Nat.add)
    let cert ← certifiedFailures env cs
    let pure ← pureFailures env cs
    let ok := cert == expected && pure == expected
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some s!"certified {cert}; pure {pure}; expected {expected}")) .done,
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
        unpublished {(missing.map (·.1)).take 4}; compileComplete {complete}")) .done,
  failClosedStatusTest,
  allowPartialStatusTest]

end Tests.Ix.Compile.GroundRefusal
