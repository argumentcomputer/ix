/-
  `getFileEnv` module-header tests: environments handed to the compiler must
  be FULL-CONTENT regardless of the header's mode, and the `module` mode must
  be honored as scoping, not content.

  An `OLeanLevel.exported` import (what module-mode header processing yields)
  loads every imported public theorem as a body-less axiom and omits
  non-exported `_private.*` constants entirely. Compiling such an env
  axiomizes imported proofs: kernel checks pass vacuously and every address
  drifts from private-level compiles of the same constants (this regressed
  once as the `tc-pins`/`tc-accel-diff` failures). So:

  - `getFileEnvCore` always imports at the classic (private) level and
    reports the header's `module` bit alongside the env;
  - `moduleVisibleNames` exposes the exported-level NAME set for scoping;
  - `defaultConstList` seeds module-mode compiles from that surface, closing
    over the full-content env so referenced private proof auxiliaries come
    along while unreferenced foreign privates stay out.
-/
module

public import LSpec
public import Ix.Meta
public import Ix.EnvScope

public section

open LSpec
open System (FilePath)
open Ix.EnvScope

namespace Tests.Ix.MetaEnv

private def isPrivateName (n : Lean.Name) : Bool :=
  (`_private).isPrefixOf n

private def constKind : Lean.ConstantInfo → String
  | .axiomInfo _ => "an axiom" | .thmInfo _ => "a theorem"
  | .defnInfo _ => "a definition" | .opaqueInfo _ => "an opaque"
  | .inductInfo _ => "an inductive" | .ctorInfo _ => "a constructor"
  | .recInfo _ => "a recursor" | .quotInfo _ => "a quotient primitive"

/-- Load a tmpdir fixture with `getFileEnvCore` and run `check` on the result
(the fixture file is gone by the time the TestSeq is folded, so checks run
eagerly here). -/
private def withFixture (name source : String)
    (check : FilePath → FileEnv → IO (Bool × Option String))
    : IO (Bool × Nat × Nat × Option String) := do
  let dir ← IO.FS.createTempDir
  let path := dir / name
  IO.FS.writeFile path source
  try
    let fe ← getFileEnvCore path
    let (ok, err?) ← check path fe
    return (ok, 0, 0, err?)
  catch e =>
    return (false, 0, 0, some s!"getFileEnvCore failed: {e}")
  finally
    IO.FS.removeDirAll dir

private def moduleSource : String :=
  "module\n\npublic def TestsMetaEnv.modMarker : Nat := 7\n"

private def classicSource : String :=
  "def TestsMetaEnv.classicMarker : Nat := 3\n"

/-- Full-content check shared by both header modes: the file's own marker is
present, and an imported theorem (`Nat.add_comm`, from the implicit `Init`
import) is a THEOREM whose proof body's references all resolve in the same
env — in a trimmed (exported-level) env it is a body-less axiom and its
private proof auxiliaries are absent. -/
private def checkFullContent (env : Lean.Environment) (marker : Lean.Name)
    : Option String := Id.run do
  if !env.contains marker then
    return some s!"marker {marker} missing from env"
  match env.constants.find? `Nat.add_comm with
  | some (.thmInfo v) =>
    for r in v.value.getUsedConstants do
      if !env.contains r then
        return some s!"Nat.add_comm proof ref {r} dangling — env is not closed"
    none
  | some ci => some s!"Nat.add_comm is {constKind ci}, expected a theorem with a proof"
  | none => some "Nat.add_comm missing from env"

def moduleFileTest : TestSeq :=
  .individualIO "module header: full content + isModule flag" none
    (withFixture "ModFixture.lean" moduleSource fun _ fe => do
      if !fe.isModule then
        return (false, some "isModule = false for a `module` header")
      -- The env must also carry private transitive imports (absent entirely
      -- at exported level).
      let privCount := fe.env.constants.toList.countP fun (n, _) => isPrivateName n
      if privCount == 0 then
        return (false, some "no _private.* constants — exported-level trim suspected")
      match checkFullContent fe.env `TestsMetaEnv.modMarker with
      | some e => return (false, some e)
      | none => return (true, none)) .done

def classicFileTest : TestSeq :=
  .individualIO "classic header: full content + isModule flag" none
    (withFixture "ClassicFixture.lean" classicSource fun _ fe => do
      if fe.isModule then
        return (false, some "isModule = true for a classic header")
      match checkFullContent fe.env `TestsMetaEnv.classicMarker with
      | some e => return (false, some e)
      | none => return (true, none)) .done

/-- Scoping: `defaultConstList` on a module-mode file must (a) keep the file's
own definitions, (b) keep module-visible imports, (c) pull in referenced
`_private.*` proof auxiliaries through the closure — with their full-content
`ConstantInfo`s (theorems stay theorems) — and (d) still exclude some of the
full env (the unreferenced foreign privates the `module` header conceals). -/
def scopedListTest : TestSeq :=
  .individualIO "module header: defaultConstList scopes names, not content" none
    (withFixture "ScopeFixture.lean" moduleSource fun path fe => do
      let closed ← defaultConstList fe path.toString
      let full := fe.env.constants.toList.length
      let names : Std.HashSet Lean.Name := .ofList (closed.map (·.1))
      if !names.contains `TestsMetaEnv.modMarker then
        return (false, some "local definition missing from scoped list")
      let addComm := closed.find? fun (n, _) => n == `Nat.add_comm
      match addComm with
      | some (_, .thmInfo _) => pure ()
      | some (_, ci) =>
        return (false, some s!"scoped Nat.add_comm is {constKind ci}, expected a theorem")
      | none => return (false, some "Nat.add_comm missing from scoped list")
      let privCount := closed.countP fun (n, _) => isPrivateName n
      if privCount == 0 then
        return (false, some "closure pulled in no _private.* proof auxiliaries")
      if closed.length ≥ full then
        return (false, some s!"scoped list ({closed.length}) does not exclude \
anything from the full env ({full})")
      return (true, none)) .done

def suite : List TestSeq := [moduleFileTest, classicFileTest, scopedListTest]

end Tests.Ix.MetaEnv
