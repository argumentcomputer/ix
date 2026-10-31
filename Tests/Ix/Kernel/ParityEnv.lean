module

-- Private imports: `ensureSelected` returns only `IO FilePath`; these provide
-- only its implementation. `Ix.Meta` re-exports `getFileEnv` and `Ix.CompileM`
-- (`rsCompileEnvBytesFFI`). The transitive dep closure comes from the shared
-- `Ix.EnvScope.collectDeps` (namespaced, so it can meet the same-named
-- top-level def in `Tests.Ix.Compile.ValidateAux` inside `Tests.Main`).
import Ix.Meta
import Ix.EnvScope
import Ix.Cli.ConstsFile

/-!
Selected fixture for the IxC regression pins (`tc-pins`):
the serialized `.ixe` env they check against. Compiled on demand from `Ix.lean`
plus the checked-in seed list when the file isn't already present, so the tests
run unconditionally instead of skipping when no fixture is supplied.
-/

namespace Tests.Tc.ParityEnv

open Lean

/-- The format version in the `.ixe` header at `path`, or `none` when the file
does not start with an env header. -/
def headerVersion? (path : System.FilePath) : IO (Option UInt64) := do
  let head ← (← IO.FS.Handle.mk path .read).read 16
  return match Ixon.runGet (Ixon.getTagN 4) head with
    | .ok tag => if tag.flag == Ixon.Env.FLAG then some tag.value else none
    | .error _ => none

/-- Path to the parity `.ixe`, compiling it from the seed closure if absent or
written under an unsupported `.ixe` envelope version. Both v4 and v5 caches
are readable and do not need a fresh corpus compilation.
`buildFile` first: the test suite only builds what `IxTests` needs, not the rest
of `Ix.lean`'s closure (e.g. the benchmarks it also imports), and `getFileEnv`
needs every olean present. Then it loads the env and hands the transitive seed
closure to the same FFI compile step `ix compile` uses. A seed that no longer
resolves is a hard error, not a skip. -/
public def ensureSelected : IO System.FilePath := do
  let out : System.FilePath := "tc-pins-ixc-v1.ixe"
  let constsFile := ".github/fixtures/tc-parity-consts.txt"
  if ← out.pathExists then
    match ← headerVersion? out with
    | some version =>
      if Ixon.Env.supportedEnvelopeVersion version then return out
      IO.println s!"tc-parity: {out} has unsupported .ixe envelope version {version}, expected \
        4 or 5 — recompiling from {constsFile}"
    | none =>
      IO.println s!"tc-parity: {out} has no .ixe header — recompiling from {constsFile}"
  else
    IO.println s!"tc-parity: {out} not found — compiling from {constsFile}"
  buildFile "Ix.lean"
  let leanEnv ← getFileEnv "Ix.lean"
  let raw ← Ix.Cli.ConstsFile.read constsFile
  let mut seeds : List Name := []
  for s in raw do
    let name := s.toName
    if leanEnv.constants.contains name then
      seeds := name :: seeds
    else
      throw <| IO.userError s!"tc-parity: seed constant not found in Ix.lean env: {s}"
  let closed := Ix.EnvScope.collectSelectedDeps leanEnv seeds
  -- Fail-closed (`allowPartial := false`): with `getFileEnv` always
  -- full-content, every referenced constant — `_private.*` proof auxiliaries
  -- included — must ground; a silent drop here is exactly how the
  -- exported-level trim regression hid until the tc gates fired.
  let status ← Ix.CompileM.rsCompileEnvBytesFFI closed out.toString false
  if !status.ungrounded.isEmpty then
    throw (IO.userError s!"tc-pins: selected fixture compilation refused {status.ungrounded.size} constants")
  return out

end Tests.Tc.ParityEnv
