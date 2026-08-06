module

-- Private imports: `ensure`'s signature is just `IO FilePath`; these provide
-- only its implementation. `Ix.Meta` re-exports `getFileEnv` and `Ix.CompileM`
-- (`rsCompileEnvBytesFFI`). The transitive dep closure is inlined below rather
-- than taken from `Ix.Cli.ValidateCmd`, whose top-level `collectDeps` collides
-- with the same-named def in `Tests.Ix.Compile.ValidateAux` once both reach
-- Main.
import Ix.Meta
import Ix.Cli.ConstsFile

/-!
Shared fixture for the typechecker parity tests (`tc-pins`, `tc-accel-diff`):
the serialized `.ixe` env they check against. Compiled on demand from `Ix.lean`
plus the checked-in seed list when the file isn't already present, so the tests
run unconditionally instead of skipping when no fixture is supplied.
-/

namespace Tests.Tc.ParityEnv

open Lean

/-- Transitive dependency closure of `seeds` in `env` — the constants a compiled
`.ixe` must contain. Mirrors `Ix.Cli.ValidateCmd.collectDeps`. -/
private partial def depClosure (env : Environment) (seeds : List Name)
    : List (Name × ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .inductInfo v =>
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- Path to the parity `.ixe`, compiling it from the seed closure if absent.
`buildFile` first: the test suite only builds what `IxTests` needs, not the rest
of `Ix.lean`'s closure (e.g. the benchmarks it also imports), and `getFileEnv`
needs every olean present. Then it loads the env and hands the transitive seed
closure to the same FFI compile step `ix compile` uses. A seed that no longer
resolves is a hard error, not a skip. -/
public def ensure : IO System.FilePath := do
  let out : System.FilePath := "tc-parity.ixe"
  if ← out.pathExists then return out
  let constsFile := ".github/fixtures/tc-parity-consts.txt"
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
  let closed := depClosure leanEnv seeds
  let _ ← Ix.CompileM.rsCompileEnvBytesFFI closed out.toString
  return out

end Tests.Tc.ParityEnv
