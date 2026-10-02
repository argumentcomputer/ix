import Ix.Compile.Verify.Audit.Statements
import Ix.CompileM

/-!
# Compiler-verification and sharing-core source sorry frontier

Fail the build if any declaration emitted from an `Ix.Compile.Verify` or an
`Ix.Sharing` source module (the sharing core, whose `@[csimp]` replacements
the compiler runs) directly references `sorryAx`.  Upstream Lean4Lean debt is
handled by per-root transitive manifests rather than being confused with local
source placeholders.
-/

open Lean Lean.Elab.Command

namespace Ix.Compile.Verify.Audit

private def directConstants : Lean.ConstantInfo → Array Lean.Name
  | .axiomInfo value => value.type.getUsedConstants
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors

/-- The module prefixes whose source declarations must not use `sorryAx`. -/
def sorryFreePrefixes : Array Lean.Name := #[`Ix.Compile.Verify, `Ix.Sharing]

def checkSorryFrontier : CommandElabM Unit := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let offenders := env.constants.toList.filterMap fun (name, info) =>
    match env.getModuleIdxFor? name with
    | none => none
    | some idx =>
      let mod := moduleNames[idx.toNat]!
      if sorryFreePrefixes.any (·.isPrefixOf mod) &&
          (directConstants info).contains ``sorryAx then
        some (mod, name)
      else
        none
  let offenders := offenders.toArray.qsort fun left right =>
    Lean.Name.lt left.1 right.1
  if offenders.isEmpty then
    logInfo m!"Ix.Compile.Verify and Ix.Sharing sorry frontier OK: no source declaration uses sorryAx"
  else
    let body := String.intercalate "\n" <| offenders.toList.map fun (mod, name) =>
      s!"  {mod} :: {name}"
    throwError m!"Ix.Compile.Verify and Ix.Sharing sorry frontier changed — \
      {offenders.size} declaration(s) directly use sorryAx:\n{body}"

run_cmd checkSorryFrontier

end Ix.Compile.Verify.Audit
