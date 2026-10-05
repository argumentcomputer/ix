import IxSharingVerify.Audit.Statements
import Ix.CompileM

/-!
# Sharing source sorry frontier

Fail the build if any declaration emitted from an `Ix.Sharing` source module
(the sharing core `Ix.Sharing.Exact`, whose `@[csimp]` replacements the
compiler runs, and its proofs `Ix.Sharing.Verify`) directly references
`sorryAx`. The per-root manifest (`Audit.Statements`) rejects `sorryAx` in each
root's closure; this check also covers declarations that no root reaches.
-/

open Lean Lean.Elab.Command

namespace Ix.Sharing.Verify.Audit

/-- The module prefixes whose source declarations must not use `sorryAx`. -/
def sorryFreePrefixes : Array Lean.Name := #[`Ix.Sharing, `IxSharingVerify]

def checkSorryFrontier : CommandElabM Unit := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut scanned : Nat := 0
  let mut offenders : Array (Lean.Name × Lean.Name) := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := moduleNames[idx.toNat]!
    unless sorryFreePrefixes.any (·.isPrefixOf mod) do continue
    scanned := scanned + 1
    if (Ix.Kernel.Audit.directConstants info).contains ``sorryAx then
      offenders := offenders.push (mod, name)
  offenders := offenders.qsort fun left right => Lean.Name.lt left.1 right.1
  if offenders.isEmpty then
    logInfo m!"Ix.Sharing sorry frontier OK: none of {scanned} source declarations uses sorryAx"
  else
    let body := String.intercalate "\n" <| offenders.toList.map fun (mod, name) =>
      s!"  {mod} :: {name}"
    throwError m!"Ix.Sharing sorry frontier changed — \
      {offenders.size} declaration(s) directly use sorryAx:\n{body}"

run_cmd checkSorryFrontier

end Ix.Sharing.Verify.Audit
