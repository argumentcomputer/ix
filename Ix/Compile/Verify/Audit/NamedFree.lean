import Ix.Compile.Verify.Statements

/-!
# Named-specification import quarantine

The compiler proofs target the set model.  Fail the build if the import
closure of the public compiler-verification frontier contains any module
under `Ix.Theory.Named`.

This check lives apart from `Audit.Statements` because the shared axiom-audit
mechanism (`Ix.Kernel.Verify.Audit.Basic`) still imports the Ix-authored
helper `Ix.Theory.Named.Std.AxiomAudit`; that helper is scheduled to leave the
named tree (plan WP-N stage 0), after which this check can move into the
statement audit.
-/

open Lean Lean.Elab.Command

namespace Ix.Compile.Verify.Audit

def checkNamedFree : CommandElabM Unit := do
  let env ← getEnv
  let offenders := env.allImportedModuleNames.filter fun name =>
    (`Ix.Theory.Named).isPrefixOf name
  if offenders.isEmpty then
    logInfo m!"Ix.Compile.Verify imports no module under Ix.Theory.Named"
  else
    let body := String.intercalate "\n" <| offenders.toList.map fun name =>
      s!"  {name}"
    throwError m!"Ix.Compile.Verify reaches the retired named specification — \
      {offenders.size} module(s) under Ix.Theory.Named are imported:\n{body}"

run_cmd checkNamedFree

end Ix.Compile.Verify.Audit
