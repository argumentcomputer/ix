import Ix.Tc.Verify.Audit.Completed
import Ix.Tc.Verify.Audit.Statements

/-!
# `Ix.Tc.Verify` source sorry frontier

Fail the build if any declaration defined in an `Ix.Tc.Verify` source module
directly uses `sorryAx` — the elaborated form of a `sorry` token in that
source. Reading it from the checked environment means `sorry` tokens in
comments, string/char literals, or nested block comments cannot cause false
positives. Filtering is by SOURCE MODULE via
`getModuleIdxFor?`, not declaration name, so macro-emitted constants registered
under unqualified names are still attributed to their host module. Upstream
(Lean4Lean) `sorryAx` users are excluded because they live outside the
`Ix.Tc.Verify` namespace — the distinction `lake build --wfail` cannot make.

Runs as a `run_cmd` at elaboration, next to the trust manifest it complements
(`Ix.Tc.Verify.Audit.check`): a build-time command, not an executable, so it
never links the Rust FFI archives an exe over these modules would clash on.
Importing the audit roots pulls the verified surface into scope; a declaration
in a Verify module not reachable from those roots is not checked here.
-/

open Lean Lean.Elab.Command

namespace Ix.Tc.Verify.Audit

/-- Constants referenced directly by a declaration's type or value, following
the same cases as `Lean.collectAxioms`. The `Lean.` qualifiers are load-bearing:
the imported Ix kernel defines its own `Name`/`ConstantInfo` that shadow Lean's
inside this namespace. -/
private def sorryFrontierDirectConstants : Lean.ConstantInfo → Array Lean.Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

/-- Fail if any `Ix.Tc.Verify` source declaration directly references `sorryAx`. -/
def checkSorryFrontier : CommandElabM Unit := do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let offenders := env.constants.toList.filterMap fun (name, info) =>
    match env.getModuleIdxFor? name with
    | none => none
    | some idx =>
      let mod := moduleNames[idx.toNat]!
      if (`Ix.Tc.Verify).isPrefixOf mod && (sorryFrontierDirectConstants info).contains ``sorryAx then some (mod, name) else none
  let offenders := offenders.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1)
  if offenders.isEmpty then
    logInfo m!"Ix.Tc.Verify sorry frontier OK: no source declaration uses sorryAx"
  else
    let body := String.intercalate "\n"
      (offenders.toList.map fun (mod, name) => s!"  {mod} :: {name}")
    throwError m!"Ix.Tc.Verify sorry frontier changed — {offenders.size} declaration(s) directly use sorryAx:\n{body}\nResolve the sorry, or extend the Ix.Tc.Verify.Audit trust manifest, only when the verification frontier intentionally changes."

run_cmd checkSorryFrontier

end Ix.Tc.Verify.Audit
