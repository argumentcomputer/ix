/-
  The Lean sources of the `compiler-selected-admission` suite
  (`Tests.Ix.Compile.SelectedAdmission`): the root of the
  `SelectedAdmissionFixtures` library (`lakefile.lean`), which `IxTests`
  needs.

  `IxTests` does not import this module. The suite loads it at run time
  through `getCompileEnv`, with `Tests.Ix.Kernel.EntryCaseDefs`, the certified
  entry's host cases, which the same library builds. Those cases include
  declarations installed unchecked on purpose, so they stay out of the
  environment that the whole-environment suites read with `get_env!`.
-/
import Lean.Elab.Command

namespace Tests.Ix.Compile.SelectedAdmission

/-- The candidate-value controls' target: an ordinary monomorphic
definition, against which a distinct well-typed value is checked. -/
def candidateTarget : Nat := 7

/-- A nested structure with a proof field: its primitive projection
`TheoremBox.witness` is a theorem. -/
structure TheoremBox where
  witness : True
  kids : List TheoremBox

/- `theoremProjection`: a theorem whose value is the projection's own value,
which the reader rewrites as a projection. -/
run_cmd do
  let some (.thmInfo d) := (← Lean.getEnv).find? `Tests.Ix.Compile.SelectedAdmission.TheoremBox.witness
    | throwError "primitive projection theorem missing"
  Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl
    { name := `Tests.Ix.Compile.SelectedAdmission.theoremProjection,
      levelParams := d.levelParams, type := d.type, value := d.value })

end Tests.Ix.Compile.SelectedAdmission
