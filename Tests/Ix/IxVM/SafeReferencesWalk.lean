import IxVM
import Aiur.Artifact

/-! Export helper for `Tests.Ix.IxVM.SafeReferences.runUnsafeOrigins`.
Kept separate from `Tests.Ix.IxVM.SafeReferences` so `IxTests` does not import
the formal `IxVM` / `Aiur` proof packages (and therefore Mathlib). -/

namespace Tests.Ix.IxVM.SafeReferencesWalk

/-- Export a compiled package for the direct-walk preservation controls. The generic
`ixvm export` command writes an execution package, which the multi-case test host cannot use. -/
def exportWalkArtifact : IO UInt32 := do
  let some path ← IO.getEnv "IX_AIUR_WALK_ARTIFACT"
    | throw (IO.userError "IX_AIUR_WALK_ARTIFACT must name the output path")
  IO.eprintln s!"IxVM program {_root_.IxVM.programDigest}"
  let exported ← IO.ofExcept (_root_.IxVM.source.exportExecution ["IxVM::verify_transitive"])
  Aiur.Artifact.write path (← IO.ofExcept (Aiur.Artifact.package exported _root_.IxVM.modulus ZMod.val))
  IO.eprintln s!"Wrote compiled walk package {path}"
  return 0

end Tests.Ix.IxVM.SafeReferencesWalk
