import Tests.Ix.CompileCert.Direct
import Tests.Ix.CompileCert.Blocks
import Tests.Ix.CompileCert.Compiled
import Tests.Ix.CompileCert.Stored
import Tests.Ix.CompileCert.Groups
import Tests.Ix.CompileCert.Universes
import Tests.Ix.CompileCert.Expressions
import Tests.Ix.CompileCert.SourceInstall
import Tests.Ix.CompileCert.SourceModels
import Tests.Ix.CompileCert.ProjectionSupport
import Tests.Ix.CompileCert.Indexed
import Tests.Ix.CompileCert.ProjectionLowering
import Tests.Ix.CompileCert.Strong
import Tests.Ix.CompileCert.Changed
import Tests.Ix.CompileCert.Sharing
import Tests.Ix.CompileCert.StrongPins
import Tests.Ix.CompileCert.StrongPlan
import Tests.Ix.CompileCert.StrongChanged
import Tests.Ix.CompileCert.StrongIndexed
import Tests.Ix.CompileCert.StrongGlobal

/-- Standalone remote driver; shared test registration belongs to the
coordinator. Production/test library modules do not define a global main. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["direct"] => Tests.Ix.CompileCert.Direct.run
  | ["blocks"] => Tests.Ix.CompileCert.Blocks.run
  | ["groups"] => Tests.Ix.CompileCert.Groups.run
  | ["universes"] => Tests.Ix.CompileCert.Universes.run
  | ["expressions"] => Tests.Ix.CompileCert.Expressions.run
  | ["source-install"] => Tests.Ix.CompileCert.SourceInstall.run
  | ["source-models"] => Tests.Ix.CompileCert.SourceModels.run
  | ["source-normalized"] => Tests.Ix.CompileCert.SourceModels.runNormalized
  | ["source-coverage"] => Tests.Ix.CompileCert.SourceModels.runCoverage
  | ["source-projection-semantics"] => Tests.Ix.CompileCert.SourceModels.runProjectionSemantics
  | ["projection-support", path] => Tests.Ix.CompileCert.ProjectionSupport.run path
  | ["compiled"] => Tests.Ix.CompileCert.Compiled.run
  | ["indexed"] => Tests.Ix.CompileCert.Indexed.run
  | ["projection-lowering"] => Tests.Ix.CompileCert.ProjectionLowering.run
  | ["strong"] => Tests.Ix.CompileCert.Strong.run
  | ["changed"] => Tests.Ix.CompileCert.Changed.run
  | "changed-probe" :: args => Tests.Ix.CompileCert.Changed.probe args
  | ["sharing"] => Tests.Ix.CompileCert.Sharing.run
  | ["strong-pins"] => Tests.Ix.CompileCert.StrongPins.run
  | ["strong-plan", dir] => Tests.Ix.CompileCert.StrongPlan.run dir
  | ["strong-changed", ixe, dir] => Tests.Ix.CompileCert.StrongChanged.run ixe dir
  | ["strong-indexed"] => Tests.Ix.CompileCert.StrongIndexed.run
  | ["strong-global", compiled, changed, dir] => Tests.Ix.CompileCert.StrongGlobal.run compiled changed dir
  | ["stored", path] => Tests.Ix.CompileCert.Stored.run path
  | [] =>
    Tests.Ix.CompileCert.Direct.run
    Tests.Ix.CompileCert.Blocks.run
    Tests.Ix.CompileCert.Groups.run
    Tests.Ix.CompileCert.Universes.run
    Tests.Ix.CompileCert.Expressions.run
  | _ => throw (IO.userError "expected direct, blocks, compiled, or stored PATH selector")
