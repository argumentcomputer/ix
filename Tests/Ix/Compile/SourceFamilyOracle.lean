import Tests.Ix.Compile.Twins

namespace Tests.Ix.Compile.SourceFamilyOracle

/-- Prepare one fixed provider over an explicitly enumerated test input.
The lookup may be lazy or altered; the condensation reads that same view. -/
def forInput (source : _root_.Ix.Environment) (names : Array _root_.Ix.Name) :
    _root_.Ix.AuxGen.SourceFamilyOracle :=
  let domain : Std.HashSet _root_.Ix.Name := names.foldl (·.insert ·) {}
  let get? n := if domain.contains n then source.get? n else none
  let refs := names.foldl (init := {}) fun refs n =>
    match source.get? n with
    | none => refs
    | some ci => refs.insert n (_root_.Ix.GraphM.run { consts := {} } .init (_root_.Ix.graphConst ci)).1
  let blocks := _root_.Ix.CondenseM.run refs
  let levels := _root_.Ix.CompileM.scheduleLevels blocks (_root_.Ix.CompileM.FoldSchedule.of blocks)
  let ra := _root_.Ix.AuxGen.Source.RunAhead.start get? blocks levels .recursors
  _root_.Ix.CompileM.sourceFamilyProvider get? blocks ra

/-- A library fixture's finite source closure, including its supplied recursors.
Call once when preparing that fixture view, and reuse it for all its queries. -/
def forLean (env : Lean.Environment) (source : _root_.Ix.Environment)
    (seeds : Array _root_.Ix.Name) : _root_.Ix.AuxGen.SourceFamilyOracle :=
  let closure := Twins.closeWithRecursors env
    (_root_.Ix.EnvScope.collectDeps env (seeds.toList.map ClosureHarness.toLeanName))
  forInput source (closure.toArray.map fun (n, _) => _root_.Ix.Name.fromLeanName n)

end Tests.Ix.Compile.SourceFamilyOracle
