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

/-- Planted run-ahead failures must survive preparation and repeated reads. -/
def cacheControls (source : _root_.Ix.Environment) (all : Array _root_.Ix.Name) : IO Unit := do
  let members : _root_.Ix.Set _root_.Ix.Name := all.foldl (·.insert ·) {}
  let key := _root_.Ix.CompileM.canonicalKey .mkAnon all
  let some owner := all.find? (· != key) | throw (IO.userError "owner/key distinction untested")
  let rep := owner.mkStr "_test_tarjan_rep"
  let blocks : _root_.Ix.CondensedBlocks := {
    lowLinks := all.foldl (fun m n => m.insert n rep) {},
    blocks := ({} : _root_.Ix.Map _root_.Ix.Name (_root_.Ix.Set _root_.Ix.Name)).insert rep members,
    blockRefs := ({} : _root_.Ix.Map _root_.Ix.Name (_root_.Ix.Set _root_.Ix.Name)).insert rep {} }
  let runs (service : Except String _root_.Ix.AuxGen.Source.Service) : _root_.Ix.AuxGen.Source.RunAhead := {
    levels := #[Task.pure { service }, Task.pure { service }]
    levelOf := ({} : Std.HashMap _root_.Ix.AuxGen.Flat.NameKey
      (Nat × _root_.Ix.Set _root_.Ix.Name)).insert ⟨key⟩ (0, members) }
  let check (provider : _root_.Ix.AuxGen.SourceFamilyOracle) (why : String) : IO Unit :=
    match provider owner with
    | .error actual => unless actual == s!"source family {owner.pretty}: {why}" do
        throw (IO.userError s!"wrong cached failure: {actual}")
    | .ok _ => throw (IO.userError s!"cached failure accepted: {why}")
  let failed := runs (.error "planted snapshot failure")
  let provider := _root_.Ix.CompileM.sourceFamilyProvider source.get? blocks failed
  for _ in [:2] do check provider "planted snapshot failure"
  check (_root_.Ix.CompileM.sourceFamilyProvider source.get? blocks { failed with levels := #[] })
    s!"scheduled Source task absent for {key.pretty}"
  check (_root_.Ix.CompileM.sourceFamilyProvider source.get? blocks { failed with levelOf := {} })
    s!"scheduled members differ at {key.pretty}"
  let missing : _root_.Ix.AuxGen.Source.Service := {
    input := default, reader := {}, env := {},
    groupOf := all.foldl (fun m n => m.insert ⟨n⟩ 0) {} }
  check (_root_.Ix.CompileM.sourceFamilyProvider source.get? blocks (runs (.ok missing)))
    s!"Source status absent for {all[0]!.pretty}"
  let pending := { missing with entries := #[{ names := all, group := none, reading := .folded }] }
  check (_root_.Ix.CompileM.sourceFamilyProvider source.get? blocks (runs (.ok pending)))
    s!"Source status pending for {all[0]!.pretty}"
  IO.println "[aux-source-family] 6 cache failures; owner, Tarjan representative and schedule key distinct"

end Tests.Ix.Compile.SourceFamilyOracle
