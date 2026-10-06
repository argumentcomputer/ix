import Ix.CompileCert.Installed

namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

/-- Paired concrete argument values recover the same source formal values
through positional renaming, without requiring ambient assignment equality. -/
theorem UniverseImage.telescope_instances_agree
    {sourceParams targetParams : List Kernel.Name} (sourceUnique : sourceParams.Nodup)
    (targetUnique : targetParams.Nodup) (sameArity : sourceParams.length = targetParams.length)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceParams.length) (targetArity : targetUs.length = targetParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (parameter : Kernel.Name) (member : parameter ∈ sourceParams) :
    (UniverseImage.select sourceParams (targetParams.map Kernel.Level.param)).valuation
      (Kernel.Level.substFn targetLevels targetParams targetUs) parameter =
    Kernel.Level.substFn sourceLevels sourceParams sourceUs parameter := by
  rw [UniverseImage.select_valuation]
  obtain ⟨index, inside, rfl⟩ := List.mem_iff_getElem.mp member
  rw [levelSubst_get _ sourceUnique (by simp [sameArity]) index inside]
  simp only [List.getElem_map, Kernel.Level.eval]
  rw [levelSubst_get _ targetUnique targetArity index (by omega),
    levelSubst_get _ sourceUnique sourceArity index inside]
  have selected := congrArg (fun values : List Nat => values[index]?) arguments
  simpa only [List.getElem?_map, List.getElem?_eq_getElem (show index < sourceUs.length by omega),
    List.getElem?_eq_getElem (show index < targetUs.length by omega), Option.map_some,
    Option.some.injEq] using selected.symm

/-- Semantic level comparison at concrete instances does not demand that
the target syntax be parameter-minimal: irrelevant target parameters may
cancel semantically. The existing source-bound and Geran comparison suffice. -/
theorem checkInstalledMemberSort_instance {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (telescopes : TelescopeAssociation source target names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : source.find? name = some sourceEntry)
    (targetLookup : target.find? (names name) = some targetEntry)
    {sourceSort targetSort : Kernel.Level}
    (checked : checkInstalledMemberExpr source target names name (.sort sourceSort) (.sort targetSort) = some true)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    sourceSort.eval (Kernel.Level.substFn sourceLevels sourceEntry.toConstantVal.levelParams sourceUs) =
      targetSort.eval (Kernel.Level.substFn targetLevels targetEntry.toConstantVal.levelParams targetUs) := by
  obtain ⟨actual, actualLookup, sourceUnique, targetUnique, sameArity⟩ := telescopes name sourceEntry sourceLookup
  rw [targetLookup] at actualLookup
  cases Option.some.inj actualLookup
  simp only [checkInstalledMemberExpr, sourceLookup, targetLookup] at checked
  split at checked
  next bounded =>
    let image := UniverseImage.select sourceEntry.toConstantVal.levelParams
      (targetEntry.toConstantVal.levelParams.map Kernel.Level.param)
    let targetInstance := Kernel.Level.substFn targetLevels targetEntry.toConstantVal.levelParams targetUs
    have compared := Kernel.Level.isEquiv_sound checked targetInstance
    have locality := UniverseImage.telescope_instances_agree sourceUnique targetUnique sameArity
      sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments
    calc
      _ = sourceSort.eval (image.valuation targetInstance) :=
        Kernel.Level.eval_ext bounded (fun p member => (locality p member).symm)
      _ = (image.level sourceSort).eval targetInstance := (image.eval targetInstance sourceSort).symm
      _ = _ := compared
  next => contradiction

end Ix.CompileCert
