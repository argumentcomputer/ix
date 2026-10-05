import Ix.CompileCert.AnnotEntry

/-! Same-carrier assembly for the remaining strong-model laws. In particular,
the actual instantiated source type and target type share one annotated
reading; no erased-denotation equality is substituted for grading. -/
namespace Ix.CompileCert
open Kernel.Model Kernel.Semantics

theorem AnnotatedAssociation.instantiated_type {V : Type u} [Kernel.SetTheory V]
    {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (checked : AnnotatedAssociation source target names)
    (sourceFacts : EnvModel V source) (targetModel : StrongInstalledModel V target)
    (entry : Kernel.ConstantInfo) (present : entry ∈ source.consts)
    (levels : Kernel.Name → Nat) (universes : List Kernel.Level) :
    ∃ targetEntry, target.find? (names entry.name) = some targetEntry ∧
    ∃ annotation,
      denoteMeta (checked.modelCore sourceFacts targetModel).base.acval source levels 0
        (entry.toConstantVal.type.instantiateLevelParams entry.toConstantVal.levelParams universes) =
          some annotation ∧
      denoteMeta targetModel.internal.base2.acval target
        ((PullbackMap.fromEnvs source target names).levels entry.name
          (Kernel.Level.substFn levels entry.toConstantVal.levelParams universes)) 0
        targetEntry.toConstantVal.type = some annotation ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ annotation := by
  obtain ⟨lookup, targetEntry, targetLookup, comparison⟩ :=
    checkInstalledTypes_member checked.installed.types present
  obtain ⟨annotation, reading⟩ := targetModel.internal.type_reads targetEntry
    (Kernel.Semantics.Env.find?_mem targetLookup)
    ((PullbackMap.fromEnvs source target names).levels entry.name
      (Kernel.Level.substFn levels entry.toConstantVal.levelParams universes))
  refine ⟨targetEntry, targetLookup, annotation, ?_, reading, ?_⟩
  · rw [denotePInstLevels]
    exact (checkInstalledMemberExpr_annotated_reading_local targetModel
      (checkTelescopes_sound checked.installed.telescopes) lookup
      (List.all_eq_true.mp checked.types entry present) comparison _ 0).trans reading
  · exact targetModel.internal.type_wellDenotedV targetEntry
      (Kernel.Semantics.Env.find?_mem targetLookup) _ annotation reading

end Ix.CompileCert
