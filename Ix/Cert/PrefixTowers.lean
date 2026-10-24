import Ix.Cert.PrefixRecRules

/-! # Projection tables at the fixed final interpretation

Actual prefix projection discipline supplies the former and constructor.
Their headers and the exact dummy telescope over the stored body resolve
in that prefix, giving reading equations at arbitrary fixed acval.
-/

namespace Ix.Cert.PrefixTowers

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.PrefixConstType

variable {md : Mode} {before final : Env md}
  {T : Key md} {i : Nat} {entry : ProjEntry md}

/-- Both heads come from the PREFIX discipline at the actual table view.
The lookup's own table name fixes the structure, without a global premise. -/
theorem stored_tower_heads (projection : ProjOkT before)
    (stored : before.findProj? T i = some entry) :
    entry.structName = T ∧ entry.idx = i ∧ i < entry.numFields ∧
    ∃ (cvT : Ix.Kernel.ConstantVal md) (caps : IndCaps md) (cvC : Ix.Kernel.ConstantVal md),
      before.find? T = some (.indInfo cvT caps) ∧ cvT.levelParams = entry.levelParams ∧
      before.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
      cvC.levelParams = entry.levelParams := by
  obtain ⟨tbl, tableFound, bound, rfl⟩ := Env.findProj?_some stored
  have name : tbl.structName = T := projTableName_inj (Semantics.Env.find?_name tableFound)
  obtain ⟨_, _, _, ⟨cvT, caps, former, levelsT⟩, ⟨cvC, ctor, levelsC, _⟩⟩ :=
    projection.towerHead stored
  refine ⟨name, rfl, bound, cvT, caps, cvC, ?_, levelsT, ctor, levelsC⟩
  simpa only [ProjTable.entry_structName, name] using former

/-- The actual positive table/heads and all three depth-zero readings.
No model, input reading, header inference, grade or level-arity premise. -/
theorem stored_tower_readings (wf : EnvWF before) (projection : ProjOkT before)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final)
    (acval : Key md → (LevelParam → Nat) → AnnotTerm) (φ : LevelParam → Nat)
    (stored : before.findProj? T i = some entry) :
    final.findProj? T i = some entry ∧
    entry.structName = T ∧ entry.idx = i ∧ i < entry.numFields ∧
    ∃ (cvT : Ix.Kernel.ConstantVal md) (caps : IndCaps md) (cvC : Ix.Kernel.ConstantVal md),
      before.find? T = some (.indInfo cvT caps) ∧ cvT.levelParams = entry.levelParams ∧
      before.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
      cvC.levelParams = entry.levelParams ∧
      ∀ us : List Ix.Kernel.Level,
        denoteMeta acval before φ 0
          (projTele (entry.numParams + 1) (entry.body.instantiateLevelParams entry.levelParams us)) =
        denoteMeta acval final φ 0
          (projTele (entry.numParams + 1) (entry.body.instantiateLevelParams entry.levelParams us)) ∧
        denoteMeta acval before φ 0 (cvT.type.instantiateLevelParams cvT.levelParams us) =
          denoteMeta acval final φ 0 (cvT.type.instantiateLevelParams cvT.levelParams us) ∧
        denoteMeta acval before φ 0 (cvC.type.instantiateLevelParams cvC.levelParams us) =
          denoteMeta acval final φ 0 (cvC.type.instantiateLevelParams cvC.levelParams us) := by
  obtain ⟨name, idx, bound, cvT, caps, cvC, former, levelsT, ctor, levelsC⟩ :=
    stored_tower_heads projection stored
  refine ⟨PrefixReadings.projection_slot lookup stored, name, idx, bound,
    cvT, caps, cvC, former, levelsT, ctor, levelsC, ?_⟩
  intro us
  have body : (projTele (entry.numParams + 1)
      (entry.body.instantiateLevelParams entry.levelParams us)).constsResolve before = true := by
    rw [projTele_constsResolve, Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact (projEntry_body_wf wf stored).2.2.1
  have typeT : (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve before = true := by
    rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact (wf _ (Semantics.Env.find?_mem former)).2.2.1
  have typeC : (cvC.type.instantiateLevelParams cvC.levelParams us).constsResolve before = true := by
    rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams]
    exact (wf _ (Semantics.Env.find?_mem ctor)).2.2.1
  exact ⟨resolving_reading_eq acval φ 0 _ lookup slots body,
    resolving_reading_eq acval φ 0 _ lookup slots typeT,
    resolving_reading_eq acval φ 0 _ lookup slots typeC⟩

end Ix.Cert.PrefixTowers
