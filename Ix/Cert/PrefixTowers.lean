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

universe w

/-- The supplied final law at the SAME table entry. Its existential heads
are identified by forward preservation of produced PREFIX hits; all A/B/C,
O5, Prop guards, offsets and the unconditional eta clause remain intact. -/
theorem tower_ok_preserved {V : Type w} [SetTheory V]
    (M : Cached.StrongModel V final) (core : EnvModel V before)
    (valuation : core.acval = M.internal.base2.acval)
    (lookup : FindPreserved before final) (slots : StoredHeadSlots before final)
    (φ : LevelParam → Nat) : TowerOk core φ := by
  intro T i entry stored
  obtain ⟨finalHit, _, _, _, cvT, caps, cvC, former, _, ctor, _, readings⟩ :=
    stored_tower_readings core.wf core.proj_ok lookup slots M.internal.base2.acval φ stored
  obtain ⟨name, idx, bound, ⟨cvTF, capsF, formerFinal, formerFacts⟩, o5,
      cvCF, ctorFinal, ctorLevels, laws, eta⟩ := M.internal.tower_ok φ T i entry finalHit
  obtain ⟨rfl, rfl⟩ := Ix.Kernel.ConstantInfo.indInfo.inj
    (Option.some.inj (formerFinal.symm.trans (lookup former)))
  obtain rfl : cvCF = cvC := (Ix.Kernel.ConstantInfo.ctorInfo.inj
    (Option.some.inj (ctorFinal.symm.trans (lookup ctor)))).1
  refine ⟨name, idx, bound, ⟨_, _, former, formerFacts⟩, o5,
    _, ctor, ctorLevels, ?_, ?_⟩
  · intro us arity
    obtain ⟨bodyEq, _, ctorEq⟩ := readings us
    obtain ⟨⟨Ta, bodyRead, typing⟩, ⟨TCa, ctorRead, iota⟩⟩ := laws us arity
    refine ⟨⟨Ta, ?_, ?_⟩, ⟨TCa, ?_, ?_⟩⟩
    · simpa only [valuation] using bodyEq.trans bodyRead
    · simpa only [valuation] using typing
    · simpa only [valuation] using ctorEq.trans ctorRead
    · simpa only [valuation] using iota
  · intro cvT' caps' found us arity
    obtain ⟨rfl, rfl⟩ := Ix.Kernel.ConstantInfo.indInfo.inj
      (Option.some.inj (found.symm.trans former))
    obtain ⟨TVa, typeRead, grade, law⟩ := eta _ _ (lookup former) us arity
    refine ⟨TVa, ?_, grade, ?_⟩
    · simpa only [valuation] using (readings us).2.1.trans typeRead
    · simpa only [valuation] using law

end Ix.Cert.PrefixTowers

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixTowers

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- Every prefix table has the complete law at the supplied final acval.
The actual front derives all heads/slots/readings and retains prior rows
and the target package. NatOpRow and final source composition remain open. -/
theorem DefinitionFrontAt.final_prefix_tower_ok
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧ (∀ φ : LevelParam → Nat, NatHeads core φ) ∧ EqLaw core ∧
      AcvalDefnInst core ∧ (∀ φ : LevelParam → Nat, ConstType core φ) ∧
      CapsOk core ∧ (∀ φ : LevelParam → Nat, Rules.NatSuccRow core φ) ∧
      (∀ φ : LevelParam → Nat, RecRules core φ) ∧
      (∀ φ : LevelParam → Nat, TowerOk core φ) ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧ Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types, caps, succ, recs, target⟩ :=
    front.final_prefix_rec_rules V M
  exact ⟨core, valuation, publicEq, valid, heads, eqLaw, definitions, types, caps, succ, recs,
    fun φ => tower_ok_preserved M core valuation front.lookup_preserved front.stored_head_slots φ,
    target⟩

end Ix.Cert.ReferenceFronts
