import IxC.Kernel.Model.Inductives.SumStageFormer
import IxC.Kernel.Model.Inductives.FixZeroField
import IxC.Kernel.Verify.Inductives.FixWF
import IxVMRefinement.Decl.ReferenceReplay

/-! # A model at the checked native constructor stage

The former and constructor checks already justify the temporary empty-family model used by
native semantic construction. No completed recursor or projection-table stage is needed.
The constructor checks supply freshness of any claimed eta constructor; the temporary empty
family satisfies the unit law. This model is used for typing coherence at this exact store,
without identifying its interpretation with that of the completed native block.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetModel

universe u

private theorem single_ctor_fresh {md : Mode} {J : Judgements md} {scope env : Env md}
    {name : Key md} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {former : ConstantVal md}
    {ctors annotated : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (checked : SumCtorsRunJ J scope env name levels nP nI sortLevel isProp large
      former ctors annotated sortss) :
    ∀ ctor, ctors = [ctor] → env.find? ctor.1.name = none := by
  intro ctor single
  obtain ⟨stored, annotatedEq⟩ := List.length_eq_one_iff.mp
    (show annotated.length = 1 by rw [checked.1, single]; rfl)
  obtain ⟨_, sorts, _, run⟩ := checked.2.2 0 ctor stored
    (by rw [single]; rfl) (by rw [annotatedEq]; rfl)
  exact run.names.2.2.1

private theorem nativeFormer_modelJ {md : Mode} {J : Judgements md} {mode : CheckMode}
    {V : Type u} [SetTheory V] {env : Env md} (model : EnvModelM V mode env)
    (etaClosed : EtaFamiliesClosed env) (frames : JudgeFrames J env)
    (sound : JudgeSound J model.base2) (inversions : JudgeInv J)
    {parts : InductiveShape md} {isRec : Bool} {raw checked stored : ConstantVal md}
    {binders : List (Expr md × BinderMeta)}
    (formerCheck : ConstantValCheckJ J env raw checked)
    (nameEq : raw.name = parts.cvT.name) (levelsEq : raw.levelParams = parts.cvT.levelParams)
    (storage : StoredFormer J env parts checked stored)
    (telescope : checked.type.stripPis (parts.nP + parts.nIdx) = some (binders, .sort parts.resSort))
    (freshCtors : ∀ ctor, parts.ctors = [ctor] →
      (⟨.indInfo stored (nativeCapsAt parts isRec) :: env.consts⟩ : Env md).find? ctor.1.name = none) :
    Nonempty (EnvModelM V mode ⟨.indInfo stored (nativeCapsAt parts isRec) :: env.consts⟩) := by
  have checkedName : checked.name = parts.cvT.name := formerCheck.name_eq.trans nameEq
  have checkedLevels : checked.levelParams = parts.cvT.levelParams := formerCheck.levelParams_eq.trans levelsEq
  obtain ⟨_, storedLevels⟩ := storage.name_lps ⟨checkedName, checkedLevels⟩
  have fresh : env.find? checked.name = none := by
    rw [formerCheck.name_eq]
    exact formerCheck.fresh
  obtain ⟨parameters, data⟩ := formerDataJ sound inversions formerCheck telescope
  have bound : ConstsBound env checked.type := constsBound_of_constsResolve _ data.cr
  have storedShape : stored = checked ∨ parts.nIdx ≠ 0 := by
    rcases storage with same | ⟨_, _, indexed⟩
    · exact .inl same
    · exact .inr indexed
  have vacuous : parts.nIdx ≠ 0 → ∀ {other : Env md} (m : EnvModel V other)
      (name : Key md) (cv : ConstantVal md), CapsLawsAt m name cv (nativeCapsAt parts isRec) :=
    fun indexed _ _ _ _ =>
      ⟨fun eta => absurd ((nativeCapsAt_nIdx parts isRec).2 eta) indexed,
        fun unit => absurd ((nativeCapsAt_nIdx parts isRec).1 unit) indexed⟩
  have capsWF : IndCapsWF (.indInfo stored (nativeCapsAt parts isRec)) := by
    have peels : (checked.type.stripPis (parts.nP + parts.nIdx)).isSome = true := by
      rw [telescope]
      rfl
    refine IndCapsWF.of_caps ?_ ?_
    · intro unit
      rcases storedShape with same | indexed
      · rw [same, (nativeCapsAt_arity parts isRec).1 unit]
        exact stripPis_isSome_of_le (Nat.le_add_right _ _) peels
      · exact absurd ((nativeCapsAt_nIdx parts isRec).1 unit) indexed
    · intro eta
      rcases storedShape with same | indexed
      · rw [same, (nativeCapsAt_arity parts isRec).2 eta]
        exact stripPis_isSome_of_le (Nat.le_add_right _ _) peels
      · exact absurd ((nativeCapsAt_nIdx parts isRec).2 eta) indexed
  have etaFresh : ∀ (m : EnvModel V ⟨.indInfo stored (nativeCapsAt parts isRec) :: env.consts⟩),
      (nativeCapsAt parts isRec).eta = true →
      EtaFamilyStored ⟨.indInfo stored (nativeCapsAt parts isRec) :: env.consts⟩
        parts.cvT.name (nativeCapsAt parts isRec) →
      ∀ assignment, EtaLaw m assignment parts.cvT.name checked (nativeCapsAt parts isRec) := by
    intro m eta family assignment
    exfalso
    unfold nativeCapsAt at eta
    split at eta
    · next ctor single =>
      obtain ⟨name, named, _, ⟨cv, nP, nF, found⟩, _⟩ := family
      simp only [nativeCapsAt, single] at named
      obtain rfl : ctor.1.name = name := Option.some.inj named
      rw [freshCtors ctor single] at found
      exact nomatch found
    · exact nomatch eta
  have unitParams : ∀ assignment, (nativeCapsAt parts isRec).unitlike = true →
      (nativeCapsAt parts isRec).unitParams = (parameters assignment).length := by
    intro assignment unit
    rw [(nativeCapsAt_arity parts isRec).1 unit, data.len assignment,
      (nativeCapsAt_nIdx parts isRec).1 unit, Nat.add_zero]
  rcases storage with same | ⟨declaredCheck, conversion, indexed⟩
  · subst stored
    obtain ⟨stageModel, _⟩ := stageSumFormerJ model etaClosed frames formerCheck nameEq data
      (fun _ => []) (fun _ _ _ => rfl) (fun _ _ impossible => nomatch impossible)
      (fun _ _ _ => ⟨(fun _ impossible => nomatch impossible), (fun _ impossible => nomatch impossible)⟩)
      (nativeCapsAt parts isRec) capsWF (fun next interpretation => by
        have crossed := data.cross fresh (ConsCrossAt.ofNtc fun _ impossible => nomatch impossible)
          bound next interpretation
        have leaf : ∀ assignment, next.acval parts.cvT.name assignment =
            sumTyAV (parts.resSort.eval assignment) (parameters assignment) [] := by
          intro assignment
          rw [interpretation, ← checkedName]
          exact congrFun acvalWith_self assignment
        rw [checkedName]
        exact ⟨etaFresh next, fun unit _ =>
          fixEmptyUnitLaw leaf crossed.read crossed.okTy (fun assignment => unitParams assignment unit)⟩)
    exact ⟨stageModel⟩
  · obtain ⟨stageModel, _⟩ := stageSumFormerDeclJ model etaClosed frames sound formerCheck nameEq
      declaredCheck rfl conversion storedLevels data (fun _ => []) (fun _ _ _ => rfl)
      (fun _ _ impossible => nomatch impossible)
      (fun _ _ _ => ⟨(fun _ impossible => nomatch impossible), (fun _ impossible => nomatch impossible)⟩)
      (nativeCapsAt parts isRec) capsWF (fun next _ => vacuous indexed next _ _)
    exact ⟨stageModel⟩

/-- Actual former and constructor checks produce a model of their intermediate store. The
constructor checks' result sort may differ syntactically from the former's telescope sort:
only their fresh constructor names are needed for this construction. -/
theorem nativeConstructorStage_modelJ {md : Mode} {J : Judgements md} {mode : CheckMode}
    {V : Type u} [SetTheory V] {env stage scope : Env md} (model : EnvModelM V mode env)
    (etaClosed : EtaFamiliesClosed env) (frames : JudgeFrames J env)
    (sound : JudgeSound J model.base2) (inversions : JudgeInv J)
    {parts completed : InductiveShape md} {isRec : Bool} {former ctorFormer : ConstantVal md}
    (formerRun : SumIndRunJ J env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key md} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ J scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss) :
    Nonempty (EnvModelM V mode stage) := by
  obtain ⟨raw, level, named, levelsEq, checked, rfl, ⟨stored, rfl, storage⟩, binders, telescope⟩ :=
    formerRun.shape
  exact nativeFormer_modelJ model etaClosed frames sound inversions checked named levelsEq
    storage telescope (single_ctor_fresh constructorRuns)

/-- The actual accepted prefix supplies both the initial model and eta-family closure. The
remaining inputs are the former and constructor stage checks, without a completed native run. -/
theorem ReferenceReplay.native_constructorStage_model {V : Type u} [SetTheory V]
    {fuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss) :
    Nonempty (EnvModelM V .verified stage) := by
  obtain ⟨⟨model, _⟩, etaClosed⟩ := replay.checked.envModelT (EnvModelT.empty (V := V))
  exact nativeConstructorStage_modelJ model etaClosed (judgeFrames_rulesJ env)
    (judgeSound_rulesJ_of model) judgeInv_rulesJ formerRun constructorRuns

end IxVM.Refinement.Decl
