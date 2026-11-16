import IxVMRefinement.Decl.NativeStageModel
import IxVMRefinement.Decl.NatRecNamedMotive

/-! # Named-motive coherence at the native constructor stage

The model needed to compare an inferred product sort with a computed named motive is built
at the actual constructor-checking store. It comes from the accepted prefix and the native
former and constructor checks, before any recursor or projection table is installed.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

/-- The actual native stage admits the named, nonuniform-motive metadata argument without
transporting its checks into a later environment or assuming a stage model. -/
theorem ReferenceReplay.native_named_natRec_zero_product_metadata {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env stage scope : Env .anon}
    {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {parts completed : InductiveShape .anon} {isRec : Bool} {former ctorFormer : ConstantVal .anon}
    (formerRun : SumIndRunJ rulesJ env parts (fun current => nativeCapsAt current isRec) stage former completed)
    {name : Key .anon} {levels : List LevelParam} {nP nI : Nat} {sortLevel : Level}
    {isProp large : Bool} {annotated : List (ConstantVal .anon × Nat)} {sortss : List (List Level)}
    (constructorRuns : SumCtorsRunJ rulesJ scope stage name levels nP nI sortLevel isProp large
      ctorFormer completed.ctors annotated sortss)
    {fuel depth : Nat} {elim kindSort resultSort : Level}
    {motiveName : Key .anon} {motiveLevels : List Level} {motiveCV : ConstantVal .anon}
    {motiveValue domain body step inferred : Expr .anon} {hint : ReducibilityHint}
    {motiveMeta productMeta : BinderMeta}
    (zeroFound : stage.find? natZeroName = some natZeroA)
    (recFound : stage.find? natRecName = some natRecA)
    (motiveFound : stage.find? motiveName = some (.defnInfo motiveCV motiveValue hint))
    (motiveHeader : motiveCV.type.instantiateLevelParams motiveCV.levelParams motiveLevels =
      .forallE (.const natName []) (.sort kindSort) motiveMeta)
    (inferredRun : inferTypeCore .verified stage fuel depth
      (.app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
        (.forallE domain body productMeta)) step) (.const natZeroName [])) = .ok inferred)
    (sortRun : ensureSortCore .verified stage fuel depth inferred = .ok resultSort) :
    productMeta.pw = Level.zeronessOf resultSort := by
  obtain ⟨model⟩ := replay.native_constructorStage_model (V := V) formerRun constructorRuns
  exact named_natRec_zero_product_metadata model zeroFound recFound motiveFound motiveHeader inferredRun sortRun

end IxVM.Refinement.Decl
