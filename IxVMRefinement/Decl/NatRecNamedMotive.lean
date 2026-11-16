import IxVMRefinement.Decl.NatRecDomainMetadata
import IxVMRefinement.Decl.ReferenceReplay

/-! # Binder data from an actually evaluated named motive

The named motive need not return one uniform type: its value may compute differently at
zero and successors. The caller's actual inferred result is the motive at its major, so its
sort check supplies the precise reduction at zero. The base-argument comparison and that
recorded reduction determine a product base's datum in the accepted reference model.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

private theorem nat_rec_complete_shape {md : Mode} (elim : Level) :
    ∃ motiveDomain stepDomain motiveMeta baseMeta stepMeta majorMeta,
      (natRecA (md := md)).toConstantVal.type.instantiateLevelParams
        (natRecA (md := md)).toConstantVal.levelParams [elim] =
      .forallE motiveDomain (.forallE (.app (.bvar 0) (.const natZeroName []))
        (.forallE stepDomain (.forallE (.const natName []) (.app (.bvar 3) (.bvar 0)) majorMeta)
          stepMeta) baseMeta) motiveMeta := by
  exact ⟨_, _, _, _, _, _, rfl⟩

/-- Actual inference of a named-motive Nat.rec application retains the motive's own check
and returns precisely that named motive applied to the supplied major. -/
theorem natRec_named_result {md : Mode} {env : Env md} {depth : Nat} {elim : Level}
    {motiveName : Key md} {motiveLevels : List Level} {base step major inferred : Expr md}
    (recFound : env.find? natRecName = some natRecA)
    (typed : Rules.Infer env .full depth
      (.app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels)) base) step) major) inferred) :
    inferred = .app (.const motiveName motiveLevels) major ∧
      ∃ motiveType, Rules.Infer env .full depth (.const motiveName motiveLevels) motiveType := by
  obtain ⟨_, _, _, _, _, stepTyped, stepReduced, _, _, finalTypeEq⟩ := Rules.Infer.app_inv typed
  obtain ⟨_, _, _, _, _, baseTyped, baseReduced, _, _, stepTypeEq⟩ := Rules.Infer.app_inv stepTyped
  obtain ⟨_, _, _, _, _, motiveTyped, motiveReduced, _, _, baseTypeEq⟩ := Rules.Infer.app_inv baseTyped
  obtain ⟨_, _, _, _, motiveType, recTyped, recReduced, motiveChecked, _, motiveTypeEq⟩ := Rules.Infer.app_inv motiveTyped
  obtain ⟨ci, found, _, _, recTypeEq⟩ := Rules.Infer.const_inv recTyped
  have same : ci = natRecA := Option.some.inj (found.symm.trans recFound)
  subst ci
  obtain ⟨_, _, _, _, _, _, shape⟩ := nat_rec_complete_shape (md := md) elim
  rw [recTypeEq, shape] at recReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid recReduced rfl)
  rw [motiveTypeEq] at motiveReduced
  simp only [Expr.instantiate1, ↓reduceIte] at motiveReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid motiveReduced rfl)
  rw [baseTypeEq] at baseReduced
  simp only [Expr.instantiate1] at baseReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid baseReduced rfl)
  rw [stepTypeEq] at stepReduced
  simp only [Expr.instantiate1] at stepReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid stepReduced rfl)
  exact ⟨by simpa [Expr.instantiate1] using finalTypeEq, motiveType, motiveChecked⟩

/-- The first type check's own ensureSort run fixes the product returned by Nat.rec at zero,
including named motives whose other branches return different types. -/
theorem named_natRec_zero_product_metadata {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) {fuel depth : Nat} {elim kindSort resultSort : Level}
    {motiveName : Key .anon} {motiveLevels : List Level} {motiveCV : ConstantVal .anon}
    {motiveValue domain body step inferred : Expr .anon} {hint : ReducibilityHint}
    {motiveMeta productMeta : BinderMeta}
    (zeroFound : env.find? natZeroName = some natZeroA)
    (recFound : env.find? natRecName = some natRecA)
    (motiveFound : env.find? motiveName = some (.defnInfo motiveCV motiveValue hint))
    (motiveHeader : motiveCV.type.instantiateLevelParams motiveCV.levelParams motiveLevels =
      .forallE (.const natName []) (.sort kindSort) motiveMeta)
    (inferredRun : inferTypeCore .verified env fuel depth
      (.app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
        (.forallE domain body productMeta)) step) (.const natZeroName [])) = .ok inferred)
    (sortRun : ensureSortCore .verified env fuel depth inferred = .ok resultSort) :
    productMeta.pw = Level.zeronessOf resultSort := by
  have typed := Rules.inferTypeCore_bridge inferredRun
  obtain ⟨resultType, motiveType, motiveTyped⟩ := natRec_named_result recFound typed
  rw [resultType] at sortRun
  have expectedReduced := Rules.whnf_bridge (ensureSortCore_inv sortRun)
  obtain ⟨ci, found, _, arity, _⟩ := Rules.Infer.const_inv motiveTyped
  have same : ci = .defnInfo motiveCV motiveValue hint := Option.some.inj (found.symm.trans motiveFound)
  subst ci
  have namedTyped : Rules.Infer env .full depth (.const motiveName motiveLevels)
      (.forallE (.const natName []) (.sort kindSort) motiveMeta) := by
    have checked := Rules.Infer.const (g := Rules.Grade.full) (d := depth) motiveFound rfl arity
    simpa only [ConstantInfo.toConstantVal, motiveHeader] using checked
  have zeroTyped : Rules.Infer env .full depth (.const natZeroName []) (.const natName []) :=
    Rules.Infer.const zeroFound rfl rfl
  have expectedTyped := Rules.Infer.app namedTyped Rules.Red.refl zeroTyped Rules.DefEq.refl
  obtain ⟨_, _, _, _, _, stepTyped, _, _, _, _⟩ := Rules.Infer.app_inv typed
  obtain ⟨_, _, _, _, _, baseTyped, _, _, _, _⟩ := Rules.Infer.app_inv stepTyped
  obtain ⟨_, productTyped, compared⟩ := natRec_base_comparison recFound baseTyped
  obtain ⟨_, domainSort, _, bodySort, _, _, _, _, metadata, productType⟩ := Rules.Infer.forallE_inv productTyped
  rw [productType] at compared
  have zero := closed_checked_sort_zero model (by rfl) (by rfl) expectedTyped expectedReduced compared
  exact metadata.symm.trans zero

/-- The required model is produced by the actual accepted prefix; no final model or metadata
correspondence is assumed by the caller. -/
theorem ReferenceReplay.named_natRec_zero_product_metadata {V : Type u} [SetTheory V]
    {prefixFuel : Nat} {ev : Evidences .anon} {sourceOut env : Env .anon} {declarations : List (Declaration .anon)}
    (replay : ReferenceReplay prefixFuel ev Env.empty Env.empty declarations sourceOut env)
    {fuel depth : Nat} {elim kindSort resultSort : Level}
    {motiveName : Key .anon} {motiveLevels : List Level} {motiveCV : ConstantVal .anon}
    {motiveValue domain body step inferred : Expr .anon} {hint : ReducibilityHint}
    {motiveMeta productMeta : BinderMeta}
    (zeroFound : env.find? natZeroName = some natZeroA)
    (recFound : env.find? natRecName = some natRecA)
    (motiveFound : env.find? motiveName = some (.defnInfo motiveCV motiveValue hint))
    (motiveHeader : motiveCV.type.instantiateLevelParams motiveCV.levelParams motiveLevels =
      .forallE (.const natName []) (.sort kindSort) motiveMeta)
    (inferredRun : inferTypeCore .verified env fuel depth
      (.app (.app (.app (.app (.const natRecName [elim]) (.const motiveName motiveLevels))
        (.forallE domain body productMeta)) step) (.const natZeroName [])) = .ok inferred)
    (sortRun : ensureSortCore .verified env fuel depth inferred = .ok resultSort) :
    productMeta.pw = Level.zeronessOf resultSort := by
  obtain ⟨⟨model, _⟩, _⟩ := replay.checked.envModelT (EnvModelT.empty (V := V))
  exact IxVM.Refinement.Decl.named_natRec_zero_product_metadata model zeroFound recFound motiveFound motiveHeader
    inferredRun sortRun

end IxVM.Refinement.Decl
