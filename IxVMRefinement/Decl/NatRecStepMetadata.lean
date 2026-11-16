import IxVMRefinement.Decl.NatRecOpenSort
import IxVMRefinement.Decl.TelescopeConversionPins

/-! # Product metadata from the actual successor-minor check of `Nat.rec`

The recursor's application validates the supplied step against its generated dependent
minor type. Inverting that comparison retains both actual opener choices. The expected
result ignores the induction-hypothesis opener and mentions the Nat opener alone, whose
satisfying frame is constructed from the pinned Nat block.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

private theorem nat_rec_first_three {md : Mode} (elim : Level) :
    ∃ motiveDomain motiveMeta baseMeta stepMeta outerMeta innerMeta rest,
      (natRecA (md := md)).toConstantVal.type.instantiateLevelParams
        (natRecA (md := md)).toConstantVal.levelParams [elim] =
      .forallE motiveDomain (.forallE (.app (.bvar 0) (.const natZeroName []))
        (.forallE (.forallE (.const natName [])
          (.forallE (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1))) innerMeta) outerMeta)
          rest stepMeta) baseMeta) motiveMeta := by
  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- The actual third argument check supplies the dependent successor-minor comparison. -/
theorem natRec_step_comparison {md : Mode} {env : Env md} {depth : Nat} {elim sortLevel : Level}
    {base step inferred : Expr md}
    (recFound : env.find? natRecName = some natRecA)
    (typed : Rules.Infer env .full depth
      (.app (.app (.app (.const natRecName [elim]) (natSortMotive sortLevel)) base) step) inferred) :
    ∃ stepType outerMeta innerMeta,
      Rules.Infer env .full depth step stepType ∧
      Rules.DefEq env depth stepType
        (.forallE (.const natName [])
          (.forallE (.app (natSortMotive sortLevel) (.bvar 0))
            (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.bvar 1))) innerMeta) outerMeta) := by
  obtain ⟨_, _, _, _, stepType, baseTyped, baseReduced, stepTyped, compared, _⟩ := Rules.Infer.app_inv typed
  obtain ⟨_, _, _, _, _, motiveTyped, motiveReduced, _, _, baseTypeEq⟩ := Rules.Infer.app_inv baseTyped
  obtain ⟨_, _, _, _, _, recTyped, recReduced, _, _, motiveTypeEq⟩ := Rules.Infer.app_inv motiveTyped
  obtain ⟨ci, found, _, _, recTypeEq⟩ := Rules.Infer.const_inv recTyped
  have same : ci = natRecA := Option.some.inj (found.symm.trans recFound)
  subst ci
  obtain ⟨_, _, _, _, outerMeta, innerMeta, _, shape⟩ := nat_rec_first_three (md := md) elim
  rw [recTypeEq, shape] at recReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid recReduced rfl)
  rw [motiveTypeEq] at motiveReduced
  simp only [natSortMotive, Expr.instantiate1, ↓reduceIte] at motiveReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid motiveReduced rfl)
  rw [baseTypeEq] at baseReduced
  simp only [Expr.instantiate1] at baseReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid baseReduced rfl)
  exact ⟨stepType, outerMeta, innerMeta, stepTyped, compared⟩

private theorem nat_step_product_type {md : Mode} {env : Env md} {depth : Nat}
    {hypothesisType domain body stepType : Expr md} {outerMeta innerMeta productMeta : BinderMeta}
    (typed : Rules.Infer env .full depth
      (.lam (.const natName []) (.lam hypothesisType (.forallE domain body productMeta) innerMeta) outerMeta) stepType) :
    ∃ inferredDomain resultSort,
      stepType = .forallE (.const natName []) (.forallE inferredDomain (.sort resultSort) innerMeta) outerMeta ∧
      Level.zeronessOf resultSort = productMeta.pw := by
  cases typed with
  | lam _ _ firstBody _ _ _ _ =>
    simp only [Expr.instantiate1] at firstBody
    cases firstBody with
    | lam _ _ finalBody _ _ _ _ =>
      simp only [Expr.instantiate1] at finalBody
      obtain ⟨_, domainSort, _, bodySort, _, _, _, _, metadata, result⟩ := Rules.Infer.forallE_inv finalBody
      cases result
      exact ⟨_, .imax domainSort bodySort, rfl, metadata⟩

/-- A product returned directly by the checked successor minor carries the constant motive's
universe datum. Its domain/body may depend on the Nat opener, the induction hypothesis and caller variables. -/
theorem natRec_step_product_metadata {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {elim sortLevel : Level}
    {base hypothesisType domain body major inferred : Expr md}
    {outerMeta innerMeta productMeta : BinderMeta}
    (natFound : env.find? natName = some natA)
    (zeroFound : env.find? natZeroName = some natZeroA)
    (succFound : env.find? natSuccName = some natSuccA)
    (recFound : env.find? natRecName = some natRecA)
    (typed : Rules.Infer env .full depth
      (.app (.app (.app (.app (.const natRecName [elim]) (natSortMotive sortLevel)) base)
        (.lam (.const natName []) (.lam hypothesisType (.forallE domain body productMeta) innerMeta) outerMeta)) major)
      inferred) : productMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨_, _, _, _, _, stepApplied, _, _, _, _⟩ := Rules.Infer.app_inv typed
  obtain ⟨stepType, expectedOuter, expectedInner, stepTyped, compared⟩ := natRec_step_comparison recFound stepApplied
  obtain ⟨inferredDomain, resultSort, stepTypeEq, metadata⟩ := nat_step_product_type stepTyped
  rw [stepTypeEq] at compared
  obtain ⟨_, _, firstLeft | firstRight⟩ := forall_conversion_components compared
  all_goals
    have firstBody : Rules.DefEq env (depth + 1)
        (.forallE (inferredDomain.instantiate1 (.fvar depth (.const natName []))) (.sort resultSort) innerMeta)
        (.forallE (.app (natSortMotive sortLevel) (.fvar depth (.const natName [])))
          (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName [])))) expectedInner) := by
      first
      | simpa only [natSortMotive, Expr.instantiate1, ↓reduceIte] using firstLeft
      | simpa only [natSortMotive, Expr.instantiate1, ↓reduceIte] using firstRight
    obtain ⟨_, _, secondLeft | secondRight⟩ := forall_conversion_components firstBody
    all_goals
      have residual : Rules.DefEq env (depth + 2) (.sort resultSort)
          (.app (natSortMotive sortLevel) (.app (.const natSuccName []) (.fvar depth (.const natName [])))) := by
        first
        | simpa only [natSortMotive, Expr.instantiate1, ↓reduceIte] using secondLeft
        | simpa only [natSortMotive, Expr.instantiate1, ↓reduceIte] using secondRight
      exact metadata.symm.trans (nat_successor_motive_sort_zero model natFound zeroFound succFound residual)

end IxVM.Refinement.Decl
