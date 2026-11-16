import IxVMRefinement.Decl.ClosedSortConversion
import IxC.Kernel.BasisA

/-! # Product metadata from the actual base-argument check of `Nat.rec`

For a constant universe motive, the base argument is compared with that motive at zero.
This is an actual inference premise of the recursor application, and its expected type is
a closed checked beta redex. It determines the datum of a product supplied as the base,
including products whose bodies depend on the surrounding constructor variables.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

/-- A constant universe motive used in type-level recursion. -/
def natSortMotive {md : Mode} (sortLevel : Level) : Expr md :=
  .lam (.const natName []) (.sort sortLevel) default

/-- The constant universe motive has its checked product type at every depth. -/
theorem natSortMotive_typed {md : Mode} {env : Env md} {depth : Nat} {sortLevel : Level}
    (natFound : env.find? natName = some natA) :
    Rules.Infer env .full depth (natSortMotive sortLevel)
      (.forallE (.const natName []) (.sort (.succ sortLevel)) default) := by
  have natTyped : Rules.Infer env .full depth (.const natName []) (.sort (.succ .zero)) :=
    Rules.Infer.const natFound rfl rfl
  refine Rules.Infer.lam (fun _ => natTyped) (fun _ => .refl) .sort ?_ (fun _ => .sort) (fun _ => .refl) ?_
  · intro pw impossible
    cases impossible
  · intro _
    rfl

private theorem nat_motive_zero_typed {md : Mode} {env : Env md} {depth : Nat} {sortLevel : Level}
    (natFound : env.find? natName = some natA) (zeroFound : env.find? natZeroName = some natZeroA) :
    Rules.Infer env .full depth (.app (natSortMotive sortLevel) (.const natZeroName [])) (.sort (.succ sortLevel)) := by
  have zeroTyped : Rules.Infer env .full depth (.const natZeroName []) (.const natName []) :=
    Rules.Infer.const zeroFound rfl rfl
  exact Rules.Infer.app (natSortMotive_typed natFound) .refl zeroTyped .refl

private theorem nat_rec_first_two {md : Mode} (elim : Level) :
    ∃ motiveDomain motiveMeta baseMeta rest,
      (natRecA (md := md)).toConstantVal.type.instantiateLevelParams
        (natRecA (md := md)).toConstantVal.levelParams [elim] =
      .forallE motiveDomain (.forallE (.app (.bvar 0) (.const natZeroName [])) rest baseMeta) motiveMeta := by
  exact ⟨_, _, _, _, rfl⟩

/-- The actual partial recursor application checks its base against the motive applied to zero. -/
theorem natRec_base_comparison {md : Mode} {env : Env md} {depth : Nat} {elim : Level}
    {motive base inferred : Expr md}
    (recFound : env.find? natRecName = some natRecA)
    (typed : Rules.Infer env .full depth (.app (.app (.const natRecName [elim]) motive) base) inferred) :
    ∃ baseType, Rules.Infer env .full depth base baseType ∧
      Rules.DefEq env depth baseType (.app motive (.const natZeroName [])) := by
  obtain ⟨_, _, _, _, baseType, motiveTyped, motiveReduced, baseTyped, compared, _⟩ := Rules.Infer.app_inv typed
  obtain ⟨_, _, _, _, _, recTyped, recReduced, _, _, motiveTypeEq⟩ := Rules.Infer.app_inv motiveTyped
  obtain ⟨ci, found, _, _, recTypeEq⟩ := Rules.Infer.const_inv recTyped
  have same : ci = natRecA := Option.some.inj (found.symm.trans recFound)
  subst ci
  obtain ⟨motiveDomain, motiveMeta, baseMeta, rest, shape⟩ := nat_rec_first_two (md := md) elim
  rw [recTypeEq, shape] at recReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid recReduced rfl)
  rw [motiveTypeEq] at motiveReduced
  simp only [Expr.instantiate1] at motiveReduced
  obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (Rules.Red.rigid motiveReduced rfl)
  exact ⟨baseType, baseTyped, compared⟩

/-- A product chosen by the zero branch of a checked type-level `Nat.rec` has the motive's
universe datum. This reads the base-argument check, not a semantic recursor-law typing assumption. -/
theorem natRec_zero_product_metadata {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {depth : Nat} {elim sortLevel : Level}
    {domain body step inferred : Expr md} {binderMeta : BinderMeta}
    (natFound : env.find? natName = some natA)
    (zeroFound : env.find? natZeroName = some natZeroA)
    (recFound : env.find? natRecName = some natRecA)
    (typed : Rules.Infer env .full depth
      (.app (.app (.app (.app (.const natRecName [elim]) (natSortMotive sortLevel))
        (.forallE domain body binderMeta)) step) (.const natZeroName [])) inferred) :
    binderMeta.pw = Level.zeronessOf sortLevel := by
  obtain ⟨_, _, _, _, _, stepTyped, _, _, _, _⟩ := Rules.Infer.app_inv typed
  obtain ⟨_, _, _, _, _, baseTyped, _, _, _, _⟩ := Rules.Infer.app_inv stepTyped
  obtain ⟨baseType, productTyped, compared⟩ := natRec_base_comparison recFound baseTyped
  obtain ⟨_, domainSort, _, bodySort, _, _, _, _, metadata, productType⟩ := Rules.Infer.forallE_inv productTyped
  rw [productType] at compared
  have expectedTyped := nat_motive_zero_typed (depth := depth) (sortLevel := sortLevel) natFound zeroFound
  have expectedReduced : Rules.Red env depth (.app (natSortMotive sortLevel) (.const natZeroName [])) (.sort sortLevel) :=
    Rules.Red.betaGate rfl
  have zeros := closed_checked_sort_zero model (by rfl) (by rfl) expectedTyped expectedReduced compared
  exact metadata.symm.trans zeros

end IxVM.Refinement.Decl
