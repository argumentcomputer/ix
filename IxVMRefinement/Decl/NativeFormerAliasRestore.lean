import IxVMRefinement.Decl.NativeFormerRestore

/-! # Restoring a direct former alias while retaining its capabilities and projection tables

The alias's actual definition supplies its type reading. A fit at a constant-headed type has
no arguments, so every fit needed by the former's semantic laws transfers to the old type by
`Fits.nil`. Constructor types, recursor rules, tables, and all constant values are retained.
-/

namespace IxVM.Refinement.Decl.NativeFormerRestore

open Ix.Kernel

universe u

variable {md : Mode}

private theorem find_ind_origin (cv : ConstantVal md) (caps : IndCaps md) (replacement : Expr md)
    {env : Env md} {name : Key md} {val : ConstantVal md} {flags : IndCaps md}
    (found : (environment cv caps replacement env).find? name = some (.indInfo val flags)) :
    (val = { cv with type := replacement } ∧ flags = caps ∧
      env.find? name = some (.indInfo cv caps)) ∨ env.find? name = some (.indInfo val flags) := by
  obtain ⟨original, originalFound, equal⟩ := found_original cv caps replacement found
  by_cases changed : original = .indInfo cv caps
  · subst original
    simp only [info, ↓reduceIte] at equal
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj equal
    exact .inl ⟨rfl, rfl, originalFound⟩
  · simp only [info, ite_eq_right changed] at equal
    exact .inr (originalFound.trans (congrArg some equal))

private theorem fits_alias_replace {V : Type u} [SetTheory V]
    {cval : Key md → (LevelParam → Nat) → V} {before after : Env md}
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {aliasKey : Key md} {levels : List Level}
    {values : List V} {residual : Expr md}
    (fitted : Fits cval after φ ρ (.const aliasKey levels) values σ residual) (oldType : Expr md) :
    ∃ oldResidual, Fits cval before φ ρ oldType values σ oldResidual := by
  cases fitted
  exact ⟨oldType, .nil⟩

/-- An actual definition of the checked type restores its direct alias without dropping
eta, unit-like behavior, or the family's projection tables. -/
def aliasModelWithTables {V : Type u} [SetTheory V]
    (cv : ConstantVal md) (caps : IndCaps md) {env : Env md} (M : Model V env)
    {aliasCV : ConstantVal md} {hint : ReducibilityHint}
    (aliasFound : env.find? aliasCV.name = some (.defnInfo aliasCV cv.type hint)) :
    Model V (environment cv caps (.const aliasCV.name (aliasCV.levelParams.map .param)) env) := by
  let replacement : Expr md := .const aliasCV.name (aliasCV.levelParams.map .param)
  have typeRead : ∀ φ ρ A, Denotes M.cval env φ ρ cv.type A → Denotes M.cval env φ ρ replacement A := by
    intro φ ρ A read
    have aliasRead := M.defn_value aliasCV cv.type hint (List.mem_of_find?_eq_some aliasFound) φ ρ
    obtain rfl := Denotes_functional read aliasRead
    have denoted := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) aliasFound
      (show (aliasCV.levelParams.map Level.param).length = aliasCV.levelParams.length by simp)
    simpa only [replacement, ConstantInfo.toConstantVal, Level.substFn_param_self] using denoted
  refine {
    cval := M.cval
    mem := ?_
    false_empty := ?_
    eq_equality := ?_
    punit_unit := ?_
    defn_value := ?_
    cval_params := ?_
    iota_rule := ?_
    unit_like := ?_
    proj_law := ?_
    proj_type := ?_
    eta_fn := ?_
    lit_ops := ?_
    nat_add := ?_
    graded := ?_ }
  · intro ci mem φ ρ
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
    obtain ⟨A, read, member⟩ := M.mem original present φ ρ
    by_cases changed : original = .indInfo cv caps
    · subst original
      refine ⟨A, ?_, ?_⟩
      · simpa only [info, ↓reduceIte, ConstantInfo.toConstantVal, denotes_eq] using typeRead φ ρ A read
      · simpa only [info, ↓reduceIte, ConstantInfo.name, ConstantInfo.toConstantVal] using member
    · exact ⟨A, by simpa only [info, ite_eq_right changed, denotes_eq] using read,
        by simpa only [info, ite_eq_right changed] using member⟩
  · simpa only [denotes_eq] using M.false_empty
  · simpa only [denotes_eq] using M.eq_equality
  · simpa only [denotes_eq] using M.punit_unit
  · intro val value redHint mem φ ρ
    obtain ⟨original, present, equal⟩ := List.mem_map.mp mem
    have same := info_eq_back cv caps replacement equal (by intros; intro h; cases h)
    subst original
    simpa only [denotes_eq] using M.defn_value val value redHint present φ ρ
  · intro name ci found φ ψ agree
    obtain ⟨original, originalFound, rfl⟩ := found_original cv caps replacement found
    exact M.cval_params name original originalFound φ ψ (by simpa only [info_levels] using agree)
  · simpa only [IotaLaw, IotaRule, find_rec, find_ctor, denotes_eq, fits_eq, denotesList_eq] using M.iota_rule
  · intro T val flags found unit
    rcases find_ind_origin cv caps replacement found with ⟨rfl, rfl, original⟩ | original
    · intro us φ ρ σ ts R F x y arity count denoted fitted hx hy
      have oldDenoted : Denotes M.cval env φ ρ (.const T us) F := by
        simpa only [denotes_eq] using denoted
      obtain ⟨oldResidual, oldFit⟩ := fits_alias_replace (before := env) fitted
        (cv.type.instantiateLevelParams cv.levelParams us)
      exact M.unit_like T cv caps original unit us φ ρ σ ts oldResidual F x y arity count oldDenoted oldFit hx hy
    · simpa only [denotes_eq, fits_eq] using M.unit_like T val flags original unit
  · intro T i entry val flags table found
    rcases find_ind_origin cv caps replacement found with ⟨rfl, rfl, original⟩ | original
    · have oldTable : env.findProj? T i = some entry := by simpa only [findProj] using table
      obtain ⟨levels, ctor, ctorFound, ctorLevels, ctorShape, laws⟩ :=
        M.proj_law T i entry cv caps oldTable original
      refine ⟨levels, ctor, (find_ctor cv caps replacement).mpr ctorFound, ctorLevels, ctorShape, ?_⟩
      intro us φ ρ F K arity formerRead ctorRead
      have formerOld : Denotes M.cval env φ ρ (.const T us) F := by simpa only [denotes_eq] using formerRead
      have ctorOld : Denotes M.cval env φ ρ (.const entry.ctor us) K := by simpa only [denotes_eq] using ctorRead
      obtain ⟨beta, eta⟩ := laws us φ ρ F K arity formerOld ctorOld
      constructor
      · intro guard σ R values count fitted
        apply beta guard σ R values count
        simpa only [fits_eq] using fitted
      · intro σ R values x count fitted member
        obtain ⟨oldResidual, oldFit⟩ := fits_alias_replace (before := env) fitted
          (cv.type.instantiateLevelParams cv.levelParams us)
        exact eta σ oldResidual values x count oldFit member
    · simpa only [find_ctor, denotes_eq, fits_eq] using
        M.proj_law T i entry val flags (by simpa only [findProj] using table) original
  · simpa only [ProjTypeLaw, findProj, denotes_eq] using M.proj_type
  · intro T val flags C found eta
    rcases find_ind_origin cv caps replacement found with ⟨rfl, rfl, original⟩ | original
    · intro notReserved ctorName ctorNotReserved ctorPresent projections us φ ρ σ R values x arity count fitted member
      have ctorOld : ∃ cvC nP nF, env.find? C = some (.ctorInfo cvC nP nF) := by
        simpa only [find_ctor] using ctorPresent
      have projectionsOld : ∀ j, j < caps.etaFields → ∃ val mI rP rules,
          env.find? (projFnName T j) = some (.recInfo val mI rP rules) := by
        simpa only [find_rec] using projections
      obtain ⟨oldResidual, oldFit⟩ := fits_alias_replace (before := env) fitted
        (cv.type.instantiateLevelParams cv.levelParams us)
      exact M.eta_fn T cv caps C original eta notReserved ctorName ctorNotReserved ctorOld projectionsOld
        us φ ρ σ oldResidual values x arity count oldFit member
    · simpa only [find_ctor, find_rec, fits_eq] using M.eta_fn T val flags C original eta
  · simpa only [NatLitLaw, find_defn, denotes_eq] using M.lit_ops
  · simpa only [NatAddLaw, find_defn, denotes_eq] using M.nat_add
  · intro ci mem φ ρ
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp mem
    have graded := M.graded original present φ ρ
    constructor
    · by_cases changed : original = .indInfo cv caps
      · subst original
        simp only [info, ↓reduceIte, ConstantInfo.toConstantVal, replacement, GradedBy]
      · simpa only [info, ite_eq_right changed, denotes_eq] using graded.1
    · intro val value redHint equal
      have originalEq := info_eq_back cv caps replacement equal (by intros; intro h; cases h)
      simpa only [denotes_eq] using graded.2 val value redHint originalEq

theorem aliasModelWithTables_cval {V : Type u} [SetTheory V]
    (cv : ConstantVal md) (caps : IndCaps md) {env : Env md} (M : Model V env)
    {aliasCV : ConstantVal md} {hint : ReducibilityHint}
    (aliasFound : env.find? aliasCV.name = some (.defnInfo aliasCV cv.type hint)) :
    (aliasModelWithTables cv caps M aliasFound).cval = M.cval := rfl

end IxVM.Refinement.Decl.NativeFormerRestore
