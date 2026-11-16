import IxVMRefinement.Decl.TheoremRestore

/-! # Final reader hints in a checked model

Reducibility hints guide checking, while the public model reads a definition's signature
and value. Retargeting hints after checking preserves that model with the same valuation.
-/

namespace IxVM.Refinement.Decl.HintRestore

open Ix.Kernel

universe u

def info {md : Mode} (chosen : Key md → Option ReducibilityHint) : ConstantInfo md → ConstantInfo md
  | .defnInfo cv value old => .defnInfo cv value ((chosen cv.name).getD old)
  | ci => ci

def setHints {md : Mode} (chosen : Key md → Option ReducibilityHint) (env : Env md) : Env md :=
  ⟨env.consts.map (info chosen)⟩

variable {md : Mode} (chosen : Key md → Option ReducibilityHint)

theorem info_cv (ci : ConstantInfo md) : (info chosen ci).toConstantVal = ci.toConstantVal := by
  cases ci <;> rfl

theorem info_name (ci : ConstantInfo md) : (info chosen ci).name = ci.name := by
  cases ci <;> rfl

theorem info_nonDefinition {ci : ConstantInfo md}
    (kind : ∀ cv value hint, ci ≠ .defnInfo cv value hint) : info chosen ci = ci := by
  cases ci with
  | defnInfo cv value hint => exact (kind cv value hint rfl).elim
  | _ => rfl

theorem info_eq_back {ci out : ConstantInfo md} (same : info chosen ci = out)
    (kind : ∀ cv value hint, out ≠ .defnInfo cv value hint) : ci = out := by
  cases ci with
  | defnInfo cv value hint => exact (kind cv value _ same.symm).elim
  | _ => exact same

theorem info_definition {ci : ConstantInfo md} {cv : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint} (same : info chosen ci = .defnInfo cv value hint) :
    ∃ old, ci = .defnInfo cv value old := by
  cases ci with
  | defnInfo cv₀ value₀ old =>
    obtain ⟨rfl, rfl, _⟩ := ConstantInfo.defnInfo.inj same
    exact ⟨old, rfl⟩
  | _ => cases same

theorem find (env : Env md) (name : Key md) :
    (setHints chosen env).find? name = (env.find? name).map (info chosen) := by
  simp only [setHints, Env.find?, List.find?_map, Function.comp_def, info_name]

theorem found_original {env : Env md} {name : Key md} {ci : ConstantInfo md}
    (found : (setHints chosen env).find? name = some ci) :
    ∃ original, env.find? name = some original ∧ info chosen original = ci := by
  rw [find] at found
  exact Option.map_eq_some_iff.mp found

theorem find_unchanged {env : Env md} {name : Key md} {ci : ConstantInfo md}
    (kind : ∀ cv value hint, ci ≠ .defnInfo cv value hint) :
    (setHints chosen env).find? name = some ci ↔ env.find? name = some ci := by
  constructor
  · intro found
    obtain ⟨original, old, same⟩ := found_original chosen found
    rw [info_eq_back chosen same kind] at old
    exact old
  · intro found
    rw [find, found, Option.map_some, info_nonDefinition chosen kind]

theorem find_ind {env : Env md} {name : Key md} {cv : ConstantVal md} {caps : IndCaps md} :
    (setHints chosen env).find? name = some (.indInfo cv caps) ↔
      env.find? name = some (.indInfo cv caps) :=
  find_unchanged chosen (by intros; intro h; cases h)

theorem find_ctor {env : Env md} {name : Key md} {cv : ConstantVal md} {nP nF : Nat} :
    (setHints chosen env).find? name = some (.ctorInfo cv nP nF) ↔
      env.find? name = some (.ctorInfo cv nP nF) :=
  find_unchanged chosen (by intros; intro h; cases h)

theorem find_rec {env : Env md} {name : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} :
    (setHints chosen env).find? name = some (.recInfo cv mI rP rules) ↔
      env.find? name = some (.recInfo cv mI rP rules) :=
  find_unchanged chosen (by intros; intro h; cases h)

theorem find_defn_back {env : Env md} {name : Key md} {cv : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint} (found : (setHints chosen env).find? name = some (.defnInfo cv value hint)) :
    ∃ old, env.find? name = some (.defnInfo cv value old) := by
  obtain ⟨original, old, same⟩ := found_original chosen found
  obtain ⟨hint₀, originalEq⟩ := info_definition chosen same
  exact ⟨hint₀, by rw [originalEq] at old; exact old⟩

theorem findProj (env : Env md) (T : Key md) (i : Nat) :
    (setHints chosen env).findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [find]
  cases env.find? (projTableName T) with
  | none => rfl
  | some ci => cases ci <;> rfl

theorem names (env : Env md) :
    (setHints chosen env).consts.map (·.name) = env.consts.map (·.name) := by
  simp only [setHints, List.map_map, Function.comp_def, info_name]

variable {V : Type u} [SetTheory V]

theorem denotes_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Denotes cval (setHints chosen env) φ = Denotes cval env φ := by
  funext ρ e value
  apply propext
  constructor
  · apply TheoremRestore.denotes_transfer
    · intro name ci found
      obtain ⟨original, old, rfl⟩ := found_original chosen found
      exact ⟨original, old, congrArg ConstantVal.levelParams (info_cv chosen original).symm⟩
    · intro T i; exact (findProj chosen env T i).symm
  · apply TheoremRestore.denotes_transfer
    · intro name ci found
      exact ⟨info chosen ci, by rw [find, found]; rfl,
        congrArg ConstantVal.levelParams (info_cv chosen ci)⟩
    · exact findProj chosen env

theorem fits_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Fits cval (setHints chosen env) φ = Fits cval env φ := by
  funext ρ type values σ rest
  exact propext ⟨TheoremRestore.fits_transfer (denotes_eq chosen env cval φ),
    TheoremRestore.fits_transfer (denotes_eq chosen env cval φ).symm⟩

theorem denotesList_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    DenotesList cval (setHints chosen env) φ = DenotesList cval env φ := by
  funext ρ terms values
  exact propext ⟨TheoremRestore.denotesList_transfer (denotes_eq chosen env cval φ),
    TheoremRestore.denotesList_transfer (denotes_eq chosen env cval φ).symm⟩

/-- Final hint selection preserves the full public model with the same constant valuation. -/
def model {env : Env md} (M : Model V env) : Model V (setHints chosen env) where
  cval := M.cval
  mem := by
    intro ci member φ ρ
    obtain ⟨original, old, rfl⟩ := List.mem_map.mp member
    obtain ⟨A, typeRead, belongs⟩ := M.mem original old φ ρ
    refine ⟨A, ?_, ?_⟩
    · simpa only [info_cv, denotes_eq] using typeRead
    · simpa only [info_name] using belongs
  false_empty := by simpa only [denotes_eq] using M.false_empty
  eq_equality := by simpa only [denotes_eq] using M.eq_equality
  punit_unit := by simpa only [denotes_eq] using M.punit_unit
  defn_value := by
    intro cv value hint member φ ρ
    obtain ⟨original, old, same⟩ := List.mem_map.mp member
    obtain ⟨hint₀, originalEq⟩ := info_definition chosen same
    rw [originalEq] at old
    simpa only [denotes_eq] using M.defn_value cv value hint₀ old φ ρ
  cval_params := by
    intro name ci found φ ψ agree
    obtain ⟨original, old, rfl⟩ := found_original chosen found
    exact M.cval_params name original old φ ψ (by simpa only [info_cv] using agree)
  iota_rule := by
    simpa only [IotaLaw, IotaRule, find_rec, find_ctor, denotes_eq, fits_eq, denotesList_eq] using M.iota_rule
  unit_like := by
    simpa only [UnitLikeLaw, find_ind, denotes_eq, fits_eq] using M.unit_like
  proj_law := by
    simpa only [ProjLaw, findProj, find_ind, find_ctor, denotes_eq, fits_eq] using M.proj_law
  proj_type := by simpa only [ProjTypeLaw, findProj, denotes_eq] using M.proj_type
  eta_fn := by simpa only [EtaFnLaw, find_ind, find_ctor, find_rec, fits_eq] using M.eta_fn
  lit_ops := by
    obtain ⟨pred, arith, cmp⟩ := M.lit_ops
    refine ⟨?_, ?_, ?_⟩
    · intro cv value hint found
      obtain ⟨old, original⟩ := find_defn_back chosen found
      simpa only [denotes_eq] using pred cv value old original
    · intro name fn member cv value hint found
      obtain ⟨old, original⟩ := find_defn_back chosen found
      simpa only [denotes_eq] using arith name fn member cv value old original
    · intro name fn member cv value hint found
      obtain ⟨old, original⟩ := find_defn_back chosen found
      simpa only [denotes_eq] using cmp name fn member cv value old original
  nat_add := by
    intro cv value hint found
    obtain ⟨old, original⟩ := find_defn_back chosen found
    simpa only [denotes_eq] using M.nat_add cv value old original
  graded := by
    intro ci member φ ρ
    obtain ⟨original, old, rfl⟩ := List.mem_map.mp member
    have grade := M.graded original old φ ρ
    refine ⟨?_, ?_⟩
    · simpa only [info_cv, denotes_eq] using grade.1
    · intro cv value hint same
      obtain ⟨oldHint, originalEq⟩ := info_definition chosen same
      simpa only [denotes_eq] using grade.2 cv value oldHint originalEq

theorem model_cval {env : Env md} (M : Model V env) : (model chosen M).cval = M.cval := rfl

end IxVM.Refinement.Decl.HintRestore
