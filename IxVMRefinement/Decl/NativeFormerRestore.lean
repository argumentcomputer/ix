import IxVMRefinement.Decl.TheoremRestore
import IxC.Kernel.Verify.Level

/-! # Restoring a native former's declared type without projection capabilities

Indexed native families have neither eta nor unit-like capabilities and install no projection
table. Their declared type can be restored once its reading agrees with the checked type.
-/

namespace IxVM.Refinement.Decl.NativeFormerRestore

open Ix.Kernel

universe u

variable {md : Mode}

def info (cv : ConstantVal md) (caps : IndCaps md) (type : Expr md) (ci : ConstantInfo md) : ConstantInfo md :=
  if ci = .indInfo cv caps then .indInfo { cv with type } caps else ci

def environment (cv : ConstantVal md) (caps : IndCaps md) (type : Expr md) (env : Env md) : Env md :=
  ⟨env.consts.map (info cv caps type)⟩

variable (cv : ConstantVal md) (caps : IndCaps md) (type : Expr md)

theorem info_name (ci : ConstantInfo md) : (info cv caps type ci).name = ci.name := by
  unfold info
  split
  · next same => subst ci; rfl
  · rfl

theorem info_levels (ci : ConstantInfo md) :
    (info cv caps type ci).toConstantVal.levelParams = ci.toConstantVal.levelParams := by
  unfold info
  split
  · next same => subst ci; rfl
  · rfl

theorem info_eq_back {ci out : ConstantInfo md} (same : info cv caps type ci = out)
    (notInductive : ∀ val flags, out ≠ .indInfo val flags) : ci = out := by
  unfold info at same
  split at same
  · exact (notInductive _ _ same.symm).elim
  · exact same

theorem info_nonInductive {ci : ConstantInfo md}
    (kind : ∀ val flags, ci ≠ .indInfo val flags) : info cv caps type ci = ci := by
  rw [info, ite_eq_right (kind cv caps)]

theorem find (env : Env md) (name : Key md) :
    (environment cv caps type env).find? name = (env.find? name).map (info cv caps type) := by
  simp only [environment, Env.find?, List.find?_map, Function.comp_def, info_name]

theorem found_original {env : Env md} {name : Key md} {ci : ConstantInfo md}
    (found : (environment cv caps type env).find? name = some ci) :
    ∃ original, env.find? name = some original ∧ info cv caps type original = ci := by
  rw [find] at found
  exact Option.map_eq_some_iff.mp found

theorem find_unchanged {env : Env md} {name : Key md} {ci : ConstantInfo md}
    (kind : ∀ val flags, ci ≠ .indInfo val flags) :
    (environment cv caps type env).find? name = some ci ↔ env.find? name = some ci := by
  constructor
  · intro found
    obtain ⟨original, ho, hi⟩ := found_original cv caps type found
    rw [info_eq_back cv caps type hi kind] at ho
    exact ho
  · intro found
    rw [find, found, Option.map_some, info_nonInductive cv caps type kind]

theorem find_ctor {env : Env md} {name : Key md} {val : ConstantVal md} {nP nF : Nat} :
    (environment cv caps type env).find? name = some (.ctorInfo val nP nF) ↔
      env.find? name = some (.ctorInfo val nP nF) :=
  find_unchanged cv caps type (by intros; intro h; cases h)

theorem find_rec {env : Env md} {name : Key md} {val : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} :
    (environment cv caps type env).find? name = some (.recInfo val mI rP rules) ↔
      env.find? name = some (.recInfo val mI rP rules) :=
  find_unchanged cv caps type (by intros; intro h; cases h)

theorem find_defn {env : Env md} {name : Key md} {val : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint} :
    (environment cv caps type env).find? name = some (.defnInfo val value hint) ↔
      env.find? name = some (.defnInfo val value hint) :=
  find_unchanged cv caps type (by intros; intro h; cases h)

theorem find_ind_cases {env : Env md} {name : Key md} {val : ConstantVal md} {flags : IndCaps md}
    (found : (environment cv caps type env).find? name = some (.indInfo val flags)) :
    (name = cv.name ∧ val = { cv with type } ∧ flags = caps) ∨
      env.find? name = some (.indInfo val flags) := by
  obtain ⟨original, ho, hi⟩ := found_original cv caps type found
  by_cases changed : original = .indInfo cv caps
  · subst original
    simp only [info, ↓reduceIte] at hi
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hi
    refine Or.inl ⟨?_, rfl, rfl⟩
    have nameEq := List.find?_some (p := fun ci : ConstantInfo md => ci.name == name) ho
    exact (eq_of_beq nameEq).symm
  · simp only [info, ite_eq_right changed] at hi
    rw [hi] at ho
    exact Or.inr ho

theorem findProj (env : Env md) (T : Key md) (i : Nat) :
    (environment cv caps type env).findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [find]
  cases env.find? (projTableName T) with
  | none => rfl
  | some ci =>
    by_cases changed : ci = .indInfo cv caps
    · subst ci
      simp only [Option.map_some, info, ↓reduceIte]
    · simp only [Option.map_some, info, ite_eq_right changed]

variable {V : Type u} [SetTheory V]

theorem denotes_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Denotes cval (environment cv caps type env) φ = Denotes cval env φ := by
  funext ρ e value
  apply propext
  constructor
  · apply TheoremRestore.denotes_transfer
    · intro name ci found
      obtain ⟨original, ho, rfl⟩ := found_original cv caps type found
      exact ⟨original, ho, (info_levels cv caps type original).symm⟩
    · intro T i; exact (findProj cv caps type env T i).symm
  · apply TheoremRestore.denotes_transfer
    · intro name ci found
      exact ⟨info cv caps type ci, by rw [find, found]; rfl, info_levels cv caps type ci⟩
    · exact findProj cv caps type env

theorem fits_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Fits cval (environment cv caps type env) φ = Fits cval env φ := by
  funext ρ ty values σ residual
  exact propext ⟨TheoremRestore.fits_transfer (denotes_eq cv caps type env cval φ),
    TheoremRestore.fits_transfer (denotes_eq cv caps type env cval φ).symm⟩

theorem denotesList_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    DenotesList cval (environment cv caps type env) φ = DenotesList cval env φ := by
  funext ρ terms values
  exact propext ⟨TheoremRestore.denotesList_transfer (denotes_eq cv caps type env cval φ),
    TheoremRestore.denotesList_transfer (denotes_eq cv caps type env cval φ).symm⟩

/-- A concrete replacement reading restores the former without changing the valuation or any rule. -/
def model {env : Env md} (M : Model V env)
    (notEta : caps.eta = false) (notUnit : caps.unitlike = false)
    (noTable : ∀ i, env.findProj? cv.name i = none)
    (typeRead : ∀ φ ρ A, Denotes M.cval env φ ρ cv.type A → Denotes M.cval env φ ρ type A)
    (typeGraded : ∀ φ ρ, GradedBy (Denotes M.cval env φ) ρ type) :
    Model V (environment cv caps type env) where
  cval := M.cval
  mem := by
    intro ci mem φ ρ
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp mem
    obtain ⟨A, ha, hm⟩ := M.mem original ho φ ρ
    by_cases changed : original = .indInfo cv caps
    · subst original
      refine ⟨A, ?_, ?_⟩
      · simpa only [info, ↓reduceIte, denotes_eq] using typeRead φ ρ A ha
      · simpa only [info, ↓reduceIte] using hm
    · refine ⟨A, ?_, ?_⟩
      · simpa only [info, ite_eq_right changed, denotes_eq] using ha
      · simpa only [info, ite_eq_right changed] using hm
  false_empty := by simpa only [denotes_eq] using M.false_empty
  eq_equality := by simpa only [denotes_eq] using M.eq_equality
  punit_unit := by simpa only [denotes_eq] using M.punit_unit
  defn_value := by
    intro val value hint mem φ ρ
    obtain ⟨original, ho, hi⟩ := List.mem_map.mp mem
    have same := info_eq_back cv caps type hi (by intros; intro h; cases h)
    subst original
    simpa only [denotes_eq] using M.defn_value val value hint ho φ ρ
  cval_params := by
    intro name ci found φ ψ agree
    obtain ⟨original, ho, rfl⟩ := found_original cv caps type found
    exact M.cval_params name original ho φ ψ (by simpa only [info_levels] using agree)
  iota_rule := by
    simpa only [IotaLaw, IotaRule, find_rec, find_ctor, denotes_eq, fits_eq, denotesList_eq] using M.iota_rule
  unit_like := by
    intro T val flags found unit
    rcases find_ind_cases cv caps type found with ⟨_, rfl, rfl⟩ | original
    · rw [notUnit] at unit; cases unit
    · simpa only [denotes_eq, fits_eq] using M.unit_like T val flags original unit
  proj_law := by
    intro T i entry val flags table found
    rcases find_ind_cases cv caps type found with ⟨rfl, rfl, rfl⟩ | original
    · rw [findProj, noTable] at table; cases table
    · simpa only [find_ctor, denotes_eq, fits_eq] using
        M.proj_law T i entry val flags (by rw [findProj] at table; exact table) original
  proj_type := by
    simpa only [ProjTypeLaw, findProj, denotes_eq] using M.proj_type
  eta_fn := by
    intro T val flags C found eta
    rcases find_ind_cases cv caps type found with ⟨_, rfl, rfl⟩ | original
    · rw [notEta] at eta; cases eta
    · simpa only [find_ctor, find_rec, fits_eq] using M.eta_fn T val flags C original eta
  lit_ops := by simpa only [NatLitLaw, find_defn, denotes_eq] using M.lit_ops
  nat_add := by simpa only [NatAddLaw, find_defn, denotes_eq] using M.nat_add
  graded := by
    intro ci mem φ ρ
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp mem
    have gr := M.graded original ho φ ρ
    refine ⟨?_, ?_⟩
    · by_cases changed : original = .indInfo cv caps
      · subst original
        simpa only [info, ↓reduceIte, denotes_eq] using typeGraded φ ρ
      · simpa only [info, ite_eq_right changed, denotes_eq] using gr.1
    · intro val value hint same
      have originalEq := info_eq_back cv caps type same (by intros; intro h; cases h)
      simpa only [denotes_eq] using gr.2 val value hint originalEq

/-- A definition whose checked value is the telescope supplies the replacement reading directly. -/
def aliasModel {env : Env md} (M : Model V env)
    (notEta : caps.eta = false) (notUnit : caps.unitlike = false)
    (noTable : ∀ i, env.findProj? cv.name i = none)
    {alias : ConstantVal md} {hint : ReducibilityHint}
    (found : env.find? alias.name = some (.defnInfo alias cv.type hint)) :
    Model V (environment cv caps (.const alias.name (alias.levelParams.map .param)) env) := by
  apply model cv caps _ M notEta notUnit noTable
  · intro φ ρ A read
    have aliasRead := M.defn_value alias cv.type hint (List.mem_of_find?_eq_some found) φ ρ
    obtain rfl := Denotes.functional read aliasRead
    have denoted := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ) found
      (show (alias.levelParams.map Level.param).length = alias.levelParams.length by simp)
    simpa only [ConstantInfo.toConstantVal, Level.substFn_param_self] using denoted
  · intro _ _; trivial

end IxVM.Refinement.Decl.NativeFormerRestore
