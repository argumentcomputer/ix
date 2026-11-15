import IxC.Kernel.Model.Restrict

/-! # Restoring theorem entries in a checked model

Selected opaque definitions become theorem entries with the same signature and checked value.
The public model keeps every type reading, definition law, recursor rule, and projection law.
-/

namespace IxVM.Refinement.Decl.TheoremRestore

open Ix.Kernel

universe u

/-- Restore selected opaque definitions to their reader's theorem kind. -/
def info {md : Mode} (selected : Key md → Bool) : ConstantInfo md → ConstantInfo md
  | .defnInfo cv value .opaque => if selected cv.name then .thmInfo cv value else .defnInfo cv value .opaque
  | ci => ci

def environment {md : Mode} (selected : Key md → Bool) (env : Env md) : Env md :=
  ⟨env.consts.map (info selected)⟩

variable {md : Mode} (selected : Key md → Bool)

theorem info_cv (ci : ConstantInfo md) : (info selected ci).toConstantVal = ci.toConstantVal := by
  cases ci with
  | defnInfo cv value hint =>
    cases hint with
    | «opaque» => by_cases chosen : selected cv.name = true <;> simp [info, chosen]
    | «abbrev» | regular => rfl
  | _ => rfl

theorem info_name (ci : ConstantInfo md) : (info selected ci).name = ci.name := by
  cases ci with
  | defnInfo cv value hint =>
    cases hint with
    | «opaque» => by_cases chosen : selected cv.name = true <;> simp [info, chosen]
    | «abbrev» | regular => rfl
  | _ => rfl

theorem info_eq_back {ci out : ConstantInfo md} (same : info selected ci = out)
    (notTheorem : ∀ cv value, out ≠ .thmInfo cv value) : ci = out := by
  cases ci with
  | defnInfo cv value hint =>
    cases hint with
    | «opaque» =>
      simp only [info] at same
      split at same
      · exact (notTheorem cv value same.symm).elim
      · exact same
    | «abbrev» | regular => exact same
  | _ => exact same

theorem info_nonValue {ci : ConstantInfo md}
    (notDefinition : ∀ cv value hint, ci ≠ .defnInfo cv value hint) : info selected ci = ci := by
  cases ci with
  | defnInfo cv value hint => exact (notDefinition cv value hint rfl).elim
  | _ => rfl

theorem find (env : Env md) (n : Key md) :
    (environment selected env).find? n = (env.find? n).map (info selected) := by
  simp only [environment, Env.find?, List.find?_map, Function.comp_def, info_name]

theorem found_original {env : Env md} {n : Key md} {ci : ConstantInfo md}
    (found : (environment selected env).find? n = some ci) :
    ∃ original, env.find? n = some original ∧ info selected original = ci := by
  rw [find] at found
  exact Option.map_eq_some_iff.mp found

theorem find_unchanged {env : Env md} {n : Key md} {ci : ConstantInfo md}
    (notDefinition : ∀ cv value hint, ci ≠ .defnInfo cv value hint)
    (notTheorem : ∀ cv value, ci ≠ .thmInfo cv value) :
    (environment selected env).find? n = some ci ↔ env.find? n = some ci := by
  constructor
  · intro found
    obtain ⟨original, ho, hi⟩ := found_original selected found
    rw [info_eq_back selected hi notTheorem] at ho
    exact ho
  · intro found
    rw [find, found, Option.map_some, info_nonValue selected notDefinition]

theorem find_ind {env : Env md} {n : Key md} {cv : ConstantVal md} {caps : IndCaps md} :
    (environment selected env).find? n = some (.indInfo cv caps) ↔
      env.find? n = some (.indInfo cv caps) :=
  find_unchanged selected (by intros; intro h; cases h) (by intros; intro h; cases h)

theorem find_ctor {env : Env md} {n : Key md} {cv : ConstantVal md} {nP nF : Nat} :
    (environment selected env).find? n = some (.ctorInfo cv nP nF) ↔
      env.find? n = some (.ctorInfo cv nP nF) :=
  find_unchanged selected (by intros; intro h; cases h) (by intros; intro h; cases h)

theorem find_rec {env : Env md} {n : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} :
    (environment selected env).find? n = some (.recInfo cv mI rP rules) ↔
      env.find? n = some (.recInfo cv mI rP rules) :=
  find_unchanged selected (by intros; intro h; cases h) (by intros; intro h; cases h)

theorem find_defn_back {env : Env md} {n : Key md} {cv : ConstantVal md}
    {value : Expr md} {hint : ReducibilityHint}
    (found : (environment selected env).find? n = some (.defnInfo cv value hint)) :
    env.find? n = some (.defnInfo cv value hint) := by
  obtain ⟨original, ho, hi⟩ := found_original selected found
  rw [info_eq_back selected hi (by intros; intro h; cases h)] at ho
  exact ho

theorem findProj (env : Env md) (T : Key md) (i : Nat) :
    (environment selected env).findProj? T i = env.findProj? T i := by
  unfold Env.findProj?
  rw [find]
  cases env.find? (projTableName T) with
  | none => rfl
  | some ci =>
    cases ci with
    | defnInfo cv value hint =>
      cases hint with
      | «opaque» => by_cases chosen : selected cv.name = true <;> simp [info, chosen]
      | «abbrev» | regular => rfl
    | _ => rfl

variable {V : Type u} [SetTheory V]

private theorem denotes_transfer {source target : Env md}
    (hcv : ∀ n ci, source.find? n = some ci →
      ∃ other, target.find? n = some other ∧ other.toConstantVal = ci.toConstantVal)
    (hproj : ∀ T i, target.findProj? T i = source.findProj? T i)
    {cval : Key md → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {e : Expr md} {value : V}
    (h : Denotes cval source φ ρ e value) : Denotes cval target φ ρ e value := by
  induction h with
  | bvar => exact .bvar
  | sort => exact .sort
  | @const ρ n us ci found arity =>
    obtain ⟨other, hother, same⟩ := hcv n ci found
    have ho := Denotes.const (cval := cval) (φ := φ) (ρ := ρ) hother
      (show us.length = other.toConstantVal.levelParams.length from by rw [same]; exact arity)
    simpa only [same] using ho
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ hproof ihA ihF => exact .lam ihA ihF hproof
  | pi _ _ hproof ihA ihB => exact .pi ihA ihB hproof
  | proj_table found _ ih => exact .proj_table (by rw [hproj]; exact found) ih
  | proj_fst found _ ih => exact .proj_fst (by rw [hproj]; exact found) ih
  | proj_snd found _ ih => exact .proj_snd (by rw [hproj]; exact found) ih
  | natLit _ ih => exact .natLit ih
  | strLit _ ih => exact .strLit ih

theorem denotes_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Denotes cval (environment selected env) φ = Denotes cval env φ := by
  funext ρ e value
  apply propext
  constructor
  · apply denotes_transfer
    · intro n ci found
      obtain ⟨original, ho, rfl⟩ := found_original selected found
      exact ⟨original, ho, (info_cv selected original).symm⟩
    · intro T i; exact (findProj selected env T i).symm
  · apply denotes_transfer
    · intro n ci found
      exact ⟨info selected ci, by rw [find, found]; rfl, info_cv selected ci⟩
    · exact findProj selected env

private theorem fits_transfer {source target : Env md}
    {cval : Key md → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    (hd : Denotes cval source φ = Denotes cval target φ)
    {ρ σ : BVarIdx → V} {ty rest : Expr md} {values : List V}
    (h : Fits cval source φ ρ ty values σ rest) : Fits cval target φ ρ ty values σ rest := by
  induction h with
  | nil => exact .nil
  | cons denoted member _ ih => exact .cons (by rw [← hd]; exact denoted) member ih

theorem fits_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    Fits cval (environment selected env) φ = Fits cval env φ := by
  funext ρ ty values σ rest
  exact propext ⟨fits_transfer (denotes_eq selected env cval φ),
    fits_transfer (denotes_eq selected env cval φ).symm⟩

private theorem denotesList_transfer {source target : Env md}
    {cval : Key md → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    (hd : Denotes cval source φ = Denotes cval target φ)
    {ρ : BVarIdx → V} {es : List (Expr md)} {vs : List V}
    (h : DenotesList cval source φ ρ es vs) : DenotesList cval target φ ρ es vs := by
  induction h with
  | nil => exact .nil
  | cons denoted _ ih => exact .cons (by rw [← hd]; exact denoted) ih

theorem denotesList_eq (env : Env md) (cval : Key md → (LevelParam → Nat) → V) (φ : LevelParam → Nat) :
    DenotesList cval (environment selected env) φ = DenotesList cval env φ := by
  funext ρ es vs
  exact propext ⟨denotesList_transfer (denotes_eq selected env cval φ),
    denotesList_transfer (denotes_eq selected env cval φ).symm⟩

/-- Restoring theorem kinds preserves the public model with the same constant valuation. -/
def model {env : Env md} (M : Model V env) : Model V (environment selected env) where
  cval := M.cval
  mem := by
    intro ci mem φ ρ
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp mem
    obtain ⟨T, ht, hm⟩ := M.mem original ho φ ρ
    refine ⟨T, ?_, ?_⟩
    · simpa only [info_cv, denotes_eq] using ht
    · simpa only [info_name] using hm
  false_empty := by simpa only [denotes_eq] using M.false_empty
  eq_equality := by simpa only [denotes_eq] using M.eq_equality
  punit_unit := by simpa only [denotes_eq] using M.punit_unit
  defn_value := by
    intro cv value hint mem φ ρ
    obtain ⟨original, ho, hi⟩ := List.mem_map.mp mem
    have same := info_eq_back selected hi (by intros; intro h; cases h)
    subst original
    simpa only [denotes_eq] using M.defn_value cv value hint ho φ ρ
  cval_params := by
    intro n ci found φ ψ agree
    obtain ⟨original, ho, rfl⟩ := found_original selected found
    exact M.cval_params n original ho φ ψ (by simpa only [info_cv] using agree)
  iota_rule := by
    simpa only [IotaLaw, IotaRule, find_rec, find_ctor, denotes_eq, fits_eq, denotesList_eq] using M.iota_rule
  unit_like := by
    simpa only [UnitLikeLaw, find_ind, denotes_eq, fits_eq] using M.unit_like
  proj_law := by
    simpa only [ProjLaw, findProj, find_ind, find_ctor, denotes_eq, fits_eq] using M.proj_law
  proj_type := by
    simpa only [ProjTypeLaw, findProj, denotes_eq] using M.proj_type
  eta_fn := by
    simpa only [EtaFnLaw, find_ind, find_ctor, find_rec, fits_eq] using M.eta_fn
  lit_ops := by
    obtain ⟨pred, arith, cmp⟩ := M.lit_ops
    refine ⟨?_, ?_, ?_⟩
    · intro cv value hint found
      simpa only [denotes_eq] using pred cv value hint (find_defn_back selected found)
    · intro c f mem cv value hint found
      simpa only [denotes_eq] using arith c f mem cv value hint (find_defn_back selected found)
    · intro c f mem cv value hint found
      simpa only [denotes_eq] using cmp c f mem cv value hint (find_defn_back selected found)
  nat_add := by
    intro cv value hint found
    simpa only [denotes_eq] using M.nat_add cv value hint (find_defn_back selected found)
  graded := by
    intro ci mem φ ρ
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp mem
    have gr := M.graded original ho φ ρ
    refine ⟨?_, ?_⟩
    · simpa only [info_cv, denotes_eq] using gr.1
    · intro cv value hint same
      have original := info_eq_back selected same (by intros; intro h; cases h)
      simpa only [denotes_eq] using gr.2 cv value hint original

end IxVM.Refinement.Decl.TheoremRestore
