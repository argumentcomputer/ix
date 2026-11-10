module

public import IxC.Kernel.CoreDefs

@[expose] public section

/-!
# The transport kit: free-variable renaming and environment extension (lane l5)

What the rules' transport (`Rules/Transport.lean`) reads of its two moves:

* **`Expr.renFV ρ`**, the renaming of free variables, annotations included. Every
  helper the rules name commutes with it: the structural ones outright
  (`instantiate1`, spines, `piResidual`, `instSpine`, `instantiateList`, the
  literal readings, `isProofFast`, `isUnitLikeTy`); `abstract1` when `ρ` is
  injective; the scope check when `ρ` is strictly increasing. The helpers that
  read stored terms commute when the stored terms are closed (`StoreClosed`).
* **`EnvExt env env'`**, an extension: every lookup `env` answers, `env'` answers
  alike, and the projection table of a structure `env` stores is the one `env`
  has. Every guard the rules read is monotone along it (`unfoldDefinition`, the
  literal and operation guards, `isProofFast`, `isUnitLikeTy`, the tower and
  recursor slots) and the fabricated projections are unchanged. A fresh cons
  that is not the table of a stored structure is an extension (`EnvExt.cons`).
-/

namespace Ix.Kernel

/-- **Rename free variables** by `ρ`, in annotations too. -/
def Expr.renFV (ρ : Nat → Nat) : Expr md → Expr md
  | .bvar i => .bvar i
  | .fvar i ty => .fvar (ρ i) (renFV ρ ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (renFV ρ f) (renFV ρ a)
  | .lam ty b m => .lam (renFV ρ ty) (renFV ρ b) m
  | .forallE ty b m => .forallE (renFV ρ ty) (renFV ρ b) m
  | .letE ty v b l => .letE (renFV ρ ty) (renFV ρ v) (renFV ρ b) l
  | .lit l => .lit l
  | .proj s i e => .proj s i (renFV ρ e)

namespace Expr

variable {ρ : Nat → Nat}

theorem renFV_of_id (h : ∀ i, ρ i = i) : ∀ e : Expr md, e.renFV ρ = e := by
  intro e
  induction e <;> simp_all [renFV]

theorem renFV_of_not_hasFvar : ∀ {e : Expr md}, e.hasFvar = false → e.renFV ρ = e := by
  intro e
  induction e <;> simp_all [renFV, hasFvar]

theorem renFV_instantiateLevelParams_closed (ks : List LevelParam) (us : List Level) :
    ∀ {e : Expr md}, e.hasFvar = false →
      (e.instantiateLevelParams ks us).renFV ρ = e.instantiateLevelParams ks us := by
  intro e
  induction e <;> simp_all [renFV, hasFvar, instantiateLevelParams]

theorem renFV_instantiate1 (v : Expr md) :
    ∀ (e : Expr md) (k : Nat),
      (e.instantiate1 v k).renFV ρ = (e.renFV ρ).instantiate1 (v.renFV ρ) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    by_cases h1 : i = k <;> by_cases h2 : i > k <;> simp [instantiate1, renFV, h1, h2]
  | fvar => intro k; rfl
  | sort => intro k; rfl
  | const => intro k; rfl
  | lit => intro k; rfl
  | app f a ihf iha => intro k; simp only [instantiate1, renFV, ihf, iha]
  | lam ty b m iht ihb => intro k; simp only [instantiate1, renFV, iht, ihb]
  | forallE ty b m iht ihb => intro k; simp only [instantiate1, renFV, iht, ihb]
  | letE ty v' b l iht ihv ihb => intro k; simp only [instantiate1, renFV, iht, ihv, ihb]
  | proj s i e ih => intro k; simp only [instantiate1, renFV, ih]

theorem renFV_abstract1 (hinj : ∀ {i j : Nat}, ρ i = ρ j → i = j) (D : Nat) :
    ∀ (e : Expr md) (k : Nat),
      (e.abstract1 D k).renFV ρ = (e.renFV ρ).abstract1 (ρ D) k := by
  intro e
  induction e with
  | bvar => intro k; rfl
  | fvar i ty _ =>
    intro k
    by_cases h : i = D
    · subst h
      simp [abstract1, renFV]
    · have h' : ρ i ≠ ρ D := fun e => h (hinj e)
      simp [abstract1, renFV, h, h']
  | sort => intro k; rfl
  | const => intro k; rfl
  | lit => intro k; rfl
  | app f a ihf iha => intro k; simp only [abstract1, renFV, ihf, iha]
  | lam ty b m iht ihb => intro k; simp only [abstract1, renFV, iht, ihb]
  | forallE ty b m iht ihb => intro k; simp only [abstract1, renFV, iht, ihb]
  | letE ty v b l iht ihv ihb => intro k; simp only [abstract1, renFV, iht, ihv, ihb]
  | proj s i e ih => intro k; simp only [abstract1, renFV, ih]

theorem getAppFn_renFV : ∀ e : Expr md, (e.renFV ρ).getAppFn = e.getAppFn.renFV ρ := by
  intro e
  induction e with
  | app f a ihf _ => exact ihf
  | _ => rfl

theorem getAppFn_renFV_const {e : Expr md} {c : Key md} {us : List Level}
    (h : e.getAppFn = .const c us) : (e.renFV ρ).getAppFn = .const c us := by
  rw [getAppFn_renFV, h]
  rfl

theorem getAppArgs_renFV : ∀ e : Expr md, (e.renFV ρ).getAppArgs = e.getAppArgs.map (renFV ρ) := by
  intro e
  induction e with
  | app f a ihf _ =>
    show (f.renFV ρ).getAppArgs ++ [a.renFV ρ] = (f.getAppArgs ++ [a]).map (renFV ρ)
    rw [ihf, List.map_append]
    rfl
  | _ => rfl

theorem renFV_mkAppN : ∀ (as : List (Expr md)) (f : Expr md),
    (Expr.mkAppN f as).renFV ρ = Expr.mkAppN (f.renFV ρ) (as.map (renFV ρ)) := by
  intro as
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; exact ih (.app f a)

theorem lamPw_renFV (e : Expr md) : (e.renFV ρ).lamPw = e.lamPw := by
  cases e <;> rfl

theorem numArgs_renFV : ∀ e : Expr md, (e.renFV ρ).numArgs = e.numArgs := by
  intro e
  induction e with
  | app f a ihf _ => show (f.renFV ρ).numArgs + 1 = f.numArgs + 1; rw [ihf]
  | _ => rfl

theorem looseBVarsBounded_renFV :
    ∀ (e : Expr md) (k : Nat), (e.renFV ρ).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;> simp_all [renFV, looseBVarsBounded]

theorem fvarLeaves_renFV :
    ∀ e : Expr md, (e.renFV ρ).fvarLeaves = e.fvarLeaves.map (fun l => (ρ l.1, l.2.renFV ρ)) := by
  intro e
  induction e <;> simp_all [renFV, fvarLeaves]

/-- The scope check survives a strictly increasing renaming into a scope that
holds the renamed indices. -/
theorem wscopedB_renFV (hmono : ∀ {i j : Nat}, i < j → ρ i < ρ j) :
    ∀ (e : Expr md) {D E : Nat}, (∀ i, i < D → ρ i < E) →
      e.wscopedB D = true → (e.renFV ρ).wscopedB E = true := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro D E hDE h
    simp only [wscopedB, renFV, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨hDE idx h.1, ih (fun i hi => hmono hi) h.2⟩
  | app f a ihf iha =>
    intro D E hDE h
    simp only [wscopedB, renFV, Bool.and_eq_true] at h ⊢
    exact ⟨ihf hDE h.1, iha hDE h.2⟩
  | lam ty b m iht ihb =>
    intro D E hDE h
    simp only [wscopedB, renFV, Bool.and_eq_true] at h ⊢
    exact ⟨iht hDE h.1, ihb hDE h.2⟩
  | forallE ty b m iht ihb =>
    intro D E hDE h
    simp only [wscopedB, renFV, Bool.and_eq_true] at h ⊢
    exact ⟨iht hDE h.1, ihb hDE h.2⟩
  | letE ty v b l iht ihv ihb =>
    intro D E hDE h
    simp only [wscopedB, renFV, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht hDE h.1.1, ihv hDE h.1.2⟩, ihb hDE h.2⟩
  | proj s i e ih =>
    intro D E hDE h
    simp only [wscopedB, renFV] at h ⊢
    exact ih hDE h
  | bvar | sort | const | lit => intro _ _ _ _; simp [wscopedB, renFV]

theorem piResidual_renFV :
    ∀ (args : List (Expr md)) (T r : Expr md), piResidual T args = some r →
      piResidual (T.renFV ρ) (args.map (renFV ρ)) = some (r.renFV ρ) := by
  intro args
  induction args with
  | nil =>
    intro T r h
    simp only [piResidual, Option.some.injEq] at h
    subst h
    simp [piResidual]
  | cons a as ih =>
    intro T r h
    cases T with
    | forallE ty b m =>
      simp only [piResidual, renFV, List.map_cons] at h ⊢
      rw [← renFV_instantiate1 a b 0]
      exact ih _ _ h
    | _ => simp [piResidual] at h

theorem renFV_instSpine :
    ∀ (as : List (Expr md)) (t : Nat) (e : Expr md),
      (Expr.instSpine as t e).renFV ρ = Expr.instSpine (as.map (renFV ρ)) t (e.renFV ρ) := by
  intro as
  induction as with
  | nil => intro t e; rfl
  | cons a as ih =>
    intro t e
    simp only [instSpine, List.map_cons]
    rw [ih, renFV_instantiate1]

theorem renFV_instantiateList :
    ∀ (n : Nat) (vs : List (Expr md)), vs.length ≤ n → ∀ (e : Expr md) (d : Nat),
      (e.instantiateList vs d).renFV ρ = (e.renFV ρ).instantiateList (vs.map (renFV ρ)) d := by
  intro n
  induction n with
  | zero =>
    intro vs hvs
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    intro e
    induction e <;> intro d <;> simp_all [instantiateList, renFV]
  | succ n ihn =>
    intro vs hvs e
    induction e with
    | bvar j =>
      intro d
      by_cases h1 : j < d
      · simp [instantiateList, renFV, h1]
      · by_cases h2 : j - d < vs.length
        · have hlen : (vs.take (j - d)).length ≤ n := by
            rw [List.length_take]; omega
          have key := ihn (vs.take (j - d)) hlen vs[j - d] d
          simp [instantiateList, renFV, h1, h2, key]
        · simp [instantiateList, renFV, h1, h2]
    | fvar => intro d; simp [instantiateList, renFV]
    | sort => intro d; simp [instantiateList, renFV]
    | const => intro d; simp [instantiateList, renFV]
    | lit => intro d; simp [instantiateList, renFV]
    | app f a ihf iha => intro d; simp only [instantiateList, renFV, ihf, iha]
    | lam ty b m iht ihb => intro d; simp only [instantiateList, renFV, iht, ihb]
    | forallE ty b m iht ihb => intro d; simp only [instantiateList, renFV, iht, ihb]
    | letE ty v b l iht ihv ihb => intro d; simp only [instantiateList, renFV, iht, ihv, ihb]
    | proj s i e ih => intro d; simp only [instantiateList, renFV, ih]

theorem renFV_natLitToConstructor (n : Nat) :
    (natLitToConstructor n : Expr md).renFV ρ = natLitToConstructor n := by
  cases n <;> rfl

theorem renFV_strLitToConstructor (s : String) :
    (strLitToConstructor s : Expr md).renFV ρ = strLitToConstructor s := by
  unfold strLitToConstructor
  simp only [renFV]
  congr 1
  generalize s.toList = l
  induction l with
  | nil => rfl
  | cons c cs ih => simp only [List.foldr, renFV, ih]

theorem natOpResult_map_renFV (c : Key md) (a b : Nat) :
    (natOpResult c a b).map (renFV ρ) = natOpResult c a b := by
  simp only [natOpResult, apply_ite (Option.map (renFV ρ)), Option.map_some, Option.map_none,
    renFV]

theorem renFV_of_natOpResult {c : Key md} {a b : Nat} {r : Expr md}
    (h : natOpResult c a b = some r) : r.renFV ρ = r := by
  have := natOpResult_map_renFV (ρ := ρ) c a b
  rw [h] at this
  exact Option.some.inj this

theorem fvarLeaves_sub_renFV {a b : Expr md} (h : ∀ l ∈ a.fvarLeaves, l ∈ b.fvarLeaves) :
    ∀ l ∈ (a.renFV ρ).fvarLeaves, l ∈ (b.renFV ρ).fvarLeaves := by
  rw [fvarLeaves_renFV, fvarLeaves_renFV]
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  exact List.mem_map.mpr ⟨l', h l' hl', rfl⟩

theorem fvarLeaves_all_renFV {a b : Expr md}
    (h : a.fvarLeaves.all (fun l => b.fvarLeaves.contains l) = true) :
    (a.renFV ρ).fvarLeaves.all (fun l => (b.renFV ρ).fvarLeaves.contains l) = true := by
  rw [List.all_eq_true] at h ⊢
  intro l hl
  have hsub : ∀ l ∈ a.fvarLeaves, l ∈ b.fvarLeaves := fun l hl =>
    List.contains_iff_mem.mp (h l hl)
  exact List.contains_iff_mem.mpr (fvarLeaves_sub_renFV hsub l hl)

theorem getD_map_renFV :
    ∀ (l : List (Expr md)) (n : Nat),
      (l.map (renFV ρ)).getD n (.bvar 0) = (l.getD n (.bvar 0)).renFV ρ
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getD_map_renFV l n

end Expr


/-! ## The prop-ness readers ignore the renaming -/

open Expr

theorem peelNeverPis_renFV {ρ : Nat → Nat} :
    ∀ (n : Nat) (e : Expr md), (e.renFV ρ).peelNeverPis n = (e.peelNeverPis n).map (renFV ρ)
  | 0, _ => rfl
  | k + 1, e => by
    cases e with
    | forallE ty b m =>
      by_cases hm : m.pw.isNever = true
      · simp [Expr.peelNeverPis, renFV, hm, peelNeverPis_renFV k b]
      · simp [Expr.peelNeverPis, renFV, hm]
    | _ => rfl

theorem residualPW_map_renFV {ρ : Nat → Nat} (o : Option (Expr md)) :
    residualPW (o.map (renFV ρ)) = residualPW o := by
  rcases o with _ | e
  · rfl
  · cases e <;> rfl

theorem headTypePW_renFV {ρ : Nat → Nat} (f : Key md → Option (ConstantInfo md)) (e : Expr md)
    (n : Nat) : headTypePW f (e.renFV ρ) n = headTypePW f e n := by
  cases e with
  | fvar i ty =>
    show residualPW ((ty.renFV ρ).peelNeverPis n) = residualPW (ty.peelNeverPis n)
    rw [peelNeverPis_renFV, residualPW_map_renFV]
  | _ => rfl

theorem typeSortPW_other {f : Key md → Option (ConstantInfo md)} {T : Expr md}
    (h1 : ∀ ty b m, T ≠ .forallE ty b m) (h2 : ∀ u, T ≠ .sort u) :
    typeSortPW f T = headTypePW f T.getAppFn T.numArgs := by
  cases T with
  | forallE ty b m => exact absurd rfl (h1 ty b m)
  | sort u => exact absurd rfl (h2 u)
  | _ => rfl

theorem proofPW_other {f : Key md → Option (ConstantInfo md)} {a : Expr md}
    (h : ∀ ty b m, a ≠ .lam ty b m) : proofPW f a = headProofPW f a.getAppFn := by
  cases a with
  | lam ty b m => exact absurd rfl (h ty b m)
  | _ => rfl

theorem typeSortPW_renFV {ρ : Nat → Nat} (f : Key md → Option (ConstantInfo md)) (T : Expr md) :
    typeSortPW f (T.renFV ρ) = typeSortPW f T := by
  by_cases h1 : ∃ ty b m, T = .forallE ty b m
  · obtain ⟨ty, b, m, rfl⟩ := h1; rfl
  by_cases h2 : ∃ u, T = .sort u
  · obtain ⟨u, rfl⟩ := h2; rfl
  have h1' : ∀ ty b m, T ≠ .forallE ty b m := fun ty b m e => h1 ⟨ty, b, m, e⟩
  have h2' : ∀ u, T ≠ .sort u := fun u e => h2 ⟨u, e⟩
  have h1r : ∀ ty b m, T.renFV ρ ≠ .forallE ty b m := by
    intro ty b m e
    cases T with
    | forallE ty' b' m' => exact h1' ty' b' m' rfl
    | _ => exact nomatch e
  have h2r : ∀ u, T.renFV ρ ≠ .sort u := by
    intro u e
    cases T with
    | sort u' => exact h2' u' rfl
    | _ => exact nomatch e
  rw [typeSortPW_other h1r h2r, typeSortPW_other h1' h2', getAppFn_renFV, numArgs_renFV,
    headTypePW_renFV]

theorem headProofPW_renFV {ρ : Nat → Nat} (f : Key md → Option (ConstantInfo md)) (e : Expr md) :
    headProofPW f (e.renFV ρ) = headProofPW f e := by
  cases e with
  | fvar i ty => exact typeSortPW_renFV f ty
  | _ => rfl

theorem isProofFast_renFV {ρ : Nat → Nat} (f : Key md → Option (ConstantInfo md)) (a : Expr md) :
    isProofFast f (a.renFV ρ) = isProofFast f a := by
  unfold isProofFast
  have : proofPW f (a.renFV ρ) = proofPW f a := by
    by_cases h : ∃ ty b m, a = .lam ty b m
    · obtain ⟨ty, b, m, rfl⟩ := h; rfl
    have h' : ∀ ty b m, a ≠ .lam ty b m := fun ty b m e => h ⟨ty, b, m, e⟩
    have hr : ∀ ty b m, a.renFV ρ ≠ .lam ty b m := by
      intro ty b m e
      cases a with
      | lam ty' b' m' => exact h' ty' b' m' rfl
      | _ => exact nomatch e
    rw [proofPW_other hr, proofPW_other h', getAppFn_renFV, headProofPW_renFV]
  rw [this]

theorem isUnitLikeTy_renFV {ρ : Nat → Nat} (env : Env md) (e : Expr md) :
    isUnitLikeTy env (e.renFV ρ) = isUnitLikeTy env e := by
  cases e <;> rfl

theorem rawNatLit?_renFV {ρ : Nat → Nat} (e : Expr md) : rawNatLit? (e.renFV ρ) = rawNatLit? e := by
  cases e <;> rfl

theorem etaProjs_renFV {ρ : Nat → Nat} (env : Env md) (T : Key md) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    etaProjs env T us (targs.map (renFV ρ)) (b.renFV ρ) nF =
      (etaProjs env T us targs b nF).map (renFV ρ) := by
  unfold etaProjs
  split
  · simp [renFV]
  · simp only [List.map_map]
    congr 1
    funext j
    simp only [Function.comp, renFV_mkAppN, List.map_append, List.map_cons, List.map_nil]
    rfl

/-! ## Stored terms closed -/

/-- **The stored terms the rules read are closed**: the stored types, a
definition's value, a recursor's rule right-hand sides and nested pins, and the
projection tables' bodies. -/
structure StoreClosed (env : Env md) : Prop where
  type : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c →
    c.toConstantVal.type.hasFvar = false
  defn : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md} {h : ReducibilityHint},
    env.find? k = some (.defnInfo cv v h) → v.hasFvar = false
  rhs : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
    env.find? k = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.rhs.hasFvar = false ∧
      ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, p.hasFvar = false
  proj : ∀ {sn : Key md} {i : Nat} {entry : ProjEntry md},
    env.findProj? sn i = some entry → entry.body.hasFvar = false

/-! ## Environment extension -/

/-- **`env'` extends `env`**: lookups `env` answers are answered alike, and the
projection table of a structure `env` stores is `env`'s (so the tower slots, and
the fabricated projections, read the same). -/
structure EnvExt (env env' : Env md) : Prop where
  find : ∀ {k : Key md} {c : ConstantInfo md}, env.find? k = some c → env'.find? k = some c
  tables : ∀ {T : Key md} {cv : ConstantVal md} {caps : IndCaps md},
    env.find? T = some (.indInfo cv caps) →
      env'.find? (projTableName T) = env.find? (projTableName T)

namespace EnvExt

variable {env env' env'' : Env md}

theorem refl (env : Env md) : EnvExt env env := ⟨id, fun _ => rfl⟩

theorem trans (h₁ : EnvExt env env') (h₂ : EnvExt env' env'') : EnvExt env env'' :=
  ⟨fun h => h₂.find (h₁.find h), fun hT => by rw [h₂.tables (h₁.find hT), h₁.tables hT]⟩

theorem find?_cons_ne {c : ConstantInfo md} {k : Key md} (h : c.name ≠ k) :
    (⟨c :: env.consts⟩ : Env md).find? k = env.find? k := by
  simp only [Env.find?, List.find?_cons]
  have : (c.name == k) = false := by simpa using h
  rw [this]

/-- **A fresh cons that is not the table of a stored structure extends.** -/
theorem cons {c : ConstantInfo md} (hfresh : env.find? c.name = none)
    (hnt : ∀ {T : Key md} {cv : ConstantVal md} {caps : IndCaps md},
      env.find? T = some (.indInfo cv caps) → c.name ≠ projTableName T) :
    EnvExt env ⟨c :: env.consts⟩ where
  find := fun {k} {c'} h => by
    have hne : c.name ≠ k := fun e => by
      rw [e, h] at hfresh
      exact nomatch hfresh
    rw [find?_cons_ne hne]
    exact h
  tables := fun hT => find?_cons_ne (hnt hT)

theorem find?_append_of_fresh {new : List (ConstantInfo md)} {k : Key md}
    (h : ∀ c ∈ new, c.name ≠ k) : (⟨new ++ env.consts⟩ : Env md).find? k = env.find? k := by
  simp only [Env.find?, List.find?_append]
  have hn : new.find? (·.name == k) = none := by
    rw [List.find?_eq_none]
    intro c hc
    simpa using h c hc
  rw [hn]
  rfl

/-- **A declaration step extends**: the new constants are fresh, and none is the
projection table of a structure already stored (a table is installed with its
structure). -/
theorem append {new : List (ConstantInfo md)}
    (hfresh : ∀ c ∈ new, env.find? c.name = none)
    (hnt : ∀ c ∈ new, ∀ {T : Key md} {cv : ConstantVal md} {caps : IndCaps md},
      env.find? T = some (.indInfo cv caps) → c.name ≠ projTableName T) :
    EnvExt env ⟨new ++ env.consts⟩ where
  find := fun {k} {_} h => by
    rw [find?_append_of_fresh (fun c hc e => by
      have := hfresh c hc
      rw [e, h] at this
      exact nomatch this)]
    exact h
  tables := fun hT => find?_append_of_fresh (fun c hc => hnt c hc hT)

theorem findProj? (h : EnvExt env env') {sn : Key md} {i : Nat} {entry : ProjEntry md}
    (hp : env.findProj? sn i = some entry) : env'.findProj? sn i = some entry := by
  unfold Env.findProj? at hp ⊢
  cases hf : env.find? (projTableName sn) with
  | none => rw [hf] at hp; exact nomatch hp
  | some c => rw [h.find hf]; rw [hf] at hp; exact hp

theorem findProj?_eq (h : EnvExt env env') {T : Key md} {cv : ConstantVal md}
    {caps : IndCaps md} (hT : env.find? T = some (.indInfo cv caps)) (j : Nat) :
    env'.findProj? T j = env.findProj? T j := by
  unfold Env.findProj?
  rw [h.tables hT]

theorem towerSlotsAll_eq (h : EnvExt env env') {T : Key md} {cv : ConstantVal md}
    {caps : IndCaps md} (hT : env.find? T = some (.indInfo cv caps)) (nF : Nat) :
    towerSlotsAll env' T nF = towerSlotsAll env T nF := by
  unfold towerSlotsAll
  simp only [h.findProj?_eq hT]

theorem etaProjs_eq (h : EnvExt env env') {T : Key md} {cv : ConstantVal md}
    {caps : IndCaps md} (hT : env.find? T = some (.indInfo cv caps)) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    etaProjs env' T us targs b nF = etaProjs env T us targs b nF := by
  unfold etaProjs
  rw [h.towerSlotsAll_eq hT]

theorem etaFabArgsE_eq (h : EnvExt env env') {T : Key md} {cv : ConstantVal md}
    {caps : IndCaps md} (hT : env.find? T = some (.indInfo cv caps)) (us : List Level)
    (targs : List (Expr md)) (b : Expr md) (nF : Nat) :
    etaFabArgsE env' T us targs b nF = etaFabArgsE env T us targs b nF := by
  unfold etaFabArgsE
  rw [h.etaProjs_eq hT]

/-- A guard reading a lookup, false on an absent constant, is monotone. -/
theorem opt_mono (h : EnvExt env env') {p : Option (ConstantInfo md) → Bool} {k : Key md}
    (hk : p (env.find? k) = true) (hp : p none = false) : p (env'.find? k) = true := by
  cases hf : env.find? k with
  | none => rw [hf, hp] at hk; exact nomatch hk
  | some c => rw [h.find hf]; rw [hf] at hk; exact hk

theorem recSlotsAll_mono (h : EnvExt env env') {T : Key md} {nF : Nat}
    (hs : recSlotsAll env T nF = true) : recSlotsAll env' T nF = true := by
  unfold recSlotsAll at hs ⊢
  rw [List.all_eq_true] at hs ⊢
  intro j hj
  have hj' := hs j hj
  cases hf : env.find? (projFnName T j) with
  | none => rw [hf] at hj'; exact nomatch hj'
  | some c => rw [h.find hf]; rw [hf] at hj'; exact hj'

theorem natLitSupported_mono (h : EnvExt env env') (hs : natLitSupported env = true) :
    natLitSupported env' = true := by
  unfold natLitSupported at hs ⊢
  simp only [Bool.and_eq_true] at hs ⊢
  exact ⟨⟨h.opt_mono (p := natIndOk) hs.1.1 rfl, h.opt_mono (p := natZeroOk) hs.1.2 rfl⟩,
    h.opt_mono (p := natSuccOk) hs.2 rfl⟩

theorem strLitSupported_mono (h : EnvExt env env') (hs : strLitSupported env = true) :
    strLitSupported env' = true := by
  unfold strLitSupported at hs ⊢
  simp only [Bool.and_eq_true] at hs ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  exact ⟨⟨⟨⟨⟨⟨⟨h.natLitSupported_mono hn, h.opt_mono (p := stringTyOk) h1 rfl⟩,
    h.opt_mono (p := stringOfListTyOk) h2 rfl⟩, h.opt_mono (p := listTyOk) h3 rfl⟩,
    h.opt_mono (p := listNilTyOk) h4 rfl⟩, h.opt_mono (p := listConsTyOk) h5 rfl⟩,
    h.opt_mono (p := charTyOk) h6 rfl⟩, h.opt_mono (p := charOfNatTyOk) h7 rfl⟩

theorem natOpStored_mono (h : EnvExt env env') {c : Key md} (hs : natOpStored env c = true) :
    natOpStored env' c = true := by
  unfold natOpStored at hs ⊢
  cases hf : env.find? c with
  | none => rw [hf] at hs; exact nomatch hs
  | some ci => rw [h.find hf]; rw [hf] at hs; exact hs

theorem unfoldDefinition_mono (h : EnvExt env env') {e e' : Expr md}
    (hu : unfoldDefinition env e = some e') : unfoldDefinition env' e = some e' := by
  unfold unfoldDefinition at hu ⊢
  split at hu
  · rename_i n _ _
    cases hf : env.find? n with
    | none => rw [hf] at hu; exact nomatch hu
    | some c => rw [h.find hf]; rw [hf] at hu; exact hu
  · exact nomatch hu

theorem isUnitLikeTy_mono (h : EnvExt env env') {e : Expr md} (hs : isUnitLikeTy env e = true) :
    isUnitLikeTy env' e = true := by
  cases e with
  | const c us =>
    unfold isUnitLikeTy at hs ⊢
    simp only [Bool.and_eq_true] at hs ⊢
    obtain ⟨⟨hc, h1⟩, h2⟩ := hs
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · cases hf : env.find? punitName with
      | none => rw [hf] at h1; exact nomatch h1
      | some ci => rw [h.find hf]; rw [hf] at h1; exact h1
    · cases hf : env.find? punitRecName with
      | none => rw [hf] at h2; exact nomatch h2
      | some ci => rw [h.find hf]; rw [hf] at h2; exact h2
  | _ => exact nomatch hs

/-! ### The prop-ness readers are monotone -/

theorem headTypePW_mono (h : EnvExt env env') {e : Expr md} {n : Nat} {pw : PropWhen}
    (hs : headTypePW env.find? e n = some pw) : headTypePW env'.find? e n = some pw := by
  cases e with
  | const I us =>
    unfold headTypePW at hs ⊢
    try dsimp only at hs ⊢
    cases hf : env.find? I with
    | none => rw [hf] at hs; exact nomatch hs
    | some c => rw [h.find hf]; rw [hf] at hs; exact hs
  | fvar => exact hs
  | _ => exact nomatch hs

theorem typeSortPW_mono (h : EnvExt env env') {T : Expr md} {pw : PropWhen}
    (hs : typeSortPW env.find? T = some pw) : typeSortPW env'.find? T = some pw := by
  by_cases h1 : ∃ ty b m, T = .forallE ty b m
  · obtain ⟨ty, b, m, rfl⟩ := h1; exact hs
  by_cases h2 : ∃ u, T = .sort u
  · obtain ⟨u, rfl⟩ := h2; exact hs
  have h1' : ∀ ty b m, T ≠ .forallE ty b m := fun ty b m e => h1 ⟨ty, b, m, e⟩
  have h2' : ∀ u, T ≠ .sort u := fun u e => h2 ⟨u, e⟩
  rw [typeSortPW_other h1' h2'] at hs ⊢
  exact h.headTypePW_mono hs

theorem headProofPW_mono (h : EnvExt env env') {e : Expr md} {pw : PropWhen}
    (hs : headProofPW env.find? e = some pw) : headProofPW env'.find? e = some pw := by
  cases e with
  | const c us =>
    unfold headProofPW at hs ⊢
    try dsimp only at hs ⊢
    cases hf : env.find? c with
    | none => rw [hf] at hs; exact nomatch hs
    | some ci =>
      rw [h.find hf]; rw [hf] at hs
      by_cases htw : ci.isTowerEntry = true
      · simp [htw] at hs
      · by_cases hl : us.length = ci.toConstantVal.levelParams.length
        · simp only [htw, hl, if_true, if_false, Bool.false_eq_true] at hs ⊢
          rcases ht : typeSortPW env.find? ci.toConstantVal.type with _ | pw'
          · rw [ht] at hs; exact nomatch hs
          · rw [h.typeSortPW_mono ht]; rw [ht] at hs; exact hs
        · simp [htw, hl] at hs
  | fvar i ty => exact h.typeSortPW_mono hs
  | _ => exact hs

theorem isProofFast_mono (h : EnvExt env env') {a : Expr md}
    (hs : isProofFast env.find? a = true) : isProofFast env'.find? a = true := by
  unfold isProofFast at hs ⊢
  have key : ∀ pw, proofPW env.find? a = some pw → proofPW env'.find? a = some pw := by
    intro pw hp
    by_cases hl : ∃ ty b m, a = .lam ty b m
    · obtain ⟨ty, b, m, rfl⟩ := hl; exact hp
    have hl' : ∀ ty b m, a ≠ .lam ty b m := fun ty b m e => hl ⟨ty, b, m, e⟩
    rw [proofPW_other hl'] at hp ⊢
    exact h.headProofPW_mono hp
  rcases hp : proofPW env.find? a with _ | pw
  · rw [hp] at hs; exact nomatch hs
  · rw [key pw hp]; rw [hp] at hs; exact hs

end EnvExt

end Ix.Kernel
