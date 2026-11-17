import IxC.Kernel.Rules.Inversion
import IxC.Kernel.Verify.Shift
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.EnvWF

/-! # Reduction keeps a term free of loose bound variables

The rules relate terms of any scope: nothing in `Red` asks its subject to be closed. But no rule
introduces a loose bound variable into a term that has none, provided the stored terms δ and ι
unfold have none (`BClosedStore`, which `EnvWF` gives):

* `red_bclosed`: a reduct of a term with no loose bound variable has none.
* `infer_full_bclosed`: a term inferred at the full grade has none (the full grade certifies
  every argument and every domain, and opens every binder at a free variable). The
  equality-reflection rule reads its right side through such an inference.

Both are one mutual structural recursion over the rules, as `Red.rigid` is.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Rules

section
variable {md : Mode}

/-- **The stored terms δ and ι unfold have no loose bound variable**: a stored definition's value
and a stored recursor's rule right-hand sides. -/
structure BClosedStore (env : Env md) : Prop where
  defn : ∀ {k : Key md} {cv : ConstantVal md} {v : Expr md} {h : ReducibilityHint},
    env.find? k = some (.defnInfo cv v h) → v.looseBVarsBounded 0 = true
  rhs : ∀ {k : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)},
    env.find? k = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules,
      rl.rhs.looseBVarsBounded 0 = true

/-- The syntactic well-formedness of the store gives it. -/
theorem BClosedStore.of_wf {env : Env md} (h : EnvWF env) : BClosedStore env where
  defn := fun hf => ((h _ (List.mem_of_find?_eq_some hf)).2.2.2.2.1 _ _ _ rfl).2.2.2
  rhs := fun hf rl hrl =>
    ((h _ (List.mem_of_find?_eq_some hf)).2.2.2.2.2.1 _ _ _ _ rfl rl hrl).2.2.2.1

/-- A stored constant's type has no loose bound variable. -/
theorem envWF_type_bclosed {env : Env md} (h : EnvWF env) {k : Key md} {c : ConstantInfo md}
    (hf : env.find? k = some c) : c.toConstantVal.type.looseBVarsBounded 0 = true :=
  (h _ (List.mem_of_find?_eq_some hf)).2.2.2.1

/-! ## Loose bound variables, structurally -/

theorem lbb_app_iff {f a : Expr md} {k : Nat} :
    (Expr.app f a).looseBVarsBounded k = true ↔
      f.looseBVarsBounded k = true ∧ a.looseBVarsBounded k = true := by
  simp [Expr.looseBVarsBounded]

theorem lbb_lam_iff {ty b : Expr md} {m : BinderMeta} {k : Nat} :
    (Expr.lam ty b m).looseBVarsBounded k = true ↔
      ty.looseBVarsBounded k = true ∧ b.looseBVarsBounded (k + 1) = true := by
  simp [Expr.looseBVarsBounded]

theorem lbb_forallE_iff {ty b : Expr md} {m : BinderMeta} {k : Nat} :
    (Expr.forallE ty b m).looseBVarsBounded k = true ↔
      ty.looseBVarsBounded k = true ∧ b.looseBVarsBounded (k + 1) = true := by
  simp [Expr.looseBVarsBounded]

theorem lbb_mkAppN (k : Nat) : ∀ (args : List (Expr md)) (f : Expr md),
    (Expr.mkAppN f args).looseBVarsBounded k =
      (f.looseBVarsBounded k && args.all (·.looseBVarsBounded k))
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).looseBVarsBounded k = _
    rw [lbb_mkAppN k as (.app f a)]
    simp only [Expr.looseBVarsBounded, List.all_cons, Bool.and_assoc]

theorem lbb_getAppArgs {k : Nat} {e : Expr md} (h : e.looseBVarsBounded k = true) :
    ∀ a ∈ e.getAppArgs, a.looseBVarsBounded k = true := by
  induction e with
  | app f a ihf _ =>
    have h' := lbb_app_iff.mp h
    intro x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h'.1 x hx
    · exact h'.2
  | _ => intro x hx; simp [Expr.getAppArgs] at hx

theorem lbb_getD_of_lt {l : List (Expr md)} {n : Nat} {dflt : Expr md}
    (hl : ∀ a ∈ l, a.looseBVarsBounded 0 = true) (hn : n < l.length) :
    (l.getD n dflt).looseBVarsBounded 0 = true := by
  have hmem : l.getD n dflt ∈ l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    exact List.getElem_mem hn
  exact hl _ hmem

theorem lbb_ilp (ks : List LevelParam) (us : List Level) {k : Nat} {e : Expr md}
    (h : e.looseBVarsBounded k = true) :
    (e.instantiateLevelParams ks us).looseBVarsBounded k = true := by
  induction e generalizing k with
  | bvar i => exact h
  | app f a ihf iha =>
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b m iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded] at h ⊢
    exact ih h
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl

/-- **Instantiating a binder with a term bounded by its depth keeps the bound.** -/
theorem lbb_instantiate1_le {v e : Expr md} {k : Nat} (he : e.looseBVarsBounded (k + 1) = true)
    (hv : v.looseBVarsBounded k = true) : (e.instantiate1 v k).looseBVarsBounded k = true := by
  induction e generalizing k with
  | bvar i =>
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at he
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp [Expr.looseBVarsBounded] <;> omega
  | app f a ihf iha =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam ty b m iht ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1 hv, ihb he.2 (Expr.looseBVarsBounded_mono (Nat.le_succ k) hv)⟩
  | forallE ty b m iht ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨iht he.1 hv, ihb he.2 (Expr.looseBVarsBounded_mono (Nat.le_succ k) hv)⟩
  | letE ty w b m iht ihw ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨⟨iht he.1.1 hv, ihw he.1.2 hv⟩,
      ihb he.2 (Expr.looseBVarsBounded_mono (Nat.le_succ k) hv)⟩
  | proj s i e ih =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded] at he ⊢
    exact ih he hv
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl

/-- **Instantiation reflects the bound**: if instantiating binder `k` leaves nothing loose at
`k`, nothing was loose at `k + 1`. -/
theorem lbb_of_instantiate1 {v e : Expr md} {k : Nat}
    (h : (e.instantiate1 v k).looseBVarsBounded k = true) : e.looseBVarsBounded (k + 1) = true := by
  induction e generalizing k with
  | bvar i =>
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    simp only [Expr.instantiate1] at h
    by_cases h1 : i = k
    · omega
    · rw [if_neg h1] at h
      by_cases h2 : i > k
      · rw [if_pos h2] at h
        simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
        omega
      · omega
  | app f a ihf iha =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m iht ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty w b m iht ihw ihb =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihw h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    simp only [Expr.instantiate1, Expr.looseBVarsBounded] at h ⊢
    exact ih h
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | lit => rfl

/-! ## The terms the literal and arithmetic rules build -/

theorem lbb_natLitToConstructor (n : Nat) :
    (natLitToConstructor (md := md) n).looseBVarsBounded 0 = true := by
  cases n <;> rfl

theorem lbb_strLitToConstructor (s : String) :
    (strLitToConstructor (md := md) s).looseBVarsBounded 0 = true := by
  unfold strLitToConstructor
  generalize s.toList = l
  induction l with
  | nil => rfl
  | cons c cs ih => simpa [Expr.looseBVarsBounded] using ih

theorem lbb_natOpResult {c : Key md} {a b : Nat} {r : Expr md} (h : natOpResult c a b = some r) :
    r.looseBVarsBounded 0 = true := by
  unfold natOpResult at h
  repeat' split at h
  all_goals (cases h <;> rfl)

theorem lbb_unfoldDefinition {env : Env md} (hS : BClosedStore env) {e e' : Expr md}
    (hu : unfoldDefinition env e = some e') (he : e.looseBVarsBounded 0 = true) :
    e'.looseBVarsBounded 0 = true := by
  unfold unfoldDefinition at hu
  split at hu
  · split at hu
    · split at hu
      · cases hu
        rw [lbb_mkAppN, Bool.and_eq_true, List.all_eq_true]
        exact ⟨lbb_ilp _ _ (hS.defn (by assumption)), fun x hx => lbb_getAppArgs he x hx⟩
      · cases hu
    · cases hu
  · cases hu

end

/-! ## The rules -/

mutual

/-- **A reduct of a term with no loose bound variable has none.** -/
theorem red_bclosed {md : Mode} {env : Env md} :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → BClosedStore env →
      e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true
  | _, _, _, .refl, _, he => he
  | _, _, _, .trans h₁ h₂, hS, he => red_bclosed h₂ hS (red_bclosed h₁ hS he)
  | _, _, _, .appFn h, hS, he =>
    lbb_app_iff.mpr ⟨red_bclosed h hS (lbb_app_iff.mp he).1, (lbb_app_iff.mp he).2⟩
  | _, _, _, .projArg h, hS, he => by
    simp only [Expr.looseBVarsBounded] at he ⊢
    exact red_bclosed h hS he
  | _, _, _, .appArg h, hS, he =>
    lbb_app_iff.mpr ⟨(lbb_app_iff.mp he).1, red_bclosed h hS (lbb_app_iff.mp he).2⟩
  | _, _, _, .betaGate _, _, he =>
    lbb_instantiate1_le (k := 0) (lbb_lam_iff.mp (lbb_app_iff.mp he).1).2 (lbb_app_iff.mp he).2
  | _, _, _, .beta _ _, _, he =>
    lbb_instantiate1_le (k := 0) (lbb_lam_iff.mp (lbb_app_iff.mp he).1).2 (lbb_app_iff.mp he).2
  | _, _, _, .delta hu, hS, he => lbb_unfoldDefinition hS hu he
  | _, _, _, .deltaThm _ _ _ hv .., _, _ => lbb_ilp _ _ hv
  | _, _, _, .eqProof _ _ _ _ _ _ _ _ hb .., _, _ => infer_full_bclosed hb rfl
  | _, _, _, .natLit _, _, _ => lbb_natLitToConstructor _
  | _, _, _, .natZeroLit _, _, _ => rfl
  | _, _, _, .strLit _, _, _ => lbb_strLitToConstructor _
  | _, _, _, .natSucc .., _, _ => rfl
  | _, _, _, .natOp _ _ _ _ _ _ hr, _, _ => lbb_natOpResult hr
  | _, _, _, .natAddSucc _ _, _, he => by
    have hb := (lbb_app_iff.mp (lbb_app_iff.mp he).1).2
    refine lbb_app_iff.mpr ⟨rfl, ?_⟩
    unfold natAddLit
    split
    · exact hb
    · exact lbb_app_iff.mpr ⟨lbb_app_iff.mpr ⟨rfl, hb⟩, rfl⟩
  | _, _, _, .natAddZero .., _, he => (lbb_app_iff.mp (lbb_app_iff.mp he).1).2
  | _, _, _, .proj _ _ hi hlen .., _, he => by
    simp only [Expr.looseBVarsBounded] at he
    exact lbb_getD_of_lt (lbb_getAppArgs he) (by omega)
  | _, _, _, .iota _ hc hlen _ hmaj _ _ hrl .., hS, he => by
    have hargs := lbb_getAppArgs he
    have hmaj' := red_bclosed hmaj hS (lbb_getD_of_lt hargs (by omega))
    rw [lbb_mkAppN, Bool.and_eq_true, List.all_eq_true]
    refine ⟨lbb_ilp _ _ (hS.rhs hc _ (List.mem_of_find?_eq_some hrl)), fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hargs x (List.mem_of_mem_take hx)
    · exact lbb_getAppArgs hmaj' x (List.mem_of_mem_drop hx)
  | _, _, _, .rescueK _ _ _ _ _ _ _ _ _ _ _ _ hb .., _, _ => hb
  | _, _, _, .rescueEta _ _ _ _ _ _ _ _ _ _ _ _ _ hb .., _, _ => hb
  | _, _, _, .rescueAnd _ _ _ _ _ _ _ _ _ _ _ _ hb .., _, _ => hb

/-- **A term inferred at the full grade has no loose bound variable.** -/
theorem infer_full_bclosed {md : Mode} {env : Env md} :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      e.looseBVarsBounded 0 = true
  | _, _, _, _, .sort, _ => rfl
  | _, _, _, _, .fvar _, _ => rfl
  | _, _, _, _, .const _ _ _, _ => rfl
  | _, _, _, _, .natLit _, _ => rfl
  | _, _, _, _, .strLit _, _ => rfl
  | _, _, _, _, .forallE hs _ hbs _ _, hg =>
    lbb_forallE_iff.mpr ⟨infer_full_bclosed hs hg,
      lbb_of_instantiate1 (k := 0) (infer_full_bclosed hbs hg)⟩
  | _, _, _, _, .lam hs _ hbt _ _ _ _, hg =>
    lbb_lam_iff.mpr ⟨infer_full_bclosed (hs hg) rfl,
      lbb_of_instantiate1 (k := 0) (infer_full_bclosed hbt hg)⟩
  | _, _, _, _, .app htf _ hta _, hg =>
    lbb_app_iff.mpr ⟨infer_full_bclosed htf hg, infer_full_bclosed hta hg⟩
  | _, _, _, _, .appSkip .., hg => nomatch hg
  | _, _, _, _, .proj htpe .., hg => by
    simp only [Expr.looseBVarsBounded]
    exact infer_full_bclosed htpe hg

theorem red_bclosed_defEq {md : Mode} {env : Env md} :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → True
  | _, _, _, _ => trivial

theorem red_bclosed_certs {md : Mode} {env : Env md} :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → True
  | _, _, _, _, _ => trivial

theorem red_bclosed_defEqList {md : Mode} {env : Env md} :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → True
  | _, _, _, _ => trivial

theorem red_bclosed_etaProjCerts {md : Mode} {env : Env md} :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → True
  | _, _, _, _, _, _, _, _ => trivial

end

end IxVM.Refinement.Decl
