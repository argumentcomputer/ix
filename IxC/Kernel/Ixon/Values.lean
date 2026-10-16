import IxC.Kernel.MainTheorem
import IxC.Kernel.Model.Denotes
import IxC.Kernel.Verify.Cached.MainC
import IxC.Kernel.Verify.Cached.Reference

/-! # Stored definitions denote their constants

The kernel's public `Model` states types only. Its internal invariant
`EnvModelM` also keeps `defn_reads` (`Model/Annot/EnvModelM.lean`,
`AcvalDefnInst` in `Model/Annot/Laws.lean`): the reading of every stored
definition's value is that constant's own leaf. Read through the kernel's
bridge from the internal reading to the public denotation
(`Model.Denotes_of_denoteMeta`), this gives a model of the accepted
environment in which every stored definition's value denotes the constant
(`checkDecls_model_defn_values`).

The value is the stored one, i.e. the checker's annotation of the declared
value (binder regimes computed, `let` reduced). Theorems and opaques keep
no such equation: their values are opaque to reduction and the invariant
records none (upstream's design, `AcvalDefnInst`'s docstring).

**The strong model** (step 7.2). The public clauses below are read off one
witness of the internal invariant, `StrongModel`, so they are about one
interpretation; a public model and a value model chosen separately would
not say that. The strong model exists for every reference accept
(`AcceptsRef.strongModel`, by the pure soundness walk), hence for every
accept of the executed fold (`checkDecls_strongModel`) and at both entries
(`Ix.LeanIngress.checkSource_strongModel`,
`Ix.Kernel.Admission.checkBytes_strongModel`). Its public clauses
(`ValueClauses`): definitions denote their values, and a stored constant's
value reads only its own level parameters. A fired recursor rule keeps its
internal law at the same witness (`StrongModel.rec_rule`), and the rule's
right-hand side has its public reading (`StrongModel.rec_rhs`). -/

namespace Ix.Kernel.Cached

open Ix.Kernel Ix.Kernel.Model

universe w

private theorem fvarsBelow_zero_of_not_hasFvar :
    ∀ {e : Expr md}, e.hasFvar = false → Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- **Model existence with definition values.** Every environment the fold
accepts has a model in which every stored definition's value denotes the
constant, at every level assignment and variable environment. -/
theorem checkDecls_model_defn_values (V : Type w) [SetTheory V] (ev : Evidences md)
    (ds : Array (Declaration md)) (env : Env md)
    (accepted : Cached.checkDecls .verified ev ds = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  refine ⟨Model.ofEnvModelM m, fun cv value hint hmem φ ρ => ?_⟩
  have hr := m.defn_reads φ cv value ⟨hint, hmem⟩
  have hv := ((m.base2.wf _ hmem).2.2.2.2.1 cv value hint rfl)
  have hb := Denotes_of_denoteMeta (V := V) m.base2.cval_closedL 0 value hr
    (fvarsBelow_zero_of_not_hasFvar hv.1) hv.2.2.2 ρ
    ⟨m.base2.acval_wellDenoted _ φ ρ, m.acval_validV _ φ ρ⟩
  rw [Expr.closeN_of_hasFvar _ 0 0 hv.1, interp_cvalOf m.base2.cval_closedL] at hb
  exact hb

/-! ## The strong model (step 7.2) -/

/-- **The public value clauses** of a model: every stored definition's value
denotes the constant, and a stored constant's value depends on the level
assignment only through its own level parameters. -/
def ValueClauses {V : Type w} [SetTheory V] {env : Env md} (M : Ix.Kernel.Model V env) : Prop :=
  (∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ)) ∧
  (∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂)

/-- **The strong model** of `env`: one witness of the fold's internal
invariant at `.verified`. Every clause below is about its public `model`. -/
structure StrongModel (V : Type w) [SetTheory V] (env : Env md) where
  internal : Model.EnvModelM V .verified env

namespace StrongModel

variable {V : Type w} [SetTheory V] {env : Env md}

/-- The public model of the strong model. -/
noncomputable def model (m : StrongModel V env) : Ix.Kernel.Model V env :=
  Model.ofEnvModelM m.internal

theorem model_cval (m : StrongModel V env) : m.model.cval = cvalOf m.internal.base2.acval := rfl

/-- **Definition values**: every stored definition's value denotes the
constant. -/
theorem defn_value (m : StrongModel V env) {cv : ConstantVal md} {value : Expr md}
    {hint : ReducibilityHint} (hmem : ConstantInfo.defnInfo cv value hint ∈ env.consts)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes m.model.cval env φ ρ value (m.model.cval cv.name φ) := by
  have hr := m.internal.defn_reads φ cv value ⟨hint, hmem⟩
  have hv := (m.internal.base2.wf _ hmem).2.2.2.2.1 cv value hint rfl
  have hb := Denotes_of_denoteMeta (V := V) m.internal.base2.cval_closedL 0 value hr
    (fvarsBelow_zero_of_not_hasFvar hv.1) hv.2.2.2 ρ
    ⟨m.internal.base2.acval_wellDenoted _ φ ρ, m.internal.acval_validV _ φ ρ⟩
  rw [Expr.closeN_of_hasFvar _ 0 0 hv.1, interp_cvalOf m.internal.base2.cval_closedL] at hb
  exact hb

/-- **Level-parameter irrelevance**: a stored constant's value depends on
the level assignment only through its own level parameters. -/
theorem cval_params (m : StrongModel V env) {n : Key md} {ci : ConstantInfo md}
    (h : env.find? n = some ci) {φ₁ φ₂ : LevelParam → Nat}
    (agree : ∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) :
    m.model.cval n φ₁ = m.model.cval n φ₂ := by
  rw [model_cval]
  unfold cvalOf
  rw [m.internal.base2.acval_params n ci h φ₁ φ₂ agree]

/-- The public value clauses hold of the strong model's public model. -/
theorem valueClauses (m : StrongModel V env) : ValueClauses m.model :=
  ⟨fun _ _ _ hmem φ ρ => m.defn_value hmem φ ρ, fun _ _ h _ _ agree => m.cval_params h agree⟩

/-- **A fired recursor rule's law**, at the strong model's own witness. -/
theorem rec_rule (m : StrongModel V env) (φ : LevelParam → Nat) {n : Key md}
    {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (h : env.find? n = some (.recInfo cv mI rP rules)) {rl : RecRule md} (hrl : rl ∈ rules)
    (fires : RecRule.fire rl ≠ .inert) : RecRuleLaw m.internal.base2 φ n cv mI rP rl :=
  m.internal.rec_rules φ n cv mI rP rules h rl hrl fires

/-- **The public reading of a fired rule's right-hand side**, at every
instantiation: the internal reading the rule's law is stated over is graded,
and denotes publicly what it interprets to. -/
theorem rec_rhs (m : StrongModel V env) (φ : LevelParam → Nat) {n : Key md}
    {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (h : env.find? n = some (.recInfo cv mI rP rules)) {rl : RecRule md} (hrl : rl ∈ rules)
    (fires : RecRule.fire rl ≠ .inert) (us : List Level) (hlen : us.length = cv.levelParams.length) :
    ∃ Ra : Semantics.AnnotTerm,
      denoteMeta m.internal.base2.acval env φ 0
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) = some Ra ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
      ∀ ρ : BVarIdx → V, Denotes m.model.cval env φ ρ
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) (Semantics.interp V ρ Ra) := by
  obtain ⟨Ra, hread, hgraded, -⟩ := (m.rec_rule φ h hrl fires).2 us hlen
  have hwf := (m.internal.base2.wf _ (Semantics.Env.find?_mem h)).2.2.2.2.2.1 cv mI rP rules rfl rl hrl
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact hwf.1
  have hlb : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  refine ⟨Ra, hread, hgraded, fun ρ => ?_⟩
  have hb := Denotes_of_denoteMeta (V := V) m.internal.base2.cval_closedL 0 _ hread
    (fvarsBelow_zero_of_not_hasFvar hnf) hlb ρ (hgraded ρ)
  rw [Expr.closeN_of_hasFvar _ 0 0 hnf] at hb
  exact hb

end StrongModel

variable {ev : Evidences md} {env : Env md}

/-- **A reference accept has a strong model** (the pure soundness walk,
`Ix.Kernel.Model.checkDeclsPure_sound_of`). -/
theorem AcceptsRef.strongModel (V : Type w) [SetTheory V] {ds : List (Declaration md)}
    (h : AcceptsRef .verified ev ds env) : Nonempty (StrongModel V env) := by
  obtain ⟨_, hF⟩ := h
  obtain ⟨m⟩ := checkDeclsPure_sound_of (V := V) rfl hF
  exact ⟨⟨m⟩⟩

/-- **Model existence with the value clauses**, at the reference level. -/
theorem AcceptsRef.model_values (V : Type w) [SetTheory V] {ds : List (Declaration md)}
    (h : AcceptsRef .verified ev ds env) : ∃ M : Ix.Kernel.Model V env, ValueClauses M := by
  obtain ⟨m⟩ := h.strongModel V
  exact ⟨m.model, m.valueClauses⟩

/-- **No proof of `False`**, at the reference level. -/
theorem AcceptsRef.no_proof_of_False (V : Type w) [SetTheory V] {ds : List (Declaration md)}
    (h : AcceptsRef .verified ev ds env) :
    ∀ c ∈ env.consts, c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨_, hF⟩ := h
  exact no_proof_of_False_pure V rfl hF

/-- **An accept of the executed fold has a strong model**, through its
reference accept (`checkDecls_refines_ref`). -/
theorem checkDecls_strongModel (V : Type w) [SetTheory V] {ds : Array (Declaration md)}
    (h : Cached.checkDecls .verified ev ds = .ok env) : Nonempty (StrongModel V env) :=
  (checkDecls_refines_ref V rfl h).strongModel V

/-- **Model existence with the value clauses**, for the executed fold. -/
theorem checkDecls_model_values (V : Type w) [SetTheory V] {ds : Array (Declaration md)}
    (h : Cached.checkDecls .verified ev ds = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ValueClauses M :=
  (checkDecls_refines_ref V rfl h).model_values V

end Ix.Kernel.Cached
