module

import ConLeche.Kernel.Core
public import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF

@[expose] public section

/-!
# `SetBase/ConstsBound` — "every constant this term mentions is stored"

`ConstsBound`, its clause kit and the two facts that go with it,
re-based at THE SEPARATION's S2 (task #161).

`ConstsBound` is the subject-side premise of every environment-extension
statement in the tree — the graded lane names it in eleven modules, the
collapsed lane in ten — and it is model-free: an `Expr`/`Env`
predicate, with `Expr` clause equations and one `instantiate1` closure
fact.  It was split across two lane modules for historical reasons: the
definition sat in `Annot/SortCoh/Discharge.lean` (which "landed it with
no lemmas"), the kit in `Interp/Denote2Extend.lean`.  The graded
lane's `Annot/BitExtend` imported the whole of the latter — a 2U module
— for the kit alone, which is the crossing S2 removes.

`strLitSupported_listNames` comes with them: it is the same kind of
fact (a guard inversion producing two `isSome` obligations) and
`BitExtend` reads it at the same clause.

Statements verbatim, namespace (`ConLeche.SetR.Interp`) unchanged.
-/

namespace ConLeche.Semantics

open ConLeche.Verify
open ConLeche (CheckMode Env Expr Name Level ConstantInfo
  natLitSupported strLitSupported)

/-- Every constant the expression mentions is bound in `env₀`
(hereditarily through annotations, like the leaf machinery). -/
def ConstsBound (env₀ : Env) : Expr → Prop
  | .const n _ => (env₀.find? n).isSome = true
  | .app f a => ConstsBound env₀ f ∧ ConstsBound env₀ a
  | .lam ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .forallE ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .letE t v b =>
      ConstsBound env₀ t ∧ ConstsBound env₀ v ∧ ConstsBound env₀ b
  | .proj _ _ e => ConstsBound env₀ e
  | .fvar _ ty => ConstsBound env₀ ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [ConLeche.Expr.sizeF]; omega)
  | simp [ConLeche.Expr.sizeF]

/-! ## The `ConstsBound` kit

`ConstsBound` landed with no lemmas — its only consumer so far took it
as a premise and never took it apart.  These are the clause equations
and the one closure fact `denoteAnnot`'s binder cases need. -/

@[simp] theorem constsBound_const {env₀ : Env} {n : Name}
    {us : List Level} :
    ConstsBound env₀ (.const n us) ↔ (env₀.find? n).isSome = true := by
  rw [ConstsBound]

@[simp] theorem constsBound_app {env₀ : Env} {f a : Expr} :
    ConstsBound env₀ (.app f a) ↔
      ConstsBound env₀ f ∧ ConstsBound env₀ a := by
  rw [ConstsBound]

@[simp] theorem constsBound_lam {env₀ : Env} {ty b : Expr}
    {m : ConLeche.BinderMeta} :
    ConstsBound env₀ (.lam ty b m) ↔
      ConstsBound env₀ ty ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_forallE {env₀ : Env}
    {ty b : Expr} {m : ConLeche.BinderMeta} :
    ConstsBound env₀ (.forallE ty b m) ↔
      ConstsBound env₀ ty ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_letE {env₀ : Env}
    {t v b : Expr} :
    ConstsBound env₀ (.letE t v b) ↔
      ConstsBound env₀ t ∧ ConstsBound env₀ v ∧ ConstsBound env₀ b := by
  rw [ConstsBound]

@[simp] theorem constsBound_proj {env₀ : Env} {s : Name} {i : Nat}
    {e : Expr} :
    ConstsBound env₀ (.proj s i e) ↔ ConstsBound env₀ e := by
  rw [ConstsBound]

@[simp] theorem constsBound_fvar {env₀ : Env} {idx : Nat}
    {ty : Expr} :
    ConstsBound env₀ (.fvar idx ty) ↔ ConstsBound env₀ ty := by
  rw [ConstsBound]

@[simp] theorem constsBound_sort {env₀ : Env} {u : Level} :
    ConstsBound env₀ (.sort u) := by rw [ConstsBound] <;> simp

@[simp] theorem constsBound_bvar {env₀ : Env} {i : Nat} :
    ConstsBound env₀ (.bvar i) := by rw [ConstsBound] <;> simp

/-- **The literal case is the catch-all.**  Stated, rather than left
implicit, because it is the whole of finding 2: the premise of
`Denote2EnvExtend` says *nothing* about a literal, while `denoteAnnot`'s
literal clauses are gated on an environment-global guard. -/
@[simp] theorem constsBound_lit {env₀ : Env} {l : ConLeche.Literal} :
    ConstsBound env₀ (.lit l) := by rw [ConstsBound] <;> simp

/-- Instantiation preserves prefix-boundness: every constant leaf of
the result comes from the body or from the substituted term. -/
theorem ConstsBound.instantiate1 {env₀ : Env} {v : Expr}
    (hv : ConstsBound env₀ v) :
    ∀ (e : Expr) (d : Nat), ConstsBound env₀ e →
      ConstsBound env₀ (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    rw [ConLeche.Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [ConLeche.Expr.instantiate1]; simp
  | const n us => intro d h; rw [ConLeche.Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [ConLeche.Expr.instantiate1]; exact h
  | lit l => intro d _; rw [ConLeche.Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [constsBound_app] at h
    rw [ConLeche.Expr.instantiate1, constsBound_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [constsBound_lam] at h
    rw [ConLeche.Expr.instantiate1, constsBound_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [constsBound_forallE] at h
    rw [ConLeche.Expr.instantiate1, constsBound_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [constsBound_letE] at h
    rw [ConLeche.Expr.instantiate1, constsBound_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s i e ihe =>
    intro d h
    rw [constsBound_proj] at h
    rw [ConLeche.Expr.instantiate1, constsBound_proj]
    exact ihe d h

/-- The string guard pins `List.nil` and `List.cons` in the store. -/
theorem strLitSupported_listNames {env₀ : Env}
    (h : strLitSupported env₀ = true) :
    (env₀.find? listNilName).isSome = true ∧
      (env₀.find? listConsName).isSome = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h
  constructor
  · revert h
    cases env₀.find? listNilName <;> simp [ConLeche.listNilTyOk]
  · revert h
    cases env₀.find? listConsName <;> simp [ConLeche.listConsTyOk]


/-! ## The extension vocabulary

`FindPreserved` came out of `Annot/SortCoh/Discharge.lean` beside
`ConstsBound`; `LitGuardsAgree` and `levelParamsAt_congr` out of
`Interp/Denote2Extend.lean` with the kit.  All three are `Env`
arithmetic, and both lanes' extension statements are phrased in
them. -/

/-- The extension is conservative on the prefix: every stored lookup
survives verbatim (no shadowing — duplicate installs are
rejected). -/
def FindPreserved (env₀ env : Env) : Prop :=
  ∀ {n : Name} {ci : ConLeche.ConstantInfo},
    env₀.find? n = some ci → env.find? n = some ci

def LitGuardsAgree (env₀ env : Env) : Prop :=
  natLitSupported env₀ = natLitSupported env ∧
  strLitSupported env₀ = strLitSupported env

/-- A stored lookup's level parameters do not move. -/
theorem levelParamsAt_congr {env₀ env : Env}
    (hF : FindPreserved env₀ env) {n : Name}
    (h : (env₀.find? n).isSome = true) :
    levelParamsAt env₀ n = levelParamsAt env n := by
  cases hf : env₀.find? n with
  | none => rw [hf] at h; exact nomatch h
  | some ci => rw [levelParamsAt, levelParamsAt, hf, hF hf]


/-! ## From the environment invariant

`constsBound_of_constsResolve` and `envWF_constsBound` came out of
`Interp/Keys2Cond.lean` at the same S2 sever: they are the bridge from
the checker's decidable `constsResolve` and from `EnvWF` to
`ConstsBound`, and both lanes' install rows start from them. -/

/-- `constsResolve` is the decidable form of `ConstsBound`, and
strictly stronger: it additionally pins the literal-support block and
a projection's structure name. -/
theorem constsBound_of_constsResolve {env₀ : Env} :
    ∀ e : Expr,
      Expr.constsResolve env₀ e = true → ConstsBound env₀ e := by
  intro e
  induction e with
  | bvar i => intro _; simp
  | sort u => intro _; simp
  | lit l => intro _; simp
  | const n us =>
    intro h
    rw [constsBound_const]
    simpa [Expr.constsResolve] using h
  | fvar idx ty ih =>
    intro h
    rw [constsBound_fvar]
    exact ih (by simpa [Expr.constsResolve] using h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b mb ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_letE.mpr ⟨ihty h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i e ihe =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact constsBound_proj.mpr (ihe h.2)

/-- **`declStep2_of_axiom`'s `hbound` premise, from the invariant.**
Every stored type and every stored `def` body is prefix-bound,
because `ConstWF` says it resolves (a theorem's stored value has no
clause: it is never read). -/
theorem envWF_constsBound {env : Env} (hwf : EnvWF env) :
    ∀ c ∈ env.consts,
      ConstsBound env c.toConstantVal.type ∧
      (∀ cv value hint, c = .defnInfo cv value hint →
        ConstsBound env value) := by
  intro c hc
  obtain ⟨-, -, hty, -, hdefn, -⟩ := hwf c hc
  exact ⟨constsBound_of_constsResolve _ hty,
    fun cv value hint heq =>
      constsBound_of_constsResolve _ (hdefn cv value hint heq).2.2.1⟩

end ConLeche.Semantics
