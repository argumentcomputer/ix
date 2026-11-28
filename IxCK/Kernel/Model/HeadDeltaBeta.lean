module

public import IxCK.Kernel.Rules.Rel
public import IxCK.Kernel.ExprOps

@[expose] public section

/-!
# Deterministic head traces through definitions and beta reduction

`Step` records one head step: a definition at a constant, beta at a lambda application,
or a step of an application's function. It does not reduce beneath a binder or in an argument.
Unlike `Rules.Red`, this operational relation has no equality-proof or iota step.

Successful traces to a sort or a telescope head agree, including across an environment extension
that preserves lookups. No termination assumption or closedness condition is needed. `Certified`
additionally records the existing rules certificate for every step, so it supplies both the
operational trace and `Rules.Red` without asserting that every beta redex is licensed.

This strategy uses the rules tier's substitution on opened kernel terms. It must not be
identified with raw heap substitution on loose de Bruijn arguments, which requires
`instantiate1Lift` (as used by `GuardClassifier.head`).

These statements compare operational traces, not arbitrary `Rules.Red` derivations. A consumer
must retain the traces from both computations; forgetting either trace to `Rules.Red` is not
sufficient to use the uniqueness result.
-/

namespace Ix.Kernel.HeadDeltaBeta

/-- One head step. Beta is a syntactic operation here; `Certified` also requires its licence. -/
inductive Step (env : Env md) : Expr md → Expr md → Prop
  | delta {n : Key md} {us : List Level} {e : Expr md} :
      unfoldDefinition env (.const n us) = some e → Step env (.const n us) e
  | beta {ty body a : Expr md} {mb : BinderMeta} :
      Step env (.app (.lam ty body mb) a) (body.instantiate1 a)
  | appFn {f f' a : Expr md} : Step env f f' → Step env (.app f a) (.app f' a)

/-- A finite head trace, including the empty trace. -/
inductive Trace (env : Env md) : Expr md → Expr md → Prop
  | refl {e : Expr md} : Trace env e e
  | cons {e e' r : Expr md} : Step env e e' → Trace env e' r → Trace env e r

/-- A term has no next step in this head strategy. -/
def Normal (env : Env md) (e : Expr md) : Prop := ∀ e', ¬ Step env e e'

/-- The strategy has at most one next term. -/
theorem Step.deterministic {env : Env md} {e r : Expr md} (h : Step env e r) :
    ∀ {r'}, Step env e r' → r = r' := by
  induction h with
  | delta hd =>
    intro r' h'
    cases h' with
    | delta hd' => exact Option.some.inj (hd.symm.trans hd')
  | beta =>
    intro r' h'
    cases h' with
    | beta => rfl
    | appFn h => cases h
  | appFn h ih =>
    intro r' h'
    cases h' with
    | beta => cases h
    | appFn h' => rw [ih h']

theorem normal_sort (env : Env md) (u : Level) : Normal env (.sort u) := by
  intro e h
  cases h

theorem normal_forallE (env : Env md) (ty body : Expr md) (mb : BinderMeta) :
    Normal env (.forallE ty body mb) := by
  intro e h
  cases h

/-- Finite traces cannot terminate in different normal forms. -/
theorem Trace.normal_unique {env : Env md} {e r : Expr md} (h : Trace env e r)
    (hr : Normal env r) :
    ∀ {r'}, Trace env e r' → Normal env r' → r = r' := by
  induction h with
  | refl =>
    intro r' h' _
    cases h' with
    | refl => rfl
    | cons hs _ => exact False.elim (hr _ hs)
  | cons hs ht ih =>
    intro r' h' hr'
    cases h' with
    | refl => exact False.elim (hr' _ hs)
    | cons hs' ht' =>
      have he := hs.deterministic hs'
      subst he
      exact ih hr ht' hr'

/-- A single head step is preserved by keeping existing lookups. -/
theorem Step.mono {env env' : Env md}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {e r : Expr md} (h : Step env e r) : Step env' e r := by
  induction h with
  | @delta n us e hd =>
    apply Step.delta
    unfold unfoldDefinition at hd ⊢
    simp only [Expr.getAppFn] at hd ⊢
    cases hf : env.find? n with
    | none => simp only [hf] at hd; cases hd
    | some ci =>
      rw [hext n ci hf]
      simpa only [hf] using hd
  | beta => exact .beta
  | appFn _ ih => exact .appFn ih

theorem Trace.mono {env env' : Env md}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {e r : Expr md} (h : Trace env e r) : Trace env' e r := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .cons (hs.mono hext) ih

/-- Two computations of a sort agree, even after extending the lookup environment. -/
theorem Trace.sort_unique {env env' : Env md}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {e : Expr md} {u v : Level} (h : Trace env e (.sort u))
    (h' : Trace env' e (.sort v)) : u = v :=
  Expr.sort.inj ((h.mono hext).normal_unique (normal_sort env' u) h' (normal_sort env' v))

/-- Two computations of a telescope head agree in domain, body and binder metadata. -/
theorem Trace.forall_unique {env env' : Env md}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {e ty body ty' body' : Expr md} {mb mb' : BinderMeta}
    (h : Trace env e (.forallE ty body mb)) (h' : Trace env' e (.forallE ty' body' mb')) :
    ty = ty' ∧ body = body' ∧ mb = mb' :=
  Expr.forallE.inj ((h.mono hext).normal_unique (normal_forallE env' ty body mb)
    h' (normal_forallE env' ty' body' mb'))

/-- A head trace whose steps also carry the checker's reduction certificates. -/
inductive Certified (env : Env md) (d : Nat) : Expr md → Expr md → Prop
  | refl {e : Expr md} : Certified env d e e
  | cons {e e' r : Expr md} :
      Step env e e' → Rules.Red env d e e' → Certified env d e' r → Certified env d e r

theorem Certified.trace {env : Env md} {d : Nat} {e r : Expr md}
    (h : Certified env d e r) : Trace env e r := by
  induction h with
  | refl => exact .refl
  | cons hs _ _ ih => exact .cons hs ih

theorem Certified.red {env : Env md} {d : Nat} {e r : Expr md}
    (h : Certified env d e r) : Rules.Red env d e r := by
  induction h with
  | refl => exact .refl
  | cons _ hr _ ih => exact .trans hr ih

/-- Concatenating finite traces preserves their operational evidence. -/
theorem Trace.trans {env : Env md} {e m r : Expr md} (h : Trace env e m)
    (h' : Trace env m r) : Trace env e r := by
  induction h with
  | refl => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

/-- Certified traces compose without discarding their operational evidence. -/
theorem Certified.trans {env : Env md} {d : Nat} {e m r : Expr md}
    (h : Certified env d e m) (h' : Certified env d m r) : Certified env d e r := by
  induction h with
  | refl => exact h'
  | cons hs hr _ ih => exact .cons hs hr (ih h')

/-- A certified head trace can run beneath a fixed application argument. -/
theorem Certified.appFn {env : Env md} {d : Nat} {e r : Expr md}
    (h : Certified env d e r) (a : Expr md) : Certified env d (.app e a) (.app r a) := by
  induction h with
  | refl => exact .refl
  | cons hs hr _ ih => exact .cons (.appFn hs) (.appFn hr) ih

/-- A certified head trace can run beneath a fixed application spine. -/
theorem Certified.mkAppN {env : Env md} {d : Nat} {e r : Expr md}
    (h : Certified env d e r) (args : List (Expr md)) :
    Certified env d (Expr.mkAppN e args) (Expr.mkAppN r args) := by
  induction args generalizing e r with
  | nil => exact h
  | cons a args ih => exact ih (h.appFn a)

/-- One definition followed by a licensed beta step is a certified trace. Its body may contain
free variables: this is a relational statement at any depth, whose semantic consumers retain
the usual scope premises. -/
theorem Certified.alias_beta {env : Env md} {d : Nat} {n : Key md} {us : List Level}
    {ty body a : Expr md} {mb : BinderMeta}
    (hdef : unfoldDefinition env (.const n us) = some (.lam ty body mb))
    (hbeta : mb.pw.isNever = true) :
    Certified env d (.app (.const n us) a) (body.instantiate1 a) :=
  .cons (.appFn (.delta hdef)) (.appFn (.delta hdef))
    (.cons .beta (.betaGate hbeta) .refl)

/-- A certified trace gives the same zero-ness as any trace to a sort in an extension. -/
theorem Certified.sort_zero_agree {env env' : Env md} {d : Nat}
    (hext : ∀ k ci, env.find? k = some ci → env'.find? k = some ci)
    {e : Expr md} {u v : Level} (h : Certified env d e (.sort u))
    (h' : Trace env' e (.sort v)) (φ : LevelParam → Nat) :
    Level.eval φ u = 0 ↔ Level.eval φ v = 0 := by
  rw [h.trace.sort_unique hext h']

/-- A concrete definition supplies a nonempty certified trace to a sort. The definition is
`fun A : Type => A`; the argument is `Prop`. -/
theorem alias_sort_inhabited (n : Key md) (d : Nat) :
    ∃ env : Env md, Certified env d (.app (.const n []) (.sort .zero)) (.sort .zero) := by
  let ty : Expr md := .sort (.succ .zero)
  let mb : BinderMeta := .leanNever
  let env : Env md := ⟨[.defnInfo ⟨n, [], .forallE ty ty mb⟩ (.lam ty (.bvar 0) mb) .abbrev]⟩
  refine ⟨env, ?_⟩
  have hdef : unfoldDefinition env (.const n []) = some (.lam ty (.bvar 0) mb) := by
    simp [env, ty, mb, unfoldDefinition, Env.find?, ConstantInfo.name, ConstantInfo.toConstantVal,
      Expr.getAppFn, Expr.getAppArgs, Expr.mkAppN, Expr.instantiateLevelParams]
    constructor
    · decide +kernel
    · rw [Level.substPW_eq_self (by simp [BinderMeta.leanNever])]
  simpa [Expr.instantiate1] using
    (Certified.alias_beta (d := d) (a := Expr.sort .zero) hdef (by simp [mb, BinderMeta.leanNever]))

end Ix.Kernel.HeadDeltaBeta
