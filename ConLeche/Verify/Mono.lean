module

public import ConLeche.Verify.PairM

public section

/-!
# Fuel monotonicity, via the relational pair monad

Instantiates `PairM` with success-refinement between two `CheckM`
computations; one induction at the knot yields fuel monotonicity for
every fueled entry point.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- `q` succeeds wherever `p` succeeds, with the same value. -/
@[expose] def MRefines {α : Type} (p q : CheckM α) : Prop :=
  ∀ v, p = .ok v → q = .ok v

theorem MRefines.rfl {α : Type} {p : CheckM α} : MRefines p p := fun _ h => h

/-- Success refinement as a monad relation. -/
@[expose] def refinesRel : MonadRel CheckM CheckM where
  R := MRefines
  pure_rel _ := MRefines.rfl
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro v h
    cases hx1 : x₁ with
    | error e =>
      rw [show (x₁ >>= f₁) = Except.bind x₁ f₁ from rfl, hx1] at h
      exact nomatch h
    | ok a =>
      rw [show (x₁ >>= f₁) = Except.bind x₁ f₁ from rfl, hx1] at h
      dsimp only [Except.bind] at h
      rw [show (x₂ >>= f₂) = Except.bind x₂ f₂ from rfl, hx a hx1]
      exact hf a v h
  throw_rel _ := fun _ h => nomatch h

/-- Componentwise refinement between two pure records. -/
abbrev FnsRefines (r₁ r₂ : CoreFns CheckM) : Prop :=
  FnsRel refinesRel r₁ r₂

section Mono

variable {r₁ r₂ : CoreFns CheckM} {env : Env}

/-! Per-body monotonicity, extracted from the pair instantiation. -/

theorem whnfCoreBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (whnfCoreBody mode r₁ env d e) (whnfCoreBody mode r₂ env d e) := by
  have := (whnfCoreBody mode (pairFns r₁ r₂ h) env d e).property
  rwa [whnfCoreBody_fst_proj, whnfCoreBody_snd_proj] at this

theorem whnfBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (whnfBody r₁ env d e) (whnfBody r₂ env d e) := by
  have := (whnfBody (pairFns r₁ r₂ h) env d e).property
  rwa [whnfBody_fst_proj, whnfBody_snd_proj] at this

theorem inferBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (inferBody mode r₁ env d e) (inferBody mode r₂ env d e) := by
  have := (inferBody mode (pairFns r₁ r₂ h) env d e).property
  rwa [inferBody_fst_proj, inferBody_snd_proj] at this

theorem defeqBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (defeqBody mode r₁ env d a b) (defeqBody mode r₂ env d a b) := by
  have := (defeqBody mode (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqBody_fst_proj, defeqBody_snd_proj] at this

theorem annotateBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (annotateBody r₁ env d e) (annotateBody r₂ env d e) := by
  have := (annotateBody (pairFns r₁ r₂ h) env d e).property
  rwa [annotateBody_fst_proj, annotateBody_snd_proj] at this

theorem inferBodyIO_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (inferBodyIO mode r₁ env d e) (inferBodyIO mode r₂ env d e) := by
  have := (inferBodyIO mode (pairFns r₁ r₂ h) env d e).property
  rwa [inferBodyIO_fst_proj, inferBodyIO_snd_proj] at this

theorem ensureSort_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (ensureSort r₁ env d e) (ensureSort r₂ env d e) := by
  have := (ensureSort (pairFns r₁ r₂ h) env d e).property
  rwa [ensureSort_fst_proj, ensureSort_snd_proj] at this

end Mono

/-! ## Fuel monotonicity at the knot -/

theorem pureFns_mono (env : Env) : ∀ {f f' : Nat}, f ≤ f' →
    FnsRefines (pureFns mode env f) (pureFns mode env f')
  | 0, f', _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d e v hv
      rw [show (pureFns mode env 0).whnfCore d e = whnfCore mode env 0 d e from rfl,
        whnfCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode env 0).whnf d e = whnf mode env 0 d e from rfl,
        whnf_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode env 0).infer d e = inferTypeCore mode env 0 d e from rfl,
        inferTypeCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d a b v hv
      rw [show (pureFns mode env 0).defeq d a b = isDefEqCore mode env 0 d a b from rfl,
        isDefEqCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode env 0).annotate d e = annotateCore mode env 0 d e from rfl,
        annotateCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns mode env 0).inferIO d e =
        throw (.internal "fuel exhausted: infer") from rfl] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
  | f + 1, f' + 1, hle => by
    have ih := pureFns_mono env (Nat.le_of_succ_le_succ hle)
    refine ⟨fun d e => whnfCoreBody_mono ih d e,
      fun d e => whnfBody_mono ih d e,
      fun d e => inferBody_mono ih d e,
      fun d a b => defeqBody_mono ih d a b,
      fun d e => annotateBody_mono ih d e,
      fun d e => ?_⟩
    -- the io slot (task #172 B4): both fuels select the same branch
    show MRefines
      (if mode.betaGate then
        inferBodyIO mode (CoreFns.ioView (pureFns mode env f)) env d e
       else inferBody mode (pureFns mode env f) env d e)
      (if mode.betaGate then
        inferBodyIO mode (CoreFns.ioView (pureFns mode env f')) env d e
       else inferBody mode (pureFns mode env f') env d e)
    cases hg : mode.betaGate
    · simp only [Bool.false_eq_true, if_false]
      exact inferBody_mono ih d e
    · simp only [if_true]
      exact inferBodyIO_mono ih.ioView d e

/-! ## Fueled corollaries -/

theorem whnfCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : whnfCore mode env f d e = .ok r) :
    whnfCore mode env f' d e = .ok r :=
  (pureFns_mono env hle).1 d e r h

theorem whnf_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : whnf mode env f d e = .ok r) :
    whnf mode env f' d e = .ok r :=
  (pureFns_mono env hle).2.1 d e r h

theorem inferTypeCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : inferTypeCore mode env f d e = .ok r) :
    inferTypeCore mode env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.1 d e r h

theorem isDefEqCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {a b : Expr} {r : Bool} (h : isDefEqCore mode env f d a b = .ok r) :
    isDefEqCore mode env f' d a b = .ok r :=
  (pureFns_mono env hle).2.2.2.1 d a b r h

theorem annotateCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : annotateCore mode env f d e = .ok r) :
    annotateCore mode env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.2.2.1 d e r h

theorem inferTypeIO_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : inferTypeIO mode env f d e = .ok r) :
    inferTypeIO mode env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.2.2.2 d e r h

theorem ensureSortCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e : Expr} {u : Level}
    (h : ensureSortCore mode env f d e = .ok u) :
    ensureSortCore mode env f' d e = .ok u := by
  cases f with
  | zero =>
    rw [show ensureSortCore mode env 0 d e =
      ensureSort (pureFns mode env 0) env d e from rfl] at h
    revert h
    unfold ensureSort
    rw [show (pureFns mode env 0).whnf d e = whnf mode env 0 d e from rfl, whnf_zero]
    intro h
    simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | succ f =>
    cases f' with
    | zero => exact absurd hle (by omega)
    | succ f' =>
      exact ensureSort_mono (pureFns_mono env hle) d e u h

end ConLeche
