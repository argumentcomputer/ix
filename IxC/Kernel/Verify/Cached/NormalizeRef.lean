module

public import IxC.Kernel.TypeChecker
import IxC.Kernel.Verify.Mono

@[expose] public section

/-!
# A reference normalizer

`nfRef mode env fuel depth e` normalizes `e` with the kernel's fueled `whnf`,
with the structure of IxVM's evaluator (`KernelEval::eval_nf` and
`eval_nf_spine`, `IxVM/IxVM/Modules/KernelEval.lean`):

* reduce the head with `whnf`;
* under a `lam` or a `forallE`, normalize the domain, then the body opened
  with a fresh variable of the (unnormalized) domain, and close it again;
* along an application spine, normalize the arguments;
* under a `proj`, normalize the structure.

`fuel` bounds both `whnf` and the depth of the recursion; running out is an
error. An `eval` claim's value relation is stated with it: at some fuel, the
input's value normalizes to the output's value (`IxVM.Refinement.EvalValues`).

`eraseMeta` forgets binder and let metadata (contracts, the `PropWhen`
annotation, display data), which IxVM's structural comparison
(`KernelCheck::kexpr_struct_eq`) does not see.

Only cheap facts are proved here (`nfGo_zero`, `nfGo_of_whnf_sort`).
-/

namespace Ix.Kernel

mutual
  /-- `eval_nf`: reduce the head, then normalize under binders, or along the
  spine. `budget` bounds the recursion. -/
  def nfGo (mode : CheckMode) (env : Env md) (fuel : Nat) : Nat → Nat → Expr md → CheckM md (Expr md)
    | 0, _, _ => throw (.notImplemented "normalization budget exhausted")
    | budget + 1, depth, e => do
      match ← whnf mode env fuel depth e with
      | .lam ty body mb => do
        let ty' ← nfGo mode env fuel budget depth ty
        let body' ← nfGo mode env fuel budget (depth + 1) (body.instantiate1 (.fvar depth ty))
        pure (.lam ty' (body'.abstract1 depth) mb)
      | .forallE ty body mb => do
        let ty' ← nfGo mode env fuel budget depth ty
        let body' ← nfGo mode env fuel budget (depth + 1) (body.instantiate1 (.fvar depth ty))
        pure (.forallE ty' (body'.abstract1 depth) mb)
      | w => nfSpine mode env fuel budget depth w

  /-- `eval_nf_spine`: along an application spine normalize the arguments,
  and under a projection the structure; any other head is left as it is. -/
  def nfSpine (mode : CheckMode) (env : Env md) (fuel : Nat) : Nat → Nat → Expr md → CheckM md (Expr md)
    | 0, _, _ => throw (.notImplemented "normalization budget exhausted")
    | budget + 1, depth, .app f a => do
      pure (.app (← nfSpine mode env fuel budget depth f) (← nfGo mode env fuel budget depth a))
    | budget + 1, depth, .proj s i e => do
      pure (.proj s i (← nfGo mode env fuel budget depth e))
    | _ + 1, _, e => pure e
end

/-- **The reference normalizer**: `nfGo` on the annotated form of `e`
(`annotateCore`, which $\zeta$-reduces `letE` and populates sort-annotation
metadata for `whnf`), with `fuel` bounding `annotateCore`, `whnf` and the
recursion. -/
def nfRef (mode : CheckMode) (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) := do
  nfGo mode env fuel fuel depth (← annotateCore mode env fuel depth e)

/-- **Binder and let metadata erased**: every `lam`, `forallE` and `letE`
carries the default metadata. -/
def Expr.eraseMeta : Expr md → Expr md
  | .fvar idx ty => .fvar idx ty.eraseMeta
  | .app f a => .app f.eraseMeta a.eraseMeta
  | .lam ty body _ => .lam ty.eraseMeta body.eraseMeta default
  | .forallE ty body _ => .forallE ty.eraseMeta body.eraseMeta default
  | .letE ty value body _ => .letE ty.eraseMeta value.eraseMeta body.eraseMeta default
  | .proj s i e => .proj s i e.eraseMeta
  | e => e

/-- With no budget left, normalization fails. -/
theorem nfGo_zero (mode : CheckMode) (env : Env md) (fuel depth : Nat) (e : Expr md) :
    nfGo mode env fuel 0 depth e = throw (.notImplemented "normalization budget exhausted") := by
  simp [nfGo]

/-- A term whose head normal form is a sort normalizes to that sort. -/
theorem nfGo_of_whnf_sort {mode : CheckMode} {env : Env md} {fuel budget depth : Nat} {e : Expr md} {u : Level}
    (h : whnf mode env fuel depth e = .ok (.sort u)) :
    nfGo mode env fuel (budget + 2) depth e = .ok (.sort u) := by
  simp [nfGo, nfSpine, h, bind, Except.bind, pure, Except.pure]

/-! ## Metadata erasure and fuel monotonicity -/

@[simp] theorem Expr.eraseMeta_idem (e : Expr md) : e.eraseMeta.eraseMeta = e.eraseMeta := by
  induction e <;> simp [Expr.eraseMeta, *]

theorem nfGo_nfSpine_mono {mode : CheckMode} {env : Env md} {f f' : Nat} (hf : f ≤ f') :
    ∀ {b b' : Nat}, b ≤ b' →
      (∀ {depth : Nat} {e r : Expr md},
        nfGo mode env f b depth e = .ok r → nfGo mode env f' b' depth e = .ok r) ∧
      (∀ {depth : Nat} {e r : Expr md},
        nfSpine mode env f b depth e = .ok r → nfSpine mode env f' b' depth e = .ok r)
  | 0, _, _ =>
    ⟨fun h => by simp [nfGo, throw, throwThe, MonadExceptOf.throw] at h,
     fun h => by simp [nfSpine, throw, throwThe, MonadExceptOf.throw] at h⟩
  | b + 1, 0, hb => absurd hb (by omega)
  | b + 1, b' + 1, hb => by
    have ⟨ihGo, ihSpine⟩ :=
      nfGo_nfSpine_mono (mode := mode) (env := env) hf (Nat.le_of_succ_le_succ hb)
    refine ⟨fun {depth e r} h => ?_, fun {depth e r} h => ?_⟩
    · rw [nfGo.eq_def] at h ⊢
      dsimp only [Bind.bind, Except.bind] at h ⊢
      cases hw : whnf mode env f depth e with
      | error err => rw [hw] at h; exact nomatch h
      | ok w =>
        rw [hw] at h
        rw [whnf_mono hf hw]
        dsimp only at h ⊢
        cases w with
        | lam ty body mb =>
          dsimp only at h ⊢
          cases hty : nfGo mode env f b depth ty with
          | error err => rw [hty] at h; exact nomatch h
          | ok ty' =>
            rw [hty] at h
            rw [ihGo hty]
            dsimp only at h ⊢
            cases hbody : nfGo mode env f b (depth + 1) (body.instantiate1 (.fvar depth ty)) with
            | error err => rw [hbody] at h; exact nomatch h
            | ok body' =>
              rw [hbody] at h
              rw [ihGo hbody]
              exact h
        | forallE ty body mb =>
          dsimp only at h ⊢
          cases hty : nfGo mode env f b depth ty with
          | error err => rw [hty] at h; exact nomatch h
          | ok ty' =>
            rw [hty] at h
            rw [ihGo hty]
            dsimp only at h ⊢
            cases hbody : nfGo mode env f b (depth + 1) (body.instantiate1 (.fvar depth ty)) with
            | error err => rw [hbody] at h; exact nomatch h
            | ok body' =>
              rw [hbody] at h
              rw [ihGo hbody]
              exact h
        | _ => exact ihSpine h
    · cases e with
      | app fn a =>
        rw [nfSpine.eq_def] at h ⊢
        dsimp only [Bind.bind, Except.bind] at h ⊢
        cases hfn : nfSpine mode env f b depth fn with
        | error err => rw [hfn] at h; exact nomatch h
        | ok fn' =>
          rw [hfn] at h
          rw [ihSpine hfn]
          dsimp only at h ⊢
          cases ha : nfGo mode env f b depth a with
          | error err => rw [ha] at h; exact nomatch h
          | ok a' =>
            rw [ha] at h
            rw [ihGo ha]
            exact h
      | proj s i p =>
        rw [nfSpine.eq_def] at h ⊢
        dsimp only [Bind.bind, Except.bind] at h ⊢
        cases hp : nfGo mode env f b depth p with
        | error err => rw [hp] at h; exact nomatch h
        | ok p' =>
          rw [hp] at h
          rw [ihGo hp]
          exact h
      | _ =>
        rw [nfSpine.eq_def] at h ⊢
        exact h

/-- **`nfGo` is monotone in both `whnf` fuel and recursion budget.** -/
theorem nfGo_mono {mode : CheckMode} {env : Env md} {f f' b b' : Nat}
    (hf : f ≤ f') (hb : b ≤ b') {depth : Nat} {e r : Expr md}
    (h : nfGo mode env f b depth e = .ok r) :
    nfGo mode env f' b' depth e = .ok r :=
  (nfGo_nfSpine_mono hf hb).1 h

/-- **`nfSpine` is monotone in both `whnf` fuel and recursion budget.** -/
theorem nfSpine_mono {mode : CheckMode} {env : Env md} {f f' b b' : Nat}
    (hf : f ≤ f') (hb : b ≤ b') {depth : Nat} {e r : Expr md}
    (h : nfSpine mode env f b depth e = .ok r) :
    nfSpine mode env f' b' depth e = .ok r :=
  (nfGo_nfSpine_mono hf hb).2 h

/-- **The reference normalizer is monotone in its fuel.** -/
theorem nfRef_mono {mode : CheckMode} {env : Env md} {f f' : Nat} (hf : f ≤ f')
    {depth : Nat} {e r : Expr md} (h : nfRef mode env f depth e = .ok r) :
    nfRef mode env f' depth e = .ok r := by
  unfold nfRef at h ⊢
  dsimp only [Bind.bind, Except.bind] at h ⊢
  cases ha : annotateCore mode env f depth e with
  | error err => rw [ha] at h; exact nomatch h
  | ok a =>
    rw [ha] at h
    rw [annotateCore_mono hf ha]
    exact nfGo_mono hf hf h

/-- **Two accepting runs of `nfRef`, at any two fuels, return the same normal
form.** -/
theorem nfRef_deterministic {mode : CheckMode} {env : Env md} {f₁ f₂ depth : Nat}
    {e r₁ r₂ : Expr md}
    (h₁ : nfRef mode env f₁ depth e = .ok r₁)
    (h₂ : nfRef mode env f₂ depth e = .ok r₂) : r₁ = r₂ := by
  have h := nfRef_mono (Nat.le_max_left f₁ f₂) h₁
  rw [nfRef_mono (Nat.le_max_right f₁ f₂) h₂] at h
  exact (Except.ok.inj h).symm

end Ix.Kernel
