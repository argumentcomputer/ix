module

public import ConLeche.Kernel.ExprOps

public section

/-!
# Free-variable bounds and shifting

Pure syntactic metatheory for nanoda-style free variables (de Bruijn levels
with annotated types):

* `fvarsBelow d e`: every `fvar` leaf reachable in `e` (not descending into
  `fvar` type annotations) has index `< d`.
* `shiftFrom p e`: bump every reachable `fvar` index `≥ p` by one (type
  annotations of shifted `fvar`s are shifted too).
* `shiftFrom_instantiate1`: shifting commutes with opening a binder — the
  key equation that lets weakening proofs step under a binder.

Everything here is used by the denotation's shifting lemmas
(`ConLeche/Verify/Denote/Shift.lean`) and, through them, by the model
tier's weakening arguments.
-/

namespace ConLeche.Expr

/-- Every reachable `fvar` index is `< d`.  (Type annotations of `fvar`s
are not descended into: the interpretation never reads them at leaves;
their well-formedness is tracked separately by `FvarsOk`.) -/
@[expose] def fvarsBelow (d : Nat) : Expr → Prop
  | .bvar _ | .sort _ | .const .. | .lit _ => True
  | .fvar idx _ => idx < d
  | .app f a => fvarsBelow d f ∧ fvarsBelow d a
  | .lam ty body _ | .forallE ty body _ => fvarsBelow d ty ∧ fvarsBelow d body
  | .letE ty val body => fvarsBelow d ty ∧ fvarsBelow d val ∧ fvarsBelow d body
  | .proj _ _ e => fvarsBelow d e

/-- `fvarRange` is exact for `fvarsBelow`. -/
theorem fvarsBelow_iff {x : Expr} {d : Nat} :
    x.fvarsBelow d ↔ x.fvarRange ≤ d := by
  induction x <;>
    (try simp [Expr.fvarsBelow, Expr.fvarRange, Nat.max_le, *]) <;>
    omega

theorem fvarsBelow_mono {d d' : Nat} (h : d ≤ d') :
    ∀ {e : Expr}, fvarsBelow d e → fvarsBelow d' e := by
  intro e
  induction e <;> simp_all [fvarsBelow] <;> omega

/-- Bump every reachable `fvar` index `≥ p` by one. -/
@[expose] def shiftFrom (p : Nat) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty => if idx ≥ p then .fvar (idx + 1) (shiftFrom p ty) else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (shiftFrom p f) (shiftFrom p a)
  | .lam ty body bi => .lam (shiftFrom p ty) (shiftFrom p body) bi
  | .forallE ty body bi => .forallE (shiftFrom p ty) (shiftFrom p body) bi
  | .letE ty val body => .letE (shiftFrom p ty) (shiftFrom p val) (shiftFrom p body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (shiftFrom p e)

/-- Shifting preserves the head shape, so the λ-rule's chain guard
(task #152) reads the same on both sides of a shift. -/
theorem isLam_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).isLam = e.isLam := by
  intro e
  cases e with
  | fvar idx ty =>
    simp only [shiftFrom]
    split <;> rfl
  | _ => rfl

/-- Shifting reads through to a λ's prop-ness datum unchanged (task
#161 P5): `shiftFrom` copies binder metadata, so the chain rule's
`(lam-cod-chain)` read is the same on both sides of a shift. -/
theorem lamPw_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).lamPw = e.lamPw := by
  intro e
  cases e with
  | fvar idx ty =>
    simp only [shiftFrom]
    split <;> rfl
  | _ => rfl

/-- The ∀ twin: shifting reads through to a ∀'s prop-ness datum
unchanged, so `annotPwPi`'s chain read is shift-stable. -/
theorem forallPw_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).forallPw = e.forallPw := by
  intro e
  cases e with
  | fvar idx ty =>
    simp only [shiftFrom]
    split <;> rfl
  | _ => rfl

/-- Shifting from `p` does nothing to a term whose reachable `fvar`s are
below `p`... except inside `fvar` type annotations, which `fvarsBelow` does
not constrain; hence this lemma requires annotation-free positions only in
the sense that it recurses with the same hypothesis shape. -/
theorem shiftFrom_eq_self {p : Nat} :
    ∀ {e : Expr}, fvarsBelow p e → shiftFrom p e = e := by
  intro e
  induction e <;> simp_all [fvarsBelow, shiftFrom]

/-- A term with all reachable `fvar`s below `0` has none. -/
theorem not_hasFvar_of_fvarsBelow_zero :
    ∀ {e : Expr}, Expr.fvarsBelow 0 e → e.hasFvar = false := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- Well-scoped at depth `d`: every reachable `fvar` has index `< d`, and
its type annotation is itself well-scoped at that index (annotations may
only mention strictly earlier variables). -/
@[expose] def WScoped : (d : Nat) → Expr → Prop
  | d, .fvar idx ty => idx < d ∧ WScoped idx ty
  | d, .app f a => WScoped d f ∧ WScoped d a
  | d, .lam ty body _ | d, .forallE ty body _ => WScoped d ty ∧ WScoped d body
  | d, .letE ty val body => WScoped d ty ∧ WScoped d val ∧ WScoped d body
  | d, .proj _ _ e => WScoped d e
  | _, .bvar _ | _, .sort _ | _, .const .. | _, .lit _ => True
termination_by _ e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- The `Bool` scope check implies `WScoped`. -/
theorem WScoped.of_wscopedB : ∀ {e : Expr} {d : Nat},
    Expr.wscopedB d e = true → WScoped d e := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d h
    simp only [Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact (by simp only [WScoped]; exact ⟨h.1, ih h.2⟩)
  | app f a ihf iha =>
    intro d h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    exact (by simp only [WScoped]; exact ⟨ihf h.1, iha h.2⟩)
  | lam ty body bi ihty ihbody =>
    intro d h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    exact (by simp only [WScoped]; exact ⟨ihty h.1, ihbody h.2⟩)
  | forallE ty body bi ihty ihbody =>
    intro d h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    exact (by simp only [WScoped]; exact ⟨ihty h.1, ihbody h.2⟩)
  | letE ty val body ihty ihval ihbody =>
    intro d h
    simp only [Expr.wscopedB, Bool.and_eq_true] at h
    exact (by simp only [WScoped]; exact ⟨ihty h.1.1, ihval h.1.2, ihbody h.2⟩)
  | proj s i e ih =>
    intro d h
    simp only [Expr.wscopedB] at h
    exact (by simp only [WScoped]; exact ih h)
  | _ => intro d h; simp [WScoped]

/-- `WScoped` implies the `Bool` scope check (the converse of
`WScoped.of_wscopedB`). -/
theorem WScoped.to_wscopedB : ∀ {e : Expr} {d : Nat},
    WScoped d e → Expr.wscopedB d e = true := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1, ih h.2⟩
  | app f a ihf iha =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body bi ihty ihbody =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihty h.1, ihbody h.2⟩
  | forallE ty body bi ihty ihbody =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB, Bool.and_eq_true]
    exact ⟨ihty h.1, ihbody h.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB, Bool.and_eq_true]
    exact ⟨⟨ihty h.1, ihval h.2.1⟩, ihbody h.2.2⟩
  | proj s i e ih =>
    intro d h
    simp only [WScoped] at h
    simp only [Expr.wscopedB]
    exact ih h
  | _ => intro d h; simp [Expr.wscopedB]

theorem WScoped.mono : ∀ {e : Expr} {d d' : Nat}, d ≤ d' → WScoped d e → WScoped d' e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨Nat.lt_of_lt_of_le hw.1 h, hw.2⟩
  | app f a ihf iha =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihf h hw.1, iha h hw.2⟩
  | lam ty body bi ihty ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihbody h hw.2⟩
  | forallE ty body bi ihty ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihbody h hw.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ⟨ihty h hw.1, ihval h hw.2.1, ihbody h hw.2.2⟩
  | proj s i e ih =>
    intro d d' h hw
    simp only [WScoped] at hw ⊢
    exact ih h hw
  | _ => intro d d' h hw; simp [WScoped]

theorem WScoped.fvarsBelow : ∀ {e : Expr} {d : Nat}, WScoped d e → Expr.fvarsBelow d e := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro d hw
    simp only [WScoped] at hw
    simpa [Expr.fvarsBelow] using hw.1
  | app f a ihf iha =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihf hw.1, iha hw.2⟩
  | lam ty body bi ihty ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihbody hw.2⟩
  | forallE ty body bi ihty ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihbody hw.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro d hw
    simp only [WScoped] at hw
    exact ⟨ihty hw.1, ihval hw.2.1, ihbody hw.2.2⟩
  | proj s i e ih =>
    intro d hw
    simp only [WScoped] at hw
    exact ih hw
  | _ => intro d hw; simp [Expr.fvarsBelow]

theorem WScoped.instantiate1 {d : Nat} {ty : Expr} (hty : WScoped d ty) :
    ∀ {e : Expr} (k : Nat), WScoped d e →
      WScoped (d + 1) (e.instantiate1 (.fvar d ty) k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · simp only [WScoped]
      exact ⟨Nat.lt_succ_self d, hty⟩
    · split <;> simp [WScoped]
  | fvar idx ty' _ =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨Nat.lt_succ_of_lt hw.1, hw.2⟩
  | app f a ihf iha =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihf _ hw.1, iha _ hw.2⟩
  | lam ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | forallE ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | letE ty' val body ihty ihval ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihval _ hw.2.1, ihbody _ hw.2.2⟩
  | proj s i e ih =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ih _ hw
  | _ => intro k hw; simp [Expr.instantiate1, WScoped]

theorem WScoped.of_not_hasFvar : ∀ {e : Expr} {d : Nat}, e.hasFvar = false → WScoped d e := by
  intro e
  induction e <;> intro d h <;> simp_all [Expr.hasFvar, WScoped]

/-- Instantiation with an arbitrary well-scoped term (e.g. a beta redex's
argument) preserves well-scopedness. -/
theorem WScoped.instantiate1_gen {d : Nat} {v : Expr} (hv : WScoped d v) :
    ∀ {e : Expr} (k : Nat), WScoped d e → WScoped d (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp [WScoped]
  | fvar idx ty' _ =>
    intro k hw
    simpa [Expr.instantiate1, WScoped] using hw
  | app f a ihf iha =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihf _ hw.1, iha _ hw.2⟩
  | lam ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | forallE ty' body bi ihty ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihbody _ hw.2⟩
  | letE ty' val body ihty ihval ihbody =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ⟨ihty _ hw.1, ihval _ hw.2.1, ihbody _ hw.2.2⟩
  | proj s i e ih =>
    intro k hw
    simp only [WScoped] at hw
    simp only [Expr.instantiate1, WScoped]
    exact ih _ hw
  | _ => intro k hw; simp [Expr.instantiate1, WScoped]

/-- Shifting commutes with instantiation by an `fvar` at the shifted
index: opening at `d` then shifting from `p ≤ d` equals shifting the body
first and opening at `d + 1` with the shifted annotation. -/
theorem shiftFrom_instantiate1 {p d : Nat} (hpd : p ≤ d) {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      shiftFrom p (e.instantiate1 (.fvar d ty) k) =
        (shiftFrom p e).instantiate1 (.fvar (d + 1) (shiftFrom p ty)) k := by
  intro e
  induction e <;> intro k <;>
    simp_all [instantiate1, shiftFrom]
  case bvar i =>
    split
    · simp [shiftFrom, hpd]
    · split <;> simp [shiftFrom]
  case fvar idx ty' ih =>
    split <;> simp [instantiate1]

/-- Opening a binder keeps reachable-`fvar` bounds. -/
theorem fvarsBelow_instantiate1 {d : Nat} {ty : Expr} :
    ∀ {e : Expr} (k : Nat), fvarsBelow d e →
      fvarsBelow (d + 1) (e.instantiate1 (.fvar d ty) k) := by
  intro e
  induction e <;> intro k hb <;> simp_all [instantiate1, fvarsBelow]
  case bvar i =>
    split
    · simp [fvarsBelow]
    · split <;> simp [fvarsBelow]
  case fvar idx ty' ih => omega

/-! ## Shift commutation lemmas

The depth-invariance bisimulation (`ConLeche/Verify/Deep.lean`) relates a
checker run at depth `d` with the run at depth `d + 1` whose opened
`fvar`s above the shift point `p` are bumped by one (`shiftFrom p`).
Everything the checker core does to expressions commutes with the
shift; this section collects those commutations. -/

/-- Shifting preserves `hasFvar` (an `fvar` stays an `fvar`). -/
theorem hasFvar_shiftFrom {p : Nat} :
    ∀ {e : Expr}, (shiftFrom p e).hasFvar = e.hasFvar := by
  intro e
  induction e with
  | fvar idx ty ih => simp only [shiftFrom]; split <;> rfl
  | _ => simp_all [Expr.hasFvar, shiftFrom]

/-- A term without `fvar`s is untouched by shifting. -/
theorem shiftFrom_eq_self_of_not_hasFvar {p : Nat} :
    ∀ {e : Expr}, e.hasFvar = false → shiftFrom p e = e := by
  intro e
  induction e <;> simp_all [hasFvar, shiftFrom]

/-- Shifting commutes with instantiation by an arbitrary term. -/
theorem shiftFrom_instantiate1_gen {p : Nat} {v : Expr} :
    ∀ (e : Expr) (k : Nat),
      shiftFrom p (e.instantiate1 v k) =
        (shiftFrom p e).instantiate1 (shiftFrom p v) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instantiate1, shiftFrom]
    split
    · rfl
    · split <;> simp [shiftFrom]
  | fvar idx ty' ih =>
    intro k
    simp only [instantiate1, shiftFrom]
    split <;> simp [instantiate1]
  | _ => intro k; simp_all [instantiate1, shiftFrom]

/-- Shifting from `p` commutes with closing the binder opened at
`d ≥ p`: the abstracted variable is at `d + 1` on the shifted side. -/
theorem shiftFrom_abstract1 {p d : Nat} (hpd : p ≤ d) :
    ∀ (e : Expr) (k : Nat),
      shiftFrom p (e.abstract1 d k) = (shiftFrom p e).abstract1 (d + 1) k := by
  intro e
  induction e with
  | fvar idx ty' ih =>
    intro k
    by_cases hi : idx = d
    · subst hi
      simp [abstract1, shiftFrom, hpd]
    · by_cases hp : p ≤ idx
      · simp [abstract1, shiftFrom, hi, hp]
      · have hi1 : ¬ (idx = d + 1) := by omega
        simp [abstract1, shiftFrom, hi, hp, hi1]
  | _ => intro k; simp_all [abstract1, shiftFrom]

/-- Shifting commutes with taking the application head. -/
theorem getAppFn_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).getAppFn = shiftFrom p e.getAppFn := by
  intro e
  induction e <;> simp_all [shiftFrom, getAppFn]
  case fvar idx ty ih => split <;> simp [getAppFn]

/-- Shifting commutes with taking the application spine. -/
theorem getAppArgs_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).getAppArgs = e.getAppArgs.map (shiftFrom p) := by
  intro e
  induction e <;> simp_all [shiftFrom, getAppArgs]
  case fvar idx ty ih => split <;> simp [getAppArgs]

/-- Shifting commutes with building an application spine. -/
theorem shiftFrom_mkAppN {p : Nat} :
    ∀ (as : List Expr) (f : Expr),
      shiftFrom p (Expr.mkAppN f as) =
        Expr.mkAppN (shiftFrom p f) (as.map (shiftFrom p)) := by
  intro as
  induction as with
  | nil => intro f; rfl
  | cons a as ih => intro f; simp [mkAppN, ih, shiftFrom]

/-- The scope check tracks the shift: a shift from `p ≤ d` moves
scoping at `d` to scoping at `d + 1`. -/
theorem wscopedB_shiftFrom {p : Nat} :
    ∀ (e : Expr) {d : Nat}, p ≤ d →
      (shiftFrom p e).wscopedB (d + 1) = e.wscopedB d := by
  intro e
  induction e <;> intro d hpd <;> simp_all [shiftFrom, wscopedB]
  case fvar idx ty ih =>
    by_cases hp : p ≤ idx
    · rw [if_pos hp]
      simp only [wscopedB]
      rw [ih hp]
      congr 1
      simp only [decide_eq_decide]
      omega
    · rw [if_neg hp]
      simp only [wscopedB]
      congr 1
      simp only [decide_eq_decide]
      omega

/-- Shifting never touches bound variables. -/
theorem looseBVarsBounded_shiftFrom {p : Nat} :
    ∀ (e : Expr) (k : Nat),
      (shiftFrom p e).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;> simp_all [shiftFrom, looseBVarsBounded]
  case fvar idx ty ih => split <;> simp [looseBVarsBounded]

/-- The inverse of `shiftFrom p`: lower every reachable `fvar` index
`> p` by one (shifted annotations lowered too). -/
def unshiftFrom (p : Nat) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx ty =>
    if idx > p then .fvar (idx - 1) (unshiftFrom p ty) else .fvar idx ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (unshiftFrom p f) (unshiftFrom p a)
  | .lam ty body bi => .lam (unshiftFrom p ty) (unshiftFrom p body) bi
  | .forallE ty body bi => .forallE (unshiftFrom p ty) (unshiftFrom p body) bi
  | .letE ty val body =>
    .letE (unshiftFrom p ty) (unshiftFrom p val) (unshiftFrom p body)
  | .lit l => .lit l
  | .proj s i e => .proj s i (unshiftFrom p e)

theorem unshiftFrom_shiftFrom {p : Nat} :
    ∀ (e : Expr), unshiftFrom p (shiftFrom p e) = e := by
  intro e
  induction e <;> simp_all [shiftFrom, unshiftFrom]
  case fvar idx ty ih =>
    by_cases hp : p ≤ idx
    · rw [if_pos hp]
      simp only [unshiftFrom]
      rw [if_pos (by omega)]
      simp [ih]
    · rw [if_neg hp]
      simp only [unshiftFrom]
      rw [if_neg (by omega)]

/-- Shifting is injective. -/
theorem shiftFrom_injective {p : Nat} {a b : Expr}
    (h : shiftFrom p a = shiftFrom p b) : a = b := by
  have := congrArg (unshiftFrom p) h
  rwa [unshiftFrom_shiftFrom, unshiftFrom_shiftFrom] at this

/-- The action of `shiftFrom p` on one recorded `fvar` leaf. -/
def shiftLeaf (p : Nat) : Nat × Expr → Nat × Expr :=
  fun l => if p ≤ l.1 then (l.1 + 1, shiftFrom p l.2) else l

theorem shiftLeaf_injective {p : Nat} {l₁ l₂ : Nat × Expr}
    (h : shiftLeaf p l₁ = shiftLeaf p l₂) : l₁ = l₂ := by
  obtain ⟨i₁, t₁⟩ := l₁
  obtain ⟨i₂, t₂⟩ := l₂
  simp only [shiftLeaf] at h
  split at h <;> split at h <;>
    simp only [Prod.mk.injEq] at h ⊢ <;>
    first
    | exact ⟨by omega, shiftFrom_injective h.2⟩
    | omega
    | exact h

/-- Every recorded leaf of a well-scoped term has index below the bound
(hereditarily: annotations are scoped below their own leaf's index). -/
theorem fvarLeaves_fst_lt :
    ∀ {e : Expr} {d : Nat}, WScoped d e → ∀ l ∈ e.fvarLeaves, l.1 < d := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hw.1
    · exact Nat.lt_trans (ih hw.2 l hl) hw.1
  | app f a ihf iha =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hw.1 l hl
    · exact iha hw.2 l hl
  | lam ty body bi ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | forallE ty body bi ihty ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hw.1 l hl
    · exact ihbody hw.2 l hl
  | letE ty val body ihty ihval ihbody =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hw.1 l hl
    · exact ihval hw.2.1 l hl
    · exact ihbody hw.2.2 l hl
  | proj s i e ih =>
    intro d hw l hl
    simp only [WScoped] at hw
    simp only [fvarLeaves] at hl
    exact ih hw l hl
  | _ => intro d hw l hl; simp [fvarLeaves] at hl

theorem map_shiftLeaf_eq_self {p : Nat} :
    ∀ {ls : List (Nat × Expr)}, (∀ l ∈ ls, l.1 < p) →
      ls.map (shiftLeaf p) = ls := by
  intro ls
  induction ls with
  | nil => intro _; rfl
  | cons l ls ih =>
    intro h
    simp only [List.map, List.cons.injEq]
    refine ⟨?_, ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')⟩
    have hlt := h l (List.mem_cons_self ..)
    simp only [shiftLeaf]
    rw [if_neg (by omega)]

/-- Shifting maps recorded leaves through `shiftLeaf` (well-scopedness
keeps below-the-point annotations untouched hereditarily). -/
theorem fvarLeaves_shiftFrom {p : Nat} :
    ∀ {e : Expr} {d : Nat}, p ≤ d → WScoped d e →
      (shiftFrom p e).fvarLeaves = e.fvarLeaves.map (shiftLeaf p) := by
  intro e
  induction e with
  | fvar idx ty ih =>
    intro d hpd hw
    simp only [WScoped] at hw
    by_cases hp : p ≤ idx
    · simp only [shiftFrom, if_pos hp, fvarLeaves, List.map, shiftLeaf]
      exact congrArg _ (ih hp hw.2)
    · simp only [shiftFrom, if_neg hp, fvarLeaves, List.map, shiftLeaf]
      rw [map_shiftLeaf_eq_self (fun l hl =>
        Nat.lt_of_lt_of_le (fvarLeaves_fst_lt hw.2 l hl) (by omega))]
  | app f a ihf iha =>
    intro d hpd hw
    simp only [WScoped] at hw
    simp only [shiftFrom, fvarLeaves, ihf hpd hw.1, iha hpd hw.2,
      List.map_append]
  | lam ty body bi ihty ihbody =>
    intro d hpd hw
    simp only [WScoped] at hw
    simp only [shiftFrom, fvarLeaves, ihty hpd hw.1, ihbody hpd hw.2,
      List.map_append]
  | forallE ty body bi ihty ihbody =>
    intro d hpd hw
    simp only [WScoped] at hw
    simp only [shiftFrom, fvarLeaves, ihty hpd hw.1, ihbody hpd hw.2,
      List.map_append]
  | letE ty val body ihty ihval ihbody =>
    intro d hpd hw
    simp only [WScoped] at hw
    simp only [shiftFrom, fvarLeaves, ihty hpd hw.1, ihval hpd hw.2.1,
      ihbody hpd hw.2.2, List.map_append]
  | proj s i e ih =>
    intro d hpd hw
    simp only [WScoped] at hw
    simp only [shiftFrom, fvarLeaves, ih hpd hw]
  | _ => intro d hpd hw; simp [shiftFrom, fvarLeaves]

theorem contains_map_shiftLeaf {p : Nat} (ls : List (Nat × Expr))
    (l : Nat × Expr) :
    (ls.map (shiftLeaf p)).contains (shiftLeaf p l) = ls.contains l := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, List.contains_cons, ih]
    congr 1
    cases hlx : l == x with
    | true =>
      have heq : l = x := eq_of_beq hlx
      subst heq
      exact beq_self_eq_true _
    | false =>
      have hne : ¬ shiftLeaf p l = shiftLeaf p x := fun h => by
        have : l = x := shiftLeaf_injective h
        subst this
        simp at hlx
      simp [hne]

/-- The free-variable containment guard is shift-invariant on
well-scoped terms. -/
theorem fvarLeaves_all_contains_shiftFrom {p d : Nat} {a b : Expr}
    (hpd : p ≤ d) (hwa : WScoped d a) (hwb : WScoped d b) :
    ((shiftFrom p a).fvarLeaves.all
        (fun l => (shiftFrom p b).fvarLeaves.contains l)) =
      (a.fvarLeaves.all (fun l => b.fvarLeaves.contains l)) := by
  rw [fvarLeaves_shiftFrom hpd hwa, fvarLeaves_shiftFrom hpd hwb,
    List.all_map]
  induction a.fvarLeaves with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, ih, Function.comp_apply, contains_map_shiftLeaf]

/-- Shifting preserves (in)equality under `==`. -/
theorem shiftFrom_beq {p : Nat} (a b : Expr) :
    (shiftFrom p a == shiftFrom p b) = (a == b) := by
  cases hab : a == b with
  | true =>
    have heq : a = b := eq_of_beq hab
    subst heq
    exact beq_self_eq_true _
  | false =>
    have hne : a ≠ b := by intro h; subst h; simp at hab
    have hne' : shiftFrom p a ≠ shiftFrom p b :=
      fun h => hne (shiftFrom_injective h)
    simp [hne']

/-- Shifting commutes with instantiating a `∀`-telescope. -/
theorem instPis_shiftFrom {p : Nat} :
    ∀ (as : List Expr) (t : Expr),
      Expr.instPis (shiftFrom p t) (as.map (shiftFrom p)) =
        (Expr.instPis t as).map (shiftFrom p)
  | [], t => rfl
  | a :: as, t => by
    cases t <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty body mb =>
      show Expr.instPis ((shiftFrom p body).instantiate1 (shiftFrom p a))
        (as.map (shiftFrom p)) = _
      rw [← shiftFrom_instantiate1_gen]
      exact instPis_shiftFrom as _

/-- Shifting commutes with converting `∀`-binders to `λ`-binders. -/
theorem pisToLams_shiftFrom {p : Nat} :
    ∀ (k : Nat) (t body : Expr),
      Expr.pisToLams k (shiftFrom p t) (shiftFrom p body) =
        (Expr.pisToLams k t body).map (shiftFrom p)
  | 0, _, _ => rfl
  | k + 1, t, body => by
    cases t <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty rest mb =>
      -- task #161 P5: `pisToLams` emits the parse placeholder `.never`
      -- (a ∀'s `pw` is not the λ's claim); the shift commutation is
      -- unaffected — `shiftFrom` never reads binder metadata.
      show (Expr.pisToLams k (shiftFrom p rest) (shiftFrom p body)).map
          (fun b => Expr.lam (shiftFrom p ty) b ⟨.never⟩) =
        ((Expr.pisToLams k rest body).map
          (fun b => Expr.lam ty b ⟨.never⟩)).map (shiftFrom p)
      rw [pisToLams_shiftFrom k rest body]
      cases Expr.pisToLams k rest body <;> rfl

theorem looseBVarsBounded_mono {k k' : Nat} (h : k ≤ k') :
    ∀ {e : Expr}, looseBVarsBounded k e = true → looseBVarsBounded k' e = true := by
  intro e
  induction e generalizing k k' with
  | bvar i => simp_all [looseBVarsBounded]; omega
  | app f a ihf iha =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf h hb.1, iha h hb.2⟩
  | lam ty body m ihty ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty h hb.1, ihbody (by omega) hb.2⟩
  | forallE ty body m ihty ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihty h hb.1, ihbody (by omega) hb.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro hb
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨⟨ihty h hb.1.1, ihval h hb.1.2⟩, ihbody (by omega) hb.2⟩
  | proj s i e ih =>
    intro hb
    simp only [looseBVarsBounded] at hb ⊢
    exact ih h hb
  | _ => simp [looseBVarsBounded]

/-- Instantiating with a bounded term keeps loose-bvar bounds. -/
theorem looseBVarsBounded_instantiate1_gen {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ {e : Expr} {k : Nat}, looseBVarsBounded (k + 1) e = true →
      looseBVarsBounded k (e.instantiate1 a k) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instantiate1]
    split
    · exact looseBVarsBounded_mono (Nat.zero_le k) hba
    · split <;> simp [looseBVarsBounded] <;> omega
  | _ =>
    intro k hb
    simp_all [looseBVarsBounded, instantiate1]

end ConLeche.Expr
