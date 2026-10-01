module

import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.Shift
import ConLeche.Verify.PropRead
import ConLeche.Verify.EnvWF
import ConLeche.Verify.InstLevels
public import ConLeche.Verify.InferIOLeaves
import ConLeche.Verify.Knot
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Abstract
import ConLeche.Verify.InstSpine
public section

/-!
# Depth invariance of the checker core

The checker core threads a binder depth, used only to name freshly
opened `fvar`s.  This module proves that every entry point's *result*
is independent of the ambient depth, for inputs well-scoped at both
depths — the theorem that justifies memoizing the executed knot
(`ConLeche/Cached/CoreC.lean`) under depth-free keys.

The proof is a bisimulation: a run at depth `d` on `e` is matched
against the run at depth `d + 1` on `shiftFrom p e` (all `fvar`s at
indices `≥ p` bumped by one, `p ≤ d` the shift point); the two runs
step in lock-step, results relating by the shift.  One claim per core
entry point (`ShiftClaims`), one helper lemma per record-parameterized
body helper (at the same fuel, against `pureFns mode env fuel`), one fuel
induction at the knot.  Setting `p := d` and shrinking with
`shiftFrom_eq_self` turns the bisimulation into
`whnfCore mode env fuel (d+1) e = whnfCore mode env fuel d e` for `e` scoped at
`d`, and chaining walks any two well-scoped depths
(`whnfCore_depth_inv` and friends).
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## `Except` bind relators -/

/-- Relate two `CheckM` binds: scrutinees related by a value map,
continuations pointwise by a result map. -/
private theorem bind_rel {α α' β β' : Type} {x : CheckM α} {x' : CheckM α'}
    {g : α → CheckM β} {g' : α' → CheckM β'} (σx : α → α') (σ : β → β')
    (hx : x' = x.map σx)
    (hg : ∀ a, x = .ok a → g' (σx a) = (g a).map σ) :
    x' >>= g' = (x >>= g).map σ := by
  subst hx
  cases x with
  | error err => rfl
  | ok a => exact hg a rfl

/-- `bind_rel` with an unchanged scrutinee. -/
private theorem bind_rel_eq {α β β' : Type} {x x' : CheckM α}
    {g : α → CheckM β} {g' : α → CheckM β'} (σ : β → β')
    (hx : x' = x)
    (hg : ∀ a, x = .ok a → g' a = (g a).map σ) :
    x' >>= g' = (x >>= g).map σ := by
  subst hx
  cases x' with
  | error err => rfl
  | ok a => exact hg a rfl

/-- Relate two `CheckM` binds with equal results (the `Bool`-valued
claims): scrutinees related by a value map, continuations equal. -/
private theorem bind_congr {α α' β : Type} {x : CheckM α} {x' : CheckM α'}
    {g : α → CheckM β} {g' : α' → CheckM β} (σx : α → α')
    (hx : x' = x.map σx)
    (hg : ∀ a, x = .ok a → g' (σx a) = g a) :
    x' >>= g' = x >>= g := by
  subst hx
  cases x with
  | error err => rfl
  | ok a => exact hg a rfl

/-- `bind_congr` with an unchanged scrutinee. -/
private theorem bind_congr_eq {α β : Type} {x x' : CheckM α}
    {g g' : α → CheckM β}
    (hx : x' = x)
    (hg : ∀ a, x = .ok a → g' a = g a) :
    x' >>= g' = x >>= g := by
  subst hx
  cases x' with
  | error err => rfl
  | ok a => exact hg a rfl

@[local simp]
private theorem map_ok {α β : Type} (σ : α → β) (a : α) :
    (Except.ok a : CheckM α).map σ = .ok (σ a) := rfl

@[local simp]
private theorem map_error {α β : Type} (σ : α → β) (e : CheckError) :
    (Except.error e : CheckM α).map σ = .error e := rfl

/-- Congruence for `if` with a common condition. -/
private theorem ite_congr' {α : Sort _} {c : Prop} [Decidable c]
    {x y x' y' : α} (hx : c → x' = x) (hy : ¬ c → y' = y) :
    (if c then x' else y') = (if c then x else y) := by
  split
  next h => exact hx h
  next h => exact hy h

/-- Congruence for `if` with a common condition, under a result map. -/
private theorem ite_rel {β β' : Type} {c : Prop} [Decidable c]
    {x' y' : CheckM β'} {x y : CheckM β} (σ : β → β')
    (hx : c → x' = x.map σ) (hy : ¬ c → y' = y.map σ) :
    (if c then x' else y') = (if c then x else y).map σ := by
  split
  next h => exact hx h
  next h => exact hy h

/-! ## Small shift facts about the checker's syntactic helpers -/

/-- The index of a shifted `fvar`. -/
private def shiftIdx (p i : Nat) : Nat := if p ≤ i then i + 1 else i

/-- The annotation of a shifted `fvar`. -/
private def shiftTy (p i : Nat) (ty : Expr) : Expr :=
  if p ≤ i then shiftFrom p ty else ty

/-- `shiftFrom` on an `fvar`, in constructor-headed form (so that
`match`es on shifted scrutinees reduce). -/
private theorem lamPw_shiftFrom (p : Nat) (e : Expr) :
    (shiftFrom p e).lamPw = e.lamPw := by
  cases e
  case fvar idx t =>
    rw [shiftFrom]
    split <;> rfl
  all_goals first
    | rfl
    | simp [shiftFrom, Expr.lamPw]

private theorem shiftFrom_fvar (p idx : Nat) (ty : Expr) :
    shiftFrom p (.fvar idx ty) =
      .fvar (shiftIdx p idx) (shiftTy p idx ty) := by
  by_cases h : p ≤ idx <;>
    simp [shiftFrom, shiftIdx, shiftTy, h, ge_iff_le]

private theorem shiftIdx_beq (p i j : Nat) :
    (shiftIdx p i == shiftIdx p j) = (i == j) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [beq_iff_eq, beq_iff_eq]
  simp only [shiftIdx]
  by_cases hi : p ≤ i <;> by_cases hj : p ≤ j <;>
    simp only [hi, hj, if_true, if_false] <;> omega

/-- Shifting a freshly opened `fvar` at depth `d ≥ p`. -/
private theorem shiftFrom_fvar_ge {p d : Nat} (h : p ≤ d)
    (ty : Expr) :
    shiftFrom p (.fvar d ty) = .fvar (d + 1) (shiftFrom p ty) := by
  simp [shiftFrom, ge_iff_le, h]

/-- `shiftFrom` distributes over `app` (definitional; a targeted simp
lemma that leaves `fvar` leaves to `shiftFrom_fvar`). -/
private theorem shiftFrom_app (p : Nat) (f a : Expr) :
    shiftFrom p (.app f a) = .app (shiftFrom p f) (shiftFrom p a) := rfl

/-- `shiftFrom` distributes over `letE` (definitional). -/
private theorem shiftFrom_letE (p : Nat) (ty v b : Expr) :
    shiftFrom p (.letE ty v b) =
      .letE (shiftFrom p ty) (shiftFrom p v) (shiftFrom p b) := rfl

/-- `getD` with the (shift-invariant) `bvar 0` default commutes with
mapping the shift. -/
private theorem getD_map_shiftFrom (p : Nat) :
    ∀ (l : List Expr) (n : Nat),
      (l.map (shiftFrom p)).getD n (.bvar 0) =
        shiftFrom p (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons x xs ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n => simpa [List.getD] using ih n

/-- `getD` with the `bvar 0` default preserves well-scopedness. -/
private theorem WScoped_getD {d : Nat} :
    ∀ {l : List Expr}, (∀ x ∈ l, WScoped d x) → ∀ (n : Nat),
      WScoped d (l.getD n (.bvar 0)) := by
  intro l
  induction l with
  | nil => intro _ n; simp [List.getD, WScoped]
  | cons x xs ih =>
    intro h n
    cases n with
    | zero => exact h x (List.mem_cons_self ..)
    | succ n =>
      simpa [List.getD] using
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) n

/-- `isCtorApp` only reads head constants, which shifting preserves. -/
private theorem isCtorApp_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    isCtorApp env (shiftFrom p e) = isCtorApp env e := by
  unfold isCtorApp
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- `isUnitLikeTy` only reads a head constant, which shifting
preserves. -/
private theorem isUnitLikeTy_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    isUnitLikeTy env (shiftFrom p e) = isUnitLikeTy env e := by
  cases e <;> try rfl
  case fvar => rw [shiftFrom_fvar]; simp [isUnitLikeTy]

/-- `rawNatLit?` only reads literal and constant heads, which shifting
preserves. -/
private theorem rawNatLit?_shiftFrom (p : Nat) (e : Expr) :
    rawNatLit? (shiftFrom p e) = rawNatLit? e := by
  cases e <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl

/-- The constructor form of a literal is closed, hence shift-fixed. -/
private theorem shiftFrom_natLitToConstructor (p n : Nat) :
    shiftFrom p (natLitToConstructor n) = natLitToConstructor n := by
  cases n <;> rfl

/-- The literal-major conversion commutes with the shift. -/
private theorem litToCtorIfNat_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    litToCtorIfNat env (shiftFrom p e) = shiftFrom p (litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    show litToCtorIfNat env (.lit (.natVal n)) = _
    rw [litToCtorIfNat]
    split
    · rw [shiftFrom_natLitToConstructor]
    · rfl
  | .lit (.strVal _) => rfl
  | .bvar _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ => rfl
  | .fvar idx ty => simp [litToCtorIfNat, shiftFrom_fvar]

/-- Delta-unfolding commutes with the shift (stored values are closed
by `EnvWF`). -/
private theorem unfoldDefinition_shiftFrom {env : Env} (henv : EnvWF env)
    (p : Nat) (e : Expr) :
    unfoldDefinition env (shiftFrom p e) =
      (unfoldDefinition env e).map (shiftFrom p) := by
  unfold unfoldDefinition
  rw [getAppFn_shiftFrom]
  cases hfn : e.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const n us =>
  simp only [shiftFrom]
  cases hf : env.find? n with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case defnInfo cv value hint =>
      dsimp only
      split
      · have hval : (value.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          obtain ⟨-, -, -, -, hvalwf, -⟩ := henv _ (find?_mem hf)
          obtain ⟨hvc, -, -, -⟩ := hvalwf cv value hint rfl
          rw [hasFvar_instantiateLevelParams]
          exact hvc
        rw [getAppArgs_shiftFrom, Option.map_some]
        rw [show Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            (e.getAppArgs.map (shiftFrom p)) =
          shiftFrom p (Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs) from by
          rw [shiftFrom_mkAppN, shiftFrom_eq_self_of_not_hasFvar hval]]
      · rfl

/-- `headHint` only reads a head constant's name, which shifting
preserves. -/
private theorem headHint_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    headHint env (shiftFrom p e) = headHint env e := by
  unfold headHint
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- The lazy-delta *decision* only reads the head constant and its
level count, which shifting preserves (task #106). -/
private theorem unfoldableHead_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    unfoldableHead env (shiftFrom p e) = unfoldableHead env e := by
  unfold unfoldableHead
  rw [getAppFn_shiftFrom]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- The same-head test only reads app shapes and head constants, which
shifting preserves. -/
private theorem sameConstHeads_shiftFrom (p : Nat) (a b : Expr) :
    sameConstHeads (shiftFrom p a) (shiftFrom p b) = sameConstHeads a b := by
  cases a <;> cases b <;>
    try (first
      | rfl
      | (simp only [shiftFrom_fvar]; rfl))
  case app.app f₁ x₁ f₂ x₂ =>
    show sameConstHeads (.app (shiftFrom p f₁) (shiftFrom p x₁))
      (.app (shiftFrom p f₂) (shiftFrom p x₂)) = _
    unfold sameConstHeads
    dsimp only
    rw [getAppFn_shiftFrom, getAppFn_shiftFrom]
    generalize f₁.getAppFn = g₁
    generalize f₂.getAppFn = g₂
    cases g₁ <;> cases g₂ <;> (try simp only [shiftFrom_fvar]) <;> rfl

/-- Peeling a `∀`-telescope along arguments commutes with the shift. -/
private theorem piResidual_shiftFrom {p : Nat} :
    ∀ (as : List Expr) (t : Expr),
      piResidual (shiftFrom p t) (as.map (shiftFrom p)) =
        (piResidual t as).map (shiftFrom p)
  | [], t => rfl
  | a :: as, t => by
    cases t <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty body mb =>
      show piResidual ((shiftFrom p body).instantiate1 (shiftFrom p a))
        (as.map (shiftFrom p)) = _
      rw [← shiftFrom_instantiate1_gen]
      exact piResidual_shiftFrom as _

/-! ## The bisimulation claims -/

/-- `whnfCore` commutes with the fvar shift. -/
def WhnfCoreShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnfCore mode env fuel (d + 1) (shiftFrom p e) =
      (whnfCore mode env fuel d e).map (shiftFrom p)

/-- The `whnf` reduction loop commutes with the fvar shift. -/
def WhnfShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    whnf mode env fuel (d + 1) (shiftFrom p e) =
      (whnf mode env fuel d e).map (shiftFrom p)

/-- `inferTypeCore` commutes with the fvar shift. -/
def InferShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    inferTypeCore mode env fuel (d + 1) (shiftFrom p e) =
      (inferTypeCore mode env fuel d e).map (shiftFrom p)

/-- `isDefEqCore` is invariant under the fvar shift. -/
def DefEqShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {a b : Expr}, WScoped d a → WScoped d b →
    isDefEqCore mode env fuel (d + 1) (shiftFrom p a) (shiftFrom p b) =
      isDefEqCore mode env fuel d a b

/-- `annotateCore` commutes with the fvar shift. -/
def AnnotShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    annotateCore mode env fuel (d + 1) (shiftFrom p e) =
      (annotateCore mode env fuel d e).map (shiftFrom p)

/-- The knot's io slot commutes with the fvar shift (task #172 B4).
At a gate-off mode this is `InferShift` through `inferTypeIO_off`; at
the gated mode it is the io lane's own walk
(`inferIOCore_step` below). -/
def InferIOShift (mode : CheckMode) (env : Env) (fuel : Nat) : Prop :=
  ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
    inferTypeIO mode env fuel (d + 1) (shiftFrom p e) =
      (inferTypeIO mode env fuel d e).map (shiftFrom p)

/-- All entry-point bisimulation claims at one fuel. -/
structure ShiftClaims (mode : CheckMode) (env : Env) (fuel : Nat) : Prop where
  whnfCore : WhnfCoreShift mode env fuel
  whnf : WhnfShift mode env fuel
  infer : InferShift mode env fuel
  defeq : DefEqShift mode env fuel
  annotate : AnnotShift mode env fuel
  inferIO : InferIOShift mode env fuel

/-! ## Helper bodies at the same fuel

Every record-parameterized helper commutes with the shift, given the
entry-point claims at the same fuel (the helpers only call the record's
entry points; the three list helpers and `projFieldDom` recurse
structurally). -/

section Helpers

variable {env : Env} {fuel : Nat}

private theorem ensureSort_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    ensureSort (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      ensureSort (pureFns mode env fuel) env d e := by
  simp only [ensureSort]
  refine bind_congr _ (ih.whnf hpd hw) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]

/-- Task #161 P5: the ∀ clause's untrusted `pw` write is depth-shift
stable.  The chain read (`forallPw`) is shift-stable by
`forallPw_shiftFrom`; the leaf path is one `infer` and one
`ensureSort` — precisely the calls the `letE` clause already makes.
Its *result* is a `PropWhen`,
which carries no de Bruijn index, so the two sides agree on the nose
rather than up to `shiftFrom`. -/
private theorem annotPwPi_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    annotPwPi (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      annotPwPi (pureFns mode env fuel) env d e := by
  simp only [annotPwPi, typeSortPW_shiftFrom]
  cases typeSortPW env.find? e with
  | some pwI => rfl
  | none =>
    dsimp only
    refine bind_congr _ (ih.inferIO hpd hw) ?_
    intro t ht
    refine bind_congr_eq (ensureSort_shift henv ih hpd
      (inferTypeIO_WScoped henv fuel ht hw)) ?_
    intro v _
    rfl

/-- The λ twin of `annotPwPi_shift`.  The chain read (`lamPw`) is
shift-stable by `lamPw_shiftFrom`; the leaf path is two `infer`s and an
`ensureSort`. -/
private theorem annotPwLam_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    annotPwLam (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      annotPwLam (pureFns mode env fuel) env d e := by
  simp only [annotPwLam, proofPW_shiftFrom]
  cases proofPW env.find? e with
  | some pwI => rfl
  | none =>
    dsimp only
    refine bind_congr _ (ih.inferIO hpd hw) ?_
    intro bt hbt
    have hwbt : WScoped d bt := inferTypeIO_WScoped henv fuel hbt hw
    refine bind_congr _ (ih.inferIO hpd hwbt) ?_
    intro btt hbtt
    refine bind_congr_eq (ensureSort_shift henv ih hpd
      (inferTypeIO_WScoped henv fuel hbtt hwbt)) ?_
    intro vb _
    rfl

private theorem reduceNat_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) :
    reduceNat (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (reduceNat (pureFns mode env fuel) env d e).map
        (Option.map (shiftFrom p)) := by
  match e with
  | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    first
    | rfl
    | (simp only [shiftFrom_fvar]; rfl)
  | .app f a =>
    have hwfa : WScoped d f ∧ WScoped d a := by simpa only [WScoped] using hw
    match f with
    | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ _ | .forallE _ _ _
    | .letE _ _ _ | .lit _ | .proj _ _ _ =>
      first
      | rfl
      | (simp only [shiftFrom_app, shiftFrom_fvar]; rfl)
    | .const c us =>
      match us with
      | _ :: _ => rfl
      | [] =>
        show reduceNat _ env (d + 1) (.app (.const c []) (shiftFrom p a)) = _
        simp only [reduceNat]
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
        intro w _
        rw [rawNatLit?_shiftFrom]
        cases rawNatLit? w <;> rfl
    | .app g b =>
      have hwgb : WScoped d g ∧ WScoped d b := by
        simpa only [WScoped] using hwfa.1
      match g with
      | .bvar _ | .fvar _ _ | .sort _ | .lam _ _ _ | .forallE _ _ _
      | .letE _ _ _ | .lit _ | .proj _ _ _ | .app _ _ =>
        first
        | rfl
        | (simp only [shiftFrom_app, shiftFrom_fvar]; rfl)
      | .const c us =>
        match us with
        | _ :: _ => rfl
        | [] =>
          show reduceNat _ env (d + 1)
            (.app (.app (.const c []) (shiftFrom p b)) (shiftFrom p a)) = _
          simp only [reduceNat]
          refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
          · -- first argument first; the second only behind a literal (D15)
            refine bind_rel _ _ (ih.whnf hpd hwgb.2) ?_
            intro w₁ _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => rfl
            | some n₁ =>
              refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
              intro w₂ _
              rw [rawNatLit?_shiftFrom]
              cases rawNatLit? w₂ with
              | none => rfl
              | some n₂ =>
                dsimp only
                cases hres : natOpResult c n₁ n₂ with
                | none => rfl
                | some r =>
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                    rfl
          · refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.whnf hpd hwgb.2) ?_
            intro w₁ _
            rw [rawNatLit?_shiftFrom]
            cases rawNatLit? w₁ with
            | none => rfl
            | some n₁ =>
              refine bind_rel _ _ (ih.whnf hpd hwfa.2) ?_
              intro w₂ _
              rw [rawNatLit?_shiftFrom]
              cases rawNatLit? w₂ <;> rfl

/-- `reduceNat_shift` under the defeq-side fvar guard: the pruned
branch is `pure none` on both sides. -/
private theorem reduceNatIf_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hw : WScoped d e) (g : Bool) :
    (if g then reduceNat (pureFns mode env fuel) env (d + 1) (shiftFrom p e)
      else pure none) =
      (if g then reduceNat (pureFns mode env fuel) env d e
        else (pure none : CheckM (Option Expr))).map
        (Option.map (shiftFrom p)) := by
  cases g
  · rfl
  · exact reduceNat_shift henv ih hpd hw

/-- A `some` result of the guarded fold always comes from `reduceNat`
itself (the pruned branch returns `none`). -/
private theorem reduceNatIf_some {g : Bool} {x : CheckM (Option Expr)}
    {a : Expr} (h : (if g then x else pure none) = .ok (some a)) :
    x = .ok (some a) := by
  cases g
  · exact absurd h (by simp [pure, Except.pure])
  · exact h

private theorem iotaCerts_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (lic : Bool) :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      iotaCerts (pureFns mode env fuel) env (d + 1) lic (shiftFrom p ty)
          (args.map (shiftFrom p)) =
        iotaCerts (pureFns mode env fuel) env d lic ty args := by
  intro args
  induction args with
  | nil => intro ty _ _; rfl
  | cons arg rest ihrest =>
    intro ty hwty hwargs
    have hwarg : WScoped d arg := hwargs arg (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ rest, WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    match ty with
    | .forallE ty' body mb =>
      have hwty' : WScoped d ty' ∧ WScoped d body := by
        simpa only [WScoped] using hwty
      show (if lic && mb.pw.isNever then
          iotaCerts (pureFns mode env fuel) env (d + 1) lic
            ((shiftFrom p body).instantiate1 (shiftFrom p arg))
            (rest.map (shiftFrom p))
        else (do
          let ta ← (pureFns mode env fuel).inferIO (d + 1) (shiftFrom p arg)
          if ← (pureFns mode env fuel).defeq (d + 1) ta (shiftFrom p ty') then
            iotaCerts (pureFns mode env fuel) env (d + 1) lic
              ((shiftFrom p body).instantiate1 (shiftFrom p arg))
              (rest.map (shiftFrom p))
          else pure false : CheckM Bool)) =
        (if lic && mb.pw.isNever then
          iotaCerts (pureFns mode env fuel) env d lic (body.instantiate1 arg) rest
        else (do
          let ta ← (pureFns mode env fuel).inferIO d arg
          if ← (pureFns mode env fuel).defeq d ta ty' then
            iotaCerts (pureFns mode env fuel) env d lic (body.instantiate1 arg) rest
          else pure false : CheckM Bool))
      have hrest := ihrest (WScoped.instantiate1_gen hwarg 0 hwty'.2) hwrest
      rw [shiftFrom_instantiate1_gen] at hrest
      by_cases hg : (lic && mb.pw.isNever) = true
      · rw [if_pos hg, if_pos hg]
        exact hrest
      · rw [if_neg hg, if_neg hg]
        refine bind_congr _ (ih.inferIO hpd hwarg) ?_
        intro ta hta
        refine bind_congr_eq
          (ih.defeq hpd (inferTypeIO_WScoped henv fuel hta hwarg)
            hwty'.1) ?_
        intro bb _
        refine ite_congr' (fun _ => ?_) (fun _ => rfl)
        exact hrest
    | .bvar i => rfl
    | .fvar idx ty'' => rw [shiftFrom_fvar]; rfl
    | .sort u => rfl
    | .const n' us => rfl
    | .app f a => rfl
    | .lam ty'' body' m' => rfl
    | .letE ty'' v' b' => rfl
    | .lit l => rfl
    | .proj sp i' e' => rfl

/-- The fabricated projections commute with the shift (task #175 W4c:
both entry kinds — the `.proj` nodes by `shiftFrom`'s own clause, the
projection-function applications by `shiftFrom_mkAppN`). -/
private theorem etaProjs_shift (p : Nat) (env : Env) (T : Name)
    (us : List Level) (targs : List Expr) (b : Expr) (nF : Nat) :
    etaProjs env T us (List.map (shiftFrom p) targs) (shiftFrom p b) nF
      = List.map (shiftFrom p) (etaProjs env T us targs b nF) := by
  unfold etaProjs
  split
  · rw [List.map_map]
    rfl
  · rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    rw [Function.comp_apply, shiftFrom_mkAppN, List.map_append]
    rfl

private theorem etaFabArgsE_shift (p : Nat) (env : Env) (T : Name)
    (ust : List Level) (targs : List Expr) (major : Expr) (nF : Nat) :
    etaFabArgsE env T ust (List.map (shiftFrom p) targs) (shiftFrom p major)
      nF = List.map (shiftFrom p) (etaFabArgsE env T ust targs major nF) := by
  unfold etaFabArgsE
  rw [List.map_append, etaProjs_shift]

private theorem defEqList_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      defEqList (pureFns mode env fuel) env (d + 1) (as.map (shiftFrom p))
          (bs.map (shiftFrom p)) =
        defEqList (pureFns mode env fuel) env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs _ _
    cases bs <;> rfl
  | cons a as ihas =>
    intro bs hwas hwbs
    cases bs with
    | nil => rfl
    | cons b bs =>
      have hwa : WScoped d a := hwas a (List.mem_cons_self ..)
      have hwb : WScoped d b := hwbs b (List.mem_cons_self ..)
      show ((do
          if ← (pureFns mode env fuel).defeq (d + 1) (shiftFrom p a)
              (shiftFrom p b) then
            defEqList (pureFns mode env fuel) env (d + 1)
              (as.map (shiftFrom p)) (bs.map (shiftFrom p))
          else pure false : CheckM Bool)) = _
      refine bind_congr_eq (ih.defeq hpd hwa hwb) ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      exact ihas (fun x hx => hwas x (List.mem_cons_of_mem _ hx))
        (fun x hx => hwbs x (List.mem_cons_of_mem _ hx))

/-- The lazy delta same-head spine congruence is invariant under the
shift: the head constants and levels are shift-fixed, the spine
lengths are preserved, and the argument comparisons commute
(`defEqList_shift`). -/
private theorem defeqSpine_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    defeqSpine (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
      (shiftFrom p b) = defeqSpine (pureFns mode env fuel) env d a b := by
  unfold defeqSpine
  rw [getAppFn_shiftFrom]
  cases hfa : a.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const n us =>
  dsimp only
  rw [getAppFn_shiftFrom]
  cases hfb : b.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const n' us' =>
  dsimp only
  rw [getAppArgs_shiftFrom, getAppArgs_shiftFrom]
  simp only [List.length_map]
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  cases Level.isEquivList us us' with
  | none => rfl
  | some r =>
    cases r with
    | true =>
      exact defEqList_shift _henv ih hpd hwa.getAppArgs hwb.getAppArgs
    | false => rfl

private theorem proofIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    proofIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      proofIrrel (pureFns mode env fuel) env d a b := by
  simp only [proofIrrel]
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.whnf hpd hwta) ?_
  intro wta _
  rw [isUnitLikeTy_shiftFrom]
  refine ite_congr' (fun _ => ?_) (fun _ => ?_)
  · refine bind_congr _ (ih.inferIO hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb _
    rw [isUnitLikeTy_shiftFrom]
  · refine bind_congr _ (ih.inferIO hpd hwta) ?_
    intro tta htta
    have hwtta : WScoped d tta := inferTypeIO_WScoped henv fuel htta hwta
    refine bind_congr _ (ih.whnf hpd hwtta) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]
    case sort u =>
    refine bind_congr_eq rfl ?_
    intro okA _
    refine bind_congr _ (ih.inferIO hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.inferIO hpd hwtb) ?_
    intro ttb httb
    have hwttb : WScoped d ttb := inferTypeIO_WScoped henv fuel httb hwtb
    refine bind_congr _ (ih.whnf hpd hwttb) ?_
    intro w' _
    cases w' <;> try rfl
    case fvar => rw [shiftFrom_fvar]

private theorem structEtaProjCerts_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (T : Name)
    (us' : List Level) {targs : List Expr} {b : Expr} (lpsT : List Name) :
    ∀ (idxs : List Nat), (∀ x ∈ targs, WScoped d x) → WScoped d b →
      structEtaProjCerts (pureFns mode env fuel) env (d + 1) T us'
          (targs.map (shiftFrom p)) (shiftFrom p b) lpsT idxs =
        structEtaProjCerts (pureFns mode env fuel) env d T us' targs b lpsT
          idxs := by
  intro idxs
  induction idxs with
  | nil => intro _ _; rfl
  | cons i rest ihrest =>
    intro hwtargs hwb
    simp only [structEtaProjCerts]
    cases hf : env.find? (projFnName T i) with
    | none => rfl
    | some ci =>
      cases ci <;> try rfl
      -- a tower-backed slot (task #175 S1) runs no certificate
      case recInfo cvp mI rP rules =>
      rw [List.length_map]
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have htel : (cvp.type.instantiateLevelParams cvp.levelParams
          us').hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1
      have h := iotaCerts_shift henv ih hpd false
        (ty := cvp.type.instantiateLevelParams cvp.levelParams us')
        (WScoped.of_not_hasFvar htel) (args := targs ++ [b]) (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hwtargs x hx
          · rw [List.mem_singleton.mp hx]; exact hwb)
      rw [shiftFrom_eq_self_of_not_hasFvar htel, List.map_append] at h
      simp only [List.map] at h
      refine bind_congr_eq h ?_
      intro bb _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      exact ihrest hwtargs hwb

private theorem structEtaCertWith_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b wtb : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) (hwwtb : WScoped d wtb) :
    structEtaCertWith mode (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) (shiftFrom p wtb) =
      structEtaCertWith mode (pureFns mode env fuel) env d a b wtb := by
  simp only [structEtaCertWith]
  rw [getAppFn_shiftFrom]
  cases hfa : a.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const c us =>
  simp only [shiftFrom]
  cases hfc : env.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case ctorInfo cvc cnP cnF =>
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    rw [getAppFn_shiftFrom]
    cases hfw : wtb.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]
    case const T us' =>
    simp only [shiftFrom]
    cases hfT : env.find? T with
    | none => rfl
    | some ciT =>
      cases ciT <;> try rfl
      case indInfo cvT caps =>
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      refine bind_congr_eq rfl ?_
      intro okl _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have htel : (cvT.type.instantiateLevelParams cvT.levelParams
          us').hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hfT)).1
      have h1 := iotaCerts_shift henv ih hpd false
        (ty := cvT.type.instantiateLevelParams cvT.levelParams us')
        (WScoped.of_not_hasFvar htel)
        (args := wtb.getAppArgs) (fun x hx => hwwtb.getAppArgs x hx)
      rw [shiftFrom_eq_self_of_not_hasFvar htel] at h1
      refine bind_congr_eq h1 ?_
      intro b₁ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      refine bind_congr_eq
        (ite_congr' (fun _ => rfl) (fun _ =>
          structEtaProjCerts_shift henv ih hpd T us' cvT.levelParams
            (List.range caps.etaFields)
            (fun x hx => hwwtb.getAppArgs x hx) hwb)) ?_
      intro b₂ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have h2 := defEqList_shift henv ih hpd (as := a.getAppArgs.take caps.etaParams)
        (bs := wtb.getAppArgs)
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_take hx))
        (fun x hx => hwwtb.getAppArgs x hx)
      rw [List.map_take] at h2
      refine bind_congr_eq h2 ?_
      intro b₃ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have hlist := etaProjs_shift p env T us' wtb.getAppArgs b caps.etaFields
      have hwprojs : ∀ x ∈ etaProjs env T us' wtb.getAppArgs b caps.etaFields,
          WScoped d x := by
        intro x hx
        unfold etaProjs at hx
        split at hx
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          simpa [WScoped] using hwb
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
          refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hwwtb.getAppArgs y hy
          · rw [List.mem_singleton.mp hy]; exact hwb
      -- task #137: the constructor-telescope certificate
      have htelc : (cvc.type.instantiateLevelParams cvc.levelParams
          us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hfc)).1
      have h4 := iotaCerts_shift henv ih hpd false
        (ty := cvc.type.instantiateLevelParams cvc.levelParams us)
        (WScoped.of_not_hasFvar htelc)
        (args := wtb.getAppArgs ++ etaProjs env T us' wtb.getAppArgs b caps.etaFields)
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hwwtb.getAppArgs x hx
          · exact hwprojs x hx)
      rw [shiftFrom_eq_self_of_not_hasFvar htelc, List.map_append,
        ← hlist] at h4
      -- task #147: the certificate is mode-gated; the gate is the same
      -- on both sides
      refine bind_congr_eq ?_ ?_
      · cases htt : mode.ttChecks
        · rfl
        · simpa using h4
      intro b₄ _
      refine ite_congr' (fun _ => ?_) (fun _ => rfl)
      have h3 := defEqList_shift henv ih hpd (as := a.getAppArgs.drop caps.etaParams)
        (bs := etaProjs env T us' wtb.getAppArgs b caps.etaFields)
        (fun x hx => hwa.getAppArgs x (List.mem_of_mem_drop hx))
        hwprojs
      rw [List.map_drop, ← hlist] at h3
      exact h3

/-- `etaCtorShape` reads the head constant and the spine length, both
shift-invariant. -/
private theorem etaCtorShape_shiftFrom {env : Env} (p : Nat) (e : Expr) :
    etaCtorShape env (shiftFrom p e) = etaCtorShape env e := by
  unfold etaCtorShape
  rw [getAppFn_shiftFrom, getAppArgs_shiftFrom, List.length_map]
  generalize e.getAppFn = f
  cases f <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem structEtaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structEtaCert mode (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structEtaCert mode (pureFns mode env fuel) env d a b := by
  simp only [structEtaCert]
  rw [etaCtorShape_shiftFrom]
  refine ite_congr' (fun _ => ?_) (fun _ => rfl)
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  exact structEtaCertWith_shift henv ih hpd hwa hwb
    (whnf_WScoped henv fuel hwtb' hwtb)

private theorem structUnitCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    structUnitCert (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      structUnitCert (pureFns mode env fuel) env d a b := by
  simp only [structUnitCert]
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.whnf hpd hwta) ?_
  intro wta hwta'
  have hwwta : WScoped d wta := whnf_WScoped henv fuel hwta' hwta
  rw [getAppFn_shiftFrom]
  cases hfn : wta.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case const T us' =>
  simp only [shiftFrom]
  cases hf : env.find? T with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case indInfo cvT caps =>
    rw [getAppArgs_shiftFrom, List.length_map]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    refine bind_congr _ (ih.inferIO hpd hwb) ?_
    intro tb htb
    have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
    refine bind_congr _ (ih.whnf hpd hwtb) ?_
    intro wtb hwtb'
    refine bind_congr_eq
      (ih.defeq hpd hwwta (whnf_WScoped henv fuel hwtb' hwtb)) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have h := iotaCerts_shift henv ih hpd false
      (ty := cvT.type.instantiateLevelParams cvT.levelParams us')
      (WScoped.of_not_hasFvar (by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1))
      (args := wta.getAppArgs) (fun x hx => hwwta.getAppArgs x hx)
    rw [shiftFrom_eq_self_of_not_hasFvar (by
      rw [hasFvar_instantiateLevelParams]
      exact (henv _ (find?_mem hf)).1)] at h
    exact h

private theorem etaCert_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d)
    {ty₁ body₁ : Expr} (m₁ : BinderMeta) {b : Expr}
    (hwty₁ : WScoped d ty₁) (hwbody₁ : WScoped d body₁)
    (hwb : WScoped d b) :
    etaCert mode (pureFns mode env fuel) env (d + 1) (shiftFrom p ty₁)
        (shiftFrom p body₁) m₁ (shiftFrom p b) =
      etaCert mode (pureFns mode env fuel) env d ty₁ body₁ m₁ b := by
  simp only [etaCert]
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.whnf hpd hwtb) ?_
  intro wtb hwtb'
  cases wtb <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case forallE ty₂ body₂ m₂ =>
    have hwPi : WScoped d (Expr.forallE ty₂ body₂ m₂) :=
      whnf_WScoped henv fuel hwtb' hwtb
    simp only [WScoped] at hwPi
    simp only [shiftFrom]
    refine bind_congr_eq (ih.defeq hpd hwPi.1 hwty₁) ?_
    intro bb _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have h := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 hwty₁ 0 hwbody₁)
      (show WScoped (d + 1) (Expr.app b (.fvar d ty₁)) by
        simp only [WScoped]
        exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwty₁⟩)
    rw [shiftFrom_instantiate1 hpd, show
        shiftFrom p (Expr.app b (.fvar d ty₁)) =
          Expr.app (shiftFrom p b) (.fvar (d + 1) (shiftFrom p ty₁))
      from by rw [shiftFrom_app, shiftFrom_fvar_ge hpd]] at h
    refine bind_congr_eq h ?_
    intro bb₂ _
    rfl

private theorem stuckIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    stuckIrrel mode (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      stuckIrrel mode (pureFns mode env fuel) env d a b := by
  simp only [stuckIrrel]
  refine bind_congr_eq (structEtaCert_shift henv ih hpd hwa hwb) ?_
  intro b₃ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (structEtaCert_shift henv ih hpd hwb hwa) ?_
  intro b₄ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr_eq (structUnitCert_shift henv ih hpd hwa hwb) ?_
  intro b₅ _
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  exact proofIrrel_shift henv ih hpd hwa hwb

/-- The hoisted `Prop`-branch test (task #168): the fast arm reads
head symbols only, which the shift preserves (`notProofFast_shiftFrom`);
the slow branch is `proofIrrel_shift`'s `Prop` branch. -/
private theorem propIrrel_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    propIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) =
      propIrrel (pureFns mode env fuel) env d a b := by
  simp only [propIrrel, notProofFast_shiftFrom, isProofFast_shiftFrom]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.inferIO hpd hwa) ?_
  intro ta hta
  have hwta : WScoped d ta := inferTypeIO_WScoped henv fuel hta hwa
  refine bind_congr _ (ih.inferIO hpd hwta) ?_
  intro tta htta
  have hwtta : WScoped d tta := inferTypeIO_WScoped henv fuel htta hwta
  refine bind_congr _ (ih.whnf hpd hwtta) ?_
  intro w _
  cases w <;> try rfl
  case fvar => rw [shiftFrom_fvar]
  case sort u =>
  refine bind_congr_eq rfl ?_
  intro okA _
  refine bind_congr _ (ih.inferIO hpd hwb) ?_
  intro tb htb
  have hwtb : WScoped d tb := inferTypeIO_WScoped henv fuel htb hwb
  refine bind_congr _ (ih.inferIO hpd hwtb) ?_
  intro ttb httb
  have hwttb : WScoped d ttb := inferTypeIO_WScoped henv fuel httb hwtb
  refine bind_congr _ (ih.whnf hpd hwttb) ?_
  intro w' _
  cases w' <;> try rfl
  case fvar => rw [shiftFrom_fvar]

private theorem projCert_shift (henv : EnvWF env) (ih : ShiftClaims mode env fuel)
    {p d : Nat} (hpd : p ≤ d) (lic : Bool) {c : Name} {us : List Level}
    {args : List Expr} (hwargs : ∀ x ∈ args, WScoped d x) :
    projCert (pureFns mode env fuel) env (d + 1) lic c us (args.map (shiftFrom p)) =
      projCert (pureFns mode env fuel) env d lic c us args := by
  simp only [projCert]
  split
  · rename_i cvC nP nF hf
    have hnf : (cvC.type.instantiateLevelParams cvC.levelParams us).hasFvar = false :=
      const_ty_hasFvar henv hf us
    have h := iotaCerts_shift henv ih hpd lic (WScoped.of_not_hasFvar hnf) hwargs
    rwa [shiftFrom_eq_self_of_not_hasFvar (p := p) hnf] at h
  · rfl

private theorem projCertAt_shift (henv : EnvWF env) (ih : ShiftClaims mode env fuel)
    {p d : Nat} (hpd : p ≤ d) (v lic : Bool) {c : Name} {us : List Level}
    {args : List Expr} (hwargs : ∀ x ∈ args, WScoped d x) :
    projCertAt (pureFns mode env fuel) env (d + 1) v lic c us (args.map (shiftFrom p)) =
      projCertAt (pureFns mode env fuel) env d v lic c us args := by
  unfold projCertAt
  split
  · exact projCert_shift henv ih hpd lic hwargs
  · rfl

private theorem majorToCtor_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (recName : Name)
    (rules : List RecRule) {major : Expr} (hwmaj : WScoped d major) :
    majorToCtor mode (pureFns mode env fuel) env (d + 1) recName rules
        (shiftFrom p major) =
      (majorToCtor mode (pureFns mode env fuel) env d recName rules major).map
        (shiftFrom p) := by
  simp only [majorToCtor]
  rw [isCtorApp_shiftFrom]
  refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
  cases rules with
  | nil => rfl
  | cons rl rest =>
    cases rest with
    | cons rl' rest' => rfl
    | nil =>
      dsimp only
      cases hfr : env.find? rl.ctor with
      | none => rfl
      | some ci =>
        cases ci <;> try rfl
        case ctorInfo cvj cnP cnF =>
        dsimp only
        cases hpi : (cvj.type.piResult).getAppFn <;> try rfl
        case const T us₀ =>
        dsimp only
        cases hfT : env.find? T with
        | none => rfl
        | some ciT =>
          cases ciT <;> try rfl
          case indInfo cvT caps =>
          dsimp only
          refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
          · -- K rescue
            refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
            intro tmaj₀ htmaj₀
            have hwtmaj₀ : WScoped d tmaj₀ :=
              inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
            refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
            intro tmaj htmaj
            have hwtmaj : WScoped d tmaj :=
              whnf_WScoped henv fuel htmaj hwtmaj₀
            rw [getAppFn_shiftFrom]
            cases hfn : tmaj.getAppFn <;> try rfl
            case fvar => rw [shiftFrom_fvar]; rfl
            case const T' ust =>
            simp only [shiftFrom]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            rw [getAppArgs_shiftFrom, List.length_map]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            have hfab : Expr.mkAppN (Expr.const rl.ctor ust)
                ((List.map (shiftFrom p) tmaj.getAppArgs).take cnP) =
                shiftFrom p (Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs.take cnP)) := by
              rw [shiftFrom_mkAppN, List.map_take]
              rfl
            rw [hfab]
            have hwfab : WScoped d (Expr.mkAppN (.const rl.ctor ust)
                (tmaj.getAppArgs.take cnP)) := by
              refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
              intro x hx
              exact hwtmaj.getAppArgs x (List.mem_of_mem_take hx)
            rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
              fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            -- the relocated synthetic-spine certificate (task #71)
            have htelC : (cvj.type.instantiateLevelParams cvj.levelParams
                ust).hasFvar = false := by
              rw [hasFvar_instantiateLevelParams]
              exact (henv _ (find?_mem hfr)).1
            have hcert := iotaCerts_shift henv ih hpd false
              (ty := cvj.type.instantiateLevelParams cvj.levelParams ust)
              (WScoped.of_not_hasFvar htelC)
              (args := tmaj.getAppArgs.take cnP)
              (fun x hx => hwtmaj.getAppArgs x (List.mem_of_mem_take hx))
            rw [shiftFrom_eq_self_of_not_hasFvar htelC, List.map_take]
              at hcert
            refine bind_rel_eq _ hcert ?_
            intro bc _
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel _ _ (ih.inferIO hpd hwfab) ?_
            intro tfab htfab
            have hwtfab : WScoped d tfab :=
              inferTypeIO_WScoped henv fuel htfab hwfab
            refine bind_rel_eq _ (ih.defeq hpd hwtmaj hwtfab) ?_
            intro bde _
            refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
            refine bind_rel_eq _ (proofIrrel_shift henv ih hpd hwfab hwmaj) ?_
            intro bb _
            exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
          · -- the structure-eta rescue, then the `And`-only rescue
            refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
            · -- structure-eta rescue
              refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
              intro tmaj₀ htmaj₀
              have hwtmaj₀ : WScoped d tmaj₀ :=
                inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
              refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
              intro tmaj htmaj
              have hwtmaj : WScoped d tmaj :=
                whnf_WScoped henv fuel htmaj hwtmaj₀
              rw [getAppFn_shiftFrom]
              cases hfn : tmaj.getAppFn <;> try rfl
              case fvar => rw [shiftFrom_fvar]; rfl
              case const T' ust =>
              simp only [shiftFrom]
              rw [getAppArgs_shiftFrom, List.length_map]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              rw [etaFabArgsE_shift]
              have hfab : Expr.mkAppN (Expr.const caps.etaCtor ust)
                  (List.map (shiftFrom p)
                    (etaFabArgsE env T ust tmaj.getAppArgs major
                      caps.etaFields)) =
                  shiftFrom p (Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE env T ust tmaj.getAppArgs major
                      caps.etaFields)) := by
                rw [shiftFrom_mkAppN]
                rfl
              rw [hfab]
              have hwfabArgs : ∀ x ∈ etaFabArgsE env T ust tmaj.getAppArgs
                  major caps.etaFields, WScoped d x := by
                intro x hx
                unfold etaFabArgsE at hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hwtmaj.getAppArgs x hx
                · unfold etaProjs at hx
                  split at hx
                  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                    simpa [WScoped] using hwmaj
                  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                    refine Expr.WScoped.mkAppN (by simp [WScoped]) ?_
                    intro y hy
                    rcases List.mem_append.mp hy with hy | hy
                    · exact hwtmaj.getAppArgs y hy
                    · rw [List.mem_singleton.mp hy]; exact hwmaj
              have hwfab : WScoped d (Expr.mkAppN (.const caps.etaCtor ust)
                  (etaFabArgsE env T ust tmaj.getAppArgs major
                    caps.etaFields)) :=
                Expr.WScoped.mkAppN (by simp [WScoped]) hwfabArgs
              rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
                fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              -- the relocated synthetic-spine certificate (task #71)
              have htelC : (cvj.type.instantiateLevelParams cvj.levelParams
                  ust).hasFvar = false := by
                rw [hasFvar_instantiateLevelParams]
                exact (henv _ (find?_mem hfr)).1
              have hcert := iotaCerts_shift henv ih hpd false
                (ty := cvj.type.instantiateLevelParams cvj.levelParams ust)
                (WScoped.of_not_hasFvar htelC)
                (args := etaFabArgsE env T ust tmaj.getAppArgs major
                  caps.etaFields)
                hwfabArgs
              rw [shiftFrom_eq_self_of_not_hasFvar htelC] at hcert
              refine bind_rel_eq _ hcert ?_
              intro bc _
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel_eq _
                (structEtaCertWith_shift henv ih hpd hwfab hwmaj hwtmaj) ?_
              intro bb _
              refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel_eq _
                (proofIrrel_shift henv ih hpd hwfab hwmaj) ?_
              intro bb' _
              exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
            · -- the `And`-only rescue (or no rescue)
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel _ _ (ih.inferIO hpd hwmaj) ?_
              intro tmaj₀ htmaj₀
              have hwtmaj₀ : WScoped d tmaj₀ :=
                inferTypeIO_WScoped henv fuel htmaj₀ hwmaj
              refine bind_rel _ _ (ih.whnf hpd hwtmaj₀) ?_
              intro tmaj htmaj
              have hwtmaj : WScoped d tmaj :=
                whnf_WScoped henv fuel htmaj hwtmaj₀
              rw [getAppFn_shiftFrom]
              cases hfn : tmaj.getAppFn <;> try rfl
              case fvar => rw [shiftFrom_fvar]; rfl
              case const T' ust =>
              simp only [shiftFrom]
              rw [getAppArgs_shiftFrom, List.length_map]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              have hlist : List.map (shiftFrom p) tmaj.getAppArgs ++
                  [Expr.proj T 0 (shiftFrom p major),
                    Expr.proj T 1 (shiftFrom p major)] =
                  List.map (shiftFrom p)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major]) := by
                rw [List.map_append]; rfl
              rw [hlist]
              have hfab : Expr.mkAppN (Expr.const rl.ctor ust)
                  (List.map (shiftFrom p)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major])) =
                  shiftFrom p (Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs ++
                      [Expr.proj T 0 major, Expr.proj T 1 major])) := by
                rw [shiftFrom_mkAppN]
                rfl
              rw [hfab]
              have hwfabArgs : ∀ x ∈ tmaj.getAppArgs ++
                  [Expr.proj T 0 major, Expr.proj T 1 major], WScoped d x := by
                intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hwtmaj.getAppArgs x hx
                · have hx' : x = Expr.proj T 0 major ∨
                      x = Expr.proj T 1 major := by simpa using hx
                  rcases hx' with rfl | rfl <;> simpa [WScoped] using hwmaj
              have hwfab : WScoped d (Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs ++
                    [Expr.proj T 0 major, Expr.proj T 1 major])) :=
                Expr.WScoped.mkAppN (by simp [WScoped]) hwfabArgs
              rw [wscopedB_shiftFrom _ hpd, looseBVarsBounded_shiftFrom,
                fvarLeaves_all_contains_shiftFrom hpd hwfab hwmaj]
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              -- the relocated synthetic-spine certificate (task #71)
              have htelC : (cvj.type.instantiateLevelParams cvj.levelParams
                  ust).hasFvar = false := by
                rw [hasFvar_instantiateLevelParams]
                exact (henv _ (find?_mem hfr)).1
              have hcert := iotaCerts_shift henv ih hpd false
                (ty := cvj.type.instantiateLevelParams cvj.levelParams ust)
                (WScoped.of_not_hasFvar htelC)
                (args := tmaj.getAppArgs ++
                  [Expr.proj T 0 major, Expr.proj T 1 major])
                hwfabArgs
              rw [shiftFrom_eq_self_of_not_hasFvar htelC] at hcert
              refine bind_rel_eq _ hcert ?_
              intro bc _
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel _ _ (ih.inferIO hpd hwfab) ?_
              intro tfab htfab
              have hwtfab : WScoped d tfab :=
                inferTypeIO_WScoped henv fuel htfab hwfab
              refine bind_rel_eq _ (ih.defeq hpd hwtmaj hwtfab) ?_
              intro bde _
              refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
              refine bind_rel_eq _ (proofIrrel_shift henv ih hpd hwfab hwmaj) ?_
              intro bb _
              exact ite_rel _ (fun _ => rfl) (fun _ => rfl)

/-- The scoping of an iota reduct (the `iotaRec` slice of the
`whnfPres_WScoped` proof, factored for the bisimulation).

**Public, not `private` like this file's other helpers**, because the
TTVerify bridge (`ConLeche/TTVerify/WhnfCoreStep.lean`) needs an iota
reduct's frame conditions from outside this file: its `IotaStepTT`
obligation has to hand the recursive `whnfCore` call a well-scoped
subject, exactly as the set model's `iota_sound` does.  Nothing else
about the lemma changes. -/
theorem iotaRec_WScoped (henv : EnvWF env)
    {d : Nat} {e e'' : Expr}
    (h : iotaRec mode (pureFns mode env fuel) env d e = .ok (some e''))
    (hw : WScoped d e) : WScoped d e'' := by
  obtain ⟨c, us, cv, mI, rP, rules, major, cj, usj,
    cvj, cnP, cnF, r, hfn, hfc, hlen, -, hprep,
    hmfn, hfj,
    hrule,
    hml, -, hlev, hpeq, hcerts, hmcerts, -, rfl⟩ :=
    iotaRec_inv h
  have hargs : ∀ x, x ∈ e.getAppArgs → WScoped d x :=
    fun x hx => hw.getAppArgs x hx
  have hrhs : WScoped d
      (r.rhs.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
    obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl r
      (List.mem_of_find?_eq_some hrule)
    exact WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hrf)
  have hmajw : WScoped d major := prepareMajorFueled_WScoped henv hprep
    (hargs _ (getD_mem (by omega)))
  refine Expr.WScoped.mkAppN hrhs ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hargs _ (List.mem_of_mem_take hx)
  · exact hmajw.getAppArgs _ (List.mem_of_mem_drop hx)

/-- Shifting commutes with the literal-major conversion (the string
branch reduces a closed term, invariant under shifting). -/
private theorem litMajorToCtor_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {e : Expr}, WScoped d e →
    litMajorToCtor (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (litMajorToCtor (pureFns mode env fuel) env d e).map (shiftFrom p)
  | .lit (.strVal s), _ => by
    show litMajorToCtor (pureFns mode env fuel) env (d + 1) (.lit (.strVal s)) = _
    simp only [litMajorToCtor]
    split
    · have hres := ih.whnf (p := p) hpd (strLitToConstructor_WScoped s d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    · rfl
  | .lit (.natVal n), _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.lit (.natVal n)))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .bvar i, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.bvar i))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .sort u, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.sort u))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .const n us, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.const n us))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .fvar idx ty, _ => by
    rw [shiftFrom_fvar]
    show pure (litToCtorIfNat env (.fvar (shiftIdx p idx) (shiftTy p idx ty))) = _
    rw [show (litToCtorIfNat env (.fvar (shiftIdx p idx) (shiftTy p idx ty))) =
      .fvar (shiftIdx p idx) (shiftTy p idx ty) from rfl]
    rw [show (litMajorToCtor (pureFns mode env fuel) env d (.fvar idx ty)) =
      pure (.fvar idx ty) from rfl]
    rw [show (Except.map (shiftFrom p) (pure (Expr.fvar idx ty)) :
        CheckM Expr) = pure (shiftFrom p (.fvar idx ty)) from rfl]
    rw [shiftFrom_fvar]
  | .app f a, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.app f a))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .lam ty body bi, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.lam ty body bi))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .forallE ty body bi, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.forallE ty body bi))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .letE ty v body, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.letE ty v body))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl
  | .proj sn i pe, _ => by
    show pure (litToCtorIfNat env (shiftFrom p (.proj sn i pe))) = _
    rw [litToCtorIfNat_shiftFrom]
    rfl

/-- Shifting commutes with the projection-scrutinee literal conversion
(the string branch reduces a closed term, invariant under shifting). -/
private theorem projLitToCtor_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) :
    ∀ {e : Expr}, WScoped d e →
    projLitToCtor (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (projLitToCtor (pureFns mode env fuel) env d e).map (shiftFrom p)
  | .lit (.strVal s), _ => by
    show projLitToCtor (pureFns mode env fuel) env (d + 1) (.lit (.strVal s)) = _
    simp only [projLitToCtor]
    split
    · have hres := ih.whnf (p := p) hpd (strLitToConstructor_WScoped s d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    · rfl
  | .lit (.natVal n), _ => rfl
  | .bvar i, _ => rfl
  | .sort u, _ => rfl
  | .const n us, _ => rfl
  | .fvar idx ty, _ => by
    rw [shiftFrom_fvar]
    show pure (Expr.fvar (shiftIdx p idx) (shiftTy p idx ty)) = _
    rw [show (projLitToCtor (pureFns mode env fuel) env d (.fvar idx ty)) =
      pure (.fvar idx ty) from rfl]
    rw [show (Except.map (shiftFrom p) (pure (Expr.fvar idx ty)) :
        CheckM Expr) = pure (shiftFrom p (.fvar idx ty)) from rfl]
    rw [shiftFrom_fvar]
  | .app f a, _ => rfl
  | .lam ty body bi, _ => rfl
  | .forallE ty body bi, _ => rfl
  | .letE ty v body, _ => rfl
  | .proj sn i pe, _ => rfl

private theorem iotaIndexOk_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d)
    {mI rP cnP : Nat} {tyCtor : Expr} (htel : tyCtor.hasFvar = false)
    {margs idx : List Expr} (hwm : ∀ x ∈ margs, WScoped d x)
    (hwi : ∀ x ∈ idx, WScoped d x) :
    iotaIndexOk (pureFns mode env fuel) env (d + 1) mI rP cnP tyCtor
        (margs.map (shiftFrom p)) (idx.map (shiftFrom p)) =
      iotaIndexOk (pureFns mode env fuel) env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, if_pos hmr]
  · simp only [iotaIndexOk, if_neg hmr]
    have hres := piResidual_shiftFrom (p := p) margs tyCtor
    rw [shiftFrom_eq_self_of_not_hasFvar htel] at hres
    rw [hres]
    cases hresid : piResidual tyCtor margs with
    | none => rfl
    | some residual =>
      simp only [Option.map_some]
      have hwres : WScoped d residual :=
        piResidual_WScoped hresid (WScoped.of_not_hasFvar htel) hwm
      have h4 := defEqList_shift henv ih hpd
        (as := residual.getAppArgs.drop cnP) (bs := idx)
        (fun x hx => hwres.getAppArgs x (List.mem_of_mem_drop hx)) hwi
      simp only [List.map_drop] at h4
      rw [← getAppArgs_shiftFrom] at h4
      exact h4

/-- The major chain commutes with the shift, in either order. -/
private theorem prepareMajor_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) (recName : Name)
    (rules : List RecRule) {major : Expr} (hwmaj : WScoped d major) :
    prepareMajor mode (pureFns mode env fuel) env (d + 1) recName rules
        (shiftFrom p major) =
      (prepareMajor mode (pureFns mode env fuel) env d recName rules major).map
        (shiftFrom p) := by
  simp only [prepareMajor]
  by_cases hk : recRuleK rules = true
  · rw [if_pos hk, if_pos hk]
    refine bind_rel _ _ (majorToCtor_shift henv ih hpd recName rules hwmaj) ?_
    intro m₁ hm₁
    have hw₁ : WScoped d m₁ := by
      rcases majorToCtor_inv hm₁ with rfl | ⟨hwsc, -, -, -⟩
      · exact hwmaj
      · exact WScoped.of_wscopedB hwsc
    refine bind_rel _ _ (ih.whnf hpd hw₁) ?_
    intro m₂ hm₂
    exact litMajorToCtor_shift henv ih hpd (whnf_WScoped henv fuel hm₂ hw₁)
  · rw [if_neg hk, if_neg hk]
    refine bind_rel _ _ (ih.whnf hpd hwmaj) ?_
    intro m₀ hm₀
    have hw₀ : WScoped d m₀ := whnf_WScoped henv fuel hm₀ hwmaj
    refine bind_rel _ _ (litMajorToCtor_shift henv ih hpd hw₀) ?_
    intro m₁ hm₁
    have hw₁ : WScoped d m₁ := by
      rcases litMajorToCtorFueled_inv hm₁ with rfl | ⟨s, -, -, hred⟩
      · exact litToCtorIfNat_WScoped hw₀
      · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
    exact majorToCtor_shift henv ih hpd recName rules hw₁

private theorem iotaRec_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {e : Expr}
    (hwe : WScoped d e) :
    iotaRec mode (pureFns mode env fuel) env (d + 1) (shiftFrom p e) =
      (iotaRec mode (pureFns mode env fuel) env d e).map
        (Option.map (shiftFrom p)) := by
  simp only [iotaRec]
  rw [getAppFn_shiftFrom]
  cases hfn : e.getAppFn <;> try rfl
  case fvar => rw [shiftFrom_fvar]; rfl
  case const c us =>
  simp only [shiftFrom]
  cases hfc : env.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    case recInfo cv mI rP rules =>
    dsimp only
    simp only [getAppArgs_shiftFrom, List.length_map]
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [getD_map_shiftFrom]
    have hwgd : WScoped d (e.getAppArgs.getD mI (.bvar 0)) :=
      WScoped_getD (fun x hx => hwe.getAppArgs x hx) _
    refine bind_rel _ _ (prepareMajor_shift henv ih hpd c rules hwgd) ?_
    intro major hmaj
    have hwmaj : WScoped d major := prepareMajorFueled_WScoped henv hmaj hwgd
    rw [getAppFn_shiftFrom]
    cases hmfn : major.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const cj usj =>
    simp only [shiftFrom]
    cases hfj : env.find? cj with
    | none => rfl
    | some cij =>
      cases cij <;> try rfl
      case ctorInfo cvj cnP cnF =>
      dsimp only
      cases hrule : rules.find? (fun r' => r'.ctor == cj) with
      | none => rfl
      | some rl =>
        dsimp only
        simp only [getAppArgs_shiftFrom, List.length_map]
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        refine ite_rel _ (fun _ => rfl) (fun _ => ?_)
        -- the level comparand does not read the argument spine
        refine bind_rel_eq _
          (by rw [recFireComparands_fst_congr rl cv.levelParams us
            cvj.levelParams (e.getAppArgs.map (shiftFrom p))
            e.getAppArgs rP]) ?_
        intro okl _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        -- the stored nested instantiations are fvar-free (`EnvWF`)
        have hpins : ∀ lvls pins, rl.fire = .nested lvls pins →
            ∀ pin ∈ pins, pin.hasFvar = false := by
          intro lvls pins hf' pin hpin
          obtain ⟨-, -, -, -, g5⟩ :=
            (henv _ (find?_mem hfc)).2.2.2.2.2.1 cv mI rP rules rfl rl
              (List.mem_of_find?_eq_some hrule)
          exact ((g5 lvls pins hf').2.2.1 pin hpin).1

        have h1 := defEqList_shift henv ih hpd
          (as := major.getAppArgs.take rl.ctorParams)
          (bs := (recFireComparands rl cv.levelParams us
            cvj.levelParams e.getAppArgs rP).2)
          (fun x hx => hwmaj.getAppArgs x (List.mem_of_mem_take hx))
          (recFireComparands_snd_WScoped rl cv.levelParams us
            cvj.levelParams e.getAppArgs rP
            (fun x hx => hwe.getAppArgs x hx) hpins)
        rw [← recFireComparands_snd_shift rl cv.levelParams us
          cvj.levelParams e.getAppArgs rP hpins,
          List.map_take] at h1
        refine bind_rel_eq _ ?_ ?_
        · by_cases hcp : rl.compareParams = true
          · rw [if_pos hcp, if_pos hcp]; exact h1
          · rw [if_neg hcp, if_neg hcp]
        intro b₁ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have htel₁ : (cv.type.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact (henv _ (find?_mem hfc)).1
        have h2 := iotaCerts_shift henv ih hpd mode.betaGate
          (ty := cv.type.instantiateLevelParams cv.levelParams us)
          (WScoped.of_not_hasFvar htel₁)
          (args := e.getAppArgs.take mI ++ [major])
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hwe.getAppArgs x (List.mem_of_mem_take hx)
            · rw [List.mem_singleton.mp hx]; exact hwmaj)
        rw [shiftFrom_eq_self_of_not_hasFvar htel₁] at h2
        simp only [List.map_append, List.map_take, List.map] at h2
        refine bind_rel_eq _ h2 ?_
        intro b₂ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have htel₂ : (cvj.type.instantiateLevelParams cvj.levelParams
            usj).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact (henv _ (find?_mem hfj)).1
        have h3 := iotaCerts_shift henv ih hpd mode.betaGate
          (ty := cvj.type.instantiateLevelParams cvj.levelParams usj)
          (WScoped.of_not_hasFvar htel₂)
          (args := major.getAppArgs)
          (fun x hx => hwmaj.getAppArgs x hx)
        rw [shiftFrom_eq_self_of_not_hasFvar htel₂] at h3
        refine bind_rel_eq _ h3 ?_
        intro b₃ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        -- the index comparison (only where indices exist): the closed
        -- telescope peeled along the shifted spines
        have hidx := iotaIndexOk_shift henv ih hpd htel₂
          (mI := mI) (rP := rP) (cnP := rl.ctorParams)
          (margs := major.getAppArgs) (idx := (e.getAppArgs.take mI).drop rP)
          (fun x hx => hwmaj.getAppArgs x hx)
          (fun x hx => hwe.getAppArgs x
            (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
        simp only [List.map_drop, List.map_take] at hidx
        refine bind_rel_eq _ hidx ?_
        intro b₄ _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have hrhs : (rl.rhs.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
          obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules rfl rl
            (List.mem_of_find?_eq_some hrule)
          rw [hasFvar_instantiateLevelParams]
          exact hrf
        have hout : Expr.mkAppN
            (rl.rhs.instantiateLevelParams cv.levelParams us)
            ((List.map (shiftFrom p) e.getAppArgs).take rP ++
              (List.map (shiftFrom p) major.getAppArgs).drop rl.ctorParams) =
            shiftFrom p (Expr.mkAppN
              (rl.rhs.instantiateLevelParams cv.levelParams us)
              (e.getAppArgs.take rP ++
                major.getAppArgs.drop rl.ctorParams)) := by
          rw [shiftFrom_mkAppN,
            shiftFrom_eq_self_of_not_hasFvar hrhs, List.map_append,
            List.map_take, List.map_drop]
        rw [hout]
        rfl

theorem instPis_WScoped {d : Nat} :
    ∀ {as : List Expr} {t res : Expr}, Expr.instPis t as = some res →
      WScoped d t → (∀ x ∈ as, WScoped d x) → WScoped d res
  | [], t, res, h, hw, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    exact h ▸ hw
  | a :: as, t, res, h, hw, has => by
    match t, h with
    | .forallE ty body mb, h =>
      have hw' : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hw
      have h' : Expr.instPis (body.instantiate1 a) as = some res := h
      exact instPis_WScoped h'
        (WScoped.instantiate1_gen (has a (List.mem_cons_self ..)) 0 hw'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))

private theorem pisToLams_WScoped {d : Nat} :
    ∀ (k : Nat) {t body minor : Expr},
      Expr.pisToLams k t body = some minor →
      WScoped d t → WScoped d body → WScoped d minor
  | 0, t, body, minor, h, _, hwb => by
    simp only [Expr.pisToLams, Option.some.injEq] at h
    exact h ▸ hwb
  | k + 1, t, body, minor, h, hwt, hwb => by
    match t, h with
    | .forallE ty rest mb, h =>
      have hw' : WScoped d ty ∧ WScoped d rest := by
        simpa only [WScoped] using hwt
      simp only [Expr.pisToLams] at h
      cases hin : Expr.pisToLams k rest body with
      | none => rw [hin] at h; exact nomatch h
      | some b' =>
        rw [hin] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [WScoped]
        exact ⟨hw'.1, pisToLams_WScoped k hin hw'.2 hwb⟩

/-! ## The body step lemmas -/

private theorem whnfCore_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : WhnfCoreShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [whnfCore_succ, whnfCore_succ]
  match e with
  | .bvar i => rfl
  | .sort u => rfl
  | .fvar idx ty =>
    rw [shiftFrom_fvar]
    simp only [whnfCoreBody, pure, Except.pure, map_ok, shiftFrom_fvar]
  | .forallE ty body mb => rfl
  | .lam ty body mb => rfl
  | .const n us => rfl
  | .lit l => rfl
  | .letE ty v body =>
    -- task #241: both sides are the same positive `.internal` error
    rfl
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [whnfCoreBody]
    refine bind_rel _ _ (ih.whnfCore hpd hw.1) ?_
    intro f' hf'
    have hwf' : WScoped d f' := whnfCore_WScoped henv fuel hf' hw.1
    have hiota : ∀ (f'' : Expr), WScoped d f'' →
        (iotaRec mode (pureFns mode env fuel) env (d + 1)
            (.app (shiftFrom p f'') (shiftFrom p a)) >>= fun o =>
          match o with
          | some e'' => (pureFns mode env fuel).whnfCore (d + 1) e''
          | none => pure (.app (shiftFrom p f'') (shiftFrom p a))) =
        ((iotaRec mode (pureFns mode env fuel) env d (.app f'' a) >>= fun o =>
          match o with
          | some e'' => (pureFns mode env fuel).whnfCore d e''
          | none => pure (.app f'' a)).map (shiftFrom p)) := by
      intro f'' hwf''
      have hwapp : WScoped d (Expr.app f'' a) := by
        simp only [WScoped]; exact ⟨hwf'', hw.2⟩
      refine bind_rel _ _ (iotaRec_shift henv ih hpd hwapp) ?_
      intro o ho
      cases o with
      | none => rfl
      | some e'' =>
        exact ih.whnfCore hpd (iotaRec_WScoped henv ho hwapp)
    cases f' with
    | lam ty₁ body₁ m₁ =>
      simp only [WScoped] at hwf'
      dsimp only [shiftFrom]
      -- task #161: the β gate's condition reads the binder's metadata,
      -- which `shiftFrom` copies verbatim, so the *same* branch is
      -- taken on both sides — one `split`, then the fired arm is the
      -- reduct step with no certificate and the other arm is the
      -- pre-gate proof, verbatim.
      by_cases hgate : betaGateFires mode m₁.pw = true
      · rw [if_pos hgate, if_pos hgate]
        have h := ih.whnfCore hpd
          (WScoped.instantiate1_gen hw.2 0 hwf'.2)
        rw [shiftFrom_instantiate1_gen] at h
        simp only [whnfCore_def]
        exact h
      · rw [if_neg hgate, if_neg hgate]
        -- task #172 B4: the certificate's inference is the io slot
        refine bind_rel _ _ (ih.inferIO hpd hw.2) ?_
        intro ta hta
        refine bind_rel_eq _
          (ih.defeq hpd (inferTypeIO_WScoped henv fuel hta hw.2)
            hwf'.1) ?_
        intro bb _
        refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
        have h := ih.whnfCore hpd
          (WScoped.instantiate1_gen hw.2 0 hwf'.2)
        rwa [shiftFrom_instantiate1_gen] at h
    | bvar i => exact hiota _ hwf'
    | fvar idx ty =>
      have h := hiota _ hwf'
      simp only [shiftFrom_fvar] at h ⊢
      exact h
    | sort u => exact hiota _ hwf'
    | const n' us => exact hiota _ hwf'
    | forallE ty' body' m' => exact hiota _ hwf'
    | letE ty' v' body' => exact hiota _ hwf'
    | lit l => exact hiota _ hwf'
    | proj s' i' e' => exact hiota _ hwf'
    | app f'' a'' => exact hiota _ hwf'
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show whnfCoreBody mode (pureFns mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (whnfCoreBody mode (pureFns mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [whnfCoreBody]
    refine bind_rel _ _ (ih.whnf hpd hw) ?_
    intro e₂ he₂
    have hwe₂ : WScoped d e₂ := whnf_WScoped henv fuel he₂ hw
    refine bind_rel _ _ (projLitToCtor_shift henv ih hpd hwe₂) ?_
    intro e₃ he₃
    have hwe₃ : WScoped d e₃ := by
      rcases projLitToCtorFueled_inv he₃ with rfl | ⟨s, -, -, hred⟩
      · exact hwe₂
      · exact whnf_WScoped henv fuel hred (strLitToConstructor_WScoped s d)
    cases hfp : env.findProj? sn i with
    | none => rfl
    | some entry =>
      rw [getAppFn_shiftFrom]
      cases hfn : e₃.getAppFn <;> try rfl
      case fvar => rw [shiftFrom_fvar]; rfl
      case const c us₂ =>
      simp only [shiftFrom]
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      rw [getD_map_shiftFrom]
      have hwarg : WScoped d
          (e₃.getAppArgs.getD (entry.numParams + i) (.bvar 0)) :=
        WScoped_getD (fun x hx => hwe₃.getAppArgs x hx) _
      refine bind_rel_eq _ (projCertAt_shift henv ih hpd mode.verifiedChecks mode.betaGate
        (fun x hx => hwe₃.getAppArgs x hx)) ?_
      intro bb _
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      exact ih.whnfCore hpd hwarg

/-- The reduction *loop* commutes with the shift, by induction on its
own step budget (task #106); the per-step head normalization comes
from the knot hypothesis `ih`. -/
theorem whnfLoop_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) :
    ∀ (n : Nat) {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      whnfLoop (pureFns mode env fuel) env (d + 1) n (shiftFrom p e) =
        (whnfLoop (pureFns mode env fuel) env d n e).map (shiftFrom p) := by
  intro n
  induction n with
  | zero => intro p d hpd e hw; rfl
  | succ n ihN =>
  intro p d hpd e hw
  simp only [whnfLoop, whnfStep]
  refine bind_rel _ _ (ih.whnfCore hpd hw) ?_
  intro e₁ he₁
  have hwe₁ : WScoped d e₁ := whnfCore_WScoped henv fuel he₁ hw
  refine bind_rel _ _ (reduceNat_shift henv ih hpd hwe₁) ?_
  intro o ho
  cases o with
  | some e₂ =>
    simp only [Option.map_some]
    have hwe₂ : WScoped d e₂ := by
      rcases reduceNat_inv ho with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ihN hpd hwe₂
  | none =>
    rw [unfoldDefinition_shiftFrom henv]
    cases hu : unfoldDefinition env e₁ with
    | none => rfl
    | some e₂ =>
      simp only [Option.map_some]
      exact ihN hpd (unfoldDefinition_WScoped henv hu hwe₁)

private theorem whnf_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : WhnfShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [whnf_succ, whnf_succ]
  exact whnfLoop_shift henv ih whnfLoopFuel hpd hw

/-- `instPisAt` commutes with the frame shift (task #175 wiring W2c:
the tower residual's depth invariance). -/
private theorem instPisAt_shiftFrom (p : Nat) :
    ∀ (args : List Expr) (ty : Expr),
      Expr.instPisAt (args.map (Expr.shiftFrom p)) (Expr.shiftFrom p ty)
        = (Expr.instPisAt args ty).map
            fun q => (q.1.map (Expr.shiftFrom p), Expr.shiftFrom p q.2) := by
  intro args
  induction args with
  | nil => intro ty; rfl
  | cons a as ih =>
    intro ty
    cases ty <;> try rfl
    case fvar idx ty =>
      simp only [shiftFrom]
      split <;> rfl
    case forallE dom body mb =>
      simp only [List.map_cons, shiftFrom, Expr.instPisAt,
        ← shiftFrom_instantiate1_gen, ih]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl

private theorem infer_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : InferShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [inferTypeCore_succ, inferTypeCore_succ]
  match e with
  | .bvar i => rfl
  | .letE ty v body =>
    -- task #241: both sides are the same positive `.internal` error
    rfl
  | .sort u => rfl
  | .lit (.natVal n) =>
    show inferBody mode (pureFns mode env fuel) env (d + 1) (.lit (.natVal n)) =
      (inferBody mode (pureFns mode env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [inferBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .lit (.strVal str) =>
    show inferBody mode (pureFns mode env fuel) env (d + 1) (.lit (.strVal str)) =
      (inferBody mode (pureFns mode env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [inferBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx ty =>
    simp only [WScoped] at hw
    rw [shiftFrom_fvar]
    simp only [inferBody]
    rw [if_pos (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        if_pos hw.1]
    by_cases hp : p ≤ idx
    · simp [shiftTy, hp, pure, Except.pure]
    · simp only [shiftTy, if_neg hp, pure, Except.pure, map_ok]
      rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
  | .const n us =>
    show inferBody mode (pureFns mode env fuel) env (d + 1) (.const n us) =
      (inferBody mode (pureFns mode env fuel) env d (.const n us)).map (shiftFrom p)
    simp only [inferBody]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hty : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1
      simp only [pure, Except.pure, map_ok,
        shiftFrom_eq_self_of_not_hasFvar hty]
  | .forallE ty body mb =>
    simp only [WScoped] at hw
    show inferBody mode (pureFns mode env fuel) env (d + 1)
        (.forallE (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBody mode (pureFns mode env fuel) env d (.forallE ty body mb)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ih.infer (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv fuel hbt hwo
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega) hwbt) ?_
    intro v _
    -- the ∀-annotation validation (task #161) is shift-invariant
    rw [apply_ite (Except.map (shiftFrom p))]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    rw [apply_ite (Except.map (shiftFrom p))]
    exact ite_congr' (fun _ => rfl) (fun _ => rfl)
  | .lam ty body mb =>
    simp only [WScoped] at hw
    show inferBody mode (pureFns mode env fuel) env (d + 1)
        (.lam (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBody mode (pureFns mode env fuel) env d (.lam ty body mb)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ih.infer (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCore_WScoped henv fuel hbt hwo
    -- the λ-annotation validation (tasks #152/#161) commutes: the
    -- body's head constructor and the data compared are
    -- shift-invariant
    rw [apply_ite (Except.map (shiftFrom p))]
    refine ite_congr' (fun hv => ?_)
      (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
    rw [lamPw_shiftFrom]
    cases hbp : body.lamPw with
    | some pwI =>
      rw [apply_ite (Except.map (shiftFrom p))]
      refine ite_congr'
        (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
        (fun _ => rfl)
    | none =>
      refine bind_rel _ _ (ih.inferIO (p := p) (d := d + 1)
        (by omega) hwbt) ?_
      intro btt hbtt
      have hwbtt : WScoped (d + 1) btt :=
        inferTypeIO_WScoped henv fuel hbtt hwbt
      refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
        (d := d + 1) (by omega) hwbtt) ?_
      intro v _
      rw [apply_ite (Except.map (shiftFrom p))]
      refine ite_congr'
        (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
        (fun _ => rfl)
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw.1) ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel htf hw.1)) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE ty' body' m' =>
    have hwPi : WScoped d (Expr.forallE ty' body' m') :=
      whnf_WScoped henv fuel hww (inferTypeCore_WScoped henv fuel htf hw.1)
    simp only [WScoped] at hwPi
    refine bind_rel _ _ (ih.infer hpd hw.2) ?_
    intro ta hta
    refine bind_rel_eq _
      (ih.defeq hpd (inferTypeCore_WScoped henv fuel hta hw.2) hwPi.1) ?_
    intro bb _
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    rw [← shiftFrom_instantiate1_gen]
    rfl
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show inferBody mode (pureFns mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (inferBody mode (pureFns mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [inferBody]
    refine bind_rel _ _ (ih.infer hpd hw) ?_
    intro te hte
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCore_WScoped henv fuel hte hw)) ?_
    intro w hww
    rw [getAppFn_shiftFrom]
    cases hfn : w.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const T us₂ =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => rfl
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun hc => ?_) (fun _ => rfl)
      -- task #175 S1: the body's instantiation commutes with the
      -- shift — the body is fvar-free, so the shift passes to the
      -- spine and the subject
      obtain ⟨-, hlen, -⟩ := hc
      have hsh := ProjEntry.typeAt_shiftFrom (p := p) henv hfp us₂ hlen pe
      -- the Prop guard (task #175 W4c) is shift-independent: split it
      -- on both sides, then the residual
      by_cases hs : (entry.structSort.isEquiv Level.zero == some true) = true
      · rw [if_pos hs, if_pos hs]
        by_cases hfs : ((Level.subst entry.levelParams us₂
            entry.fieldSort).isEquiv Level.zero == some true) = true
        · rw [if_pos hfs, if_pos hfs, ← hsh]
          rfl
        · rw [if_neg hfs, if_neg hfs]
          rfl
      · rw [if_neg hs, if_neg hs, ← hsh]
        rfl


/-- The io *lane* (the leaf knot, `inferTypeCoreIO`) commutes with the
shift (task #172 B4): `infer_step`'s walk with the io folds, the io
scoping lemmas, and the one gated clause split on its (shift-invariant)
datum. -/
private theorem inferIOCore_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel)
    (ihio : ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      inferTypeCoreIO mode env fuel (d + 1) (shiftFrom p e) =
        (inferTypeCoreIO mode env fuel d e).map (shiftFrom p)) :
    ∀ {p d : Nat}, p ≤ d → ∀ {e : Expr}, WScoped d e →
      inferTypeCoreIO mode env (fuel + 1) (d + 1) (shiftFrom p e) =
        (inferTypeCoreIO mode env (fuel + 1) d e).map (shiftFrom p) := by
  intro p d hpd e hw
  rw [inferTypeCoreIO_succ, inferTypeCoreIO_succ]
  match e with
  | .bvar i => rfl
  | .letE ty v body =>
    -- task #241: both sides are the same positive `.internal` error
    rfl
  | .sort u => rfl
  | .lit (.natVal n) =>
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1) (.lit (.natVal n)) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [inferBodyIO]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .lit (.strVal str) =>
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1) (.lit (.strVal str)) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [inferBodyIO]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx ty =>
    simp only [WScoped] at hw
    rw [shiftFrom_fvar]
    simp only [inferBodyIO]
    rw [if_pos (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        if_pos hw.1]
    by_cases hp : p ≤ idx
    · simp [shiftTy, hp, pure, Except.pure]
    · simp only [shiftTy, if_neg hp, pure, Except.pure, map_ok]
      rw [shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
  | .const n us =>
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1) (.const n us) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.const n us)).map (shiftFrom p)
    simp only [inferBodyIO]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      have hty : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).hasFvar = false := by
        rw [hasFvar_instantiateLevelParams]
        exact (henv _ (find?_mem hf)).1
      simp only [pure, Except.pure, map_ok,
        shiftFrom_eq_self_of_not_hasFvar hty]
  | .forallE ty body mb =>
    simp only [WScoped] at hw
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1)
        (.forallE (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.forallE ty body mb)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf, ensureSortIO_def]
    refine bind_rel _ _ (ihio hpd hw.1) ?_
    intro tty htty
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel htty hw.1)) ?_
    intro w _
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case sort u =>
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ihio (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCoreIO_WScoped henv fuel hbt hwo
    refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
      (d := d + 1) (by omega) hwbt) ?_
    intro v _
    -- the ∀-annotation validation (task #161) is shift-invariant
    rw [apply_ite (Except.map (shiftFrom p))]
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    rw [apply_ite (Except.map (shiftFrom p))]
    exact ite_congr' (fun _ => rfl) (fun _ => rfl)
  | .lam ty body mb =>
    simp only [WScoped] at hw
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1)
        (.lam (shiftFrom p ty) (shiftFrom p body) mb) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.lam ty body mb)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def,
      ensureSortIO_def]
    -- task #168 stage 2: no domain-sort run at the io λ clause
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d ty)) :=
      WScoped.instantiate1 hw.1 0 hw.2
    have hbody := ihio (p := p) (d := d + 1) (by omega) hwo
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro bt hbt
    have hwbt : WScoped (d + 1) bt :=
      inferTypeCoreIO_WScoped henv fuel hbt hwo
    -- the λ-annotation validation (tasks #152/#161) commutes: the
    -- body's head constructor and the data compared are
    -- shift-invariant
    rw [apply_ite (Except.map (shiftFrom p))]
    refine ite_congr' (fun hv => ?_)
      (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
    rw [lamPw_shiftFrom]
    cases hbp : body.lamPw with
    | some pwI =>
      rw [apply_ite (Except.map (shiftFrom p))]
      refine ite_congr'
        (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
        (fun _ => rfl)
    | none =>
      refine bind_rel _ _ (ihio (p := p) (d := d + 1)
        (by omega) hwbt) ?_
      intro btt hbtt
      have hwbtt : WScoped (d + 1) btt :=
        inferTypeCoreIO_WScoped henv fuel hbtt hwbt
      refine bind_rel_eq _ (ensureSort_shift henv ih (p := p)
        (d := d + 1) (by omega) hwbtt) ?_
      intro v _
      rw [apply_ite (Except.map (shiftFrom p))]
      refine ite_congr'
        (fun _ => by rw [← shiftFrom_abstract1 hpd]; rfl)
        (fun _ => rfl)
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf, pureFnsIO_defeq]
    refine bind_rel _ _ (ihio hpd hw.1) ?_
    intro tf htf
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel htf hw.1)) ?_
    intro w hww
    cases w <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case forallE ty' body' m' =>
    have hwPi : WScoped d (Expr.forallE ty' body' m') :=
      whnf_WScoped henv fuel hww (inferTypeCoreIO_WScoped henv fuel htf hw.1)
    simp only [WScoped] at hwPi
    dsimp only [shiftFrom]
    -- **the io gate**: the datum is the whnf'd type's own binder meta,
    -- which the shift copies verbatim, so both sides take one branch
    by_cases hg2 : m'.pw.isNever = true
    · simp only [hg2, if_true]
      simp only [pure, Except.pure, map_ok]
      rw [← shiftFrom_instantiate1_gen]
    · simp only [hg2, Bool.false_eq_true, if_false]
      refine bind_rel (shiftFrom p) _ (ihio hpd hw.2) ?_
      intro ta hta
      refine bind_rel_eq _
        (ih.defeq hpd (inferTypeCoreIO_WScoped henv fuel hta hw.2)
          hwPi.1) ?_
      intro bb _
      refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
      simp only [pure, Except.pure, map_ok]
      rw [← shiftFrom_instantiate1_gen]
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show inferBodyIO mode (pureFnsIO mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (inferBodyIO mode (pureFnsIO mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [inferBodyIO, inferIO_def,
      pureFnsIO_whnf]
    refine bind_rel _ _ (ihio hpd hw) ?_
    intro te hte
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeCoreIO_WScoped henv fuel hte hw)) ?_
    intro w hww
    rw [getAppFn_shiftFrom]
    cases hfn : w.getAppFn <;> try rfl
    case fvar => rw [shiftFrom_fvar]; rfl
    case const T us₂ =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => rfl
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      refine ite_rel _ (fun hc => ?_) (fun _ => rfl)
      -- task #175 S1: the body's instantiation commutes with the
      -- shift — the body is fvar-free, so the shift passes to the
      -- spine and the subject
      obtain ⟨-, hlen, -⟩ := hc
      have hsh := ProjEntry.typeAt_shiftFrom (p := p) henv hfp us₂ hlen pe
      -- the Prop guard (task #175 W4c) is shift-independent: split it
      -- on both sides, then the residual
      by_cases hs : (entry.structSort.isEquiv Level.zero == some true) = true
      · rw [if_pos hs, if_pos hs]
        by_cases hfs : ((Level.subst entry.levelParams us₂
            entry.fieldSort).isEquiv Level.zero == some true) = true
        · rw [if_pos hfs, if_pos hfs, ← hsh]
          rfl
        · rw [if_neg hfs, if_neg hfs]
          rfl
      · rw [if_neg hs, if_neg hs, ← hsh]
        rfl


/-- The knot's io *slot* commutes with the shift, at `fuel + 1`
(task #172 B4): at a gate-off mode it is `infer_step` through
`inferTypeIO_off`; at the gated mode it is the io lane's walk through
`inferTypeIO_on`. -/
private theorem inferIOSlot_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : InferIOShift mode env (fuel + 1) := by
  intro p d hpd e hw
  cases hg : mode.betaGate with
  | false =>
    rw [inferTypeIO_off hg, inferTypeIO_off hg]
    exact infer_step henv ih hpd hw
  | true =>
    rw [inferTypeIO_on hg, inferTypeIO_on hg]
    refine inferIOCore_step henv ih ?_ hpd hw
    intro p' d' hpd' e' hw'
    rw [← inferTypeIO_on hg, ← inferTypeIO_on hg]
    exact ih.inferIO hpd' hw'

private theorem isBoolTrue_shiftFrom {p : Nat} {e : Expr} :
    (shiftFrom p e).isBoolTrue = e.isBoolTrue := by
  cases e <;> first
    | rfl
    | (simp only [shiftFrom]; split <;> rfl)

/-- The eq-true shortcut (the audit's E2) is shift-invariant: one `whnf`
and a head test that ignores the shift. -/
private theorem boolTrueShortcut_shift (_henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a : Expr}
    (hwa : WScoped d a) :
    boolTrueShortcut (pureFns mode env fuel) (d + 1) (shiftFrom p a) =
      boolTrueShortcut (pureFns mode env fuel) d a := by
  unfold boolTrueShortcut
  refine bind_congr (shiftFrom p) (ih.whnf hpd hwa) ?_
  intro w _
  rw [isBoolTrue_shiftFrom]

/-- `boolTrueShortcut_shift` under its guard. -/
private theorem boolTrueShortcutIf_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a : Expr}
    (hwa : WScoped d a) (g : Bool) :
    (if g then boolTrueShortcut (pureFns mode env fuel) (d + 1) (shiftFrom p a)
        else pure false) =
      (if g then boolTrueShortcut (pureFns mode env fuel) d a else pure false) := by
  cases g
  · rfl
  · exact boolTrueShortcut_shift henv ih hpd hwa

private theorem quickPair_shiftFrom {p : Nat} {a b : Expr} :
    (shiftFrom p a).quickPair (shiftFrom p b) = a.quickPair b := by
  cases a <;> cases b <;> first
    | rfl
    | (simp only [shiftFrom]; (repeat split) <;> rfl)

/-- `propIrrel_shift` under the once-per-entry gate (the audit's D3). -/
private theorem propIrrelIf_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) {p d : Nat} (hpd : p ≤ d) {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) (g : Bool) :
    (if g then propIrrel (pureFns mode env fuel) env (d + 1) (shiftFrom p a)
        (shiftFrom p b) else pure false) =
      (if g then propIrrel (pureFns mode env fuel) env d a b
        else pure false) := by
  cases g
  · rfl
  · exact propIrrel_shift henv ih hpd hwa hwb

/-- The lazy-delta *loop* is shift-invariant, by induction on its own
step budget (task #106); the per-step `whnfCore`, proof irrelevance
and the structural congruences come from the knot hypothesis `ih`. -/
private theorem defeqLoop_shift (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) :
    ∀ (n : Nat) {p d : Nat}, p ≤ d → ∀ (pi : Bool) {a b : Expr},
      WScoped d a → WScoped d b →
      defeqLoop mode (pureFns mode env fuel) env (d + 1) n pi (shiftFrom p a)
          (shiftFrom p b) =
        defeqLoop mode (pureFns mode env fuel) env d n pi a b := by
  intro n
  induction n with
  | zero => intro p d _ pi a b _ _; rfl
  | succ n ihN =>
  intro p d hpd pi a b hwa hwb
  simp only [defeqLoop, defeqStep]
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  -- the eq-true shortcut (E2): its guard reads the shifted sides' head
  -- and fvar range, both shift-invariant
  rw [isBoolTrue_shiftFrom, hasFvar_shiftFrom]
  refine bind_congr_eq (boolTrueShortcutIf_shift henv ih hpd hwa _) ?_
  rintro rbt -
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  refine bind_congr _ (ih.whnfCore hpd hwa) ?_
  intro wa hwa'
  refine bind_congr _ (ih.whnfCore hpd hwb) ?_
  intro wb hwb'
  have hwwa : WScoped d wa := whnfCore_WScoped henv fuel hwa' hwa
  have hwwb : WScoped d wb := whnfCore_WScoped henv fuel hwb' hwb
  rw [shiftFrom_beq]
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  -- hoisted proof irrelevance (the `Prop` branch, task #168)
  rw [quickPair_shiftFrom]
  refine bind_congr_eq (propIrrelIf_shift henv ih hpd hwwa hwwb _) ?_
  rintro rpi -
  refine ite_congr' (fun _ => rfl) (fun _ => ?_)
  -- literal acceleration branches (guarded on fvar-free sides; the
  -- shift preserves the guard)
  simp only [hasFvar_shiftFrom]
  refine bind_congr (Option.map (shiftFrom p))
    (reduceNatIf_shift henv ih hpd hwwa _) ?_
  intro oa hoa
  cases oa with
  | some a₂ =>
    have hwa₂ : WScoped d a₂ := by
      rcases reduceNat_inv (reduceNatIf_some hoa) with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ihN hpd _ hwa₂ hwwb
  | none =>
  refine bind_congr (Option.map (shiftFrom p))
    (reduceNatIf_shift henv ih hpd hwwb _) ?_
  intro ob hob
  cases ob with
  | some b₂ =>
    have hwb₂ : WScoped d b₂ := by
      rcases reduceNat_inv (reduceNatIf_some hob) with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
        simp [WScoped]
    exact ihN hpd _ hwwa hwb₂
  | none =>
  simp only [Option.map_none]
  -- The lazy delta *decision* is taken before any unfolding is
  -- materialized (task #106); the decision, the hints and each
  -- unfolding are separately shift-invariant.
  have hunfL : ∀ {x y : Expr}, WScoped d x → WScoped d y →
      (match unfoldDefinition env (shiftFrom p x) with
        | some a₂ =>
          defeqLoop mode (pureFns mode env fuel) env (d + 1) n false a₂ (shiftFrom p y)
        | none => pure false) =
      (match unfoldDefinition env x with
        | some a₂ => defeqLoop mode (pureFns mode env fuel) env d n false a₂ y
        | none => pure false) := by
    intro x y hx hy
    rw [unfoldDefinition_shiftFrom henv]
    cases hu : unfoldDefinition env x with
    | none => rfl
    | some a₂ =>
      simp only [Option.map_some]
      exact ihN hpd _ (unfoldDefinition_WScoped henv hu hx) hy
  have hunfR : ∀ {x y : Expr}, WScoped d x → WScoped d y →
      (match unfoldDefinition env (shiftFrom p y) with
        | some b₂ =>
          defeqLoop mode (pureFns mode env fuel) env (d + 1) n false (shiftFrom p x) b₂
        | none => pure false) =
      (match unfoldDefinition env y with
        | some b₂ => defeqLoop mode (pureFns mode env fuel) env d n false x b₂
        | none => pure false) := by
    intro x y hx hy
    rw [unfoldDefinition_shiftFrom henv]
    cases hv : unfoldDefinition env y with
    | none => rfl
    | some b₂ =>
      simp only [Option.map_some]
      exact ihN hpd _ hx (unfoldDefinition_WScoped henv hv hy)
  have hunfB : ∀ {x y : Expr}, WScoped d x → WScoped d y →
      (match unfoldDefinition env (shiftFrom p x),
          unfoldDefinition env (shiftFrom p y) with
        | some a₂, some b₂ => defeqLoop mode (pureFns mode env fuel) env (d + 1) n false a₂ b₂
        | _, _ => pure false) =
      (match unfoldDefinition env x, unfoldDefinition env y with
        | some a₂, some b₂ => defeqLoop mode (pureFns mode env fuel) env d n false a₂ b₂
        | _, _ => pure false) := by
    intro x y hx hy
    rw [unfoldDefinition_shiftFrom henv, unfoldDefinition_shiftFrom henv]
    cases hu : unfoldDefinition env x <;> cases hv : unfoldDefinition env y <;>
      simp only [Option.map_some, Option.map_none] <;> try rfl
    exact ihN hpd _ (unfoldDefinition_WScoped henv hu hx)
      (unfoldDefinition_WScoped henv hv hy)
  rw [unfoldableHead_shiftFrom, unfoldableHead_shiftFrom]
  cases hda : unfoldableHead env wa with
  | true =>
    cases hdb : unfoldableHead env wb with
    | false => dsimp only; exact hunfL hwwa hwwb
    | true =>
      dsimp only
      rw [headHint_shiftFrom, headHint_shiftFrom]
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · exact hunfL hwwa hwwb
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · exact hunfR hwwa hwwb
      rw [sameConstHeads_shiftFrom]
      refine ite_congr' (fun _ => ?_) (fun _ => ?_)
      · refine bind_congr_eq (defeqSpine_shift henv ih hpd hwwa hwwb) ?_
        intro bb _
        refine ite_congr' (fun _ => rfl) (fun _ => ?_)
        exact hunfB hwwa hwwb
      · exact hunfB hwwa hwwb
  | false =>
  cases hdb : unfoldableHead env wb with
  | true => dsimp only; exact hunfR hwwa hwwb
  | false =>
  dsimp only
  have hstuck : stuckIrrel mode (pureFns mode env fuel) env (d + 1) (shiftFrom p wa)
      (shiftFrom p wb) = stuckIrrel mode (pureFns mode env fuel) env d wa wb :=
    stuckIrrel_shift henv ih hpd hwwa hwwb
  cases wa <;> cases wb <;>
    try (first
      | exact hstuck
      | (try simp only [shiftFrom_fvar] at hstuck
         simp only [shiftFrom_fvar]
         exact hstuck))
  case sort.sort => rfl
  case lit.lit => rfl
  case lit.const l cn cus hne =>
    cases l with
    | strVal str =>
      try simp only [shiftFrom_fvar] at hstuck
      exact hstuck
    | natVal n =>
      exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.lit cn cus l hne =>
    cases l with
    | strVal str =>
      try simp only [shiftFrom_fvar] at hstuck
      exact hstuck
    | natVal n =>
      exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lit.app l f x hne =>
    simp only [WScoped] at hwwb
    cases l with
    | strVal str =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
      case const cn cus =>
      refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
      have hres := ih.defeq (p := p) hpd
        (strLitToConstructor_WScoped str d)
        (show WScoped d (Expr.app (.const cn cus) x) by
          simp only [WScoped]; exact ⟨trivial, hwwb.2⟩)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    | natVal nn =>
      cases nn with
      | zero => exact hstuck
      | succ k =>
        cases f <;>
          try (first
            | exact hstuck
            | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
               exact hstuck))
        case const cn cus =>
        cases cus with
        | cons u us => exact hstuck
        | nil =>
          refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
          exact ih.defeq hpd (WScoped.of_not_hasFvar (e := .lit (.natVal k)) rfl) hwwb.2
  case app.lit f x l hne =>
    simp only [WScoped] at hwwa
    cases l with
    | strVal str =>
      cases f <;>
        try (first
          | exact hstuck
          | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
             exact hstuck))
      case const cn cus =>
      refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
      have hres := ih.defeq (p := p) hpd
        (show WScoped d (Expr.app (.const cn cus) x) by
          simp only [WScoped]; exact ⟨trivial, hwwa.2⟩)
        (strLitToConstructor_WScoped str d)
      rw [strLitToConstructor_shiftFrom] at hres
      exact hres
    | natVal nn =>
      cases nn with
      | zero => exact hstuck
      | succ k =>
        cases f <;>
          try (first
            | exact hstuck
            | (simp only [shiftFrom_app, shiftFrom_fvar] at hstuck ⊢
               exact hstuck))
        case const cn cus =>
        cases cus with
        | cons u us => exact hstuck
        | nil =>
          refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
          exact ih.defeq hpd hwwa.2 (WScoped.of_not_hasFvar (e := .lit (.natVal k)) rfl)
  case fvar.fvar idx₁ ty₁ idx₂ ty₂ hne =>
    simp only [shiftFrom_fvar] at hstuck ⊢
    rw [shiftIdx_beq]
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.const n us n' us' hne =>
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq rfl ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case forallE.forallE ty₁ body₁ m₁ ty₂ body₂ m₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine bind_congr_eq (ih.defeq hpd hwwa.1 hwwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hb := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 hwwb.1 0 hwwa.2)
      (WScoped.instantiate1 hwwb.1 0 hwwb.2)
    rw [shiftFrom_instantiate1 hpd, shiftFrom_instantiate1 hpd] at hb
    refine bind_congr_eq hb ?_
    intro b₂ _
    rfl
  case lam.lam ty₁ body₁ m₁ ty₂ body₂ m₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine bind_congr_eq (ih.defeq hpd hwwa.1 hwwb.1) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => rfl)
    have hb := ih.defeq (p := p) (d := d + 1) (by omega)
      (WScoped.instantiate1 hwwb.1 0 hwwa.2)
      (WScoped.instantiate1 hwwb.1 0 hwwb.2)
    rw [shiftFrom_instantiate1 hpd, shiftFrom_instantiate1 hpd] at hb
    refine bind_congr_eq hb ?_
    intro b₂ _
    rfl
  case app.app f₁ a₁ f₂ a₂ hne =>
    -- spine-wise congruence (task #106): one head comparison and the
    -- argument lists pairwise, all shift-invariant
    have hwa' : WScoped d (Expr.app f₁ a₁) := hwwa
    have hwb' : WScoped d (Expr.app f₂ a₂) := hwwb
    simp only [shiftFrom_app] at hstuck ⊢
    have hargs₁ : (Expr.app (shiftFrom p f₁) (shiftFrom p a₁)).getAppArgs
        = (Expr.app f₁ a₁).getAppArgs.map (shiftFrom p) :=
      getAppArgs_shiftFrom (.app f₁ a₁)
    have hargs₂ : (Expr.app (shiftFrom p f₂) (shiftFrom p a₂)).getAppArgs
        = (Expr.app f₂ a₂).getAppArgs.map (shiftFrom p) :=
      getAppArgs_shiftFrom (.app f₂ a₂)
    have hfn₁ : (Expr.app (shiftFrom p f₁) (shiftFrom p a₁)).getAppFn
        = shiftFrom p (Expr.app f₁ a₁).getAppFn :=
      getAppFn_shiftFrom (.app f₁ a₁)
    have hfn₂ : (Expr.app (shiftFrom p f₂) (shiftFrom p a₂)).getAppFn
        = shiftFrom p (Expr.app f₂ a₂).getAppFn :=
      getAppFn_shiftFrom (.app f₂ a₂)
    rw [hargs₁, hargs₂, List.length_map, List.length_map, hfn₁, hfn₂]
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq (ih.defeq hpd hwa'.getAppFn hwb'.getAppFn) ?_
    intro b₁ _
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq
      (defEqList_shift henv ih hpd hwa'.getAppArgs hwb'.getAppArgs) ?_
    intro b₂ _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case proj.proj s₁ i₁ e₁ s₂ i₂ e₂ hne =>
    simp only [WScoped] at hwwa hwwb
    refine ite_congr' (fun _ => ?_) (fun _ => hstuck)
    refine bind_congr_eq (ih.defeq hpd hwwa hwwb) ?_
    intro b₁ _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.bvar ty1 body1 m1 i hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.fvar ty1 body1 m1 ix tt hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.sort ty1 body1 m1 u hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.const ty1 body1 m1 cn cus hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.app ty1 body1 m1 ff aa hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.forallE ty1 body1 m1 fty fbody fm hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.letE ty1 body1 m1 lty lv lb hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.lit ty1 body1 m1 ll hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lam.proj ty1 body1 m1 ps pi2 pe2 hne =>
    simp only [WScoped] at hwwa
    have he := etaCert_shift henv ih hpd m1 hwwa.1 hwwa.2 hwwb
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case bvar.lam i ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case fvar.lam ix tt ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    try simp only [shiftFrom_fvar] at hstuck
    try simp only [shiftFrom_fvar]
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case sort.lam u ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case const.lam cn cus ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case app.lam ff aa ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case forallE.lam fty fbody fm ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case letE.lam lty lv lb ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case lit.lam ll ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)
  case proj.lam ps pi2 pe2 ty2 body2 m2 hne =>
    simp only [WScoped] at hwwb
    have he := etaCert_shift henv ih hpd m2 hwwb.1 hwwb.2 hwwa
    try simp only [shiftFrom_fvar] at he
    refine bind_congr_eq he ?_
    intro bb _
    exact ite_congr' (fun _ => rfl) (fun _ => hstuck)

private theorem defeq_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : DefEqShift mode env (fuel + 1) := by
  intro p d hpd a b hwa hwb
  rw [isDefEqCore_succ, isDefEqCore_succ]
  exact defeqLoop_shift henv ih defeqLoopFuel hpd true hwa hwb

private theorem annotate_step (henv : EnvWF env)
    (ih : ShiftClaims mode env fuel) : AnnotShift mode env (fuel + 1) := by
  intro p d hpd e hw
  rw [annotateCore_succ, annotateCore_succ]
  match e with
  | .bvar i => rfl
  | .sort u => rfl
  | .const n us => rfl
  | .lit (.strVal str) =>
    show annotateBody (pureFns mode env fuel) env (d + 1) (.lit (.strVal str)) =
      (annotateBody (pureFns mode env fuel) env d (.lit (.strVal str))).map
        (shiftFrom p)
    simp only [annotateBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .letE ty v body =>
    simp only [WScoped] at hw
    rw [shiftFrom_letE]
    show annotateBody (pureFns mode env fuel) env (d + 1)
        (.letE (shiftFrom p ty) (shiftFrom p v) (shiftFrom p body)) =
      (annotateBody (pureFns mode env fuel) env d (.letE ty v body)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro ty' hty'
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hw.1
    refine bind_rel _ _ (ih.infer hpd hwty') ?_
    intro tty htty
    refine bind_rel_eq _ (ensureSort_shift henv ih hpd
      (inferTypeCore_WScoped henv fuel htty hwty')) ?_
    intro u _
    refine bind_rel _ _ (ih.annotate hpd hw.2.1) ?_
    intro v' hv'
    have hwv' : WScoped d v' := annotateCore_WScoped fuel v hv' hw.2.1
    refine bind_rel _ _ (ih.infer hpd hwv') ?_
    intro tv htv
    refine bind_rel_eq _
      (ih.defeq hpd (inferTypeCore_WScoped henv fuel htv hwv') hwty') ?_
    intro bb _
    refine ite_rel _ (fun _ => ?_) (fun _ => rfl)
    have hbody := ih.annotate hpd
      (WScoped.instantiate1_gen hw.2.1 0 hw.2.2)
    rwa [shiftFrom_instantiate1_gen] at hbody
  | .lit (.natVal n) =>
    show annotateBody (pureFns mode env fuel) env (d + 1) (.lit (.natVal n)) =
      (annotateBody (pureFns mode env fuel) env d (.lit (.natVal n))).map
        (shiftFrom p)
    simp only [annotateBody]
    exact ite_rel _ (fun _ => rfl) (fun _ => rfl)
  | .fvar idx ty =>
    have hw' : idx < d ∧ WScoped idx ty := by
      simpa only [WScoped] using hw
    rw [shiftFrom_fvar]
    simp only [annotateBody]
    rw [if_pos (show shiftIdx p idx < d + 1 by
          simp only [shiftIdx]; split <;> omega),
        if_pos hw'.1]
    simp only [pure, Except.pure, map_ok, shiftFrom_fvar]
  | .app f a =>
    simp only [WScoped] at hw
    rw [shiftFrom_app]
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro f' hf'
    have hwf' : WScoped d f' := annotateCore_WScoped fuel f hf' hw.1
    refine bind_rel _ _ (ih.annotate hpd hw.2) ?_
    intro a' ha'
    rfl
  | .forallE ty body mb =>
    simp only [WScoped] at hw
    show annotateBody (pureFns mode env fuel) env (d + 1)
        (.forallE (shiftFrom p ty) (shiftFrom p body) mb) =
      (annotateBody (pureFns mode env fuel) env d (.forallE ty body mb)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro ty' hty'
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hw.1
    have hopen : WScoped (d + 1) (body.instantiate1 (.fvar d ty')) :=
      WScoped.instantiate1 hwty' 0 hw.2
    have hbody := ih.annotate (p := p) (d := d + 1) (by omega) hopen
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro body' hbody'
    have hwbody' : WScoped (d + 1) body' :=
      annotateCore_WScoped fuel _ hbody' hopen
    -- task #161 P5: the untrusted `pw` write, one bind further in.  The
    -- datum is index-free, so the two sides agree exactly; the `if` has
    -- the same condition on both.
    refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
    · refine bind_rel_eq _ (annotPwPi_shift henv ih (by omega) hwbody') ?_
      intro pw _
      rw [← shiftFrom_abstract1 hpd]
      rfl
    · refine bind_rel_eq _ rfl ?_
      intro pw _
      rw [← shiftFrom_abstract1 hpd]
      rfl
  | .lam ty body mb =>
    simp only [WScoped] at hw
    show annotateBody (pureFns mode env fuel) env (d + 1)
        (.lam (shiftFrom p ty) (shiftFrom p body) mb) =
      (annotateBody (pureFns mode env fuel) env d (.lam ty body mb)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw.1) ?_
    intro ty' hty'
    have hwty' : WScoped d ty' := annotateCore_WScoped fuel ty hty' hw.1
    have hopen : WScoped (d + 1) (body.instantiate1 (.fvar d ty')) :=
      WScoped.instantiate1 hwty' 0 hw.2
    have hbody := ih.annotate (p := p) (d := d + 1) (by omega) hopen
    rw [shiftFrom_instantiate1 hpd] at hbody
    refine bind_rel _ _ hbody ?_
    intro body' hbody'
    have hwbody' : WScoped (d + 1) body' :=
      annotateCore_WScoped fuel _ hbody' hopen
    -- task #161 P5: the untrusted `pw` write, one bind further in.  The
    -- datum is index-free, so the two sides agree exactly; the `if` has
    -- the same condition on both.
    refine ite_rel _ (fun _ => ?_) (fun _ => ?_)
    · refine bind_rel_eq _ (annotPwLam_shift henv ih (by omega) hwbody') ?_
      intro pw _
      rw [← shiftFrom_abstract1 hpd]
      rfl
    · refine bind_rel_eq _ rfl ?_
      intro pw _
      rw [← shiftFrom_abstract1 hpd]
      rfl
  | .proj sn i pe =>
    simp only [WScoped] at hw
    show annotateBody (pureFns mode env fuel) env (d + 1)
        (.proj sn i (shiftFrom p pe)) =
      (annotateBody (pureFns mode env fuel) env d (.proj sn i pe)).map
        (shiftFrom p)
    simp only [annotateBody]
    refine bind_rel _ _ (ih.annotate hpd hw) ?_
    intro e'' he''
    have hwe'' : WScoped d e'' := annotateCore_WScoped fuel pe he'' hw
    refine bind_rel _ _ (ih.inferIO hpd hwe'') ?_
    intro te₀ hte₀
    refine bind_rel _ _
      (ih.whnf hpd (inferTypeIO_WScoped henv fuel hte₀ hwe'')) ?_
    intro te hte
    rw [getAppFn_shiftFrom]
    cases hfn : te.getAppFn <;> try rfl
    case fvar =>
      rw [shiftFrom_fvar]
      rfl
    case const T cus =>
    simp only [shiftFrom]
    cases hfp : env.findProj? T i with
    | none => rfl
    | some entry =>
      dsimp only
      simp only [getAppArgs_shiftFrom, List.length_map]
      -- the node's structure name (task #271), then the parameter count
      exact ite_rel _ (fun _ => ite_rel _ (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl)

end Helpers

/-- The bisimulation: every core entry point commutes with the fvar
shift, at every fuel. -/
theorem shiftClaims {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat), ShiftClaims mode env fuel := by
  intro fuel
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ fuel ih =>
    exact ⟨whnfCore_step henv ih, whnf_step henv ih, infer_step henv ih,
      defeq_step henv ih, annotate_step henv ih, inferIOSlot_step henv ih⟩

/-! ## Depth invariance -/

section DepthInv

variable {env : Env}

private theorem whnfCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    whnfCore mode env fuel (d + 1) e = whnfCore mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).whnfCore (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnfCore mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnfCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem whnf_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    whnf mode env fuel (d + 1) e = whnf mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).whnf (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : whnf mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self (whnf_WScoped henv fuel hres hw).fvarsBelow]

private theorem inferTypeCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    inferTypeCore mode env fuel (d + 1) e = inferTypeCore mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).infer (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : inferTypeCore mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (inferTypeCore_WScoped henv fuel hres hw).fvarsBelow]

private theorem isDefEqCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {a b : Expr} (hwa : WScoped d a) (hwb : WScoped d b) :
    isDefEqCore mode env fuel (d + 1) a b = isDefEqCore mode env fuel d a b := by
  have h := (shiftClaims (mode := mode) henv fuel).defeq (Nat.le_refl d) hwa hwb
  rwa [shiftFrom_eq_self hwa.fvarsBelow, shiftFrom_eq_self hwb.fvarsBelow]
    at h

private theorem annotateCore_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    annotateCore mode env fuel (d + 1) e = annotateCore mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).annotate (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : annotateCore mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (annotateCore_WScoped fuel e hres hw).fvarsBelow]

private theorem whnfCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    whnfCore mode env fuel d₂ e = whnfCore mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnfCore_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem whnf_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    whnf mode env fuel d₂ e = whnf mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      whnf_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem inferTypeCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    inferTypeCore mode env fuel d₂ e = inferTypeCore mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      inferTypeCore_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem isDefEqCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {a b : Expr} (hwa : WScoped d₁ a)
    (hwb : WScoped d₁ b) :
    isDefEqCore mode env fuel d₂ a b = isDefEqCore mode env fuel d₁ a b := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      isDefEqCore_depth_succ henv fuel (hwa.mono (by omega))
        (hwb.mono (by omega)), ih]

private theorem inferTypeIO_depth_succ (henv : EnvWF env) (fuel : Nat)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    inferTypeIO mode env fuel (d + 1) e = inferTypeIO mode env fuel d e := by
  have h := (shiftClaims (mode := mode) henv fuel).inferIO (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [h]
  cases hres : inferTypeIO mode env fuel d e with
  | error err => rfl
  | ok r =>
    simp [shiftFrom_eq_self
      (inferTypeIO_WScoped henv fuel hres hw).fvarsBelow]

private theorem inferTypeIO_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    inferTypeIO mode env fuel d₂ e = inferTypeIO mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      inferTypeIO_depth_succ henv fuel (hw.mono (by omega)), ih]

private theorem annotateCore_depth_le (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) {e : Expr} (hw : WScoped d₁ e) :
    annotateCore mode env fuel d₂ e = annotateCore mode env fuel d₁ e := by
  obtain ⟨k, rfl⟩ : ∃ k, d₂ = d₁ + k := ⟨d₂ - d₁, by omega⟩
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show d₁ + (k + 1) = (d₁ + k) + 1 from rfl,
      annotateCore_depth_succ henv fuel (hw.mono (by omega)), ih]

/-- **Depth invariance of head normalization**: `whnfCore`'s result
does not depend on the ambient binder depth, for inputs well-scoped at
both depths. -/
theorem whnfCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnfCore mode env fuel d₁ e = whnfCore mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnfCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of the reduction loop**. -/
theorem whnf_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    whnf mode env fuel d₁ e = whnf mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₁)).symm
  · exact whnf_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of inference**. -/
theorem inferTypeCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    inferTypeCore mode env fuel d₁ e = inferTypeCore mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (inferTypeCore_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact inferTypeCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of the io inference slot** (task #172 B4). -/
theorem inferTypeIO_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    inferTypeIO mode env fuel d₁ e = inferTypeIO mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (inferTypeIO_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact inferTypeIO_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

/-- **Depth invariance of definitional equality**. -/
theorem isDefEqCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {a b : Expr} (ha₁ : a.wscopedB d₁ = true)
    (hb₁ : b.wscopedB d₁ = true) (ha₂ : a.wscopedB d₂ = true)
    (hb₂ : b.wscopedB d₂ = true) :
    isDefEqCore mode env fuel d₁ a b = isDefEqCore mode env fuel d₂ a b := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₁)
      (WScoped.of_wscopedB hb₁)).symm
  · exact isDefEqCore_depth_le henv fuel hle (WScoped.of_wscopedB ha₂)
      (WScoped.of_wscopedB hb₂)

/-- **Depth invariance of annotation**. -/
theorem annotateCore_depth_inv (henv : EnvWF env) (fuel : Nat)
    {d₁ d₂ : Nat} {e : Expr} (h₁ : e.wscopedB d₁ = true)
    (h₂ : e.wscopedB d₂ = true) :
    annotateCore mode env fuel d₁ e = annotateCore mode env fuel d₂ e := by
  rcases Nat.le_total d₁ d₂ with hle | hle
  · exact (annotateCore_depth_le henv fuel hle
      (WScoped.of_wscopedB h₁)).symm
  · exact annotateCore_depth_le henv fuel hle (WScoped.of_wscopedB h₂)

end DepthInv

end ConLeche
