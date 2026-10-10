import Ix.CompileCert.Opt.Total
import Ix.CompileCert.Canon.Loop

/-!
# M7 L3-def: core copies of the `partial` AuxGen helpers (design D-3), and abstraction

O2 and O11a build their adapted minors with the source-recursion helpers in
`Ix/AuxSource.lean` over the de Bruijn helpers of `Ix/AuxGen/ExprUtils.lean`,
several of which were originally `partial` (opaque to proofs). Ruling D-3 retains the total structural core
copy and the original `AuxGenCopies` proposition for compatibility. The actual abstraction
now uses one total lookup-function traversal. `AuxRuntime.lean` proves exact raw-result
equality for every supplied hash map and provides the unconditional witness `auxGenCopies`.
The fixture comparison remains regression evidence; it is not the proof of that equality.

* `batchAbstractP`: `Ix.AuxGen.batchAbstract` (the abstraction of `mkLambda`/`mkForall`);
* `babs`: what it does on erased terms (a variable of the telescope becomes a bound variable,
  the loose bound variables are lifted past the telescope), `er_batchAbstractP`;
* **`Conv.babs`**: conversion survives the abstraction (given `BAbsClosed Γ`, the rules closed
  under it, as rules over closed terms are: `bAbsClosed_of_closed`);
* **`mkLambda_conv`**: `mkLambda b ds` and `mkLambda b' ds` convert when `b` and `b'` do.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.CompileCert.Conv
open Ix.Compile.Pass.Opt

/-! ## The copies -/

/-- `Ix.AuxGen.batchAbstract`, total: the same clauses. -/
def batchAbstractP (expr : Expr) (fvarMap : Std.HashMap Name Nat) (scopeDepth internalDepth : Nat) :
    Expr :=
  if scopeDepth == 0 then expr
  else match expr with
  | .fvar name _ =>
    match fvarMap.get? name with
    | some pos =>
      if pos < scopeDepth then Expr.mkBVar ((scopeDepth - 1 - pos) + internalDepth)
      else expr
    | none => expr
  | .bvar i _ =>
    if i >= internalDepth then Expr.mkBVar (i + scopeDepth) else expr
  | .app f a _ =>
    Expr.mkApp (batchAbstractP f fvarMap scopeDepth internalDepth)
      (batchAbstractP a fvarMap scopeDepth internalDepth)
  | .lam n t b bi _ =>
    Expr.mkLam n (batchAbstractP t fvarMap scopeDepth internalDepth)
      (batchAbstractP b fvarMap scopeDepth (internalDepth + 1)) bi
  | .forallE n t b bi _ =>
    Expr.mkForallE n (batchAbstractP t fvarMap scopeDepth internalDepth)
      (batchAbstractP b fvarMap scopeDepth (internalDepth + 1)) bi
  | .letE n t v b nd _ =>
    Expr.mkLetE n (batchAbstractP t fvarMap scopeDepth internalDepth)
      (batchAbstractP v fvarMap scopeDepth internalDepth)
      (batchAbstractP b fvarMap scopeDepth (internalDepth + 1)) nd
  | .proj n i e _ =>
    Expr.mkProj n i (batchAbstractP e fvarMap scopeDepth internalDepth)
  | .mdata kvs e _ =>
    Expr.mkMData kvs (batchAbstractP e fvarMap scopeDepth internalDepth)
  | _ => expr

/-- The original executable-copy proposition, with its arbitrary-map domain unchanged.
`AuxRuntime.lean` supplies the unconditional exact-runtime witness `auxGenCopies`. -/
structure AuxGenCopies : Prop where
  batchAbstract : Ix.AuxGen.batchAbstract = batchAbstractP

/-! ## Abstraction on erased terms -/

/-- `batchAbstract` on erased terms: under `d` binders of the term, a free variable `n` with
`f n = some pos`, `pos < S`, becomes `bvar (S - 1 - pos + d)`; a loose `bvar i` (`i ≥ d`) is
lifted by `S`. -/
def babs (f : Name → Option Nat) (S : Nat) : Nat → Tm → Tm
  | d, .fvar n =>
    match f n with
    | some pos => if pos < S then .bvar (S - 1 - pos + d) else .fvar n
    | none => .fvar n
  | d, .bvar i => .bvar (if d ≤ i then i + S else i)
  | d, .app a b => .app (babs f S d a) (babs f S d b)
  | d, .lam t b => .lam (babs f S d t) (babs f S (d + 1) b)
  | d, .pi t b => .pi (babs f S d t) (babs f S (d + 1) b)
  | d, .letE t v b => .letE (babs f S d t) (babs f S d v) (babs f S (d + 1) b)
  | d, .proj s i e => .proj s i (babs f S d e)
  | _, .mvar x => .mvar x
  | _, .sort u => .sort u
  | _, .const c us => .const c us
  | _, .lit l => .lit l

section
variable (f : Name → Option Nat) (S : Nat)

theorem babs_zero : ∀ (d : Nat) (t : Tm), babs f 0 d t = t
  | d, .fvar n => by
    simp only [babs]
    cases f n with
    | none => rfl
    | some pos => simp
  | d, .bvar i => by simp only [babs, Nat.add_zero, ite_self]
  | d, .app a b => by simp only [babs, babs_zero d a, babs_zero d b]
  | d, .lam t b => by simp only [babs, babs_zero d t, babs_zero (d + 1) b]
  | d, .pi t b => by simp only [babs, babs_zero d t, babs_zero (d + 1) b]
  | d, .letE t v b => by simp only [babs, babs_zero d t, babs_zero d v, babs_zero (d + 1) b]
  | d, .proj s i e => by simp only [babs, babs_zero d e]
  | _, .mvar _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl

theorem babs_lift : ∀ (n c d : Nat) (t : Tm), c ≤ d →
    babs f S (d + n) (Tm.lift n c t) = Tm.lift n c (babs f S d t)
  | n, c, d, .fvar x, h => by
    simp only [Tm.lift, babs]
    cases f x with
    | none => rfl
    | some pos =>
      simp only
      by_cases hp : pos < S
      · simp only [hp, ↓reduceIte, Tm.lift]
        congr 1
        have : c ≤ S - 1 - pos + d := by omega
        simp only [this, ↓reduceIte]; omega
      · simp only [hp, ↓reduceIte, Tm.lift]
  | n, c, d, .bvar i, h => by
    simp only [Tm.lift, babs]
    congr 1
    by_cases h1 : c ≤ i <;> by_cases h2 : d ≤ i <;> simp only [h1, h2, ↓reduceIte] <;>
      (try split) <;> (try split) <;> omega
  | n, c, d, .app a b, h => by
    simp only [Tm.lift, babs, babs_lift n c d a h, babs_lift n c d b h]
  | n, c, d, .lam t b, h => by
    simp only [Tm.lift, babs, babs_lift n c d t h]
    rw [show d + n + 1 = (d + 1) + n by omega, babs_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, .pi t b, h => by
    simp only [Tm.lift, babs, babs_lift n c d t h]
    rw [show d + n + 1 = (d + 1) + n by omega, babs_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, .letE t v b, h => by
    simp only [Tm.lift, babs, babs_lift n c d t h, babs_lift n c d v h]
    rw [show d + n + 1 = (d + 1) + n by omega, babs_lift n (c + 1) (d + 1) b (by omega)]
  | n, c, d, .proj s i e, h => by simp only [Tm.lift, babs, babs_lift n c d e h]
  | _, _, _, .mvar _, _ | _, _, _, .sort _, _ | _, _, _, .const _ _, _ | _, _, _, .lit _, _ => rfl

theorem babs_inst : ∀ (v : Tm) (d k : Nat) (t : Tm),
    babs f S (d + k) (Tm.inst v k t) = Tm.inst (babs f S d v) k (babs f S (d + k + 1) t)
  | v, d, k, .bvar i => by
    simp only [Tm.inst, babs]
    by_cases hi : i = k
    · subst hi
      have h1 : ¬ (d + i + 1 ≤ i) := by omega
      simp only [h1, ↓reduceIte]
      have := babs_lift f S i 0 d v (Nat.zero_le _)
      exact this
    · simp only [hi, ↓reduceIte, babs]
      by_cases hk : k < i
      · by_cases h2 : d + k + 1 ≤ i
        · have h3 : d + k ≤ i - 1 := by omega
          have h4 : i + S ≠ k := by omega
          have h5 : k < i + S := by omega
          simp only [hk, h2, h3, ↓reduceIte, h4, h5]
          congr 1; omega
        · have h3 : ¬ d + k ≤ i - 1 := by omega
          simp only [hk, h2, h3, ↓reduceIte, hi]
      · have h2 : ¬ d + k + 1 ≤ i := by omega
        have h3 : ¬ d + k ≤ i := by omega
        simp only [hk, h2, h3, ↓reduceIte, hi]
  | v, d, k, .fvar x => by
    simp only [Tm.inst, babs]
    cases f x with
    | none => rfl
    | some pos =>
      simp only
      by_cases hp : pos < S
      · simp only [hp, ↓reduceIte, Tm.inst]
        have h1 : S - 1 - pos + (d + k + 1) ≠ k := by omega
        have h2 : k < S - 1 - pos + (d + k + 1) := by omega
        simp only [h1, h2, ↓reduceIte]
        congr 1
      · simp only [hp, ↓reduceIte, Tm.inst]
  | v, d, k, .app a b => by simp only [Tm.inst, babs, babs_inst v d k a, babs_inst v d k b]
  | v, d, k, .lam t b => by
    simp only [Tm.inst, babs, babs_inst v d k t]
    rw [show d + k + 1 = d + (k + 1) by omega, babs_inst v d (k + 1) b]
  | v, d, k, .pi t b => by
    simp only [Tm.inst, babs, babs_inst v d k t]
    rw [show d + k + 1 = d + (k + 1) by omega, babs_inst v d (k + 1) b]
  | v, d, k, .letE t w b => by
    simp only [Tm.inst, babs, babs_inst v d k t, babs_inst v d k w]
    rw [show d + k + 1 = d + (k + 1) by omega, babs_inst v d (k + 1) b]
  | v, d, k, .proj s i e => by simp only [Tm.inst, babs, babs_inst v d k e]
  | _, _, _, .mvar _ | _, _, _, .sort _ | _, _, _, .const _ _ | _, _, _, .lit _ => rfl

theorem occ_babs : ∀ (t : Tm) (d k : Nat), k < d → Tm.occ (babs f S d t) k = Tm.occ t k
  | .fvar x, d, k, h => by
    simp only [babs]
    cases f x with
    | none => rfl
    | some pos =>
      simp only
      split
      · simp only [Tm.occ]; simp; omega
      · rfl
  | .bvar i, d, k, h => by
    simp only [babs, Tm.occ]
    split
    · have h1 : i + S ≠ k := by omega
      have h2 : i ≠ k := by omega
      apply Bool.eq_iff_iff.2
      simp only [beq_iff_eq]
      constructor <;> intro h <;> omega
    · rfl
  | .app a b, d, k, h => by simp only [babs, Tm.occ, occ_babs a d k h, occ_babs b d k h]
  | .lam t b, d, k, h => by
    simp only [babs, Tm.occ, occ_babs t d k h, occ_babs b (d + 1) (k + 1) (by omega)]
  | .pi t b, d, k, h => by
    simp only [babs, Tm.occ, occ_babs t d k h, occ_babs b (d + 1) (k + 1) (by omega)]
  | .letE t v b, d, k, h => by
    simp only [babs, Tm.occ, occ_babs t d k h, occ_babs v d k h, occ_babs b (d + 1) (k + 1) (by omega)]
  | .proj s i e, d, k, h => by simp only [babs, Tm.occ, occ_babs e d k h]
  | .mvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl

theorem babs_appN (d : Nat) (g : Tm) (as : List Tm) :
    babs f S d (Tm.appN g as) = Tm.appN (babs f S d g) (as.map (babs f S d)) := by
  induction as generalizing g with
  | nil => rfl
  | cons a as ih => simp only [Tm.appN_cons, ih, babs, List.map_cons]

end

/-- No free variable. -/
def fvarFree : Tm → Bool
  | .fvar _ => false
  | .app a b => fvarFree a && fvarFree b
  | .lam t b | .pi t b => fvarFree t && fvarFree b
  | .letE t v b => fvarFree t && fvarFree v && fvarFree b
  | .proj _ _ e => fvarFree e
  | _ => true

theorem babs_of_closed (f : Name → Option Nat) (S : Nat) :
    ∀ (t : Tm) (d : Nat), t.range ≤ d → fvarFree t = true → babs f S d t = t
  | .bvar i, d, h, _ => by
    simp only [Tm.range] at h
    simp only [babs]
    have : ¬ d ≤ i := by omega
    simp only [this, ↓reduceIte]
  | .fvar _, _, _, h => by simp [fvarFree] at h
  | .app a b, d, h, hf => by
    simp only [Tm.range] at h
    simp only [fvarFree, Bool.and_eq_true] at hf
    simp only [babs, babs_of_closed f S a d (by omega) hf.1, babs_of_closed f S b d (by omega) hf.2]
  | .lam t b, d, h, hf => by
    simp only [Tm.range] at h
    simp only [fvarFree, Bool.and_eq_true] at hf
    simp only [babs, babs_of_closed f S t d (by omega) hf.1,
      babs_of_closed f S b (d + 1) (by omega) hf.2]
  | .pi t b, d, h, hf => by
    simp only [Tm.range] at h
    simp only [fvarFree, Bool.and_eq_true] at hf
    simp only [babs, babs_of_closed f S t d (by omega) hf.1,
      babs_of_closed f S b (d + 1) (by omega) hf.2]
  | .letE t v b, d, h, hf => by
    simp only [Tm.range] at h
    simp only [fvarFree, Bool.and_eq_true] at hf
    simp only [babs, babs_of_closed f S t d (by omega) hf.1.1, babs_of_closed f S v d (by omega) hf.1.2,
      babs_of_closed f S b (d + 1) (by omega) hf.2]
  | .proj s i e, d, h, hf => by
    simp only [Tm.range] at h
    simp only [fvarFree] at hf
    simp only [babs, babs_of_closed f S e d h hf]
  | .mvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl


/-- The rules are closed under the abstraction of `mkLambda`/`mkForall`. -/
def BAbsClosed (Γ : Env) : Prop :=
  ∀ f S d l r, Γ.ax l r → Γ.ax (babs f S d l) (babs f S d r)

/-- Rules between closed terms with no free variable (δ-rules of constants) are closed under it. -/
theorem bAbsClosed_of_closed {Γ : Env}
    (h : ∀ l r, Γ.ax l r → l.range = 0 ∧ r.range = 0 ∧ fvarFree l = true ∧ fvarFree r = true) :
    BAbsClosed Γ := by
  intro f S d l r hlr
  obtain ⟨h1, h2, h3, h4⟩ := h l r hlr
  rw [babs_of_closed f S l d (by omega) h3, babs_of_closed f S r d (by omega) h4]
  exact hlr

/-- **Conversion under the abstraction of `mkLambda`.** -/
theorem conv_babs {Γ : Env} (hΓ : BAbsClosed Γ) (f : Name → Option Nat) (S : Nat) {a b : Tm}
    (hc : Conv Γ a b) : ∀ d, Conv Γ (babs f S d a) (babs f S d b) := by
  induction hc with
  | refl a => exact fun _ => .refl _
  | symm _ ih => exact fun d => .symm (ih d)
  | trans _ _ ih1 ih2 => exact fun d => .trans (ih1 d) (ih2 d)
  | step s =>
    intro d
    cases s with
    | beta t b a =>
      have := babs_inst f S a d 0 b
      simp only [Nat.add_zero] at this
      show Conv Γ (Tm.app (Tm.lam (babs f S d t) (babs f S (d + 1) b)) (babs f S d a)) _
      rw [this]; exact .step (.beta _ _ _)
    | eta t g hg =>
      have hg' : Tm.occ (babs f S (d + 1) g) 0 = false := by
        rw [occ_babs f S g (d + 1) 0 (by omega)]; exact hg
      have e1 : babs f S d (g.lower 1 0) = (babs f S (d + 1) g).lower 1 0 := by
        rw [← Tm.inst_eq_lower (.bvar 0) 0 g hg, ← Tm.inst_eq_lower (babs f S d (.bvar 0)) 0 _ hg']
        have := babs_inst f S (.bvar 0) d 0 g
        simpa using this
      have e2 : babs f S (d + 1) (Tm.bvar 0) = Tm.bvar 0 := by
        simp only [babs]
        have : ¬ d + 1 ≤ 0 := by omega
        simp only [this, ↓reduceIte]
      simp only [babs]
      rw [e1]
      have e3 : Tm.app (babs f S (d + 1) g) (Tm.bvar (if d + 1 ≤ 0 then 0 + S else 0)) =
          Tm.app (babs f S (d + 1) g) (Tm.bvar 0) := by
        have : ¬ d + 1 ≤ 0 := by omega
        simp only [this, ↓reduceIte]
      rw [e3]
      exact .step (.eta _ _ hg')
    | proj0 s c us α β a b hpn =>
      simp only [babs, babs_appN, List.map_cons, List.map_nil]
      exact .step (.proj0 _ _ _ _ _ _ _ hpn)
    | proj1 s c us α β a b hpn =>
      simp only [babs, babs_appN, List.map_cons, List.map_nil]
      exact .step (.proj1 _ _ _ _ _ _ _ hpn)
    | ax hl => exact .step (.ax (hΓ _ _ _ _ _ hl))
  | app _ _ ih1 ih2 => exact fun d => .app (ih1 d) (ih2 d)
  | lam _ _ ih1 ih2 => exact fun d => .lam (ih1 d) (ih2 (d + 1))
  | pi _ _ ih1 ih2 => exact fun d => .pi (ih1 d) (ih2 (d + 1))
  | letE _ _ _ ih1 ih2 ih3 => exact fun d => .letE (ih1 d) (ih2 d) (ih3 (d + 1))
  | proj s i _ ih => exact fun d => .proj s i (ih d)

/-! ## The executables, erased -/

theorem er_batchAbstractP (m : Std.HashMap Name Nat) (S : Nat) :
    ∀ (e : Expr) (d : Nat), er (batchAbstractP e m S d) = babs (fun n => m.get? n) S d (er e) := by
  intro e
  by_cases hS : S = 0
  · subst hS
    intro d
    unfold batchAbstractP
    simp only [beq_self_eq_true, ↓reduceIte, babs_zero]
  · have hS' : (S == 0) = false := by simpa using hS
    induction e with
    | fvar n _ =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
      cases m.get? n with
      | none => rfl
      | some pos =>
        simp only
        split <;> simp [er]
    | bvar i _ =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
      by_cases hi : d ≤ i
      · have : (i ≥ d) := hi
        simp only [ge_iff_le, hi, ↓reduceIte, er_mkBVar]
      · simp only [ge_iff_le, hi, ↓reduceIte, er]
    | app f a _ ihf iha =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkApp, er, babs, ihf, iha]
    | lam n t b bi _ iht ihb =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkLam, er, babs, iht, ihb]
    | forallE n t b bi _ iht ihb =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkForallE, er, babs, iht, ihb]
    | letE n t v b nd _ iht ihv ihb =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkLetE, er, babs, iht, ihv,
        ihb]
    | proj n i e _ ihe =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkProj, er, babs, ihe]
    | mdata kvs e _ ihe =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er_mkMData, er, ihe]
    | mvar =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | sort =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | const =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]
    | lit =>
      intro d
      simp only [batchAbstractP, hS', Bool.false_eq_true, ↓reduceIte, er, babs]

/-- `mkBinderChain`'s binder loop, as a fold: each step wraps the result in one binder whose domain
does not depend on the result. -/
theorem binderLoop_conv {Γ : Env} (step : Ix.AuxGen.LocalDecl × Nat → Expr → Expr)
    (hstep : ∀ x a b, Conv Γ (er a) (er b) → Conv Γ (er (step x a)) (er (step x b))) :
    ∀ (l : List (Ix.AuxGen.LocalDecl × Nat)) (a b : Expr), Conv Γ (er a) (er b) →
      Conv Γ (er (l.foldl (fun r x => step x r) a)) (er (l.foldl (fun r x => step x r) b))
  | [], _, _, h => h
  | x :: l, a, b, h => binderLoop_conv step hstep l _ _ (hstep x a b h)

end Ix.CompileCert.Opt
