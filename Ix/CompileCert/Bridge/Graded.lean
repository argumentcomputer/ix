import Ix.CompileCert.Bridge.Induction

/-!
# M7 X2: graded readings, graph-regime β-reduction, and the annotation lemmas

**Graded readings** (`Graded`): the public-reading counterpart of IxC's `WellDenoted`: a term
whose every application applies a member of a product to a member of its domain, whose every
binder's body is graded over its domain, and whose squash-regime binders really carry proofs
(λ) or truth values (∀). A graded term denotes (`Graded.denotes`). Grading is semantic: it reads
only the denotations of subterms, so it survives lifting (`Graded.lift`) and substitution of a
graded value (`Graded.inst`) with nothing about the substituted value's syntax (a created redex
`(λ t. b) c` is graded exactly when `x c` was).

**Graph-regime β-reduction** (`RedB φ`): β at binders whose regime is positive at `φ`, closed under
every context. On graded terms it is sound and preserves grading (`RedB.sound`): the domain premise
of `semEq_beta` is automatic there (a graph is a member of a product only over its own domain,
`lam_dom_of_mem`, and never of a truth value). This is IxC's graph-regime β licence
(`Red.betaGate`, `WellDenotedV_beta_gate`) on the public reading. Squash-regime β, η and the pair
projections keep their premises (`Rules.lean`).

**The annotation lemmas.** The reader's terms carry `.never` at every binder (the bridge's form);
the checker installs its own annotations. (a) At an assignment where every binder of two terms is
in the graph regime, terms with one annotation erasure denote the same (`denotes_of_erasePw_pos`):
the bridge's reading *is* the installed reading there (`bridge_reading_pos`). (b) In the squash
regime every member of a product, and every inhabitant of a truth value, is the proof point
(`squash_pt`): both sides of an equation between proofs denote `pt`.
-/

namespace Ix.CompileCert.Bridge

open Kernel (Denotes push)
open Kernel.SetTheory Kernel.SetModel

universe u

section Graded

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

variable (cval env φ) in
/-- A semantically graded term (see the module docstring). -/
def Graded : (Nat → V) → Kernel.Expr → Prop
  | _, .bvar _ => True
  | _, .sort _ => True
  | ρ, .const n us => ∃ v, Denotes cval env φ ρ (.const n us) v
  | ρ, .app f a => Graded ρ f ∧ Graded ρ a ∧
      ∃ F X r A B, Denotes cval env φ ρ f F ∧ Denotes cval env φ ρ a X ∧ F ∈ˢ piR r A B ∧
        X ∈ˢ A ∧ (r = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)
  | ρ, .lam t b m => Graded ρ t ∧ ∃ A, Denotes cval env φ ρ t A ∧
      (∀ x, x ∈ˢ A → Graded (push x ρ) b) ∧
      (Kernel.regime φ m.pw = 0 → ∀ x, x ∈ˢ A → ∀ y, Denotes cval env φ (push x ρ) b y → y = pt)
  | ρ, .forallE t b m => Graded ρ t ∧ ∃ A, Denotes cval env φ ρ t A ∧
      (∀ x, x ∈ˢ A → Graded (push x ρ) b) ∧
      (Kernel.regime φ m.pw = 0 → ∀ x, x ∈ˢ A → ∀ y, Denotes cval env φ (push x ρ) b y →
        y ∈ˢ univ 0)
  | ρ, .proj s i e => Graded ρ e ∧ ∃ v, Denotes cval env φ ρ (.proj s i e) v
  | ρ, .lit l => ∃ v, Denotes cval env φ ρ (.lit l) v
  | _, .letE _ _ _ => False
  | _, .fvar _ _ => False

/-- A graded term denotes. -/
theorem Graded.denotes : ∀ {ρ : Nat → V} {e : Kernel.Expr}, Graded cval env φ ρ e →
    ∃ v, Denotes cval env φ ρ e v
  | ρ, .bvar i, _ => ⟨_, .bvar⟩
  | ρ, .sort l, _ => ⟨_, .sort⟩
  | ρ, .const n us, h => h
  | ρ, .app f a, h => by
    obtain ⟨-, -, F, X, -, -, -, hF, hX, -, -, -⟩ := h
    exact ⟨_, .app hF hX⟩
  | ρ, .lam t b m, h => by
    obtain ⟨-, A, hA, hb, hP⟩ := h
    classical
    have hd : ∀ x, x ∈ˢ A → ∃ y, Denotes cval env φ (push x ρ) b y := fun x hx => (hb x hx).denotes
    let F : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (hd x hx) else empty
    have hF : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (F x) := fun x hx => by
      simp only [F, hx, ↓reduceDIte]; exact Classical.choose_spec (hd x hx)
    exact ⟨_, .lam hA hF (fun h0 x hx => hP h0 x hx (F x) (hF x hx))⟩
  | ρ, .forallE t b m, h => by
    obtain ⟨-, A, hA, hb, hP⟩ := h
    classical
    have hd : ∀ x, x ∈ˢ A → ∃ y, Denotes cval env φ (push x ρ) b y := fun x hx => (hb x hx).denotes
    let B : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (hd x hx) else empty
    have hB : ∀ x, x ∈ˢ A → Denotes cval env φ (push x ρ) b (B x) := fun x hx => by
      simp only [B, hx, ↓reduceDIte]; exact Classical.choose_spec (hd x hx)
    exact ⟨_, .pi hA hB (fun h0 x hx => hP h0 x hx (B x) (hB x hx))⟩
  | ρ, .proj s i e, h => h.2
  | ρ, .lit l, h => h
  | _, .letE _ _ _, h => h.elim
  | _, .fvar _ _, h => h.elim

open Kernel.Expr in
/-- Grading survives lifting. -/
theorem Graded.lift (n : Nat) : ∀ (e : Kernel.Expr) {c : Nat} {ρ' : Nat → V},
    Graded cval env φ (liftEnv n c ρ') e → Graded cval env φ ρ' (liftLooseBVars n c e) := by
  intro e
  induction e with
  | bvar i => intro c ρ' _; by_cases h : i ≥ c <;> simp [liftLooseBVars, h, Graded]
  | fvar _ _ => intro c ρ' h; exact h.elim
  | sort l => intro c ρ' _; trivial
  | const x us =>
    intro c ρ' h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, denotes_lift n hv c ρ' rfl⟩
  | app f a ihf iha =>
    intro c ρ' h
    obtain ⟨gf, ga, F, X, r, A, B, hF, hX, hm, hXA, h0⟩ := h
    exact ⟨ihf gf, iha ga, F, X, r, A, B, denotes_lift n hF c ρ' rfl, denotes_lift n hX c ρ' rfl,
      hm, hXA, h0⟩
  | lam t b m iht ihb =>
    intro c ρ' h
    obtain ⟨gt, A, hA, hb, hP⟩ := h
    refine ⟨iht gt, A, denotes_lift n hA c ρ' rfl, fun x hx => ?_, fun h0 x hx y hy => ?_⟩
    · exact ihb (c := c + 1) (by rw [← push_liftEnv]; exact hb x hx)
    · obtain ⟨y₀, hy₀⟩ := (hb x hx).denotes
      have hl := denotes_lift n hy₀ (c + 1) (push x ρ') (by rw [push_liftEnv])
      rw [Kernel.Denotes_functional hy hl]; exact hP h0 x hx y₀ hy₀
  | forallE t b m iht ihb =>
    intro c ρ' h
    obtain ⟨gt, A, hA, hb, hP⟩ := h
    refine ⟨iht gt, A, denotes_lift n hA c ρ' rfl, fun x hx => ?_, fun h0 x hx y hy => ?_⟩
    · exact ihb (c := c + 1) (by rw [← push_liftEnv]; exact hb x hx)
    · obtain ⟨y₀, hy₀⟩ := (hb x hx).denotes
      have hl := denotes_lift n hy₀ (c + 1) (push x ρ') (by rw [push_liftEnv])
      rw [Kernel.Denotes_functional hy hl]; exact hP h0 x hx y₀ hy₀
  | letE _ _ _ _ _ _ => intro c ρ' h; exact h.elim
  | lit l =>
    intro c ρ' h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, denotes_lift n hv c ρ' rfl⟩
  | proj s i e ih =>
    intro c ρ' h
    obtain ⟨ge, v, hv⟩ := h
    exact ⟨ih ge, v, denotes_lift n hv c ρ' rfl⟩

open Kernel.Expr in
/-- Grading survives substitution of a graded value (below `k` binders). -/
theorem Graded.inst {a : Kernel.Expr} {x : V} : ∀ (e : Kernel.Expr) {k : Nat} {ρ' : Nat → V},
    Graded cval env φ (instEnv k x ρ') e → Denotes cval env φ (dropEnv k ρ') a x →
    Graded cval env φ (dropEnv k ρ') a → Graded cval env φ ρ' (e.instantiate1Lift a k) := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ' _ ha ga
    rcases Nat.lt_trichotomy i k with h1 | h1 | h1
    · have e2 : (Kernel.Expr.bvar i).instantiate1Lift a k = .bvar i := by
        simp [instantiate1Lift, Nat.ne_of_lt h1, Nat.not_lt.mpr (Nat.le_of_lt h1)]
      rw [e2]; trivial
    · subst h1
      have e2 : (Kernel.Expr.bvar i).instantiate1Lift a i = liftLooseBVars i 0 a := by
        simp [instantiate1Lift]
      rw [e2]
      exact Graded.lift i a (by rw [liftEnv_zero_cut]; exact ga)
    · have e2 : (Kernel.Expr.bvar i).instantiate1Lift a k = .bvar (i - 1) := by
        simp [instantiate1Lift, Nat.ne_of_gt h1, h1]
      rw [e2]; trivial
  | fvar _ _ => intro k ρ' h; exact h.elim
  | sort l => intro k ρ' _ _ _; trivial
  | const n us =>
    intro k ρ' h ha _
    obtain ⟨v, hv⟩ := h
    exact ⟨v, denotes_inst hv k ρ' a x rfl ha⟩
  | app f b ihf ihb =>
    intro k ρ' h ha ga
    obtain ⟨gf, gb, F, X, r, A, B, hF, hX, hm, hXA, h0⟩ := h
    exact ⟨ihf gf ha ga, ihb gb ha ga, F, X, r, A, B, denotes_inst hF k ρ' a x rfl ha,
      denotes_inst hX k ρ' a x rfl ha, hm, hXA, h0⟩
  | lam t b m iht ihb =>
    intro k ρ' h ha ga
    obtain ⟨gt, A, hA, hb, hP⟩ := h
    refine ⟨iht gt ha ga, A, denotes_inst hA k ρ' a x rfl ha, fun y hy => ?_,
      fun h0 y hy z hz => ?_⟩
    · exact ihb (k := k + 1) (by rw [← push_instEnv]; exact hb y hy)
        (by rw [dropEnv_push]; exact ha) (by rw [dropEnv_push]; exact ga)
    · obtain ⟨z₀, hz₀⟩ := (hb y hy).denotes
      have hi := denotes_inst hz₀ (k + 1) (push y ρ') a x (by rw [push_instEnv])
        (by rw [dropEnv_push]; exact ha)
      rw [Kernel.Denotes_functional hz hi]; exact hP h0 y hy z₀ hz₀
  | forallE t b m iht ihb =>
    intro k ρ' h ha ga
    obtain ⟨gt, A, hA, hb, hP⟩ := h
    refine ⟨iht gt ha ga, A, denotes_inst hA k ρ' a x rfl ha, fun y hy => ?_,
      fun h0 y hy z hz => ?_⟩
    · exact ihb (k := k + 1) (by rw [← push_instEnv]; exact hb y hy)
        (by rw [dropEnv_push]; exact ha) (by rw [dropEnv_push]; exact ga)
    · obtain ⟨z₀, hz₀⟩ := (hb y hy).denotes
      have hi := denotes_inst hz₀ (k + 1) (push y ρ') a x (by rw [push_instEnv])
        (by rw [dropEnv_push]; exact ha)
      rw [Kernel.Denotes_functional hz hi]; exact hP h0 y hy z₀ hz₀
  | letE _ _ _ _ _ _ => intro k ρ' h; exact h.elim
  | lit l =>
    intro k ρ' h ha _
    obtain ⟨v, hv⟩ := h
    exact ⟨v, denotes_inst hv k ρ' a x rfl ha⟩
  | proj s i e ih =>
    intro k ρ' h ha ga
    obtain ⟨ge, v, hv⟩ := h
    exact ⟨ih ge ha ga, v, denotes_inst hv k ρ' a x rfl ha⟩

/-- Substitution at the outermost binder. -/
theorem Graded.inst0 {ρ : Nat → V} {b a : Kernel.Expr} {x : V}
    (hb : Graded cval env φ (push x ρ) b) (ha : Denotes cval env φ ρ a x)
    (ga : Graded cval env φ ρ a) : Graded cval env φ ρ (b.instantiate1Lift a 0) := by
  have hd : dropEnv 0 ρ = ρ := by funext i; simp [dropEnv]
  refine Graded.inst b ?_ (by rw [hd]; exact ha) (by rw [hd]; exact ga)
  have : instEnv 0 x ρ = push x ρ := by funext i; cases i <;> simp [instEnv, Kernel.push]
  rw [this]; exact hb

/-- **β on graded terms in the graph regime**: sound, and the reduct is graded. -/
theorem Graded.beta {ρ : Nat → V} {t b a : Kernel.Expr} {m : Kernel.BinderMeta}
    (h : Graded cval env φ ρ (.app (.lam t b m) a)) (hpos : Kernel.regime φ m.pw ≠ 0) :
    SemEq cval env φ ρ (.app (.lam t b m) a) (b.instantiate1Lift a 0) ∧
      Graded cval env φ ρ (b.instantiate1Lift a 0) := by
  obtain ⟨gl, ga, F, X, r, A, B, hF, hX, hm, hXA, -⟩ := h
  obtain ⟨-, A', hA', hb, -⟩ := gl
  obtain ⟨A₀, F₀, hA₀, hF₀, hP₀, rfl⟩ := denotes_lam_inv hF
  obtain rfl := Kernel.Denotes_functional hA' hA₀
  have hr : r ≠ 0 := by
    intro hr0; subst hr0
    have hpt := eq_pt_of_mem_piR_zero hm
    rw [lamR_pos hpos] at hpt
    exact graph_ne_pt hpt
  have hdom : A' = A := lam_dom_of_mem hpos hr hm
  subst hdom
  exact ⟨semEq_beta (.lam hA₀ hF₀ hP₀) hX (fun A hA => (Kernel.Denotes_functional hA hA₀) ▸ hXA),
    Graded.inst0 (hb X hXA) hX ga⟩

end Graded

/-! ## Graph-regime β-reduction under every context -/

section RedB

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env}

/-- β at binders positive at `φ`, in every context, reflexive and transitive. -/
inductive RedB (φ : Kernel.Name → Nat) : Kernel.Expr → Kernel.Expr → Prop
  | refl (e : Kernel.Expr) : RedB φ e e
  | trans {a b c : Kernel.Expr} : RedB φ a b → RedB φ b c → RedB φ a c
  | beta {t b a : Kernel.Expr} {m : Kernel.BinderMeta} : Kernel.regime φ m.pw ≠ 0 →
      RedB φ (.app (.lam t b m) a) (b.instantiate1Lift a 0)
  | app {f f' a a' : Kernel.Expr} : RedB φ f f' → RedB φ a a' → RedB φ (.app f a) (.app f' a')
  | lam {t t' b b' : Kernel.Expr} {m : Kernel.BinderMeta} : RedB φ t t' → RedB φ b b' →
      RedB φ (.lam t b m) (.lam t' b' m)
  | pi {t t' b b' : Kernel.Expr} {m : Kernel.BinderMeta} : RedB φ t t' → RedB φ b b' →
      RedB φ (.forallE t b m) (.forallE t' b' m)
  | letE {t t' v v' b b' : Kernel.Expr} : RedB φ t t' → RedB φ v v' → RedB φ b b' →
      RedB φ (.letE t v b) (.letE t' v' b')
  | proj {s : Kernel.Name} {i : Nat} {e e' : Kernel.Expr} : RedB φ e e' →
      RedB φ (.proj s i e) (.proj s i e')

/-- **Soundness of graph-regime β-reduction on graded terms**: the reduct denotes the same and is
graded. -/
theorem RedB.sound {φ : Kernel.Name → Nat} {a b : Kernel.Expr} (h : RedB φ a b) :
    ∀ {ρ : Nat → V}, Graded cval env φ ρ a → SemEq cval env φ ρ a b ∧ Graded cval env φ ρ b := by
  induction h with
  | refl e => intro ρ g; obtain ⟨v, hv⟩ := g.denotes; exact ⟨SemEq.refl hv, g⟩
  | trans _ _ ih1 ih2 =>
    intro ρ g
    obtain ⟨s1, g1⟩ := ih1 g
    obtain ⟨s2, g2⟩ := ih2 g1
    exact ⟨s1.trans s2, g2⟩
  | beta hpos => intro ρ g; exact g.beta hpos
  | app _ _ ihf iha =>
    intro ρ g
    obtain ⟨gf, ga, F, X, r, A, B, hF, hX, hm, hXA, h0⟩ := g
    obtain ⟨sf, gf'⟩ := ihf gf
    obtain ⟨sa, ga'⟩ := iha ga
    exact ⟨sf.app sa, gf', ga', F, X, r, A, B, sf.value hF, sa.value hX, hm, hXA, h0⟩
  | lam _ _ iht ih =>
    intro ρ g
    obtain ⟨gt, A, hA, hb, hP⟩ := g
    obtain ⟨st, gt'⟩ := iht gt
    have hb' : ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) _ _ ∧ Graded cval env φ (push x ρ) _ :=
      fun x hx => ih (hb x hx)
    obtain ⟨Λ, hΛ⟩ := Graded.denotes (cval := cval) (env := env) (φ := φ) (ρ := ρ)
      (e := .lam _ _ _) ⟨gt, A, hA, hb, hP⟩
    refine ⟨SemEq.lam hΛ st (fun A' hA' x hx => ?_) rfl,
      gt', A, st.value hA, fun x hx => (hb' x hx).2, fun h0 x hx y hy => ?_⟩
    · obtain rfl := Kernel.Denotes_functional hA' hA
      exact (hb' x hx).1
    · obtain ⟨y₀, hy₀⟩ := (hb x hx).denotes
      have := (hb' x hx).1.value hy₀
      rw [Kernel.Denotes_functional hy this]; exact hP h0 x hx y₀ hy₀
  | pi _ _ iht ih =>
    intro ρ g
    obtain ⟨gt, A, hA, hb, hP⟩ := g
    obtain ⟨st, gt'⟩ := iht gt
    have hb' : ∀ x, x ∈ˢ A → SemEq cval env φ (push x ρ) _ _ ∧ Graded cval env φ (push x ρ) _ :=
      fun x hx => ih (hb x hx)
    obtain ⟨P, hPi⟩ := Graded.denotes (cval := cval) (env := env) (φ := φ) (ρ := ρ)
      (e := .forallE _ _ _) ⟨gt, A, hA, hb, hP⟩
    refine ⟨SemEq.pi hPi st (fun A' hA' x hx => ?_) rfl,
      gt', A, st.value hA, fun x hx => (hb' x hx).2, fun h0 x hx y hy => ?_⟩
    · obtain rfl := Kernel.Denotes_functional hA' hA
      exact (hb' x hx).1
    · obtain ⟨y₀, hy₀⟩ := (hb x hx).denotes
      have := (hb' x hx).1.value hy₀
      rw [Kernel.Denotes_functional hy this]; exact hP h0 x hx y₀ hy₀
  | letE _ _ _ _ _ _ => intro ρ g; exact g.elim
  | proj _ ih =>
    intro ρ g
    obtain ⟨ge, v, hv⟩ := g
    obtain ⟨se, ge'⟩ := ih ge
    have hs := se.proj hv
    exact ⟨hs, ge', hs.right⟩

end RedB

/-! ## The annotation lemmas -/

section Annotation

variable {V : Type u} [Kernel.SetTheory V] {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Every binder of a term is in the graph regime at `φ`. -/
def PosAt (φ : Kernel.Name → Nat) : Kernel.Expr → Prop
  | .app f a => PosAt φ f ∧ PosAt φ a
  | .lam t b m => Kernel.regime φ m.pw ≠ 0 ∧ PosAt φ t ∧ PosAt φ b
  | .forallE t b m => Kernel.regime φ m.pw ≠ 0 ∧ PosAt φ t ∧ PosAt φ b
  | .letE t v b => PosAt φ t ∧ PosAt φ v ∧ PosAt φ b
  | .proj _ _ e => PosAt φ e
  | .fvar _ _ => True
  | _ => True

theorem regime_ne_zero_iff {m m' : Kernel.BinderMeta} (h : Kernel.regime φ m.pw ≠ 0)
    (h' : Kernel.regime φ m'.pw ≠ 0) : Kernel.regime φ m.pw = Kernel.regime φ m'.pw := by
  unfold Kernel.regime at *
  split at h <;> split at h' <;> simp_all

/-- **(a) The reading is annotation-free in the graph regime**: two terms with one annotation
erasure, both graph-regime at `φ`, denote the same. -/
theorem denotes_of_erasePw_pos : ∀ {ρ : Nat → V} {e e' : Kernel.Expr} {v : V},
    e.erasePw = e'.erasePw → PosAt φ e → PosAt φ e' →
    Denotes cval env φ ρ e v → Denotes cval env φ ρ e' v := by
  intro ρ e e' v he hp hp' h
  induction h generalizing e' with
  | bvar => cases e' <;> simp [Kernel.Expr.erasePw] at he; subst he; exact .bvar
  | sort => cases e' <;> simp [Kernel.Expr.erasePw] at he; subst he; exact .sort
  | const hf hlen =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he; obtain ⟨rfl, rfl⟩ := he; exact .const hf hlen
  | app _ _ ihf iha =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case app f' a' => exact .app (ihf he.1 hp.1 hp'.1) (iha he.2 hp.2 hp'.2)
  | @lam ρ ty body m A F _ _ hP ihA ihF =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case lam ty' body' m' =>
      have hm := regime_ne_zero_iff hp.1 hp'.1
      rw [hm]
      exact .lam (ihA he.1 hp.2.1 hp'.2.1) (fun x hx => ihF x hx he.2 hp.2.2 hp'.2.2)
        (fun h0 => absurd h0 hp'.1)
  | @pi ρ ty body m A B _ _ hP ihA ihB =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case forallE ty' body' m' =>
      have hm := regime_ne_zero_iff hp.1 hp'.1
      rw [hm]
      exact .pi (ihA he.1 hp.2.1 hp'.2.1) (fun x hx => ihB x hx he.2 hp.2.2 hp'.2.2)
        (fun h0 => absurd h0 hp'.1)
  | proj_table ht _ ih =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case proj s' i' e'' => obtain ⟨rfl, rfl, he⟩ := he; exact .proj_table ht (ih he hp hp')
  | proj_fst ht _ ih =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case proj s' i' e'' => obtain ⟨rfl, rfl, he⟩ := he; exact .proj_fst ht (ih he hp hp')
  | proj_snd ht _ ih =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he
    case proj s' i' e'' => obtain ⟨rfl, rfl, he⟩ := he; exact .proj_snd ht (ih he hp hp')
  | natLit h _ =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he; subst he; exact .natLit h
  | strLit h _ =>
    cases e' <;> simp [Kernel.Expr.erasePw] at he; subst he; exact .strLit h

/-- The bridge's terms carry `.never` everywhere: graph regime at every assignment. -/
theorem bridgeT_posAt {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level} :
    ∀ (t : Conv.Tm) {k : Kernel.Expr}, bridgeT N L t = some k → PosAt φ k := by
  intro t
  induction t with
  | bvar i => intro k h; rw [bridgeT_bvar_inv h]; trivial
  | fvar _ => intro k h; simp [bridgeT] at h
  | mvar _ => intro k h; simp [bridgeT] at h
  | sort u => intro k h; obtain ⟨_, _, rfl⟩ := bridgeT_sort_inv h; trivial
  | const x us => intro k h; obtain ⟨_, _, _, _, rfl⟩ := bridgeT_const_inv h; trivial
  | app f a ihf iha =>
    intro k h; obtain ⟨f', a', hf, ha, rfl⟩ := bridgeT_app_inv h; exact ⟨ihf hf, iha ha⟩
  | lam t b iht ihb =>
    intro k h; obtain ⟨t', b', ht, hb, rfl⟩ := bridgeT_lam_inv h
    exact ⟨by simp [regime_never], iht ht, ihb hb⟩
  | pi t b iht ihb =>
    intro k h; obtain ⟨t', b', ht, hb, rfl⟩ := bridgeT_pi_inv h
    exact ⟨by simp [regime_never], iht ht, ihb hb⟩
  | letE t v b iht ihv ihb =>
    intro k h; obtain ⟨t', v', b', ht, hv, hb, rfl⟩ := bridgeT_letE_inv h
    exact ⟨iht ht, ihv hv, ihb hb⟩
  | lit l => intro k h; simp only [bridgeT, Option.some.injEq] at h; subst h; trivial
  | proj s i e ih =>
    intro k h; obtain ⟨_, e', _, he, rfl⟩ := bridgeT_proj_inv h
    simp only [PosAt]; exact ih he

/-- **The bridge's reading is the installed reading in the graph regime**: an annotated term over a
bridged skeleton, graph-regime at `φ`, denotes what the bridge (the reader's `.never` form) does. -/
theorem bridge_reading_pos {N : Ix.Name → Option Kernel.Name} {L : Ix.Level → Option Kernel.Level}
    {t : Conv.Tm} {k k₀ : Kernel.Expr} {ρ : Nat → V} {v : V} (hs : Skel N L t k)
    (hk : bridgeT N L t = some k₀) (hp : PosAt φ k) (h : Denotes cval env φ ρ k v) :
    Denotes cval env φ ρ k₀ v := by
  have he : k.erasePw = k₀.erasePw := by
    unfold Skel at hs; rw [hk] at hs; rw [bridgeT_erasePw t hk]; exact (Option.some.inj hs).symm
  exact denotes_of_erasePw_pos he hp (bridgeT_posAt t hk) h

/-- **(b) The squash collapse**: an inhabitant of a truth value, or a member of a squash-regime
product, is the proof point. -/
theorem squash_pt {T y : V} (hT : T ∈ˢ univ 0) (hy : y ∈ˢ T) : y = pt := by
  rw [univ_zero] at hT; exact eq_pt_of_mem_univZero hT hy

theorem squash_pi_pt {A f : V} {B : V → V} (hf : f ∈ˢ piR 0 A B) : f = pt :=
  eq_pt_of_mem_piR_zero hf

end Annotation

end Ix.CompileCert.Bridge
