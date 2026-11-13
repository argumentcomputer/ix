module

public import IxC.Kernel.Semantics.Inductives.WrapRel
public import IxC.Kernel.Verify.ProjSlots
public import IxC.Kernel.Verify.EnvWF
public import IxC.Kernel.Inductives.NativeParts
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.Inductives.FixRec

@[expose] public section

/-!
# `WrapRel` at a declared term without `let`

A declared recursor term the block stores is an annotated one, and annotation expands every
`let`. At such a term `WrapRel`'s two `let` rules never apply, and the relation is a plain
structural one (`WrapT`): at every binder domain the generated domain consumes wrappers
(`ConsumeStar`) down to a domain related to the declared one. `WrapT` relates free variables
whatever their types (the reading does not look at them), so it is closed under opening a
binder at two such variables (`WrapT.instantiate1`), which is what the reading's binder clauses
do.

Scoping moves from the generated term to the declared one: closedness, the loose-variable
bound, the level parameters, the resolution of constants and the absence of a projection node.
A consumption leaves an argument of the wrapper's application, so each of these, true of the
application, is true of what it leaves.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Key Expr Level ConstantInfo ConstantVal Literal Env RecRule)

/-- Two lists related position by position. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a : α} {b : β} {l₁ : List α} {l₂ : List β} :
      R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

/-- No `let` node (a free variable's type is not looked into). -/
def letFree : Expr md → Bool
  | .letE .. => false
  | .app f a => letFree f && letFree a
  | .lam t b _ => letFree t && letFree b
  | .forallE t b _ => letFree t && letFree b
  | .proj _ _ e => letFree e
  | _ => true

/-- A term whose instance has no `let` has none. -/
theorem letFree_of_instantiate1 (v : Expr md) :
    ∀ (e : Expr md) (j : Nat), letFree (e.instantiate1 v j) = true → letFree e = true
  | .bvar _, _, _ => rfl
  | .fvar _ _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, j, h => by
    simp only [Ix.Kernel.Expr.instantiate1, letFree, Bool.and_eq_true] at h ⊢
    exact ⟨letFree_of_instantiate1 v f j h.1, letFree_of_instantiate1 v a j h.2⟩
  | .lam t b _, j, h => by
    simp only [Ix.Kernel.Expr.instantiate1, letFree, Bool.and_eq_true] at h ⊢
    exact ⟨letFree_of_instantiate1 v t j h.1, letFree_of_instantiate1 v b (j + 1) h.2⟩
  | .forallE t b _, j, h => by
    simp only [Ix.Kernel.Expr.instantiate1, letFree, Bool.and_eq_true] at h ⊢
    exact ⟨letFree_of_instantiate1 v t j h.1, letFree_of_instantiate1 v b (j + 1) h.2⟩
  | .letE .., _, h => by simp [Ix.Kernel.Expr.instantiate1, letFree] at h
  | .proj _ _ e, j, h => by
    simp only [Ix.Kernel.Expr.instantiate1, letFree] at h ⊢
    exact letFree_of_instantiate1 v e j h

/-! ## One consumption -/

section Consume

variable {find? : Key md → Option (ConstantInfo md)}

/-- A wrapper applied to its arity is consumed to its first argument. -/
theorem consumeWrapper_mkAppN {w : Key md} {us : List Level} {x : Expr md} {xs : List (Expr md)}
    (hw : wrapperArity find? w = some (xs.length + 1)) :
    consumeWrapper find? (Expr.mkAppN (.const w us) (x :: xs)) = some x := by
  unfold consumeWrapper
  rw [Ix.Kernel.Expr.getAppFn_mkAppN, Ix.Kernel.Expr.getAppArgs_mkAppN]
  simp [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.getAppArgs, hw]

/-- **A consumption, inverted**: the term is the wrapper applied to its arity. -/
theorem consumeWrapper_inv {t a : Expr md} (h : consumeWrapper find? t = some a) :
    ∃ (w : Key md) (us : List Level) (rest : List (Expr md)),
      t = Expr.mkAppN (.const w us) (a :: rest) ∧
      wrapperArity find? w = some (rest.length + 1) := by
  have ht := Ix.Kernel.Expr.mkAppN_getApp t
  unfold consumeWrapper at h
  cases hf : t.getAppFn
  case const w us =>
    cases hargs : t.getAppArgs with
    | nil => rw [hf, hargs] at h; simp at h
    | cons a' rest =>
      rw [hf, hargs] at h
      simp only at h
      split at h
      · next hw =>
        obtain rfl := Option.some.inj h
        exact ⟨w, us, rest, by rw [← ht, hf, hargs], beq_iff_eq.mp hw⟩
      · exact nomatch h
  all_goals (rw [hf] at h; first | (simp at h; done) | (split at h <;> simp_all))

/-- A consumption commutes with instantiation. -/
theorem consumeWrapper_instantiate1 {t a : Expr md} (h : consumeWrapper find? t = some a)
    (v : Expr md) (j : Nat) :
    consumeWrapper find? (t.instantiate1 v j) = some (a.instantiate1 v j) := by
  obtain ⟨w, us, rest, rfl, hw⟩ := consumeWrapper_inv h
  rw [Ix.Kernel.Expr.mkAppN_instantiate1]
  exact consumeWrapper_mkAppN (by rw [List.length_map]; exact hw)

theorem sizeB_le_mkAppN : ∀ (args : List (Expr md)) (f : Expr md),
    f.sizeB ≤ (Expr.mkAppN f args).sizeB
  | [], _ => Nat.le_refl _
  | a :: as, f =>
    Nat.le_trans (by simp only [Ix.Kernel.Expr.sizeB]; omega) (sizeB_le_mkAppN as (.app f a))

/-- What a consumption leaves is smaller. -/
theorem sizeB_lt_of_consumeWrapper {t a : Expr md} (h : consumeWrapper find? t = some a) :
    a.sizeB < t.sizeB := by
  obtain ⟨w, us, rest, rfl, -⟩ := consumeWrapper_inv h
  exact Nat.lt_of_lt_of_le (by simp only [Ix.Kernel.Expr.sizeB]; omega)
    (sizeB_le_mkAppN rest (.app (.const w us) a))

/-- A property of an application that holds of both sides holds of every argument of a spine. -/
theorem mkAppN_head_of {P : Expr md → Prop} (hP : ∀ f x, P (.app f x) → P f ∧ P x) :
    ∀ (args : List (Expr md)) (f : Expr md), P (Expr.mkAppN f args) → P f
  | [], _, h => h
  | a :: as, f, h => (hP f a (mkAppN_head_of hP as (.app f a) h)).1

theorem consumeWrapper_of {P : Expr md → Prop} (hP : ∀ f x, P (.app f x) → P f ∧ P x)
    {t a : Expr md} (h : consumeWrapper find? t = some a) (ht : P t) : P a := by
  obtain ⟨w, us, rest, rfl, -⟩ := consumeWrapper_inv h
  exact (hP _ a (mkAppN_head_of hP rest _ ht)).2

end Consume

/-! ## The relation at a declared term without `let` -/

/-- Zero or more consumptions. -/
inductive ConsumeStar (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | refl (t : Expr md) : ConsumeStar find? t t
  | step {t a c : Expr md} :
      consumeWrapper find? t = some a → ConsumeStar find? a c → ConsumeStar find? t c

/-- **`WrapRel` at a declared term without `let`**, with free variables related whatever their
types. -/
inductive WrapT (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | bvar (i : Nat) : WrapT find? (.bvar i) (.bvar i)
  | fvar (i : Nat) (t t' : Expr md) : WrapT find? (.fvar i t) (.fvar i t')
  | sort (u : Level) : WrapT find? (.sort u) (.sort u)
  | const (n : Key md) (us : List Level) : WrapT find? (.const n us) (.const n us)
  | lit (l : Literal) : WrapT find? (.lit l) (.lit l)
  | app {f a f' a' : Expr md} :
      WrapT find? f f' → WrapT find? a a' → WrapT find? (.app f a) (.app f' a')
  | lam {t a t' b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → WrapT find? a t' → WrapT find? b b' →
      WrapT find? (.lam t b m) (.lam t' b' m')
  | forallE {t a t' b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → WrapT find? a t' → WrapT find? b b' →
      WrapT find? (.forallE t b m) (.forallE t' b' m')
  | proj {s : Key md} {i : Nat} {e e' : Expr md} :
      WrapT find? e e' → WrapT find? (.proj s i e) (.proj s i e')

section Rel

variable {find? : Key md → Option (ConstantInfo md)}

/-- **At a declared term without `let`, `WrapRel` is `WrapT`.** -/
theorem WrapRel.toWrapT {g d : Expr md} (h : WrapRel find? g d) (hd : letFree d = true) :
    WrapT find? g d :=
  WrapRel.rec
    (motive_1 := fun g d _ => letFree d = true → WrapT find? g d)
    (motive_2 := fun t t' _ => letFree t' = true →
      ∃ a, ConsumeStar find? t a ∧ WrapT find? a t')
    (bvar := fun i _ => .bvar i)
    (fvar := fun _ _ _ => .fvar _ _ _)
    (sort := fun u _ => .sort u)
    (const := fun n us _ => .const n us)
    (lit := fun l _ => .lit l)
    (app := fun _ _ ihf iha hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      exact .app (ihf hl.1) (iha hl.2))
    (lam := fun hpw _ _ ihd ihb hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      obtain ⟨a, hs, hw⟩ := ihd hl.1
      exact .lam hpw hs hw (ihb hl.2))
    (forallE := fun hpw _ _ ihd ihb hl => by
      simp only [letFree, Bool.and_eq_true] at hl
      obtain ⟨a, hs, hw⟩ := ihd hl.1
      exact .forallE hpw hs hw (ihb hl.2))
    (letE := fun _ _ _ _ _ _ hl => by simp [letFree] at hl)
    (proj := fun _ ih hl => .proj (ih (by simpa only [letFree] using hl)))
    (zeta := fun _ _ hl => by simp [letFree] at hl)
    (keep := fun _ ih hl => ⟨_, .refl _, ih hl⟩)
    (consume := fun hc _ ih hl => by
      obtain ⟨a, hs, hw⟩ := ih hl
      exact ⟨a, .step hc hs, hw⟩)
    h hd

theorem ConsumeStar.instantiate1 {t a : Expr md} (h : ConsumeStar find? t a) (v : Expr md)
    (j : Nat) : ConsumeStar find? (t.instantiate1 v j) (a.instantiate1 v j) := by
  induction h with
  | refl t => exact .refl _
  | step hc _ ih => exact .step (consumeWrapper_instantiate1 hc v j) ih

/-- **Opening a binder at two related terms** keeps the relation. -/
theorem WrapT.instantiate1 {v v' : Expr md} (hv : WrapT find? v v') {g d : Expr md}
    (h : WrapT find? g d) : ∀ j, WrapT find? (g.instantiate1 v j) (d.instantiate1 v' j) := by
  induction h with
  | bvar i =>
    intro j
    show WrapT find? (if i = j then v else if i > j then .bvar (i - 1) else .bvar i)
      (if i = j then v' else if i > j then .bvar (i - 1) else .bvar i)
    by_cases h1 : i = j
    · rw [if_pos h1, if_pos h1]; exact hv
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i > j
      · rw [if_pos h2]; exact .bvar _
      · rw [if_neg h2]; exact .bvar _
  | fvar i t t' => intro j; exact .fvar i t t'
  | sort u => intro j; exact .sort u
  | const n us => intro j; exact .const n us
  | lit l => intro j; exact .lit l
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | lam hpw hs _ _ ihw ihb => intro j; exact .lam hpw (hs.instantiate1 v j) (ihw j) (ihb (j + 1))
  | forallE hpw hs _ _ ihw ihb =>
    intro j; exact .forallE hpw (hs.instantiate1 v j) (ihw j) (ihb (j + 1))
  | proj _ ih => intro j; exact .proj (ih j)

theorem ConsumeStar.of {P : Expr md → Prop} (hP : ∀ f x, P (.app f x) → P f ∧ P x)
    {t a : Expr md} (h : ConsumeStar find? t a) (ht : P t) : P a := by
  induction h with
  | refl => exact ht
  | step hc _ ih => exact ih (consumeWrapper_of hP hc ht)

theorem ConsumeStar.sizeB_le {t a : Expr md} (h : ConsumeStar find? t a) : a.sizeB ≤ t.sizeB := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hc _ ih => exact Nat.le_trans ih (Nat.le_of_lt (sizeB_lt_of_consumeWrapper hc))

/-! ## Scoping, from the generated term to the declared one -/

theorem WrapT.hasFvar {g d : Expr md} (h : WrapT find? g d) (hg : g.hasFvar = false) :
    d.hasFvar = false := by
  have hP : ∀ f x : Expr md, (Expr.app f x).hasFvar = false →
      f.hasFvar = false ∧ x.hasFvar = false := by
    intro f x h; simpa [Ix.Kernel.Expr.hasFvar] using h
  induction h with
  | bvar | sort | const | lit => exact hg
  | fvar => simp [Ix.Kernel.Expr.hasFvar] at hg
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hg ⊢
    exact ⟨ihf hg.1, iha hg.2⟩
  | lam _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hg ⊢
    exact ⟨ihw (hs.of (P := fun e : Expr md => e.hasFvar = false) hP hg.1), ihb hg.2⟩
  | forallE _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hg ⊢
    exact ⟨ihw (hs.of (P := fun e : Expr md => e.hasFvar = false) hP hg.1), ihb hg.2⟩
  | proj _ ih => exact ih hg

theorem WrapT.looseBVarsBounded {g d : Expr md} (h : WrapT find? g d) :
    ∀ k, g.looseBVarsBounded k = true → d.looseBVarsBounded k = true := by
  induction h with
  | bvar | fvar | sort | const | lit => intro k hg; exact hg
  | app _ _ ihf iha =>
    intro k hg
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hg ⊢
    exact ⟨ihf k hg.1, iha k hg.2⟩
  | lam _ hs _ _ ihw ihb =>
    intro k hg
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hg ⊢
    refine ⟨ihw k (hs.of (P := fun e => e.looseBVarsBounded k = true) ?_ hg.1), ihb (k + 1) hg.2⟩
    intro f x h; simpa [Ix.Kernel.Expr.looseBVarsBounded] using h
  | forallE _ hs _ _ ihw ihb =>
    intro k hg
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hg ⊢
    refine ⟨ihw k (hs.of (P := fun e => e.looseBVarsBounded k = true) ?_ hg.1), ihb (k + 1) hg.2⟩
    intro f x h; simpa [Ix.Kernel.Expr.looseBVarsBounded] using h
  | proj _ ih => intro k hg; exact ih k hg

theorem WrapT.allLevelParamsDefined {g d : Expr md} (h : WrapT find? g d)
    (ps : List LevelParam) (hf : g.hasFvar = false)
    (hg : g.allLevelParamsDefined ps = true) : d.allLevelParamsDefined ps = true := by
  have hP : ∀ f x : Expr md,
      (fun e : Expr md => e.hasFvar = false ∧ e.allLevelParamsDefined ps = true) (.app f x) →
      (fun e : Expr md => e.hasFvar = false ∧ e.allLevelParamsDefined ps = true) f ∧
      (fun e : Expr md => e.hasFvar = false ∧ e.allLevelParamsDefined ps = true) x := by
    intro f x h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff,
      Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
  induction h with
  | bvar | sort | const | lit => exact hg
  | fvar => simp [Ix.Kernel.Expr.hasFvar] at hf
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hg ⊢
    exact ⟨ihf hf.1 hg.1, iha hf.2 hg.2⟩
  | lam hpw hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ e.allLevelParamsDefined ps = true) hP
      ⟨hf.1, hg.1.1⟩
    exact ⟨⟨ihw hfa hga, ihb hf.2 hg.1.2⟩, by rw [← hpw]; exact hg.2⟩
  | forallE hpw hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ e.allLevelParamsDefined ps = true) hP
      ⟨hf.1, hg.1.1⟩
    exact ⟨⟨ihw hfa hga, ihb hf.2 hg.1.2⟩, by rw [← hpw]; exact hg.2⟩
  | proj _ ih => exact ih hf hg

theorem WrapT.constsResolve {g d : Expr md} (h : WrapT find? g d) (E : Env md)
    (hf : g.hasFvar = false) (hg : g.constsResolve E = true) : d.constsResolve E = true := by
  have hP : ∀ f x : Expr md,
      (fun e : Expr md => e.hasFvar = false ∧ e.constsResolve E = true) (.app f x) →
      (fun e : Expr md => e.hasFvar = false ∧ e.constsResolve E = true) f ∧
      (fun e : Expr md => e.hasFvar = false ∧ e.constsResolve E = true) x := by
    intro f x h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff,
      Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
  induction h with
  | bvar | sort | const | lit => exact hg
  | fvar => simp [Ix.Kernel.Expr.hasFvar] at hf
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hg ⊢
    exact ⟨ihf hf.1 hg.1, iha hf.2 hg.2⟩
  | lam _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ e.constsResolve E = true) hP ⟨hf.1, hg.1⟩
    exact ⟨ihw hfa hga, ihb hf.2 hg.2⟩
  | forallE _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ e.constsResolve E = true) hP ⟨hf.1, hg.1⟩
    exact ⟨ihw hfa hga, ihb hf.2 hg.2⟩
  | proj _ ih =>
    simp only [Ix.Kernel.Expr.constsResolve, Bool.and_eq_true] at hg ⊢
    exact ⟨hg.1, ih hf hg.2⟩

theorem WrapT.noProjAt {g d : Expr md} (h : WrapT find? g d) (T : Key md) (i : Nat)
    (hf : g.hasFvar = false) (hg : Ix.Kernel.Expr.NoProjAt T i g) :
    Ix.Kernel.Expr.NoProjAt T i d := by
  have hP : ∀ f x : Expr md,
      (fun e : Expr md => e.hasFvar = false ∧ Ix.Kernel.Expr.NoProjAt T i e) (.app f x) →
      (fun e : Expr md => e.hasFvar = false ∧ Ix.Kernel.Expr.NoProjAt T i e) f ∧
      (fun e : Expr md => e.hasFvar = false ∧ Ix.Kernel.Expr.NoProjAt T i e) x := by
    intro f x h
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff,
      Ix.Kernel.Expr.noProjAt_app] at h
    exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
  induction h with
  | bvar | sort | const | lit => simp
  | fvar => simp [Ix.Kernel.Expr.hasFvar] at hf
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.noProjAt_app] at hg ⊢
    exact ⟨ihf hf.1 hg.1, iha hf.2 hg.2⟩
  | lam _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.noProjAt_lam] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ Ix.Kernel.Expr.NoProjAt T i e) hP ⟨hf.1, hg.1⟩
    exact ⟨ihw hfa hga, ihb hf.2 hg.2⟩
  | forallE _ hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Ix.Kernel.Expr.noProjAt_forallE] at hg ⊢
    obtain ⟨hfa, hga⟩ := hs.of
      (P := fun e : Expr md => e.hasFvar = false ∧ Ix.Kernel.Expr.NoProjAt T i e) hP ⟨hf.1, hg.1⟩
    exact ⟨ihw hfa hga, ihb hf.2 hg.2⟩
  | proj _ ih =>
    simp only [Ix.Kernel.Expr.noProjAt_proj] at hg ⊢
    exact ⟨hg.1, ih hf hg.2⟩

end Rel

/-! ## A recursor type, and the literal guards

A generated recursor type is a `∀`-telescope (parameters, motive, minor premises, indices, major
premise) over the motive applied: a term headed by a bound variable. A declared type related to
it has the same shape. Such a type matches none of the string-literal guards' shapes, so a
recursor stored at one of their names leaves the guard false, whichever of the two types it
carries. -/

/-- `k` `∀`s over a term headed by a bound variable. -/
inductive PiToBvar : Nat → Expr md → Prop
  | base {C : Expr md} {i : Nat} : C.getAppFn = .bvar i → PiToBvar 0 C
  | pi {k : Nat} {t b : Expr md} {m : Ix.Kernel.BinderMeta} :
      PiToBvar k b → PiToBvar (k + 1) (.forallE t b m)

theorem PiToBvar.replacePisPw {pw : Ix.Kernel.PropWhen} {j : Nat} {b : Expr md}
    (hb : PiToBvar j b) :
    ∀ (k : Nat) (e r : Expr md), Expr.replacePisPw pw k e b = some r → PiToBvar (k + j) r
  | 0, _, r, h => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    subst h; simpa using hb
  | k + 1, .forallE ty rest _, r, h => by
    simp only [Expr.replacePisPw] at h
    cases hr : Expr.replacePisPw pw k rest b with
    | none => rw [hr] at h; exact nomatch h
    | some r' =>
      rw [hr] at h
      obtain rfl := Option.some.inj h
      rw [show k + 1 + j = (k + j) + 1 by omega]
      exact .pi (PiToBvar.replacePisPw hb k rest r' hr)
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => by
    simp [Expr.replacePisPw] at h

theorem PiToBvar.structMinorsPisR {lps : List LevelParam} {nP : Nat} {pw : Ix.Kernel.PropWhen}
    {j : Nat} {body : Expr md} (hb : PiToBvar j body) :
    ∀ (cs : List (Key md × Nat × Expr md × List Nat)) (o : Nat) (r : Expr md),
      Ix.Kernel.structMinorsPisR lps nP pw cs o body = some r → PiToBvar (cs.length + j) r
  | [], _, r, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.some.injEq] at h
    subst h; simpa using hb
  | (C, nF, cty, recIdx) :: cs, o, r, h => by
    simp only [Ix.Kernel.structMinorsPisR] at h
    cases hm : Ix.Kernel.structMinorTyR C lps nP nF o pw cty recIdx with
    | none => rw [hm] at h; exact nomatch h
    | some mty =>
      rw [hm] at h
      cases hr : Ix.Kernel.structMinorsPisR lps nP pw cs (o + 1) body with
      | none => rw [hr] at h; exact nomatch h
      | some r' =>
        rw [hr] at h
        obtain rfl := Option.some.inj h
        rw [List.length_cons, show cs.length + 1 + j = (cs.length + j) + 1 by omega]
        exact .pi (PiToBvar.structMinorsPisR hb cs (o + 1) r' hr)

/-- **The generated recursor type**: its binders over the motive applied. -/
theorem piToBvar_structRecTyR {T : Key md} {lps : List LevelParam} {elim : LevelParam}
    {large : Bool} {nP nIdx : Nat} {tty recTy : Expr md}
    {ctors : List (Key md × Nat × Expr md × List Nat)}
    (h : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    PiToBvar (nP + 1 + ctors.length + nIdx + 1) recTy := by
  obtain ⟨_tbs, _itele, motiveTy, major, minors, -, -, hmaj, hmin, hr⟩ :=
    Ix.Kernel.structRecTyR_unfold h
  have h0 : PiToBvar 0 (Expr.mkAppN (.bvar (nIdx + ctors.length + 1) : Expr md)
      (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0])) :=
    PiToBvar.base (i := nIdx + ctors.length + 1)
      (by simp [Ix.Kernel.Expr.getAppFn_mkAppN, Ix.Kernel.Expr.getAppFn])
  have h1 := PiToBvar.replacePisPw (PiToBvar.pi h0) nIdx _ major hmaj
  have h2 := PiToBvar.structMinorsPisR h1 ctors 1 minors hmin
  have h3 := PiToBvar.replacePisPw (PiToBvar.pi h2) nP tty recTy hr
  rw [show nP + 1 + ctors.length + nIdx + 1 = nP + (ctors.length + (nIdx + (0 + 1)) + 1) by
    omega]
  exact h3

theorem WrapT.getAppFn_bvar {find? : Key md → Option (ConstantInfo md)} {g d : Expr md}
    (h : WrapT find? g d) {i : Nat} (hg : g.getAppFn = .bvar i) : d.getAppFn = .bvar i := by
  induction h with
  | bvar => exact hg
  | app _ _ ihf _ => exact ihf hg
  | _ => simp [Ix.Kernel.Expr.getAppFn] at hg

/-- The shape moves to a related term. -/
theorem WrapT.piToBvar {find? : Key md → Option (ConstantInfo md)} {k : Nat} {g : Expr md}
    (hg : PiToBvar k g) : ∀ {d : Expr md}, WrapT find? g d → PiToBvar k d := by
  induction hg with
  | base hC => intro d h; exact .base (h.getAppFn_bvar hC)
  | pi _ ih =>
    intro d h
    cases h with
    | forallE _ _ _ hb => exact .pi (ih hb)

theorem PiToBvar.not_app_const : ∀ {j : Nat} {C : Expr md}, PiToBvar j C →
    ∀ (l : Key md) (us : List Level) (Y : Expr md), C ≠ .app (.const l us) Y
  | _, _, .base hC, l, us, Y, h => by
    subst h; simp [Ix.Kernel.Expr.getAppFn] at hC
  | _, _, .pi _, _, _, _, h => nomatch h

theorem PiToBvar.two_inv {k : Nat} {T : Expr md} (h : PiToBvar k T) (hk : 2 ≤ k) :
    ∃ (t₁ t₂ B : Expr md) (m₁ m₂ : Ix.Kernel.BinderMeta) (j : Nat),
      T = .forallE t₁ (.forallE t₂ B m₂) m₁ ∧ PiToBvar j B := by
  cases h with
  | base => omega
  | pi hb =>
    cases hb with
    | base => omega
    | pi hB => exact ⟨_, _, _, _, _, _, rfl, hB⟩

theorem listConsTyOk_shape {ci : ConstantInfo md} (h : Ix.Kernel.listConsTyOk (some ci) = true) :
    ∃ (u1 : Level) (l1 l2 : Key md) (us1 us2 : List Level) (mb1 mb2 mb3 : Ix.Kernel.BinderMeta),
      ci.toConstantVal.type = .forallE (.sort u1) (.forallE (.bvar 0)
        (.forallE (.app (.const l1 us1) (.bvar 1)) (.app (.const l2 us2) (.bvar 2)) mb3) mb2)
        mb1 := by
  simp only [Ix.Kernel.listConsTyOk] at h
  split at h
  · split at h
    · exact ⟨_, _, _, _, _, _, _, _, by assumption⟩
    · exact nomatch h
  · exact nomatch h

/-- **A constant of such a type passes none of the string-literal guards.** -/
theorem strGuards_false {ci : ConstantInfo md} {k : Nat}
    (hT : PiToBvar k ci.toConstantVal.type) (hk : 2 ≤ k) :
    Ix.Kernel.stringTyOk (some ci) = false ∧ Ix.Kernel.charTyOk (some ci) = false ∧
    Ix.Kernel.listTyOk (some ci) = false ∧ Ix.Kernel.listNilTyOk (some ci) = false ∧
    Ix.Kernel.listConsTyOk (some ci) = false ∧ Ix.Kernel.charOfNatTyOk (some ci) = false ∧
    Ix.Kernel.stringOfListTyOk (some ci) = false := by
  obtain ⟨t₁, t₂, B, m₁, m₂, j, hTy, hB⟩ := hT.two_inv hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Bool.eq_false_iff] <;> intro h
  · simp only [Ix.Kernel.stringTyOk, Bool.and_eq_true, beq_iff_eq, hTy] at h
    exact nomatch h.2
  · simp only [Ix.Kernel.charTyOk, Bool.and_eq_true, beq_iff_eq, hTy] at h
    exact nomatch h.2
  · simp only [Ix.Kernel.listTyOk, hTy] at h
    split at h <;> first | exact nomatch h | (split at h <;> exact nomatch h)
  · simp only [Ix.Kernel.listNilTyOk, hTy] at h
    split at h <;> first | exact nomatch h | (split at h <;> exact nomatch h)
  · obtain ⟨u1, l1, l2, us1, us2, mb1, mb2, mb3, hs⟩ := listConsTyOk_shape h
    rw [hTy] at hs
    simp only [Ix.Kernel.Expr.forallE.injEq] at hs
    obtain ⟨-, ⟨-, rfl, -⟩, -⟩ := hs
    cases hB with
    | base hg => simp [Ix.Kernel.Expr.getAppFn] at hg
    | pi hC => exact hC.not_app_const l2 us2 (.bvar 2) rfl
  · simp only [Ix.Kernel.charOfNatTyOk, hTy, Bool.and_eq_true] at h
    first | exact nomatch h | exact nomatch h.2 | (obtain ⟨-, h⟩ := h; split at h <;> exact nomatch h)
  · simp only [Ix.Kernel.stringOfListTyOk, hTy, Bool.and_eq_true] at h
    first | exact nomatch h | exact nomatch h.2 | (obtain ⟨-, h⟩ := h; split at h <;> exact nomatch h)

/-- A lookup guard that refuses a recursor and an absent name is unchanged by consing a fresh
recursor. -/
theorem guard_cons_rec {E : Env md} {cv : ConstantVal md} {mI rP : Nat} {r : List (RecRule md)}
    (hfresh : E.find? cv.name = none) (chk : Option (ConstantInfo md) → Bool)
    (hchk : chk (some (.recInfo cv mI rP r)) = false) (hnone : chk none = false) (s : Key md) :
    chk ((⟨.recInfo cv mI rP r :: E.consts⟩ : Env md).find? s) = chk (E.find? s) := by
  rw [Ix.Kernel.Env.find?_cons]
  split
  · next h =>
    have h' : cv.name = s := h
    rw [← h', hfresh, hchk, hnone]
  · rfl

/-- **The literal guards are unchanged by consing a fresh recursor whose type is a recursor
type.** -/
theorem litGuards_cons_rec {E : Env md} {cv : ConstantVal md} {mI rP : Nat}
    {r : List (RecRule md)} {k : Nat} (hfresh : E.find? cv.name = none)
    (hT : PiToBvar k cv.type) (hk : 2 ≤ k) :
    Ix.Kernel.natLitSupported (⟨.recInfo cv mI rP r :: E.consts⟩ : Env md)
        = Ix.Kernel.natLitSupported E ∧
      Ix.Kernel.strLitSupported (⟨.recInfo cv mI rP r :: E.consts⟩ : Env md)
        = Ix.Kernel.strLitSupported E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    strGuards_false (ci := .recInfo cv mI rP r) hT hk
  have hnat : Ix.Kernel.natLitSupported (⟨.recInfo cv mI rP r :: E.consts⟩ : Env md)
      = Ix.Kernel.natLitSupported E := by
    unfold Ix.Kernel.natLitSupported
    rw [guard_cons_rec hfresh Ix.Kernel.natIndOk rfl rfl,
      guard_cons_rec hfresh Ix.Kernel.natZeroOk rfl rfl,
      guard_cons_rec hfresh Ix.Kernel.natSuccOk rfl rfl]
  refine ⟨hnat, ?_⟩
  unfold Ix.Kernel.strLitSupported
  rw [hnat, guard_cons_rec hfresh Ix.Kernel.stringTyOk h1 rfl,
    guard_cons_rec hfresh Ix.Kernel.stringOfListTyOk h7 rfl,
    guard_cons_rec hfresh Ix.Kernel.listTyOk h3 rfl,
    guard_cons_rec hfresh Ix.Kernel.listNilTyOk h4 rfl,
    guard_cons_rec hfresh Ix.Kernel.listConsTyOk h5 rfl,
    guard_cons_rec hfresh Ix.Kernel.charTyOk h2 rfl,
    guard_cons_rec hfresh Ix.Kernel.charOfNatTyOk h6 rfl]

end Ix.Kernel.Semantics
