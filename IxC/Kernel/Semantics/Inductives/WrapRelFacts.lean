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

open Ix.Kernel (Key Expr Level LevelParam ConstantInfo ConstantVal Literal Env RecRule)

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
  | sort {u v : Level} :
      (∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) → WrapT find? (.sort u) (.sort v)
  | const {n : Key md} {us vs : List Level} :
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us vs →
      WrapT find? (.const n us) (.const n vs)
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
    (sort := fun h _ => .sort h)
    (const := fun h _ => .const h)
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
  | sort h => intro _; exact .sort h
  | const h => intro _; exact .const h
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
  | bvar | lit => exact hg
  | sort | const => rfl
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
  | bvar | fvar | lit => intro k hg; exact hg
  | sort | const => intro _ _; rfl
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
  | bvar | lit => exact hg
  | sort => rfl
  | const => simpa [Ix.Kernel.Expr.constsResolve] using hg
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

/-! ## The generated recursor's major premise

Past the parameters, the motive, the minor premises and the indices, the generated recursor
type's next domain is the family at its own level parameters applied to the parameter variables
and the index variables (`structFamI`). So the generated type fires every rule whose constructor
carries the family's level parameters (`Expr.recRulePlain`), and the major premise's index
arguments are the trailing bound variables. A declared type without `let` related to it carries
the same domain: no wrapper heads it while the family is stored as an inductive type. -/

theorem stripPis_succ_forallE {t b body : Expr md} {m : Ix.Kernel.BinderMeta} {k : Nat}
    {bs : List (Expr md × Ix.Kernel.BinderMeta)} (h : b.stripPis k = some (bs, body)) :
    (Expr.forallE t b m).stripPis (k + 1) = some ((t, m) :: bs, body) := by
  simp only [Expr.stripPis, h, Option.map_some]

theorem stripPis_succ_inv : ∀ {e : Expr md} {k : Nat} {bs : List (Expr md × Ix.Kernel.BinderMeta)}
    {body : Expr md}, e.stripPis (k + 1) = some (bs, body) →
      ∃ t b m bs0, e = .forallE t b m ∧ b.stripPis k = some (bs0, body)
  | .forallE t b m, k, _, body, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs0, body0⟩, hs0, heq⟩ := h
    obtain rfl : body0 = body := congrArg Prod.snd heq
    exact ⟨t, b, m, bs0, rfl, hs0⟩
  | .bvar _, _, _, _, h | .fvar _ _, _, _, _, h | .sort _, _, _, _, h | .const _ _, _, _, _, h
  | .app _ _, _, _, _, h | .lam _ _ _, _, _, _, h | .letE _ _ _ _, _, _, _, h
  | .lit _, _, _, _, h | .proj _ _ _, _, _, _, h => by simp [Expr.stripPis] at h

/-- The strip of `k` binders replaced over a body lands on the body. -/
theorem stripPis_replacePisPw {pw : Ix.Kernel.PropWhen} {b : Expr md} :
    ∀ (k : Nat) (e r : Expr md), Expr.replacePisPw pw k e b = some r →
      ∃ bs, r.stripPis k = some (bs, b)
  | 0, _, r, h => by
    simp only [Expr.replacePisPw, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl⟩
  | k + 1, .forallE ty rest _, r, h => by
    simp only [Expr.replacePisPw] at h
    cases hr : Expr.replacePisPw pw k rest b with
    | none => rw [hr] at h; exact nomatch h
    | some r' =>
      rw [hr] at h
      obtain rfl := Option.some.inj h
      obtain ⟨bs, hbs⟩ := stripPis_replacePisPw k rest r' hr
      exact ⟨_, stripPis_succ_forallE hbs⟩
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => by
    simp [Expr.replacePisPw] at h

/-- The strip of the minor premises' telescope lands on its body. -/
theorem stripPis_structMinorsPisR {lps : List LevelParam} {nP : Nat} {pw : Ix.Kernel.PropWhen}
    {body : Expr md} :
    ∀ (cs : List (Key md × Nat × Expr md × List Nat)) (o : Nat) (r : Expr md),
      Ix.Kernel.structMinorsPisR lps nP pw cs o body = some r →
      ∃ bs, r.stripPis cs.length = some (bs, body)
  | [], _, r, h => by
    simp only [Ix.Kernel.structMinorsPisR, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl⟩
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
        obtain ⟨bs, hbs⟩ := stripPis_structMinorsPisR cs (o + 1) r' hr
        exact ⟨_, stripPis_succ_forallE hbs⟩

/-- **The generated recursor type's major premise**: the domain after the parameters, the
motive, the minor premises and the indices is the family applied to the parameter and index
variables. -/
theorem structRecTyR_major {T : Key md} {lps : List LevelParam} {elim : LevelParam}
    {large : Bool} {nP nIdx : Nat} {tty recTy : Expr md}
    {ctors : List (Key md × Nat × Expr md × List Nat)}
    (h : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    ∃ bs B m, recTy.stripPis (nP + 1 + ctors.length + nIdx) =
      some (bs, .forallE (Ix.Kernel.structFamI T lps nP nIdx (ctors.length + 1) 0) B m) := by
  obtain ⟨_tbs, _itele, motiveTy, major, minors, -, -, hmaj, hmin, hr⟩ :=
    Ix.Kernel.structRecTyR_unfold h
  obtain ⟨bs1, h1⟩ := stripPis_replacePisPw nP tty recTy hr
  obtain ⟨bs2, h2⟩ := stripPis_structMinorsPisR ctors 1 minors hmin
  obtain ⟨bs3, h3⟩ := stripPis_replacePisPw nIdx _ major hmaj
  have h0 := stripPis_succ_forallE (t := motiveTy)
    (m := { pw := Ix.Kernel.Level.zeronessOf (Ix.Kernel.structElimLevel elim large) })
    (Ix.Kernel.stripPis_append _ h2 h3)
  have := Ix.Kernel.stripPis_append _ h1 h0
  rw [show nP + (ctors.length + nIdx + 1) = nP + 1 + ctors.length + nIdx by omega] at this
  exact ⟨_, _, _, this⟩

theorem structFamI_getAppFn {T : Key md} {lps : List LevelParam} {nP nIdx e o : Nat} :
    (Ix.Kernel.structFamI T lps nP nIdx e o).getAppFn = .const T (lps.map .param) := by
  simp [Ix.Kernel.structFamI, Ix.Kernel.Expr.getAppFn_mkAppN, Ix.Kernel.Expr.getAppFn]

theorem structFamI_getAppArgs {T : Key md} {lps : List LevelParam} {nP nIdx e o : Nat} :
    (Ix.Kernel.structFamI T lps nP nIdx e o).getAppArgs =
      Ix.Kernel.structPsAt (o + e + nIdx) nP ++ Ix.Kernel.structPsAt o nIdx := by
  simp [Ix.Kernel.structFamI, Ix.Kernel.Expr.getAppArgs_mkAppN, Ix.Kernel.Expr.getAppArgs]

theorem length_structPsAt {o n : Nat} : (Ix.Kernel.structPsAt (md := md) o n).length = n := by
  simp [Ix.Kernel.structPsAt]

/-- **A major premise at the family fires every rule** of a constructor at the family's level
parameters: the domain's head is the family at those parameters and its first `nP` arguments are
the recursor's leading bound variables. -/
theorem recRulePlain_of_major {recTy B : Expr md} {bs : List (Expr md × Ix.Kernel.BinderMeta)}
    {m : Ix.Kernel.BinderMeta} {T : Key md} {lps : List LevelParam} {nP n nIdx : Nat}
    (hs : recTy.stripPis (nP + 1 + n + nIdx) =
      some (bs, .forallE (Ix.Kernel.structFamI T lps nP nIdx (n + 1) 0) B m)) :
    Expr.recRulePlain recTy (nP + 1 + n + nIdx) (nP + 1 + n) nP lps = true := by
  have hps : Ix.Kernel.structPsAt (md := md) (0 + (n + 1) + nIdx) nP =
      (List.range nP).map (fun k => Expr.bvar (nP + 1 + n + nIdx - 1 - k)) := by
    unfold Ix.Kernel.structPsAt
    refine List.map_congr_left fun k _ => ?_
    congr 1
    omega
  have htake : (Ix.Kernel.structFamI T lps nP nIdx (n + 1) 0).getAppArgs.take nP =
      (List.range nP).map (fun k => Expr.bvar (nP + 1 + n + nIdx - 1 - k)) := by
    rw [structFamI_getAppArgs, List.take_left' length_structPsAt, hps]
  unfold Expr.recRulePlain
  rw [hs]
  simp only [structFamI_getAppFn, htake]
  simp <;> omega

/-- **The generated recursor type fires every rule** of a constructor at the family's level
parameters. -/
theorem recRulePlain_structRecTyR {T : Key md} {lps : List LevelParam} {elim : LevelParam}
    {large : Bool} {nP nIdx : Nat} {tty recTy : Expr md}
    {ctors : List (Key md × Nat × Expr md × List Nat)}
    (h : Ix.Kernel.structRecTyR T lps elim large nP nIdx tty ctors = some recTy) :
    Expr.recRulePlain recTy (nP + 1 + ctors.length + nIdx) (nP + 1 + ctors.length) nP lps
      = true :=
  let ⟨_, _, _, hs⟩ := structRecTyR_major h
  recRulePlain_of_major hs

/-- The major premise's index arguments are the trailing bound variables. -/
theorem structFamI_args_drop {T : Key md} {lps : List LevelParam} {nP nIdx e : Nat} :
    (Ix.Kernel.structFamI T lps nP nIdx e 0).getAppArgs.drop nP =
      (List.range nIdx).map fun i => Expr.bvar (nIdx - 1 - i) := by
  rw [structFamI_getAppArgs, List.drop_left' length_structPsAt]
  simp [Ix.Kernel.structPsAt]

/-- A spine of bound-variable applications over a constant. -/
def appBVC : Expr md → Bool
  | .app f (.bvar _) => appBVC f
  | .const _ _ => true
  | _ => false

def isBVar : Expr md → Bool
  | .bvar _ => true
  | _ => false

theorem appBVC_mkAppN : ∀ (args : List (Expr md)) (f : Expr md),
    appBVC f = true → args.all isBVar = true → appBVC (Expr.mkAppN f args) = true
  | [], _, hf, _ => hf
  | .bvar _ :: as, f, hf, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at ha
    exact appBVC_mkAppN as (.app f (.bvar _)) hf ha.2
  | .fvar _ _ :: _, _, _, ha | .sort _ :: _, _, _, ha | .const _ _ :: _, _, _, ha
  | .app _ _ :: _, _, _, ha | .lam _ _ _ :: _, _, _, ha | .forallE _ _ _ :: _, _, _, ha
  | .letE _ _ _ _ :: _, _, _, ha | .lit _ :: _, _, _, ha | .proj _ _ _ :: _, _, _, ha => by
    simp [isBVar] at ha

theorem appBVC_structFamI {T : Key md} {lps : List LevelParam} {nP nIdx e o : Nat} :
    appBVC (Ix.Kernel.structFamI T lps nP nIdx e o) = true := by
  apply appBVC_mkAppN _ _ rfl
  simp [Ix.Kernel.structPsAt, isBVar]

/-- The family stored as an inductive type heads no wrapper. -/
theorem consumeWrapper_structFamI {find? : Key md → Option (ConstantInfo md)} {T : Key md}
    {lps : List LevelParam} {nP nIdx e o : Nat}
    (hT : ∃ cv caps, find? T = some (.indInfo cv caps)) :
    consumeWrapper find? (Ix.Kernel.structFamI T lps nP nIdx e o) = none := by
  obtain ⟨cv, caps, hT⟩ := hT
  have hw : wrapperArity find? T = none := by simp [wrapperArity, hT]
  unfold consumeWrapper
  rw [structFamI_getAppFn, structFamI_getAppArgs]
  generalize Ix.Kernel.structPsAt (md := md) (o + e + nIdx) nP ++ Ix.Kernel.structPsAt o nIdx
    = args
  cases args with
  | nil => rfl
  | cons a rest => simp [hw]

section Major

variable {find? : Key md → Option (ConstantInfo md)}

theorem ConsumeStar.eq_of_none {t a : Expr md} (h : ConsumeStar find? t a)
    (hn : consumeWrapper find? t = none) : a = t := by
  cases h with
  | refl => rfl
  | step hc _ => rw [hn] at hc; exact nomatch hc

/-- A related bound-variable application spine over a constant with matching head levels is
the term itself. -/
theorem WrapT.eq_of_appBVC_head {g d : Expr md} {ls : List Level}
    (h : WrapT find? g d) (hg : appBVC g = true)
    (hd : ∃ K, d.getAppFn = .const K ls) (hgfn : ∃ T, g.getAppFn = .const T ls) :
    d = g := by
  induction h with
  | const _ =>
    obtain ⟨K, hd⟩ := hd
    obtain ⟨T, hgfn⟩ := hgfn
    simp only [Ix.Kernel.Expr.getAppFn, Expr.const.injEq] at hd hgfn
    rw [hd.2, hgfn.2]
  | app _ ha ihf _ =>
    cases ha with
    | bvar _ =>
      simp only [appBVC] at hg
      simp only [Ix.Kernel.Expr.getAppFn] at hd hgfn
      rw [ihf hg hd hgfn]
    | _ => simp [appBVC] at hg
  | _ => simp [appBVC] at hg

/-- The strip moves to a related term, its body related. -/
theorem WrapT.stripPis : ∀ (k : Nat) {g d : Expr md} {bs : List (Expr md × Ix.Kernel.BinderMeta)}
    {body : Expr md}, WrapT find? g d → g.stripPis k = some (bs, body) →
      ∃ bs' body', d.stripPis k = some (bs', body') ∧ WrapT find? body body'
  | 0, _, d, _, _, h, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ⟨[], d, rfl, h⟩
  | k + 1, _, _, _, _, h, hs => by
    obtain ⟨t, b, m, bs0, rfl, hs0⟩ := stripPis_succ_inv hs
    cases h with
    | forallE _ _ _ hb =>
      obtain ⟨bs', body', h1, h2⟩ := WrapT.stripPis k hb hs0
      exact ⟨_, body', stripPis_succ_forallE h1, h2⟩

/-- **A declared type without `let` carries the generated major premise verbatim**, when the
family is stored as an inductive type and the major head carries the family's level parameters. -/
theorem WrapRel.major_structFamI {g d : Expr md} (h : WrapRel find? g d) (hd : letFree d = true)
    {k : Nat} {bs : List (Expr md × Ix.Kernel.BinderMeta)} {B : Expr md}
    {m : Ix.Kernel.BinderMeta} {T : Key md} {lps : List LevelParam} {nP nIdx e o : Nat}
    (hT : ∃ cv caps, find? T = some (.indInfo cv caps))
    (hlvls : ∀ bs' dom' B' m', d.stripPis k = some (bs', .forallE dom' B' m') →
      ∃ K, dom'.getAppFn = .const K (lps.map .param))
    (hs : g.stripPis k = some (bs, .forallE (Ix.Kernel.structFamI T lps nP nIdx e o) B m)) :
    ∃ bs' B' m', d.stripPis k =
      some (bs', .forallE (Ix.Kernel.structFamI T lps nP nIdx e o) B' m') := by
  obtain ⟨bs', body', h1, h2⟩ := WrapT.stripPis k (h.toWrapT hd) hs
  cases h2 with
  | forallE _ hc hdom _ =>
    rw [ConsumeStar.eq_of_none hc (consumeWrapper_structFamI hT)] at hdom
    rw [hdom.eq_of_appBVC_head appBVC_structFamI (hlvls _ _ _ _ h1) ⟨T, structFamI_getAppFn⟩] at h1
    exact ⟨_, _, _, h1⟩

end Major

/-! ## Symmetric wrapper consumption and twin rule prefix matching -/

section SymWrap

variable {find? : Key md → Option (ConstantInfo md)}

theorem ConsumeStar.linear {t a b : Expr md}
    (ha : ConsumeStar find? t a) (hb : ConsumeStar find? t b) :
    ConsumeStar find? a b ∨ ConsumeStar find? b a := by
  induction ha generalizing b with
  | refl => exact Or.inl hb
  | step hc ha' ih =>
    cases hb with
    | refl => exact Or.inr (.step hc ha')
    | step hc' hb' =>
      have heq := Option.some.inj (hc.symm.trans hc')
      subst heq
      exact ih hb'

theorem WrapT.refl (find? : Key md → Option (ConstantInfo md)) :
    ∀ e : Expr md, letFree e = true → WrapT find? e e
  | .bvar i, _ => .bvar i
  | .fvar i t, _ => .fvar i t t
  | .sort _, _ => .sort (fun _ => rfl)
  | .const _ us, _ => .const (Forall₂.refl (fun _ _ => rfl) us)
  | .lit l, _ => .lit l
  | .app f a, h => by
    simp only [letFree, Bool.and_eq_true] at h
    exact .app (WrapT.refl find? f h.1) (WrapT.refl find? a h.2)
  | .lam t b _, h => by
    simp only [letFree, Bool.and_eq_true] at h
    exact .lam rfl (.refl t) (WrapT.refl find? t h.1) (WrapT.refl find? b h.2)
  | .forallE t b _, h => by
    simp only [letFree, Bool.and_eq_true] at h
    exact .forallE rfl (.refl t) (WrapT.refl find? t h.1) (WrapT.refl find? b h.2)
  | .letE .., h => by simp [letFree] at h
  | .proj _ _ e, h => .proj (WrapT.refl find? e h)

theorem WrapT.mkAppN : ∀ {args args' : List (Expr md)} {f f' : Expr md},
    WrapT find? f f' → Forall₂ (WrapT find?) args args' →
      WrapT find? (Expr.mkAppN f args) (Expr.mkAppN f' args')
  | [], [], _, _, hf, .nil => hf
  | _ :: _, _ :: _, _, _, hf, .cons ha has => WrapT.mkAppN (.app hf ha) has

theorem WrapT.mkAppN_inv : ∀ (args : List (Expr md)) {f t : Expr md},
    WrapT find? (Expr.mkAppN f args) t →
      ∃ f' args', t = Expr.mkAppN f' args' ∧ args'.length = args.length ∧
        WrapT find? f f' ∧ Forall₂ (WrapT find?) args args'
  | [], _, t, h => ⟨t, [], rfl, rfl, h, .nil⟩
  | a :: as, f, t, h => by
    obtain ⟨fa', as', rfl, hlen, hfa, has'⟩ := WrapT.mkAppN_inv as (f := .app f a) h
    cases hfa with
    | app hf ha =>
      exact ⟨_, _ :: as', rfl, by simp [hlen], hf, .cons ha has'⟩

theorem WrapT.consumeWrapper {t₁ t₂ a₁ : Expr md}
    (h : WrapT find? t₁ t₂) (hc : Ix.Kernel.Semantics.consumeWrapper find? t₁ = some a₁) :
    ∃ a₂, Ix.Kernel.Semantics.consumeWrapper find? t₂ = some a₂ ∧ WrapT find? a₁ a₂ := by
  obtain ⟨w, us, rest, rfl, hw⟩ := consumeWrapper_inv hc
  obtain ⟨f', args', rfl, hlen, hf, hargs⟩ := WrapT.mkAppN_inv (a₁ :: rest) h
  cases hf with
  | const _ =>
    cases hargs with
    | cons ha hrest =>
      rename_i a₂ rest₂
      have hlen' : rest₂.length = rest.length := by simpa using hlen
      exact ⟨a₂, consumeWrapper_mkAppN (by rw [hlen']; exact hw), ha⟩

theorem WrapT.consumeStar {t₁ t₂ a₁ : Expr md}
    (h : WrapT find? t₁ t₂) (hs : ConsumeStar find? t₁ a₁) :
    ∃ a₂, ConsumeStar find? t₂ a₂ ∧ WrapT find? a₁ a₂ := by
  induction hs generalizing t₂ with
  | refl => exact ⟨t₂, .refl t₂, h⟩
  | step hc _ ih =>
    obtain ⟨a₂', hc₂, ha⟩ := h.consumeWrapper hc
    obtain ⟨a₂, hs₂, hfin⟩ := ih ha
    exact ⟨a₂, .step hc₂ hs₂, hfin⟩

theorem ConsumeStar.toWrapDom {t a t' : Expr md}
    (hs : ConsumeStar find? t a) (h : WrapRel find? a t') : WrapDom find? t t' := by
  induction hs with
  | refl => exact .keep h
  | step hc _ ih => exact .consume hc (ih h)

theorem WrapT.toWrapRel {g d : Expr md} (h : WrapT find? g d) (hf : g.hasFvar = false) :
    WrapRel find? g d := by
  have hP : ∀ f x : Expr md, (Expr.app f x).hasFvar = false →
      f.hasFvar = false ∧ x.hasFvar = false := by
    intro f x h; simpa [Ix.Kernel.Expr.hasFvar] using h
  induction h with
  | bvar i => exact .bvar i
  | fvar => simp [Ix.Kernel.Expr.hasFvar] at hf
  | sort h => exact .sort h
  | const h => exact .const h
  | lit l => exact .lit l
  | app _ _ ihf iha =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .app (ihf hf.1) (iha hf.2)
  | lam hpw hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .lam hpw (hs.toWrapDom (ihw (hs.of (P := fun e => e.hasFvar = false) hP hf.1)))
      (ihb hf.2)
  | forallE hpw hs _ _ ihw ihb =>
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact .forallE hpw (hs.toWrapDom (ihw (hs.of (P := fun e => e.hasFvar = false) hP hf.1)))
      (ihb hf.2)
  | proj _ ih => exact .proj (ih hf)

theorem consumeWrapper_none_empty (t : Expr md) :
    consumeWrapper (fun _ : Key md => (none : Option (ConstantInfo md))) t = none := by
  unfold consumeWrapper
  cases t.getAppFn <;> try rfl
  cases t.getAppArgs <;> simp [wrapperArity]

theorem ConsumeStar.eq_of_empty {t a : Expr md}
    (h : ConsumeStar (fun _ : Key md => (none : Option (ConstantInfo md))) t a) : a = t :=
  h.eq_of_none (consumeWrapper_none_empty t)

theorem WrapT.mono_empty {g d : Expr md}
    (h : WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) g d) :
    WrapT find? g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i t t' => exact .fvar i t t'
  | sort h => exact .sort h
  | const h => exact .const h
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hs _ _ ihw ihb =>
    have ha := hs.eq_of_empty; subst ha
    exact .lam hpw (.refl _) ihw ihb
  | forallE hpw hs _ _ ihw ihb =>
    have ha := hs.eq_of_empty; subst ha
    exact .forallE hpw (.refl _) ihw ihb
  | proj _ ih => exact .proj ih

private theorem forall₂_eval_symm :
    ∀ {us vs : List Level},
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us vs →
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) vs us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hr => .cons (fun φ => (h φ).symm) (forall₂_eval_symm hr)

private theorem forall₂_eval_symm_trans :
    ∀ {gs us vs : List Level},
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) gs us →
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) gs vs →
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us vs
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 r1, .cons h2 r2 =>
    .cons (fun φ => (h1 φ).symm.trans (h2 φ)) (forall₂_eval_symm_trans r1 r2)

theorem WrapT.symm_empty {a b : Expr md}
    (h : WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) a b) :
    WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) b a := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i t t' => exact .fvar i t' t
  | sort h => exact .sort (fun φ => (h φ).symm)
  | const h => exact .const (forall₂_eval_symm h)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hs _ _ ihw ihb =>
    have ha := hs.eq_of_empty; subst ha
    exact .lam hpw.symm (.refl _) ihw ihb
  | forallE hpw hs _ _ ihw ihb =>
    have ha := hs.eq_of_empty; subst ha
    exact .forallE hpw.symm (.refl _) ihw ihb
  | proj _ ih => exact .proj ih

/-- **Symmetric wrapper relation on `let`-free terms**: at each binder domain, wrappers may be
consumed on either the left or the right. -/
inductive SymWrapT (find? : Key md → Option (ConstantInfo md)) : Expr md → Expr md → Prop
  | bvar (i : Nat) : SymWrapT find? (.bvar i) (.bvar i)
  | fvar (i : Nat) (t t' : Expr md) : SymWrapT find? (.fvar i t) (.fvar i t')
  | sort {u v : Level} :
      (∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) → SymWrapT find? (.sort u) (.sort v)
  | const {n : Key md} {us vs : List Level} :
      Forall₂ (fun u v => ∀ φ : LevelParam → Nat, u.eval φ = v.eval φ) us vs →
      SymWrapT find? (.const n us) (.const n vs)
  | lit (l : Literal) : SymWrapT find? (.lit l) (.lit l)
  | app {f a f' a' : Expr md} :
      SymWrapT find? f f' → SymWrapT find? a a' → SymWrapT find? (.app f a) (.app f' a')
  | lamL {t a t' b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → SymWrapT find? a t' → SymWrapT find? b b' →
      SymWrapT find? (.lam t b m) (.lam t' b' m')
  | lamR {t t' a b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t' a → SymWrapT find? t a → SymWrapT find? b b' →
      SymWrapT find? (.lam t b m) (.lam t' b' m')
  | forallEL {t a t' b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t a → SymWrapT find? a t' → SymWrapT find? b b' →
      SymWrapT find? (.forallE t b m) (.forallE t' b' m')
  | forallER {t t' a b b' : Expr md} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumeStar find? t' a → SymWrapT find? t a → SymWrapT find? b b' →
      SymWrapT find? (.forallE t b m) (.forallE t' b' m')
  | proj {s : Key md} {i : Nat} {e e' : Expr md} :
      SymWrapT find? e e' → SymWrapT find? (.proj s i e) (.proj s i e')

theorem SymWrapT.of_wrapT {g d : Expr md} (h : WrapT find? g d) : SymWrapT find? g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i t t' => exact .fvar i t t'
  | sort h => exact .sort h
  | const h => exact .const h
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hs _ _ ihw ihb => exact .lamL hpw hs ihw ihb
  | forallE hpw hs _ _ ihw ihb => exact .forallEL hpw hs ihw ihb
  | proj _ ih => exact .proj ih

theorem SymWrapT.symm {d₁ d₂ : Expr md} (h : SymWrapT find? d₁ d₂) : SymWrapT find? d₂ d₁ := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i t t' => exact .fvar i t' t
  | sort h => exact .sort (fun φ => (h φ).symm)
  | const h => exact .const (forall₂_eval_symm h)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lamL hpw hs _ _ ihw ihb => exact .lamR hpw.symm hs ihw ihb
  | lamR hpw hs _ _ ihw ihb => exact .lamL hpw.symm hs ihw ihb
  | forallEL hpw hs _ _ ihw ihb => exact .forallER hpw.symm hs ihw ihb
  | forallER hpw hs _ _ ihw ihb => exact .forallEL hpw.symm hs ihw ihb
  | proj _ ih => exact .proj ih

theorem SymWrapT.instantiate1 {v₁ v₂ : Expr md} (hv : SymWrapT find? v₁ v₂) {d₁ d₂ : Expr md}
    (h : SymWrapT find? d₁ d₂) : ∀ j, SymWrapT find? (d₁.instantiate1 v₁ j) (d₂.instantiate1 v₂ j) := by
  induction h with
  | bvar i =>
    intro j
    show SymWrapT find? (if i = j then v₁ else if i > j then .bvar (i - 1) else .bvar i)
      (if i = j then v₂ else if i > j then .bvar (i - 1) else .bvar i)
    by_cases h1 : i = j
    · rw [if_pos h1, if_pos h1]; exact hv
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : i > j
      · rw [if_pos h2]; exact .bvar _
      · rw [if_neg h2]; exact .bvar _
  | fvar i t t' => intro _; exact .fvar i t t'
  | sort h => intro _; exact .sort h
  | const h => intro _; exact .const h
  | lit l => intro _; exact .lit l
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | lamL hpw hs _ _ ihw ihb =>
    intro j; exact .lamL hpw (hs.instantiate1 v₁ j) (ihw j) (ihb (j + 1))
  | lamR hpw hs _ _ ihw ihb =>
    intro j; exact .lamR hpw (hs.instantiate1 v₂ j) (ihw j) (ihb (j + 1))
  | forallEL hpw hs _ _ ihw ihb =>
    intro j; exact .forallEL hpw (hs.instantiate1 v₁ j) (ihw j) (ihb (j + 1))
  | forallER hpw hs _ _ ihw ihb =>
    intro j; exact .forallER hpw (hs.instantiate1 v₂ j) (ihw j) (ihb (j + 1))
  | proj _ ih => intro j; exact .proj (ih j)

private theorem symWrapT_of_span_aux : ∀ (n : Nat) (g d₁ d₂ : Expr md), g.sizeB < n →
    WrapT find? g d₁ → WrapT find? g d₂ → SymWrapT find? d₁ d₂
  | 0, _, _, _, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, _, _, _, hlt, h₁, h₂ => by
    cases h₁ with
    | bvar i => cases h₂; exact .bvar i
    | fvar i _ _ => cases h₂; exact .fvar i _ _
    | sort hu₁ =>
      cases h₂ with
      | sort hu₂ => exact .sort (fun φ => (hu₁ φ).symm.trans (hu₂ φ))
    | const hus₁ =>
      cases h₂ with
      | const hus₂ => exact .const (forall₂_eval_symm_trans hus₁ hus₂)
    | lit l => cases h₂; exact .lit l
    | app hf₁ ha₁ =>
      cases h₂ with
      | app hf₂ ha₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        exact .app (symWrapT_of_span_aux n _ _ _ (by omega) hf₁ hf₂)
          (symWrapT_of_span_aux n _ _ _ (by omega) ha₁ ha₂)
    | lam hpw₁ hs₁ hw₁ hb₁ =>
      cases h₂ with
      | lam hpw₂ hs₂ hw₂ hb₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        have hb := symWrapT_of_span_aux n _ _ _ (by omega) hb₁ hb₂
        rcases hs₁.linear hs₂ with h12 | h21
        · obtain ⟨c₁, hcs₁, hwc₁⟩ := hw₁.consumeStar h12
          have hsz := hs₂.sizeB_le
          exact .lamL (hpw₁.symm.trans hpw₂) hcs₁
            (symWrapT_of_span_aux n _ _ _ (by omega) hwc₁ hw₂) hb
        · obtain ⟨c₂, hcs₂, hwc₂⟩ := hw₂.consumeStar h21
          have hsz := hs₁.sizeB_le
          exact .lamR (hpw₁.symm.trans hpw₂) hcs₂
            (symWrapT_of_span_aux n _ _ _ (by omega) hw₁ hwc₂) hb
    | forallE hpw₁ hs₁ hw₁ hb₁ =>
      cases h₂ with
      | forallE hpw₂ hs₂ hw₂ hb₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        have hb := symWrapT_of_span_aux n _ _ _ (by omega) hb₁ hb₂
        rcases hs₁.linear hs₂ with h12 | h21
        · obtain ⟨c₁, hcs₁, hwc₁⟩ := hw₁.consumeStar h12
          have hsz := hs₂.sizeB_le
          exact .forallEL (hpw₁.symm.trans hpw₂) hcs₁
            (symWrapT_of_span_aux n _ _ _ (by omega) hwc₁ hw₂) hb
        · obtain ⟨c₂, hcs₂, hwc₂⟩ := hw₂.consumeStar h21
          have hsz := hs₁.sizeB_le
          exact .forallER (hpw₁.symm.trans hpw₂) hcs₂
            (symWrapT_of_span_aux n _ _ _ (by omega) hw₁ hwc₂) hb
    | proj he₁ =>
      cases h₂ with
      | proj he₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        exact .proj (symWrapT_of_span_aux n _ _ _ (by omega) he₁ he₂)

/-- Two `WrapT` descendants of a common term are related by `SymWrapT`. -/
theorem symWrapT_of_span {g d₁ d₂ : Expr md}
    (h₁ : WrapT find? g d₁) (h₂ : WrapT find? g d₂) : SymWrapT find? d₁ d₂ :=
  symWrapT_of_span_aux (g.sizeB + 1) g d₁ d₂ (Nat.lt_succ_self _) h₁ h₂

private theorem mkAppN_hasFvar_false : ∀ (args : List (Expr md)) (f : Expr md),
    (Expr.mkAppN f args).hasFvar = false ↔ f.hasFvar = false ∧ ∀ a ∈ args, a.hasFvar = false
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    simp only [Expr.mkAppN, mkAppN_hasFvar_false as (.app f a), Expr.hasFvar,
      Bool.or_eq_false_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨hf, ha⟩, has⟩
      exact ⟨hf, fun x hx => hx.elim (fun h => h ▸ ha) (has x)⟩
    · rintro ⟨hf, hall⟩
      exact ⟨⟨hf, hall a (Or.inl rfl)⟩, fun x hx => hall x (Or.inr hx)⟩

private theorem mkAppN_letFree : ∀ (args : List (Expr md)) (f : Expr md),
    letFree (Expr.mkAppN f args) = true ↔ letFree f = true ∧ ∀ a ∈ args, letFree a = true
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    simp only [Expr.mkAppN, mkAppN_letFree as (.app f a), letFree, Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨hf, ha⟩, has⟩
      exact ⟨hf, fun x hx => hx.elim (fun h => h ▸ ha) (has x)⟩
    · rintro ⟨hf, hall⟩
      exact ⟨⟨hf, hall a (Or.inl rfl)⟩, fun x hx => hall x (Or.inr hx)⟩

private theorem mkAppN_renameConsts (f : Key md → Key md) :
    ∀ (args : List (Expr md)) (hd : Expr md),
      (Expr.mkAppN hd args).renameConsts f =
        Expr.mkAppN (hd.renameConsts f) (args.map (Expr.renameConsts f))
  | [], _ => rfl
  | a :: as, hd => by
    simp only [Expr.mkAppN, List.map_cons]
    exact mkAppN_renameConsts f as (.app hd a)

private theorem mkAppN_renameConsts_eq (f : Key md → Key md) :
    ∀ (args : List (Expr md)) (hd : Expr md),
      (Expr.mkAppN hd args).renameConsts f = Expr.mkAppN hd args →
      hd.renameConsts f = hd ∧ ∀ a ∈ args, a.renameConsts f = a
  | [], _, h => ⟨h, fun _ hm => nomatch hm⟩
  | a :: as, hd, h => by
    obtain ⟨hha, has⟩ := mkAppN_renameConsts_eq f as (.app hd a) h
    simp only [Expr.renameConsts, Expr.app.injEq] at hha
    exact ⟨hha.1, fun x hx => (List.mem_cons.mp hx).elim (fun hx => hx ▸ hha.2) (has x)⟩

private theorem liftConsumeStar {t a ga : Expr md}
    (hs : ConsumeStar find? t a) (hga : WrapT find? ga a) :
    letFree t = true →
    ∃ gt : Expr md,
      WrapT find? gt t ∧ ConsumeStar find? gt ga ∧
      (t.hasFvar = false → ga.hasFvar = false → gt.hasFvar = false) ∧
      (∀ f : Key md → Key md, t.renameConsts f = t → ga.renameConsts f = ga →
        gt.renameConsts f = gt) := by
  induction hs with
  | refl _ =>
    intro _
    exact ⟨ga, hga, .refl ga, fun _ h => h, fun _ _ h => h⟩
  | @step t a₁ c hc hs' ih =>
    intro hlf
    obtain ⟨w, us, rest, rfl, hw⟩ := consumeWrapper_inv hc
    have hlf' := (mkAppN_letFree (a₁ :: rest) (.const w us)).mp hlf
    have hlf_a₁ : letFree a₁ = true := hlf'.2 a₁ List.mem_cons_self
    obtain ⟨gt₁, hgt₁_a₁, hcs₁, hfv₁, hren₁⟩ := ih hga hlf_a₁
    refine ⟨Expr.mkAppN (.const w us) (gt₁ :: rest), ?_, ?_, ?_, ?_⟩
    · refine WrapT.mkAppN (.const (Forall₂.refl (fun _ _ => rfl) us)) (.cons hgt₁_a₁ ?_)
      have hrefl : ∀ l : List (Expr md), (∀ x ∈ l, letFree x = true) → Forall₂ (WrapT find?) l l := by
        intro l
        induction l with
        | nil => intro _; exact .nil
        | cons x xs ihx =>
          intro hx
          exact .cons (WrapT.refl find? x (hx x List.mem_cons_self))
            (ihx fun y hy => hx y (List.mem_cons_of_mem _ hy))
      exact hrefl rest (fun x hx => hlf'.2 x (List.mem_cons_of_mem _ hx))
    · exact .step (consumeWrapper_mkAppN hw) hcs₁
    · intro hfv_t hfv_ga
      have hf' := (mkAppN_hasFvar_false (a₁ :: rest) (.const w us)).mp hfv_t
      rw [mkAppN_hasFvar_false]
      refine ⟨rfl, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hfv₁ (hf'.2 a₁ List.mem_cons_self) hfv_ga
      · exact hf'.2 x (List.mem_cons_of_mem _ hx')
    · intro f hrt hrga
      obtain ⟨hfw, hargs⟩ := mkAppN_renameConsts_eq f (a₁ :: rest) (.const w us) hrt
      rw [mkAppN_renameConsts, hfw, List.map_cons,
        hren₁ f (hargs a₁ List.mem_cons_self) hrga]
      have hmap : rest.map (Expr.renameConsts f) = rest := by
        have h : ∀ l : List (Expr md), (∀ x ∈ l, x.renameConsts f = x) → l.map (Expr.renameConsts f) = l := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons x xs ihx =>
            intro hx
            simp only [List.map_cons, hx x List.mem_cons_self,
              ihx fun y hy => hx y (List.mem_cons_of_mem _ hy)]
        exact h rest (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
      rw [hmap]

/-- Any two `let`-free terms related by `SymWrapT` admit a common `WrapT` ancestor `g` preserving
fvar-freeness and fixedness under any constant renaming. -/
theorem SymWrapT.exists_join {d₁ d₂ : Expr md} (h : SymWrapT find? d₁ d₂) :
    letFree d₁ = true → letFree d₂ = true →
    ∃ g : Expr md,
      WrapT find? g d₁ ∧ WrapT find? g d₂ ∧
      (d₁.hasFvar = false → d₂.hasFvar = false → g.hasFvar = false) ∧
      (∀ f : Key md → Key md, d₁.renameConsts f = d₁ → d₂.renameConsts f = d₂ →
        g.renameConsts f = g) := by
  have hlfP : ∀ f x : Expr md, letFree (.app f x) = true → letFree f = true ∧ letFree x = true := by
    intro f x h; simpa [letFree] using h
  have hfvP : ∀ f x : Expr md, (Expr.app f x).hasFvar = false →
      f.hasFvar = false ∧ x.hasFvar = false := by
    intro f x h; simpa [Expr.hasFvar] using h
  have hrenP : ∀ (f : Key md → Key md) (fn arg : Expr md),
      (Expr.app fn arg).renameConsts f = .app fn arg →
      fn.renameConsts f = fn ∧ arg.renameConsts f = arg := by
    intro f fn arg h; simpa [Expr.renameConsts] using h
  induction h with
  | bvar i => intro _ _; exact ⟨.bvar i, .bvar i, .bvar i, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | fvar i t t' =>
    intro _ _
    exact ⟨.fvar i t, .fvar i t t, .fvar i t t', fun h _ => h, fun _ h _ => h⟩
  | sort hu =>
    intro _ _
    exact ⟨.sort _, .sort (fun _ => rfl), .sort hu, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | const hus =>
    intro _ _
    exact ⟨.const _ _, .const (Forall₂.refl (fun _ _ => rfl) _), .const hus,
      fun _ _ => rfl, fun _ h _ => h⟩
  | lit l => intro _ _; exact ⟨.lit l, .lit l, .lit l, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | app _ _ ihf iha =>
    intro h1 h2
    simp only [letFree, Bool.and_eq_true] at h1 h2
    obtain ⟨gf, hgf1, hgf2, hff, hrf⟩ := ihf h1.1 h2.1
    obtain ⟨ga, hga1, hga2, hfa, hra⟩ := iha h1.2 h2.2
    refine ⟨.app gf ga, .app hgf1 hga1, .app hgf2 hga2, ?_, ?_⟩
    · intro hfv1 hfv2
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv1 hfv2 ⊢
      exact ⟨hff hfv1.1 hfv2.1, hfa hfv1.2 hfv2.2⟩
    · intro f hr1 hr2
      simp only [Expr.renameConsts, Expr.app.injEq] at hr1 hr2 ⊢
      exact ⟨hrf f hr1.1 hr2.1, hra f hr1.2 hr2.2⟩
  | @lamL t a t' b b' m m' hpw hs _ _ ihw ihb =>
    intro h1 h2
    simp only [letFree, Bool.and_eq_true] at h1 h2
    obtain ⟨ga, hga1, hga2, hfa, hra⟩ := ihw (hs.of hlfP h1.1) h2.1
    obtain ⟨gt, hgt_t, hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga1 h1.1
    obtain ⟨gb, hgb1, hgb2, hfb, hrb⟩ := ihb h1.2 h2.2
    refine ⟨.lam gt gb m, .lam rfl (.refl gt) hgt_t hgb1, .lam hpw hcs_gt hga2 hgb2, ?_, ?_⟩
    · intro hfv1 hfv2
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv1 hfv2 ⊢
      exact ⟨hft hfv1.1 (hfa (hs.of hfvP hfv1.1) hfv2.1), hfb hfv1.2 hfv2.2⟩
    · intro f hr1 hr2
      simp only [Expr.renameConsts, Expr.lam.injEq] at hr1 hr2 ⊢
      exact ⟨hrt f hr1.1 (hra f (hs.of (hP := hrenP f) hr1.1) hr2.1), hrb f hr1.2 hr2.2⟩
  | @lamR t t' a b b' m m' hpw hs _ _ ihw ihb =>
    intro h1 h2
    simp only [letFree, Bool.and_eq_true] at h1 h2
    obtain ⟨ga, hga1, hga2, hfa, hra⟩ := ihw h1.1 (hs.of hlfP h2.1)
    obtain ⟨gt, hgt_t', hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga2 h2.1
    obtain ⟨gb, hgb1, hgb2, hfb, hrb⟩ := ihb h1.2 h2.2
    refine ⟨.lam gt gb m, .lam rfl hcs_gt hga1 hgb1, .lam hpw (.refl gt) hgt_t' hgb2, ?_, ?_⟩
    · intro hfv1 hfv2
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv1 hfv2 ⊢
      exact ⟨hft hfv2.1 (hfa hfv1.1 (hs.of hfvP hfv2.1)), hfb hfv1.2 hfv2.2⟩
    · intro f hr1 hr2
      simp only [Expr.renameConsts, Expr.lam.injEq] at hr1 hr2 ⊢
      exact ⟨hrt f hr2.1 (hra f hr1.1 (hs.of (hP := hrenP f) hr2.1)), hrb f hr1.2 hr2.2⟩
  | @forallEL t a t' b b' m m' hpw hs _ _ ihw ihb =>
    intro h1 h2
    simp only [letFree, Bool.and_eq_true] at h1 h2
    obtain ⟨ga, hga1, hga2, hfa, hra⟩ := ihw (hs.of hlfP h1.1) h2.1
    obtain ⟨gt, hgt_t, hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga1 h1.1
    obtain ⟨gb, hgb1, hgb2, hfb, hrb⟩ := ihb h1.2 h2.2
    refine ⟨.forallE gt gb m, .forallE rfl (.refl gt) hgt_t hgb1,
      .forallE hpw hcs_gt hga2 hgb2, ?_, ?_⟩
    · intro hfv1 hfv2
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv1 hfv2 ⊢
      exact ⟨hft hfv1.1 (hfa (hs.of hfvP hfv1.1) hfv2.1), hfb hfv1.2 hfv2.2⟩
    · intro f hr1 hr2
      simp only [Expr.renameConsts, Expr.forallE.injEq] at hr1 hr2 ⊢
      exact ⟨hrt f hr1.1 (hra f (hs.of (hP := hrenP f) hr1.1) hr2.1), hrb f hr1.2 hr2.2⟩
  | @forallER t t' a b b' m m' hpw hs _ _ ihw ihb =>
    intro h1 h2
    simp only [letFree, Bool.and_eq_true] at h1 h2
    obtain ⟨ga, hga1, hga2, hfa, hra⟩ := ihw h1.1 (hs.of hlfP h2.1)
    obtain ⟨gt, hgt_t', hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga2 h2.1
    obtain ⟨gb, hgb1, hgb2, hfb, hrb⟩ := ihb h1.2 h2.2
    refine ⟨.forallE gt gb m, .forallE rfl hcs_gt hga1 hgb1,
      .forallE hpw (.refl gt) hgt_t' hgb2, ?_, ?_⟩
    · intro hfv1 hfv2
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv1 hfv2 ⊢
      exact ⟨hft hfv2.1 (hfa hfv1.1 (hs.of hfvP hfv2.1)), hfb hfv1.2 hfv2.2⟩
    · intro f hr1 hr2
      simp only [Expr.renameConsts, Expr.forallE.injEq] at hr1 hr2 ⊢
      exact ⟨hrt f hr2.1 (hra f hr1.1 (hs.of (hP := hrenP f) hr2.1)), hrb f hr1.2 hr2.2⟩
  | proj _ ih =>
    intro h1 h2
    obtain ⟨ge, hge1, hge2, hfe, hre⟩ := ih h1 h2
    refine ⟨.proj _ _ ge, .proj hge1, .proj hge2, hfe, fun f hr1 hr2 => ?_⟩
    simp only [Expr.renameConsts, Expr.proj.injEq] at hr1 hr2 ⊢
    exact ⟨hr1.1, hre f hr1.2 hr2.2⟩

/-- Strip `n` leading λ-binders, returning the body. -/
def stripLams : Nat → Expr md → Option (Expr md)
  | 0, e => some e
  | n + 1, .lam _ b _ => stripLams n b
  | _ + 1, _ => none

/-- `l` starts with `n` λ-binders whose domains are level-equivalent (`WrapT (fun _ => none)`)
to the first `n` `∀`-domains of `p`, leaving residual body `r`. -/
inductive LamDomAlong : Nat → Expr md → Expr md → Expr md → Prop
  | zero {l p : Expr md} : LamDomAlong 0 l p l
  | succ {n : Nat} {dl bl dp bp r : Expr md} {m mp : Ix.Kernel.BinderMeta} :
      WrapT (fun _ => none) dl dp →
      LamDomAlong n bl bp r →
      LamDomAlong (n + 1) (.lam dl bl m) (.forallE dp bp mp) r

/-- **Symmetric wrapper + λ-domain match for a twin rule**: `rhsW'` is symmetrically
wrapper-related to `rhsC.renameConsts f`, its leading `nPre` λ-domains match `tyW'`'s leading
`∀`-domains, its next `nf` λ-domains match the `iMin`-th `∀`-domain of `tyW'` lifted by
`nPre - iMin` (when `nf > 0`, with `iMin < nPre`), and its inner body is level-equivalent to
the inner body of `rhsC.renameConsts f` under `nPre + nf` λs. -/
def TwinRuleMatch (find? : Key md → Option (ConstantInfo md)) (f : Key md → Key md)
    (tyW' rhsC rhsW' : Expr md) : Prop :=
  SymWrapT find? (rhsC.renameConsts f) rhsW' ∧
  ∃ (nPre nf : Nat) (afterW sbW sbC : Expr md),
    LamDomAlong nPre rhsW' tyW' afterW ∧
    (nf = 0 ∧ sbW = afterW ∨
      ∃ (iMin : Nat) (bs : List (Expr md × Ix.Kernel.BinderMeta))
        (mdomW restW : Expr md) (mmW : Ix.Kernel.BinderMeta),
        iMin < nPre ∧
        tyW'.stripPis iMin = some (bs, .forallE mdomW restW mmW) ∧
        LamDomAlong nf afterW (mdomW.liftLooseBVars (nPre - iMin) 0) sbW) ∧
    stripLams (nPre + nf) (rhsC.renameConsts f) = some sbC ∧
    WrapT (fun _ => none) sbC sbW

theorem liftLooseBVars_zero : ∀ (e : Expr md) (c : Nat), e.liftLooseBVars 0 c = e
  | .bvar i, c => by simp only [Expr.liftLooseBVars]; split <;> simp
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by simp [Expr.liftLooseBVars, liftLooseBVars_zero f c, liftLooseBVars_zero a c]
  | .lam t b _, c => by
    simp [Expr.liftLooseBVars, liftLooseBVars_zero t c, liftLooseBVars_zero b (c + 1)]
  | .forallE t b _, c => by
    simp [Expr.liftLooseBVars, liftLooseBVars_zero t c, liftLooseBVars_zero b (c + 1)]
  | .letE t v b _, c => by
    simp [Expr.liftLooseBVars, liftLooseBVars_zero t c, liftLooseBVars_zero v c,
      liftLooseBVars_zero b (c + 1)]
  | .proj _ _ e, c => by simp [Expr.liftLooseBVars, liftLooseBVars_zero e c]

theorem liftLooseBVars_instantiate1_fvar (s k : Nat) (ty : Expr md) :
    ∀ (e : Expr md) (c i : Nat), c ≤ i →
      (e.liftLooseBVars s c).instantiate1 (.fvar k ty) (i + s) =
        (e.instantiate1 (.fvar k ty) i).liftLooseBVars s c
  | .bvar j, c, i, hci => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1]
    by_cases hjc : j ≥ c
    · rw [if_pos hjc]
      simp only [Expr.instantiate1]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, if_pos rfl]; rfl
      · rw [if_neg (by omega : ¬ j + s = i + s), if_neg hji]
        by_cases hgt : j > i
        · rw [if_pos (by omega : j + s > i + s), if_pos hgt]
          simp only [Expr.liftLooseBVars]
          rw [if_pos (by omega : j - 1 ≥ c)]
          congr 1; omega
        · rw [if_neg (by omega : ¬ j + s > i + s), if_neg hgt]
          simp only [Expr.liftLooseBVars, if_pos hjc]
    · rw [if_neg hjc]
      simp only [Expr.instantiate1]
      rw [if_neg (by omega : ¬ j = i + s), if_neg (by omega : ¬ j > i + s),
        if_neg (by omega : ¬ j = i), if_neg (by omega : ¬ j > i)]
      simp only [Expr.liftLooseBVars, if_neg hjc]
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, c, i, hci => by
    simp [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_instantiate1_fvar s k ty f c i hci,
      liftLooseBVars_instantiate1_fvar s k ty a c i hci]
  | .lam t b _, c, i, hci => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_instantiate1_fvar s k ty t c i hci]
    have h1 := liftLooseBVars_instantiate1_fvar s k ty b (c + 1) (i + 1) (by omega)
    rw [show i + 1 + s = i + s + 1 by omega] at h1
    rw [h1]
  | .forallE t b _, c, i, hci => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_instantiate1_fvar s k ty t c i hci]
    have h1 := liftLooseBVars_instantiate1_fvar s k ty b (c + 1) (i + 1) (by omega)
    rw [show i + 1 + s = i + s + 1 by omega] at h1
    rw [h1]
  | .letE t v b _, c, i, hci => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_instantiate1_fvar s k ty t c i hci,
      liftLooseBVars_instantiate1_fvar s k ty v c i hci]
    have h1 := liftLooseBVars_instantiate1_fvar s k ty b (c + 1) (i + 1) (by omega)
    rw [show i + 1 + s = i + s + 1 by omega] at h1
    rw [h1]
  | .proj _ _ e, c, i, hci => by
    simp [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_instantiate1_fvar s k ty e c i hci]

theorem liftLooseBVars_succ_instantiate1 (v : Expr md) (s : Nat) :
    ∀ (e : Expr md) (c : Nat),
      (e.liftLooseBVars (s + 1) c).instantiate1 v (c + s) = e.liftLooseBVars s c
  | .bvar j, c => by
    simp only [Expr.liftLooseBVars]
    by_cases hjc : j ≥ c
    · rw [if_pos hjc, if_pos hjc]
      simp only [Expr.instantiate1]
      rw [if_neg (by omega : ¬ j + (s + 1) = c + s), if_pos (by omega : j + (s + 1) > c + s)]
      congr 1; omega
    · rw [if_neg hjc, if_neg hjc]
      simp only [Expr.instantiate1]
      rw [if_neg (by omega : ¬ j = c + s), if_neg (by omega : ¬ j > c + s)]
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_succ_instantiate1 v s f c, liftLooseBVars_succ_instantiate1 v s a c]
  | .lam t b _, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1, liftLooseBVars_succ_instantiate1 v s t c]
    have h1 := liftLooseBVars_succ_instantiate1 v s b (c + 1)
    rw [show c + 1 + s = c + s + 1 by omega] at h1
    rw [h1]
  | .forallE t b _, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1, liftLooseBVars_succ_instantiate1 v s t c]
    have h1 := liftLooseBVars_succ_instantiate1 v s b (c + 1)
    rw [show c + 1 + s = c + s + 1 by omega] at h1
    rw [h1]
  | .letE t v' b _, c => by
    simp only [Expr.liftLooseBVars, Expr.instantiate1,
      liftLooseBVars_succ_instantiate1 v s t c, liftLooseBVars_succ_instantiate1 v s v' c]
    have h1 := liftLooseBVars_succ_instantiate1 v s b (c + 1)
    rw [show c + 1 + s = c + s + 1 by omega] at h1
    rw [h1]
  | .proj _ _ e, c => by
    simp [Expr.liftLooseBVars, Expr.instantiate1, liftLooseBVars_succ_instantiate1 v s e c]

theorem LamDomAlong.instantiate1 {v₁ v₂ : Expr md}
    (hv : WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) v₁ v₂)
    {n : Nat} {l p r : Expr md} (h : LamDomAlong n l p r) :
    ∀ j, LamDomAlong n (l.instantiate1 v₁ j) (p.instantiate1 v₂ j) (r.instantiate1 v₁ (j + n)) := by
  induction h with
  | zero => intro j; simpa using LamDomAlong.zero
  | @succ n dl bl dp bp r m mp hdom _ ih =>
    intro j
    have h1 := ih (j + 1)
    rw [show j + 1 + n = j + (n + 1) by omega] at h1
    exact .succ (WrapT.instantiate1 hv hdom j) h1

theorem LamDomAlong.split : ∀ (m n : Nat) {l p r : Expr md},
    LamDomAlong (m + n) l p r →
    ∃ mid midP bs,
      LamDomAlong m l p mid ∧ p.stripPis m = some (bs, midP) ∧ LamDomAlong n mid midP r
  | 0, _, l, p, _, h => by
    simp only [Nat.zero_add] at h
    exact ⟨l, p, [], .zero, rfl, h⟩
  | m + 1, n, _, _, _, h => by
    rw [show m + 1 + n = (m + n) + 1 by omega] at h
    cases h with
    | succ hdom hrest =>
      obtain ⟨mid, midP, bs, h1, hsp, h2⟩ := LamDomAlong.split m n hrest
      exact ⟨mid, midP, _, .succ hdom h1, stripPis_succ_forallE hsp, h2⟩

theorem stripLams_instantiate1 : ∀ (n : Nat) {e r : Expr md},
    stripLams n e = some r → ∀ v j, stripLams n (e.instantiate1 v j) = some (r.instantiate1 v (j + n))
  | 0, _, _, h, _, j => by
    simp only [stripLams, Option.some.injEq] at h ⊢
    subst h; simp
  | n + 1, .lam _ b _, _, h, v, j => by
    simp only [stripLams, Expr.instantiate1] at h ⊢
    have h1 := stripLams_instantiate1 n h v (j + 1)
    rwa [show j + 1 + n = j + (n + 1) by omega] at h1
  | _ + 1, .bvar _, _, h, _, _ | _ + 1, .fvar _ _, _, h, _, _ | _ + 1, .sort _, _, h, _, _
  | _ + 1, .const _ _, _, h, _, _ | _ + 1, .app _ _, _, h, _, _ | _ + 1, .forallE _ _ _, _, h, _, _
  | _ + 1, .letE _ _ _ _, _, h, _, _ | _ + 1, .lit _, _, h, _, _ | _ + 1, .proj _ _ _, _, h, _, _ => by
    simp [stripLams] at h

theorem stripLams_add : ∀ (m n : Nat) (e : Expr md),
    stripLams (m + n) e = (stripLams m e).bind (stripLams n)
  | 0, _, _ => by simp [stripLams]
  | m + 1, n, .lam _ b _ => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    exact stripLams_add m n b
  | m + 1, n, .bvar _ | m + 1, n, .fvar _ _ | m + 1, n, .sort _ | m + 1, n, .const _ _
  | m + 1, n, .app _ _ | m + 1, n, .forallE _ _ _ | m + 1, n, .letE _ _ _ _
  | m + 1, n, .lit _ | m + 1, n, .proj _ _ _ => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp [stripLams]

theorem stripPis_instantiate1 : ∀ (n : Nat) {e rest : Expr md}
    {bs : List (Expr md × Ix.Kernel.BinderMeta)},
    e.stripPis n = some (bs, rest) → ∀ v j,
      ∃ bs', (e.instantiate1 v j).stripPis n = some (bs', rest.instantiate1 v (j + n))
  | 0, _, _, _, h, _, j => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis]⟩
  | n + 1, _, _, _, h, v, j => by
    obtain ⟨t, b, m, bs0, rfl, hs0⟩ := stripPis_succ_inv h
    obtain ⟨bs', h1⟩ := stripPis_instantiate1 n hs0 v (j + 1)
    rw [show j + 1 + n = j + (n + 1) by omega] at h1
    exact ⟨_, stripPis_succ_forallE h1⟩

/-- Every leading λ-domain of `lC` and `lW` up to depth `n` is fixed by `f`. -/
inductive LamDomsFix (f : Key md → Key md) : Nat → Expr md → Expr md → Prop
  | zero {lC lW : Expr md} : LamDomsFix f 0 lC lW
  | succ {n : Nat} {dC bC dW bW : Expr md} {mC mW : Ix.Kernel.BinderMeta} :
      dC.renameConsts f = dC → dW.renameConsts f = dW →
      LamDomsFix f n bC bW →
      LamDomsFix f (n + 1) (.lam dC bC mC) (.lam dW bW mW)

/-- Build a common `WrapRel` ancestor `rhsG` for a pair of `let`-free rules related by `SymWrapT`
whose first `n` λ-domains are fixed by `f` and whose bodies match under `WrapT (fun _ => none)`. -/
theorem SymWrapT.exists_join_prefix {f : Key md → Key md} :
    ∀ (n : Nat) {lC lW sbC sbW : Expr md},
      SymWrapT find? (lC.renameConsts f) lW →
      stripLams n lC = some sbC →
      stripLams n lW = some sbW →
      WrapT (fun _ : Key md => (none : Option (ConstantInfo md))) (sbC.renameConsts f) sbW →
      LamDomsFix f n lC lW →
      lC.hasFvar = false → lW.hasFvar = false →
      letFree lC = true → letFree lW = true →
      ∃ rhsG : Expr md,
        WrapRel find? rhsG lC ∧ WrapRel find? (rhsG.renameConsts f) lW
  | 0, lC, lW, sbC, sbW, _, hC, hW, hsb, _, hfvC, _, _, _ => by
    simp only [stripLams, Option.some.injEq] at hC hW
    subst hC hW
    have hfvRen : (lC.renameConsts f).hasFvar = false := by
      clear hsb
      induction lC with
      | bvar _ | sort _ | const _ _ | lit _ => rfl
      | fvar _ _ => simp [Expr.hasFvar] at hfvC
      | app a b iha ihb =>
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfvC
        simp [Expr.renameConsts, Expr.hasFvar, iha hfvC.1, ihb hfvC.2]
      | lam t b _ iht ihb | forallE t b _ iht ihb =>
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfvC
        simp [Expr.renameConsts, Expr.hasFvar, iht hfvC.1, ihb hfvC.2]
      | letE t v b _ iht ihv ihb =>
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfvC
        simp [Expr.renameConsts, Expr.hasFvar, iht hfvC.1.1, ihv hfvC.1.2, ihb hfvC.2]
      | proj _ _ e ihe => exact ihe hfvC
    exact ⟨lC, WrapRel.refl find? lC, (hsb.mono_empty (find? := find?)).toWrapRel hfvRen⟩
  | n + 1, _, _, sbC, sbW, hSym, hC, hW, hsb, hfix, hfvC, hfvW, hlfC, hlfW => by
    cases hfix with
    | @succ _ dC bC dW bW mC mW hdC_fix hdW_fix hfix' =>
      simp only [stripLams] at hC hW
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfvC hfvW
      simp only [letFree, Bool.and_eq_true] at hlfC hlfW
      have hlfP : ∀ fn a : Expr md, letFree (.app fn a) = true →
          letFree fn = true ∧ letFree a = true := by
        intro fn a h; simpa [letFree] using h
      have hfvP : ∀ fn a : Expr md, (Expr.app fn a).hasFvar = false →
          fn.hasFvar = false ∧ a.hasFvar = false := by
        intro fn a h; simpa [Expr.hasFvar] using h
      have hrenP : ∀ fn a : Expr md, (Expr.app fn a).renameConsts f = .app fn a →
          fn.renameConsts f = fn ∧ a.renameConsts f = a := by
        intro fn a h; simpa [Expr.renameConsts] using h
      simp only [Expr.renameConsts, hdC_fix] at hSym
      cases hSym with
      | lamL hpw hs hd hb =>
        obtain ⟨ga, hga1, hga2, hfa, hra⟩ := hd.exists_join (hs.of hlfP hlfC.1) hlfW.1
        obtain ⟨gt, hgt_t, hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga1 hlfC.1
        have hgt_fv : gt.hasFvar = false :=
          hft hfvC.1 (hfa (hs.of hfvP hfvC.1) hfvW.1)
        have hgt_fix : gt.renameConsts f = gt :=
          hrt f hdC_fix (hra f (hs.of hrenP hdC_fix) hdW_fix)
        obtain ⟨gB, hgBC, hgBW⟩ :=
          SymWrapT.exists_join_prefix n hb hC hW hsb hfix' hfvC.2 hfvW.2 hlfC.2 hlfW.2
        refine ⟨.lam gt gB mC, .lam rfl (.keep (hgt_t.toWrapRel hgt_fv)) hgBC, ?_⟩
        simp only [Expr.renameConsts, hgt_fix]
        exact .lam hpw (hcs_gt.toWrapDom (hga2.toWrapRel (hfa (hs.of hfvP hfvC.1) hfvW.1))) hgBW
      | lamR hpw hs hd hb =>
        obtain ⟨ga, hga1, hga2, hfa, hra⟩ := hd.exists_join hlfC.1 (hs.of hlfP hlfW.1)
        obtain ⟨gt, hgt_t', hcs_gt, hft, hrt⟩ := liftConsumeStar hs hga2 hlfW.1
        have hgt_fv : gt.hasFvar = false :=
          hft hfvW.1 (hfa hfvC.1 (hs.of hfvP hfvW.1))
        have hgt_fix : gt.renameConsts f = gt :=
          hrt f hdW_fix (hra f hdC_fix (hs.of hrenP hdW_fix))
        obtain ⟨gB, hgBC, hgBW⟩ :=
          SymWrapT.exists_join_prefix n hb hC hW hsb hfix' hfvC.2 hfvW.2 hlfC.2 hlfW.2
        refine ⟨.lam gt gB mC,
          .lam rfl (hcs_gt.toWrapDom (hga1.toWrapRel (hfa hfvC.1 (hs.of hfvP hfvW.1)))) hgBC, ?_⟩
        simp only [Expr.renameConsts, hgt_fix]
        exact .lam hpw (.keep (hgt_t'.toWrapRel hgt_fv)) hgBW

end SymWrap

end Ix.Kernel.Semantics
