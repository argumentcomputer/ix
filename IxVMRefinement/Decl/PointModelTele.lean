import IxCK.Kernel.Rules.Inversion
import IxCK.Kernel.Verify.Abstract
import IxCK.Kernel.Verify.Shift
import IxCK.Kernel.Verify.InstLevels
import IxCK.Kernel.Verify.PropRead
import IxCK.Kernel.Verify.Denote.IndFrame

/-! # Telescopes with a replaced end, and the derivations over them

A block of inductive types whose recursors are never used can be interpreted with every type a
one-point type. The terms that say so are built from the members' own types by replacing the
end of a syntactic `∀`-telescope:

* `lamTele w e` turns the binders of `e` into `λ`s over the closed term `w`: over a former's
  type `∀ xs, Sort l` it is `λ xs, PUnit.{l}`, and over a constructor's type `∀ ys, T as` it is
  `λ ys, PUnit.unit.{v}`;
* `piTele W e` keeps the binders and ends in `W`: the type of the `λ`-telescope.

This file is syntax and derivations only. It proves

* `infer_lamTele`: the `λ`-telescope has the `∀`-telescope's type, from a typing of `e`;
* `defEq_piTele`: `piTele W e` converts to `e` when `W` converts to every application `e`
  can end in;
* `red_shadow_apply`: where a former is stored as the definition `lamTele PUnit.{l}` of its
  type, an application of it to as many arguments as it has binders reduces to `PUnit` (δ, then
  β at binders whose datum is `never`);
* `sort_of_endsHead`: the sort of a typed telescope ending in an application of a constant whose
  stored type is a telescope into `Sort l` has the zero-ness of `l` at the use's levels.
-/

namespace IxVM.Refinement.Decl.Point

open Ix.Kernel (Expr Level LevelParam Key Env ConstantInfo ConstantVal BinderMeta PropWhen
  ReducibilityHint)
open Ix.Kernel.Rules (Red DefEq Infer Grade)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The two telescopes -/

/-- The `∀`-telescope of `e` with its end replaced by `W`. -/
def piTele (W : Expr .anon) : Expr .anon → Expr .anon
  | .forallE ty b m => .forallE ty (piTele W b) m
  | _ => W

/-- The `∀`-telescope of `e` as a `λ`-telescope over `w`. -/
def lamTele (w : Expr .anon) : Expr .anon → Expr .anon
  | .forallE ty b m => .lam ty (lamTele w b) m
  | _ => w

@[simp] theorem piTele_forallE (W ty b : Expr .anon) (m : BinderMeta) :
    piTele W (.forallE ty b m) = .forallE ty (piTele W b) m := rfl

@[simp] theorem lamTele_forallE (w ty b : Expr .anon) (m : BinderMeta) :
    lamTele w (.forallE ty b m) = .lam ty (lamTele w b) m := rfl

/-- **The end of the telescope is a sort, a constant or an application**: no substitution turns
it into a binder. -/
def Shape : Expr .anon → Prop
  | .forallE _ b _ => Shape b
  | .sort _ => True
  | .const _ _ => True
  | .app _ _ => True
  | _ => False

/-- **The telescope ends in an application of the constant `T` at the levels `us` to `n`
arguments.** -/
def EndsHead (T : Key .anon) (us : List Level) (n : Nat) : Expr .anon → Prop
  | .forallE _ b _ => EndsHead T us n b
  | e => e.getAppFn = .const T us ∧ e.getAppArgs.length = n

/-- **Every binder of the telescope carries the datum `P`.** -/
def PwAll (P : PropWhen) : Expr .anon → Prop
  | .forallE _ b m => m.pw = P ∧ PwAll P b
  | _ => True

/-! ### Arity -/

theorem piTele_of_piArity_zero (W : Expr .anon) :
    ∀ {e : Expr .anon}, e.piArity = 0 → piTele W e = W
  | .forallE _ _ _, h => absurd h (Nat.succ_ne_zero _)
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

theorem lamTele_of_piArity_zero (w : Expr .anon) :
    ∀ {e : Expr .anon}, e.piArity = 0 → lamTele w e = w
  | .forallE _ _ _, h => absurd h (Nat.succ_ne_zero _)
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

theorem exists_forallE_of_piArity_succ :
    ∀ {e : Expr .anon} {n : Nat}, e.piArity = n + 1 →
      ∃ ty b m, e = .forallE ty b m ∧ b.piArity = n
  | .forallE ty b m, n, h => ⟨ty, b, m, rfl, Nat.succ.inj h⟩
  | .bvar _, n, h | .fvar _ _, n, h | .sort _, n, h | .const _ _, n, h | .app _ _, n, h
  | .lam _ _ _, n, h | .letE _ _ _ _, n, h | .lit _, n, h | .proj _ _ _, n, h =>
    absurd h (Nat.succ_ne_zero n).symm

/-! ### Shapes -/

theorem shape_of_resultSort :
    ∀ (e : Expr .anon) (l : Level), e.resultSort = some l → Shape e
  | .forallE _ b _, l, h => shape_of_resultSort b l h
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .app _ _, _, _ => trivial
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => nomatch h

theorem EndsHead.shape {T : Key .anon} {us : List Level} {n : Nat} :
    ∀ (e : Expr .anon), EndsHead T us n e → Shape e
  | .forallE _ b _, h => EndsHead.shape b h
  | .sort _, _ => trivial
  | .const _ _, _ => trivial
  | .app _ _, _ => trivial
  | .bvar _, h | .fvar _ _, h | .lam _ _ _, h | .letE _ _ _ _, h | .lit _, h
  | .proj _ _ _, h => nomatch h.1

/-- At the end of the telescope, `EndsHead` is the two facts about the application. -/
theorem EndsHead.base {T : Key .anon} {us : List Level} {n : Nat} :
    ∀ {e : Expr .anon}, e.piArity = 0 → EndsHead T us n e →
      e.getAppFn = .const T us ∧ e.getAppArgs.length = n
  | .forallE _ _ _, h, _ => absurd h (Nat.succ_ne_zero _)
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h | .app _ _, _, h
  | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => h

theorem shape_instantiate1 (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → Shape (e.instantiate1 v k)
  | .forallE _ b _, k, h => shape_instantiate1 v b (k + 1) h
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .app _ _, _, _ => trivial
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => False.elim h

theorem piArity_instantiate1 (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → (e.instantiate1 v k).piArity = e.piArity
  | .forallE _ b _, k, h => congrArg (· + 1) (piArity_instantiate1 v b (k + 1) h)
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app _ _, _, _ => rfl
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => False.elim h

theorem forallPw_instantiate1 (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → (e.instantiate1 v k).forallPw = e.forallPw
  | .forallE _ _ _, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app _ _, _, _ => rfl
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => False.elim h

theorem resultSort_instantiate1 (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat) (l : Level), e.resultSort = some l →
      (e.instantiate1 v k).resultSort = some l
  | .forallE _ b _, k, l, h => resultSort_instantiate1 v b (k + 1) l h
  | .sort _, _, _, h => h
  | .bvar _, _, _, h | .fvar _ _, _, _, h | .const _ _, _, _, h | .app _ _, _, _, h
  | .lam _ _ _, _, _, h | .letE _ _ _ _, _, _, h | .lit _, _, _, h | .proj _ _ _, _, _, h =>
    nomatch h

theorem EndsHead.instantiate1 {T : Key .anon} {us : List Level} {n : Nat} (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), EndsHead T us n e → EndsHead T us n (e.instantiate1 v k)
  | .forallE _ b _, k, h => EndsHead.instantiate1 v b (k + 1) h
  | .app f a, k, h =>
    have h2 := Ix.Kernel.Verify.Expr.getAppArgs_length_instantiate1_const (v := v)
      (Expr.app f a) k h.1
    ⟨h2.2, h2.1.trans h.2⟩
  | .const _ _, _, h => h
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h
  | .lit _, _, h | .proj _ _ _, _, h => nomatch h.1

theorem PwAll.instantiate1 {P : PropWhen} (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → PwAll P e → PwAll P (e.instantiate1 v k)
  | .forallE _ b _, k, hs, h => ⟨h.1, PwAll.instantiate1 v b (k + 1) hs h.2⟩
  | .sort _, _, _, _ => trivial
  | .const _ _, _, _, _ => trivial
  | .app _ _, _, _, _ => trivial
  | .bvar _, _, h, _ | .fvar _ _, _, h, _ | .lam _ _ _, _, h, _ | .letE _ _ _ _, _, h, _
  | .lit _, _, h, _ | .proj _ _ _, _, h, _ => False.elim h

/-! ### Substitution into the telescopes -/

theorem piTele_instantiate1 {W : Expr .anon} (hW : ∀ v k, W.instantiate1 v k = W)
    (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e →
      (piTele W e).instantiate1 v k = piTele W (e.instantiate1 v k)
  | .forallE ty b m, k, h => by
    have ih := piTele_instantiate1 hW v b (k + 1) h
    simp only [piTele_forallE, Expr.instantiate1, ih]
  | .sort _, k, _ => hW v k
  | .const _ _, k, _ => hW v k
  | .app _ _, k, _ => hW v k
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => False.elim h

theorem lamTele_instantiate1 {w : Expr .anon} (hw : ∀ v k, w.instantiate1 v k = w)
    (v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e →
      (lamTele w e).instantiate1 v k = lamTele w (e.instantiate1 v k)
  | .forallE ty b m, k, h => by
    have ih := lamTele_instantiate1 hw v b (k + 1) h
    simp only [lamTele_forallE, Expr.instantiate1, ih]
  | .sort _, k, _ => hw v k
  | .const _ _, k, _ => hw v k
  | .app _ _, k, _ => hw v k
  | .bvar _, _, h | .fvar _ _, _, h | .lam _ _ _, _, h | .letE _ _ _ _, _, h | .lit _, _, h
  | .proj _ _ _, _, h => False.elim h

/-- Where the telescope has no binder left, it is its end, under every substitution. -/
theorem piTele_of_forallPw_none (W v : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → e.forallPw = none →
      piTele W (e.instantiate1 v k) = W
  | .forallE _ _ _, _, _, h => nomatch h
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app _ _, _, _, _ => rfl
  | .bvar _, _, h, _ | .fvar _ _, _, h, _ | .lam _ _ _, _, h, _ | .letE _ _ _ _, _, h, _
  | .lit _, _, h, _ | .proj _ _ _, _, h, _ => False.elim h

theorem lamPw_lamTele {w : Expr .anon} (hw : w.lamPw = none) :
    ∀ (e : Expr .anon), (lamTele w e).lamPw = e.forallPw
  | .forallE _ _ _ => rfl
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ _ | .lit _
  | .proj _ _ _ => hw

/-! ### Level instantiation -/

theorem piArity_instantiateLevelParams (ks : List LevelParam) (us : List Level) :
    ∀ (e : Expr .anon), (e.instantiateLevelParams ks us).piArity = e.piArity
  | .forallE _ b _ => congrArg (· + 1) (piArity_instantiateLevelParams ks us b)
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ | .letE _ _ _ _ | .lit _
  | .proj _ _ _ => rfl

theorem resultSort_instantiateLevelParams (ks : List LevelParam) (us : List Level) :
    ∀ (e : Expr .anon) (l : Level), e.resultSort = some l →
      (e.instantiateLevelParams ks us).resultSort = some (Level.subst ks us l)
  | .forallE _ b _, l, h => resultSort_instantiateLevelParams ks us b l h
  | .sort u, l, h => by
    obtain rfl : u = l := Option.some.inj h
    rfl
  | .bvar _, _, h | .fvar _ _, _, h | .const _ _, _, h | .app _ _, _, h | .lam _ _ _, _, h
  | .letE _ _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => nomatch h

theorem PwAll.instantiateLevelParams {P : PropWhen} (ks : List LevelParam) (us : List Level) :
    ∀ (e : Expr .anon), PwAll P e →
      PwAll (Level.substPW ks us P) (e.instantiateLevelParams ks us)
  | .forallE _ b m, h =>
    ⟨congrArg (Level.substPW ks us) h.1, PwAll.instantiateLevelParams ks us b h.2⟩
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => trivial

theorem lamTele_instantiateLevelParams (w : Expr .anon) (ks : List LevelParam)
    (us : List Level) :
    ∀ (e : Expr .anon), Shape e →
      (lamTele w e).instantiateLevelParams ks us =
        lamTele (w.instantiateLevelParams ks us) (e.instantiateLevelParams ks us)
  | .forallE ty b m, h => by
    have ih := lamTele_instantiateLevelParams w ks us b h
    simp only [lamTele_forallE, Expr.instantiateLevelParams, ih]
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app _ _, _ => rfl
  | .bvar _, h | .fvar _ _, h | .lam _ _ _, h | .letE _ _ _ _, h | .lit _, h
  | .proj _ _ _, h => False.elim h

/-! ### What the telescopes keep -/

theorem lamTele_hasFvar {w : Expr .anon} (hw : w.hasFvar = false) :
    ∀ (e : Expr .anon), e.hasFvar = false → (lamTele w e).hasFvar = false
  | .forallE ty b m, h => by
    have h' : ty.hasFvar = false ∧ b.hasFvar = false := by
      simpa [Expr.hasFvar] using h
    have ih := lamTele_hasFvar hw b h'.2
    simp [Expr.hasFvar, h'.1, ih]
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => hw

theorem lamTele_looseBVarsBounded {w : Expr .anon} (hw : ∀ k, w.looseBVarsBounded k = true) :
    ∀ (e : Expr .anon) (k : Nat), e.looseBVarsBounded k = true →
      (lamTele w e).looseBVarsBounded k = true
  | .forallE ty b m, k, h => by
    have h' : ty.looseBVarsBounded k = true ∧ b.looseBVarsBounded (k + 1) = true := by
      simpa [Expr.looseBVarsBounded] using h
    have ih := lamTele_looseBVarsBounded hw b (k + 1) h'.2
    simp [Expr.looseBVarsBounded, h'.1, ih]
  | .bvar _, k, _ | .fvar _ _, k, _ | .sort _, k, _ | .const _ _, k, _ | .app _ _, k, _
  | .lam _ _ _, k, _ | .letE _ _ _ _, k, _ | .lit _, k, _ | .proj _ _ _, k, _ => hw k

theorem piTele_looseBVarsBounded {W : Expr .anon} (hW : ∀ k, W.looseBVarsBounded k = true) :
    ∀ (e : Expr .anon) (k : Nat), e.looseBVarsBounded k = true →
      (piTele W e).looseBVarsBounded k = true
  | .forallE ty b m, k, h => by
    have h' : ty.looseBVarsBounded k = true ∧ b.looseBVarsBounded (k + 1) = true := by
      simpa [Expr.looseBVarsBounded] using h
    have ih := piTele_looseBVarsBounded hW b (k + 1) h'.2
    simp [Expr.looseBVarsBounded, h'.1, ih]
  | .bvar _, k, _ | .fvar _ _, k, _ | .sort _, k, _ | .const _ _, k, _ | .app _ _, k, _
  | .lam _ _ _, k, _ | .letE _ _ _ _, k, _ | .lit _, k, _ | .proj _ _ _, k, _ => hW k

theorem piTele_fvarsBelow {W : Expr .anon} {d : Nat} (hW : W.fvarsBelow d) :
    ∀ (e : Expr .anon), e.fvarsBelow d → (piTele W e).fvarsBelow d
  | .forallE ty b m, h => ⟨h.1, piTele_fvarsBelow hW b h.2⟩
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => hW

theorem lamTele_allLevelParamsDefined {w : Expr .anon} {ps : List LevelParam}
    (hw : w.allLevelParamsDefined ps = true) :
    ∀ (e : Expr .anon), e.allLevelParamsDefined ps = true →
      (lamTele w e).allLevelParamsDefined ps = true
  | .forallE ty b m, h => by
    have h' : (ty.allLevelParamsDefined ps = true ∧ b.allLevelParamsDefined ps = true) ∧
        m.pw.paramsDefined ps = true := by
      simpa [Expr.allLevelParamsDefined] using h
    have ih := lamTele_allLevelParamsDefined hw b h'.1.2
    simp [Expr.allLevelParamsDefined, h'.1.1, h'.2, ih]
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => hw

theorem lamTele_constsResolve {w : Expr .anon} {env : Env .anon}
    (hw : w.constsResolve env = true) :
    ∀ (e : Expr .anon), e.constsResolve env = true → (lamTele w e).constsResolve env = true
  | .forallE ty b m, h => by
    have h' : ty.constsResolve env = true ∧ b.constsResolve env = true := by
      simpa [Expr.constsResolve] using h
    have ih := lamTele_constsResolve hw b h'.2
    simp [Expr.constsResolve, h'.1, ih]
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => hw

/-- The levels at a constant head are defined where the application's are. -/
theorem head_levels_defined {ps : List LevelParam} :
    ∀ (g : Expr .anon) {T : Key .anon} {us : List Level}, g.getAppFn = .const T us →
      g.allLevelParamsDefined ps = true → ∀ u ∈ us, u.allParamsDefined ps = true
  | .app g₁ g₂, _, _, hg, hd => by
    have h' : g₁.allLevelParamsDefined ps = true ∧ g₂.allLevelParamsDefined ps = true := by
      simpa [Expr.allLevelParamsDefined] using hd
    exact head_levels_defined g₁ hg h'.1
  | .const c cs, _, _, hg, hd => by
    obtain ⟨-, hcs⟩ := Expr.const.inj hg
    intro u hu
    rw [← hcs] at hu
    have hall : cs.all (Level.allParamsDefined ps) = true := hd
    exact List.all_eq_true.mp hall u hu
  | .bvar _, _, _, hg, _ | .fvar _ _, _, _, hg, _ | .sort _, _, _, hg, _
  | .lam _ _ _, _, _, hg, _ | .forallE _ _ _, _, _, hg, _ | .letE _ _ _ _, _, _, hg, _
  | .lit _, _, _, hg, _ | .proj _ _ _, _, _, hg, _ => nomatch hg

/-- The levels at the head of the telescope's end are defined where the telescope's are. -/
theorem EndsHead.levels_defined {T : Key .anon} {us : List Level} {n : Nat}
    {ps : List LevelParam} :
    ∀ (k : Nat) (e : Expr .anon), e.piArity = k → EndsHead T us n e →
      e.allLevelParamsDefined ps = true → ∀ u ∈ us, u.allParamsDefined ps = true
  | 0, e, hk, h, hd => head_levels_defined e (h.base hk).1 hd
  | k + 1, e, hk, h, hd => by
    obtain ⟨ty, b, m, rfl, hk'⟩ := exists_forallE_of_piArity_succ hk
    have h' : (ty.allLevelParamsDefined ps = true ∧ b.allLevelParamsDefined ps = true) ∧
        m.pw.paramsDefined ps = true := by
      simpa [Expr.allLevelParamsDefined] using hd
    exact EndsHead.levels_defined k b hk' h h'.1.2

/-- The level a telescope into a sort ends in is defined where the telescope's levels are. -/
theorem resultSort_defined {ps : List LevelParam} :
    ∀ (e : Expr .anon) (l : Level), e.resultSort = some l →
      e.allLevelParamsDefined ps = true → l.allParamsDefined ps = true
  | .forallE ty b m, l, h, hd => by
    have h' : (ty.allLevelParamsDefined ps = true ∧ b.allLevelParamsDefined ps = true) ∧
        m.pw.paramsDefined ps = true := by
      simpa [Expr.allLevelParamsDefined] using hd
    exact resultSort_defined b l h h'.1.2
  | .sort u, l, h, hd => by
    obtain rfl : u = l := Option.some.inj h
    exact hd
  | .bvar _, _, h, _ | .fvar _ _, _, h, _ | .const _ _, _, h, _ | .app _ _, _, h, _
  | .lam _ _ _, _, h, _ | .letE _ _ _ _, _, h, _ | .lit _, _, h, _ | .proj _ _ _, _, h, _ =>
    nomatch h

/-- A telescope with no binder that ends in a sort is that sort. -/
theorem eq_sort_of_resultSort :
    ∀ {e : Expr .anon} {l : Level}, e.piArity = 0 → e.resultSort = some l → e = .sort l
  | .forallE _ _ _, _, h, _ => absurd h (Nat.succ_ne_zero _)
  | .sort u, l, _, h => by
    obtain rfl : u = l := Option.some.inj h
    rfl
  | .bvar _, _, _, h | .fvar _ _, _, _, h | .const _ _, _, _, h | .app _ _, _, _, h
  | .lam _ _ _, _, _, h | .letE _ _ _ _, _, _, h | .lit _, _, _, h | .proj _ _ _, _, _, h =>
    nomatch h

/-! ### Opening, then closing, a binder body -/

/-- Opening a binder body at a variable it does not mention and closing it again is the
identity. -/
theorem abstract1_instantiate1_cancel {d : Nat} (ty : Expr .anon) :
    ∀ {e : Expr .anon} (k : Nat), e.fvarsBelow d → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d ty) k).abstract1 d k = e
  | .bvar i, k, _, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    by_cases hik : i = k
    · subst hik; simp [Expr.abstract1]
    · rw [ite_eq_right hik, ite_eq_right (by omega)]
      rfl
  | .fvar i fty, k, hf, _ => by
    simp only [Expr.fvarsBelow] at hf
    simp [Expr.instantiate1, Expr.abstract1, Nat.ne_of_lt hf]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty k hf.2 hb.2]
  | .lam ty₀ b _, k, hf, hb | .forallE ty₀ b _, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1,
      abstract1_instantiate1_cancel ty (k + 1) hf.2 hb.2]
  | .letE ty₀ v b _, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded, Bool.and_eq_true] at hf hb
    simp [Expr.instantiate1, Expr.abstract1,
      abstract1_instantiate1_cancel ty k hf.1 hb.1.1,
      abstract1_instantiate1_cancel ty k hf.2.1 hb.1.2,
      abstract1_instantiate1_cancel ty (k + 1) hf.2.2 hb.2]
  | .proj s i e, k, hf, hb => by
    simp only [Expr.fvarsBelow, Expr.looseBVarsBounded] at hf hb
    simpa [Expr.instantiate1, Expr.abstract1] using abstract1_instantiate1_cancel ty k hf hb

/-! ## Derivations -/

/-- **A typed `∀`-binder's datum is the zero-ness of the type's sort.** -/
theorem pw_of_infer_forallE {env : Env .anon} {d : Nat} {ty b s : Expr .anon} {m : BinderMeta}
    {v : Level} (h : Infer env .full d (.forallE ty b m) s) (hs : Red env d s (.sort v)) :
    m.pw = Level.zeronessOf v := by
  obtain ⟨s1, u, bs, v1, -, -, -, -, hz, rfl⟩ := Infer.forallE_inv h
  obtain rfl : v = .imax u v1 := Red.sort_eq hs
  exact hz.symm

/-- The datum at the head of a typed telescope, where it has a binder. -/
theorem forallPw_of_infer {env : Env .anon} {d : Nat} {s : Expr .anon} {v : Level}
    {pw : PropWhen} :
    ∀ {e : Expr .anon}, Infer env .full d e s → Red env d s (.sort v) →
      e.forallPw = some pw → pw = Level.zeronessOf v
  | .forallE _ _ _, h, hs, hp => by
    obtain rfl := Option.some.inj hp
    exact pw_of_infer_forallE h hs
  | .bvar _, _, _, hp | .fvar _ _, _, _, hp | .sort _, _, _, hp | .const _ _, _, _, hp
  | .app _ _, _, _, hp | .lam _ _ _, _, _, hp | .letE _ _ _ _, _, _, hp | .lit _, _, _, hp
  | .proj _ _ _, _, _, hp => nomatch hp

/-- The binders' data are read off the body before or after a substitution. -/
theorem PwAll.of_instantiate1 {P : PropWhen} (x : Expr .anon) :
    ∀ (e : Expr .anon) (k : Nat), Shape e → PwAll P (e.instantiate1 x k) → PwAll P e
  | .forallE _ b _, k, hs, h => ⟨h.1, PwAll.of_instantiate1 x b (k + 1) hs h.2⟩
  | .sort _, _, _, _ => trivial
  | .const _ _, _, _, _ => trivial
  | .app _ _, _, _, _ => trivial
  | .bvar _, _, h, _ | .fvar _ _, _, h, _ | .lam _ _ _, _, h, _ | .letE _ _ _ _, _, h, _
  | .lit _, _, h, _ | .proj _ _ _, _, h, _ => False.elim h

/-- Every binder of a typed telescope carries the zero-ness of the telescope's sort. -/
theorem pwAll_of_infer {env : Env .anon} :
    ∀ (n : Nat) (e : Expr .anon) (d : Nat) (s : Expr .anon) (v : Level), e.piArity = n →
      Shape e → Infer env .full d e s → Red env d s (.sort v) →
      PwAll (Level.zeronessOf v) e
  | 0, e, _, _, _, hn, _, _, _ => by
    cases e with
    | forallE _ _ _ => exact absurd hn (Nat.succ_ne_zero _)
    | _ => trivial
  | n + 1, e, d, s, v, hn, hsh, h, hs => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    have hm := pw_of_infer_forallE h hs
    obtain ⟨s1, u, bs, v1, -, -, hb, hv1, -, rfl⟩ := Infer.forallE_inv h
    obtain rfl : v = .imax u v1 := Red.sort_eq hs
    have hsh' : Shape b := hsh
    have ih : PwAll (Level.zeronessOf v1) (b.instantiate1 (.fvar d ty)) :=
      pwAll_of_infer n (b.instantiate1 (.fvar d ty)) (d + 1) bs v1
        (by rw [piArity_instantiate1 _ b 0 hsh']; exact hn')
        (shape_instantiate1 _ b 0 hsh') hb hv1
    exact ⟨hm, PwAll.of_instantiate1 (Expr.fvar d ty) b 0 hsh' ih⟩

/-- **The `λ`-telescope has the `∀`-telescope's type.** From a typing of the telescope `e`
whose sort has the zero-ness of `W`'s sort, the term `lamTele w e` has the type `piTele W e`,
for closed `w : W`. -/
theorem infer_lamTele {env : Env .anon} {w W : Expr .anon} {v' : Level}
    (hwi : ∀ x k, w.instantiate1 x k = w) (hWi : ∀ x k, W.instantiate1 x k = W)
    (hWf : ∀ d, W.fvarsBelow d) (hWb : ∀ k, W.looseBVarsBounded k = true)
    (hwpw : w.lamPw = none)
    (hw : ∀ d, Infer env .full d w W)
    (hW : ∀ d, Infer env .io d W (.sort v')) :
    ∀ (n : Nat) (e : Expr .anon) (d : Nat) (s : Expr .anon) (v : Level),
      e.piArity = n → Shape e → e.fvarsBelow d → e.looseBVarsBounded 0 = true →
      Infer env .full d e s → Red env d s (.sort v) →
      Level.zeronessOf v = Level.zeronessOf v' →
      Infer env .full d (lamTele w e) (piTele W e)
  | 0, e, d, _, _, hn, _, _, _, _, _, _ => by
    rw [lamTele_of_piArity_zero w hn, piTele_of_piArity_zero W hn]
    exact hw d
  | n + 1, e, d, s, v, hn, hsh, hf, hb, h, hs, hz => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    obtain ⟨s1, u, bs, v1, hty, hu, hbs, hv1, hz1, rfl⟩ := Infer.forallE_inv h
    obtain rfl : v = .imax u v1 := Red.sort_eq hs
    have hsh' : Shape b := hsh
    have hf' : ty.fvarsBelow d ∧ b.fvarsBelow d := hf
    have hb' : ty.looseBVarsBounded 0 = true ∧ b.looseBVarsBounded (0 + 1) = true := by
      simpa [Expr.looseBVarsBounded] using hb
    have hz' : Level.zeronessOf v1 = Level.zeronessOf v' := hz
    -- the body, by recursion
    have ih := infer_lamTele hwi hWi hWf hWb hwpw hw hW n (b.instantiate1 (.fvar d ty)) (d + 1)
      bs v1 (by rw [piArity_instantiate1 _ b 0 hsh']; exact hn')
      (shape_instantiate1 _ b 0 hsh') (Expr.fvarsBelow_instantiate1 0 hf'.2)
      (Ix.Kernel.looseBVarsBounded_instantiate1 b 0 hb'.2) hbs hv1 hz'
    rw [← lamTele_instantiate1 hwi (.fvar d ty) b 0 hsh'] at ih
    -- the binder's datum agrees with the body's own
    have hpw : ∀ pwI, (lamTele w b).lamPw = some pwI → m.pw = pwI := by
      intro pwI hI
      rw [lamPw_lamTele hwpw] at hI
      have hI' : (b.instantiate1 (.fvar d ty)).forallPw = some pwI := by
        rw [forallPw_instantiate1 _ b 0 hsh']; exact hI
      have := forallPw_of_infer hbs hv1 hI'
      rw [this]
      exact hz1.symm
    have hlam := Infer.lam (env := env) (g := .full) (d := d) (ty := ty)
      (body := lamTele w b) (s := s1) (bt := piTele W (b.instantiate1 (.fvar d ty)))
      (btt := .sort v') (u := u) (v := v') (mb := m)
      (fun _ => hty) (fun _ => hu) ih hpw
      (fun hnone => by
        rw [lamPw_lamTele hwpw] at hnone
        rw [piTele_of_forallPw_none W (.fvar d ty) b 0 hsh' hnone]
        exact hW (d + 1))
      (fun _ => Red.refl)
      (fun _ => hz'.symm.trans hz1)
    have hcancel : (piTele W (b.instantiate1 (.fvar d ty))).abstract1 d = piTele W b := by
      rw [← piTele_instantiate1 hWi (.fvar d ty) b 0 hsh']
      exact abstract1_instantiate1_cancel ty 0 (piTele_fvarsBelow (hWf d) b hf'.2)
        (piTele_looseBVarsBounded hWb b (0 + 1) hb'.2)
    rw [hcancel] at hlam
    rw [lamTele_forallE, piTele_forallE]
    exact hlam

/-- **The `∀`-telescope over `W` converts to the telescope it was taken from**, where `W`
converts to every application the telescope can end in. -/
theorem defEq_piTele {env : Env .anon} {W : Expr .anon} {T : Key .anon} {us : List Level}
    {nT : Nat} (hWi : ∀ x k, W.instantiate1 x k = W)
    (hbase : ∀ (d : Nat) (e : Expr .anon), e.getAppFn = .const T us →
      e.getAppArgs.length = nT → DefEq env d W e) :
    ∀ (n : Nat) (e : Expr .anon) (d : Nat), e.piArity = n → EndsHead T us nT e →
      DefEq env d (piTele W e) e
  | 0, e, d, hn, he => by
    obtain ⟨h1, h2⟩ := he.base hn
    rw [piTele_of_piArity_zero W hn]
    exact hbase d e h1 h2
  | n + 1, e, d, hn, he => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    have he' : EndsHead T us nT b := he
    have hsh' : Shape b := EndsHead.shape b he'
    rw [piTele_forallE]
    refine DefEq.forallE DefEq.refl ?_ rfl
    rw [piTele_instantiate1 hWi (.fvar d ty) b 0 hsh']
    exact defEq_piTele hWi hbase n (b.instantiate1 (.fvar d ty)) (d + 1)
      (by rw [piArity_instantiate1 _ b 0 hsh']; exact hn')
      (EndsHead.instantiate1 _ b 0 he')

/-- Reduction of the head of an application spine. -/
theorem red_mkAppN {env : Env .anon} {d : Nat} :
    ∀ (args : List (Expr .anon)) {f f' : Expr .anon}, Red env d f f' →
      Red env d (Expr.mkAppN f args) (Expr.mkAppN f' args)
  | [], _, _, h => h
  | a :: as, _, _, h => red_mkAppN as (Red.appFn (a := a) h)

/-- **A `λ`-telescope at binders whose datum is `never`, applied to as many arguments as it
has binders, reduces to its end** (β at a fired gate: no certificate). -/
theorem red_lamTele_apply {env : Env .anon} {d : Nat} {w : Expr .anon}
    (hwi : ∀ x k, w.instantiate1 x k = w) {l : Level} :
    ∀ (args : List (Expr .anon)) (e : Expr .anon), e.piArity = args.length →
      e.resultSort = some l → PwAll PropWhen.never e →
      Red env d (Expr.mkAppN (lamTele w e) args) w
  | [], e, hn, _, _ => by
    rw [lamTele_of_piArity_zero w hn]
    exact Red.refl
  | a :: as, e, hn, hr, hp => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    have hr' : b.resultSort = some l := hr
    have hsh' : Shape b := shape_of_resultSort b l hr'
    have hp' : m.pw = PropWhen.never ∧ PwAll PropWhen.never b := hp
    have hgate : m.pw.isNever = true := by
      rw [hp'.1]; exact PropWhen.isNever_never
    have hstep : Red env d (Expr.mkAppN (.app (.lam ty (lamTele w b) m) a) as)
        (Expr.mkAppN ((lamTele w b).instantiate1 a) as) :=
      red_mkAppN as (Red.betaGate hgate)
    rw [lamTele_instantiate1 hwi a b 0 hsh'] at hstep
    have hrest : Red env d (Expr.mkAppN (lamTele w (b.instantiate1 a)) as) w :=
      red_lamTele_apply hwi as (b.instantiate1 a)
      (by rw [piArity_instantiate1 a b 0 hsh']; exact hn')
      (resultSort_instantiate1 a b 0 l hr') (PwAll.instantiate1 a b 0 hsh' hp'.2)
    exact Red.trans hstep hrest

/-- **Where a former is stored as the `PUnit`-valued definition over its own type, an
application of it to as many arguments as it has binders reduces to `PUnit`** at the level its
type ends in, instantiated at the use's levels: δ, then β at the binders of a telescope into a
sort, whose data are all `never`. -/
theorem red_shadow_apply {env : Env .anon} {d : Nat} {T : Key .anon} {cv : ConstantVal .anon}
    {hint : ReducibilityHint} {l : Level} {us : List Level} {e : Expr .anon}
    (hf : env.find? T =
      some (.defnInfo cv (lamTele (.const Ix.Kernel.punitName [l]) cv.type) hint))
    (hr : cv.type.resultSort = some l) (hp : PwAll PropWhen.never cv.type)
    (hus : us.length = cv.levelParams.length)
    (hhead : e.getAppFn = .const T us) (hargs : e.getAppArgs.length = cv.type.piArity) :
    Red env d e (.const Ix.Kernel.punitName [Level.subst cv.levelParams us l]) := by
  have hunf : Ix.Kernel.unfoldDefinition env e = some (Expr.mkAppN
      ((lamTele (.const Ix.Kernel.punitName [l]) cv.type).instantiateLevelParams
        cv.levelParams us) e.getAppArgs) := by
    simp only [Ix.Kernel.unfoldDefinition, hhead, hf, hus, ↓reduceIte]
  have hsh : Shape cv.type := shape_of_resultSort _ l hr
  rw [lamTele_instantiateLevelParams _ _ _ _ hsh] at hunf
  have hbeta := red_lamTele_apply (env := env) (d := d)
    (w := (Expr.const Ix.Kernel.punitName [l]).instantiateLevelParams cv.levelParams us)
    (fun _ _ => rfl) (l := Level.subst cv.levelParams us l) e.getAppArgs
    (cv.type.instantiateLevelParams cv.levelParams us)
    (by rw [piArity_instantiateLevelParams]; exact hargs.symm)
    (resultSort_instantiateLevelParams _ _ _ l hr)
    (by
      have := PwAll.instantiateLevelParams cv.levelParams us cv.type hp
      rwa [Ix.Kernel.Level.substPW_never] at this)
  exact Red.trans (Red.delta hunf) hbeta

/-- **The type of an application of a constant to its arguments**, by inversion along the
spine: at a constant whose stored type is a telescope of `n` binders into `Sort l`, the type of
an application to `k ≤ n` arguments is a telescope of `n - k` binders into the sort at the
use's levels. -/
theorem infer_spine {env : Env .anon} {d : Nat} {T : Key .anon} {us : List Level}
    {ci : ConstantInfo .anon} {l : Level}
    (hf : env.find? T = some ci) (hr : ci.toConstantVal.type.resultSort = some l) :
    ∀ (e : Expr .anon) (s : Expr .anon), Infer env .full d e s → e.getAppFn = .const T us →
      e.getAppArgs.length ≤ ci.toConstantVal.type.piArity →
      us.length = ci.toConstantVal.levelParams.length ∧
      s.resultSort = some (Level.subst ci.toConstantVal.levelParams us l) ∧
      s.piArity = ci.toConstantVal.type.piArity - e.getAppArgs.length := by
  intro e
  induction e with
  | const c cs =>
    intro s h hh _
    obtain ⟨rfl, rfl⟩ := Expr.const.inj hh
    obtain ⟨ci', hf', -, hlen, rfl⟩ := Infer.const_inv h
    obtain rfl : ci' = ci := Option.some.inj (hf'.symm.trans hf)
    refine ⟨hlen, resultSort_instantiateLevelParams _ _ _ l hr, ?_⟩
    rw [piArity_instantiateLevelParams]
    rfl
  | app f a ihf _ =>
    intro s h hh hle
    have hhf : f.getAppFn = .const T us := hh
    have hargs : (Expr.app f a).getAppArgs.length = f.getAppArgs.length + 1 := by
      simp [Expr.getAppArgs]
    obtain ⟨tf, ty, body, mt, ta, htf, hred, -, -, rfl⟩ := Infer.app_inv h
    obtain ⟨hlen, hrs, hpa⟩ := ihf tf htf hhf (by omega)
    have hpos : tf.piArity = (ci.toConstantVal.type.piArity - f.getAppArgs.length - 1) + 1 := by
      omega
    obtain ⟨ty0, b0, m0, rfl, hb0⟩ := exists_forallE_of_piArity_succ hpos
    have hrig := Red.rigid hred rfl
    have hbody : body = b0 := (Expr.forallE.inj hrig).2.1
    rw [hbody]
    have hrs' : b0.resultSort = some (Level.subst ci.toConstantVal.levelParams us l) := hrs
    refine ⟨hlen, resultSort_instantiate1 a b0 0 _ hrs', ?_⟩
    rw [piArity_instantiate1 a b0 0 (shape_of_resultSort b0 _ hrs'), hb0, hargs]
    omega
  | _ => intro s h hh; exact nomatch hh

/-- **The sort of a typed telescope ending in a fully applied former** has the zero-ness of
the level the former's type ends in, at the use's levels; and the use's levels are as many as
the former's parameters. -/
theorem sort_of_endsHead {env : Env .anon} {T : Key .anon} {us : List Level}
    {ci : ConstantInfo .anon} {l : Level}
    (hf : env.find? T = some ci) (hr : ci.toConstantVal.type.resultSort = some l) :
    ∀ (n : Nat) (e : Expr .anon) (d : Nat) (s : Expr .anon) (v : Level), e.piArity = n →
      EndsHead T us ci.toConstantVal.type.piArity e →
      Infer env .full d e s → Red env d s (.sort v) →
      us.length = ci.toConstantVal.levelParams.length ∧
      Level.zeronessOf v =
        Level.zeronessOf (Level.subst ci.toConstantVal.levelParams us l)
  | 0, e, d, s, v, hn, he, h, hs => by
    obtain ⟨h1, h2⟩ := he.base hn
    obtain ⟨hlen, hrs, hpa⟩ := infer_spine hf hr e s h h1 (Nat.le_of_eq h2)
    have hs0 : s.piArity = 0 := by rw [hpa, h2]; exact Nat.sub_self _
    obtain rfl := eq_sort_of_resultSort hs0 hrs
    obtain rfl := Red.sort_eq hs
    exact ⟨hlen, rfl⟩
  | n + 1, e, d, s, v, hn, he, h, hs => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    have he' : EndsHead T us ci.toConstantVal.type.piArity b := he
    have hsh' : Shape b := EndsHead.shape b he'
    obtain ⟨s1, u, bs, v1, -, -, hb, hv1, -, rfl⟩ := Infer.forallE_inv h
    obtain rfl : v = .imax u v1 := Red.sort_eq hs
    exact sort_of_endsHead hf hr n (b.instantiate1 (.fvar d ty)) (d + 1) bs v1
      (by rw [piArity_instantiate1 _ b 0 hsh']; exact hn')
      (EndsHead.instantiate1 _ b 0 he') hb hv1

/-- A telescope into `Sort l` is its own `∀`-telescope over `Sort l`. -/
theorem piTele_sort_self :
    ∀ (e : Expr .anon) (l : Level), e.resultSort = some l → piTele (.sort l) e = e
  | .forallE ty b m, l, h => by
    rw [piTele_forallE, piTele_sort_self b l h]
  | .sort u, l, h => by
    obtain rfl : u = l := Option.some.inj h
    rfl
  | .bvar _, _, h | .fvar _ _, _, h | .const _ _, _, h | .app _ _, _, h | .lam _ _ _, _, h
  | .letE _ _ _ _, _, h | .lit _, _, h | .proj _ _ _, _, h => nomatch h

/-- **The sort of a typed telescope into a sort is never zero.** -/
theorem sort_of_resultSort {env : Env .anon} {l : Level} :
    ∀ (n : Nat) (e : Expr .anon) (d : Nat) (s : Expr .anon) (v : Level), e.piArity = n →
      e.resultSort = some l → Infer env .full d e s → Red env d s (.sort v) →
      Level.zeronessOf v = PropWhen.never
  | 0, e, d, s, v, hn, hr, h, hs => by
    obtain rfl := eq_sort_of_resultSort hn hr
    obtain rfl := Infer.sort_inv h
    obtain rfl := Red.sort_eq hs
    rfl
  | n + 1, e, d, s, v, hn, hr, h, hs => by
    obtain ⟨ty, b, m, rfl, hn'⟩ := exists_forallE_of_piArity_succ hn
    have hr' : b.resultSort = some l := hr
    have hsh' : Shape b := shape_of_resultSort b l hr'
    obtain ⟨s1, u, bs, v1, -, -, hb, hv1, -, rfl⟩ := Infer.forallE_inv h
    obtain rfl : v = .imax u v1 := Red.sort_eq hs
    exact sort_of_resultSort n (b.instantiate1 (.fvar d ty)) (d + 1) bs v1
      (by rw [piArity_instantiate1 _ b 0 hsh']; exact hn')
      (resultSort_instantiate1 _ b 0 l hr') hb hv1

end IxVM.Refinement.Decl.Point
