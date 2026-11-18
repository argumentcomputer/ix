import IxVMRefinement.FamilyAlias.RuleCopy
import IxVMRefinement.Decl.ModeledRules
import IxC.Kernel.Verify.Close
import IxC.Kernel.Verify.Subst
import IxC.Kernel.Verify.Abstract
import IxC.Kernel.Verify.Denote.TeleOpen
import IxC.Kernel.Model.Iota

/-! # Opening a telescope, and closing it again

A statement is given to the family step opened: its binders replaced by variables, as IxC's
rule record reads it. A copy of the statement is a closed term. This module has what passes
between the two forms.

* `OpenVars d fvs`: the variables an opening at depth `d` introduces, the `j`-th at index
  `d + j`.
* `closeN_instSeq_openVars`, `closeN_instSeq_closed`: instantiating a body at such variables
  and closing them again gives the body back. So instantiation at the variables of an opening
  is injective on terms without free variables.
* `SameTele n a a'`, `openPisAtFvars_sameTele`: two terms with the same first `n` binder
  domains open at the same variables.
* small facts about lists and renamings used with them: `dropLast_append_getLastD`,
  `getLastD_map`, `map_dropLast_eq`, `eq_three_of_length`,
  `renameConsts_eq_self_of_constsResolve`, `renameConsts_liftLooseBVars`. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key Level LevelParam BinderMeta openPisAtFvars)

set_option linter.unusedVariables false

/-! ## Lists -/

/-- A non-empty list is its initial segment followed by its last element. -/
theorem dropLast_append_getLastD {α : Type} : ∀ (l : List α) (d : α), l ≠ [] →
    l.dropLast ++ [l.getLastD d] = l
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | a :: b :: l, d, _ => by
    have ih := dropLast_append_getLastD (b :: l) d (List.cons_ne_nil _ _)
    show a :: ((b :: l).dropLast ++ [(b :: l).getLastD d]) = a :: b :: l
    rw [ih]

/-- The last element of a mapped non-empty list. -/
theorem getLastD_map {α β : Type} (f : α → β) (d₁ : β) (d₂ : α) :
    ∀ (l : List α), l ≠ [] → (l.map f).getLastD d₁ = f (l.getLastD d₂)
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: b :: l, _ => getLastD_map f d₁ d₂ (b :: l) (List.cons_ne_nil _ _)

/-- The initial segment of a mapped list. -/
theorem map_dropLast_eq {α β : Type} (f : α → β) :
    ∀ (l : List α), l.dropLast.map f = (l.map f).dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    have ih := map_dropLast_eq f (b :: l)
    show f a :: (b :: l).dropLast.map f = f a :: ((b :: l).map f).dropLast
    rw [ih]

/-- A list of three elements. -/
theorem eq_three_of_length {α : Type} (d : α) (l : List α) (h : l.length = 3) :
    l = [l.getD 0 d, l.getD 1 d, l.getD 2 d] := by
  match l, h with
  | [a, b, c], _ => rfl
  | [], h => exact absurd h (by simp)
  | [_], h => exact absurd h (by simp)
  | [_, _], h => exact absurd h (by simp)
  | _ :: _ :: _ :: _ :: l, h =>
    exact absurd h (by simp only [List.length_cons] <;> omega)

/-! ## Renamings -/

/-- **A renaming that fixes what an environment stores fixes a term that resolves in it.** -/
theorem renameConsts_eq_self_of_constsResolve {env : Env .anon} {h : KKey → KKey}
    (hfix : ∀ k, (env.find? k).isSome = true → h k = k) :
    ∀ e : KExpr, e.constsResolve env = true → e.renameConsts h = e := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | const n _ =>
    intro hr
    have hn : h n = n := hfix n hr
    simp only [Expr.renameConsts, hn]
  | fvar _ _ ih =>
    intro hr
    simp only [Expr.renameConsts, ih hr]
  | app _ _ ihf iha =>
    intro hr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, ihf hr.1, iha hr.2]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro hr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, iht hr.1, ihb hr.2]
  | letE _ _ _ _ iht ihv ihb =>
    intro hr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, iht hr.1.1, ihv hr.1.2, ihb hr.2]
  | proj _ _ _ ihe =>
    intro hr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, ihe hr.2]

/-- Renaming constants commutes with lifting loose bound variables. -/
theorem renameConsts_liftLooseBVars (h : KKey → KKey) (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars n c).renameConsts h = (e.renameConsts h).liftLooseBVars n c := by
  intro e
  induction e with
  | bvar i =>
    intro c
    by_cases hic : i ≥ c <;> simp [Expr.liftLooseBVars, Expr.renameConsts, hic]
  | fvar _ _ _ => intro c; rfl
  | sort _ | const _ _ | lit _ => intro c; rfl
  | app _ _ ihf iha =>
    intro c
    simp only [Expr.liftLooseBVars, Expr.renameConsts, ihf, iha]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro c
    simp only [Expr.liftLooseBVars, Expr.renameConsts, iht, ihb]
  | letE _ _ _ _ iht ihv ihb =>
    intro c
    simp only [Expr.liftLooseBVars, Expr.renameConsts, iht, ihv, ihb]
  | proj _ _ _ ihe =>
    intro c
    simp only [Expr.liftLooseBVars, Expr.renameConsts, ihe]

/-! ## Applications -/

/-- Closing commutes with an application spine. -/
theorem closeN_mkAppN (d k : Nat) : ∀ (xs : List KExpr) (f : KExpr),
    Expr.closeN d (Expr.mkAppN f xs) k =
      Expr.mkAppN (Expr.closeN d f k) (xs.map fun x => Expr.closeN d x k)
  | [], _ => rfl
  | x :: xs, f => closeN_mkAppN d k xs (.app f x)

/-- An application spine of terms without free variables has none. -/
theorem hasFvar_mkAppN : ∀ (xs : List KExpr) (f : KExpr), f.hasFvar = false →
    (∀ x ∈ xs, x.hasFvar = false) → (Expr.mkAppN f xs).hasFvar = false
  | [], _, hf, _ => hf
  | x :: xs, f, hf, hx =>
    hasFvar_mkAppN xs (.app f x)
      (by simp [Expr.hasFvar, hf, hx x List.mem_cons_self])
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

/-- An application spine of terms with loose bound variables below `b` has them below `b`. -/
theorem looseBVarsBounded_mkAppN (b : Nat) : ∀ (xs : List KExpr) (f : KExpr),
    f.looseBVarsBounded b = true → (∀ x ∈ xs, x.looseBVarsBounded b = true) →
    (Expr.mkAppN f xs).looseBVarsBounded b = true
  | [], _, hf, _ => hf
  | x :: xs, f, hf, hx =>
    looseBVarsBounded_mkAppN b xs (.app f x)
      (by simp [Expr.looseBVarsBounded, hf, hx x List.mem_cons_self])
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

/-! ## The variables of an opening -/

/-- **The variables an opening at depth `d` introduces**: the `j`-th is the variable `d + j`,
with some annotation. -/
def OpenVars : Nat → List KExpr → Prop
  | _, [] => True
  | d, x :: rest => (∃ ty, x = Expr.fvar d ty) ∧ OpenVars (d + 1) rest

theorem openVars_of_getElem : ∀ (fvs : List KExpr) (d : Nat),
    (∀ k (hk : k < fvs.length), ∃ ty, fvs[k] = Expr.fvar (d + k) ty) → OpenVars d fvs
  | [], _, _ => trivial
  | x :: rest, d, h => by
    refine ⟨?_, openVars_of_getElem rest (d + 1) (fun k hk => ?_)⟩
    · obtain ⟨ty, hty⟩ := h 0 (Nat.succ_pos _)
      exact ⟨ty, hty⟩
    · obtain ⟨ty, hty⟩ := h (k + 1) (Nat.succ_lt_succ hk)
      refine ⟨ty, ?_⟩
      have h2 : rest[k] = Expr.fvar (d + (k + 1)) ty := hty
      rw [h2, show d + (k + 1) = d + 1 + k by omega]

/-- Each is a variable. -/
theorem OpenVars.fvars : ∀ {fvs : List KExpr} {d : Nat}, OpenVars d fvs →
    ∀ a ∈ fvs, ∃ (i : Nat) (ty : KExpr), a = Expr.fvar i ty
  | [], _, _, _, ha => nomatch ha
  | x :: rest, d, hv, a, ha => by
    obtain ⟨⟨ty, hx⟩, hrest⟩ := hv
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨d, ty, hx⟩
    · exact OpenVars.fvars hrest a ha

/-- Each has no loose bound variable. -/
theorem OpenVars.bounded {fvs : List KExpr} {d : Nat} (hv : OpenVars d fvs) :
    ∀ a ∈ fvs, a.looseBVarsBounded 0 = true := by
  intro a ha
  obtain ⟨i, ty, rfl⟩ := hv.fvars a ha
  rfl

/-- **Instantiating a body at the variables of an opening and closing them again** is closing
the body under its binders. -/
theorem closeN_instSeq_openVars : ∀ (fvs : List KExpr) (d : Nat) (b : KExpr),
    OpenVars d fvs → b.looseBVarsBounded fvs.length = true → Expr.fvarsBelow d b →
    Expr.closeN (d + fvs.length) (Expr.instSeq fvs (fvs.length - 1) b) 0 =
      Expr.closeN d b fvs.length
  | [], _, _, _, _, _ => rfl
  | x :: rest, d, b, hv, hb, hf => by
    obtain ⟨⟨ty, rfl⟩, hrest⟩ := hv
    have hb' : b.looseBVarsBounded (rest.length + 1) = true := hb
    show Expr.closeN (d + (rest.length + 1))
        (Expr.instSeq rest (rest.length + 1 - 1 - 1)
          (b.instantiate1 (.fvar d ty) (rest.length + 1 - 1))) 0 =
      Expr.closeN d b (rest.length + 1)
    rw [show rest.length + 1 - 1 = rest.length by omega,
      show d + (rest.length + 1) = d + 1 + rest.length by omega,
      closeN_instSeq_openVars rest (d + 1) (b.instantiate1 (.fvar d ty) rest.length) hrest
        (Ix.Kernel.looseBVarsBounded_instantiate1 (d := d) (ty := ty) b rest.length hb')
        (Ix.Kernel.Expr.fvarsBelow_instantiate1 (ty := ty) rest.length hf),
      Ix.Kernel.Expr.closeN_instantiate1 (ty := ty) b rest.length hb' hf]

/-- **A body without free variables is recovered from its instantiation at the variables of
an opening.** -/
theorem closeN_instSeq_closed {fvs : List KExpr} (hv : OpenVars 0 fvs) {b : KExpr}
    (hf : b.hasFvar = false) (hb : b.looseBVarsBounded fvs.length = true) :
    Expr.closeN fvs.length (Expr.instSeq fvs (fvs.length - 1) b) 0 = b := by
  have h := closeN_instSeq_openVars fvs 0 b hv hb (Ix.Kernel.fvarsBelow_zero_of_hasFvar_false hf)
  rw [Nat.zero_add] at h
  exact h.trans (Ix.Kernel.Expr.closeN_of_hasFvar b 0 fvs.length hf)

/-! ## Telescopes with the same domains -/

/-- **Two terms with the same first `n` binder domains.** -/
inductive SameTele : Nat → KExpr → KExpr → Prop where
  | zero (a a' : KExpr) : SameTele 0 a a'
  | succ {n : Nat} {ty b b' : KExpr} {m m' : BinderMeta} :
      SameTele n b b' → SameTele (n + 1) (.forallE ty b m) (.forallE ty b' m')

theorem SameTele.instantiate1 (x : KExpr) {n : Nat} {a a' : KExpr} (h : SameTele n a a') :
    ∀ k : Nat, SameTele n (a.instantiate1 x k) (a'.instantiate1 x k) := by
  induction h with
  | zero a a' => intro k; exact SameTele.zero _ _
  | succ _ ih =>
    intro k
    simp only [Expr.instantiate1]
    exact SameTele.succ (ih (k + 1))

/-- **Two terms with the same first `n` binder domains open at the same variables.** -/
theorem openPisAtFvars_sameTele : ∀ (n : Nat) {a a' : KExpr} (d : Nat) {fvs : List KExpr}
    {body : KExpr}, SameTele n a a' → openPisAtFvars n a d = some (fvs, body) →
    ∃ body', openPisAtFvars n a' d = some (fvs, body') := by
  intro n
  induction n with
  | zero =>
    intro a a' d fvs body _ ho
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, -⟩ := ho
    exact ⟨a', rfl⟩
  | succ n ih =>
    intro a a' d fvs body h ho
    cases h with
    | @succ _ ty b b' m m' hbb' =>
      simp only [openPisAtFvars] at ho
      cases hop : openPisAtFvars n (b.instantiate1 (.fvar d ty)) (d + 1) with
      | none => rw [hop] at ho; exact nomatch ho
      | some p =>
        rw [hop] at ho
        simp only [Option.some.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        obtain ⟨body', hb'⟩ := ih (d + 1) (hbb'.instantiate1 (.fvar d ty) 0) hop
        refine ⟨body', ?_⟩
        simp only [openPisAtFvars, hb']

end IxVM.Refinement.Decl.FamilyAlias
