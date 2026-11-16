import IxVMRefinement.Decl.NativeConstructorOrigin

/-! # The constructor result head retained by the actual rebuild

Opening at free variables and closing those variables preserve an application's constant
head, its level arguments, and its argument count. Field normalization changes domains;
the result expression is only opened and reclosed. Its retained shape is therefore an
actual computation fact, independent of annotation or conversion assumptions.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- The constant head and argument count visible at an expression's application spine. -/
def applicationShape {md : Mode} : Expr md → Option (Key md × List Level) × Nat
  | .const name levels => (some (name, levels), 0)
  | .app fn _ => ((applicationShape fn).1, (applicationShape fn).2 + 1)
  | _ => (none, 0)

theorem applicationShape_eq {md : Mode} (e : Expr md) :
    applicationShape e =
      ((match e.getAppFn with | .const name levels => some (name, levels) | _ => none),
        e.getAppArgs.length) := by
  induction e with
  | app fn argument ih _ =>
    simp only [applicationShape, Expr.getAppFn, Expr.getAppArgs, List.length_append, List.length_singleton, ih]
  | _ => rfl

private theorem applicationShape_instantiate {md : Mode} (index : Nat) (type : Expr md) :
    ∀ (e : Expr md) (cut : Nat), applicationShape (e.instantiate1 (.fvar index type) cut) = applicationShape e
  | .bvar _, _ => by simp only [Expr.instantiate1]; split <;> first | rfl | (split <;> rfl)
  | .app fn argument, cut => by
    simp only [Expr.instantiate1, applicationShape, applicationShape_instantiate index type fn cut]
  | .fvar .., _ | .sort .., _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit .., _ | .proj .., _ => rfl

private theorem applicationShape_abstract {md : Mode} (index : Nat) :
    ∀ (e : Expr md) (cut : Nat), applicationShape (e.abstract1 index cut) = applicationShape e
  | .fvar .., _ => by simp only [Expr.abstract1]; split <;> rfl
  | .app fn argument, cut => by
    simp only [Expr.abstract1, applicationShape, applicationShape_abstract index fn cut]
  | .bvar .., _ | .sort .., _ | .const .., _ | .lam .., _ | .forallE .., _
  | .letE .., _ | .lit .., _ | .proj .., _ => rfl

/-- The result head after a specified number of syntactic product binders. -/
def telescopeTailShape {md : Mode} : Nat → Expr md → Option (Option (Key md × List Level) × Nat)
  | 0, e => some (applicationShape e)
  | count + 1, .forallE _ body _ => telescopeTailShape count body
  | _ + 1, _ => none

private theorem telescopeTailShape_instantiate {md : Mode} (index : Nat) (type : Expr md) :
    ∀ (count : Nat) (e : Expr md) (cut : Nat),
      telescopeTailShape count (e.instantiate1 (.fvar index type) cut) = telescopeTailShape count e
  | 0, e, cut => by simp only [telescopeTailShape, applicationShape_instantiate]
  | count + 1, e, cut => by
    cases e with
    | forallE _ body _ =>
      simp only [Expr.instantiate1, telescopeTailShape]
      exact telescopeTailShape_instantiate index type count body (cut + 1)
    | bvar _ => simp only [Expr.instantiate1]; split <;> first | rfl | (split <;> rfl)
    | _ => rfl

private theorem telescopeTailShape_abstract {md : Mode} (index : Nat) :
    ∀ (count : Nat) (e : Expr md) (cut : Nat),
      telescopeTailShape count (e.abstract1 index cut) = telescopeTailShape count e
  | 0, e, cut => by simp only [telescopeTailShape, applicationShape_abstract]
  | count + 1, e, cut => by
    cases e with
    | forallE _ body _ =>
      simp only [Expr.abstract1, telescopeTailShape]
      exact telescopeTailShape_abstract index count body (cut + 1)
    | fvar _ _ => simp only [Expr.abstract1]; split <;> rfl
    | _ => rfl

private theorem opened_tailShape {md : Mode} :
    ∀ {count depth : Nat} {e body : Expr md} {fvars : List (Expr md)},
      openPisAtFvars count e depth = some (fvars, body) → ∀ rest,
        telescopeTailShape (count + rest) e = telescopeTailShape rest body
  | 0, _, _, _, _, opened, rest => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    simp only [Nat.zero_add]
  | count + 1, depth, e, _, _, opened, rest => by
    cases e with
    | forallE domain body bm =>
      simp only [openPisAtFvars] at opened
      cases next : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
      | none => rw [next] at opened; cases opened
      | some pair =>
        obtain ⟨vars, output⟩ := pair
        rw [next] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        have tail := opened_tailShape next rest
        rw [telescopeTailShape_instantiate] at tail
        simpa only [Nat.succ_add, telescopeTailShape] using tail
    | _ => cases opened

private theorem normalized_fields_tailShape {md : Mode} {env : Env md} {fuel : Nat} {T : Key md} :
    ∀ {count depth : Nat} {e residual : Expr md} {binders : List (Expr md × BinderMeta)},
      normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (binders, residual) →
      binders.length = count ∧ telescopeTailShape count e = some (applicationShape residual)
  | 0, _, _, _, _, run => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨rfl, rfl⟩
  | count + 1, depth, e, _, _, run => by
    cases e with
    | forallE domain body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨_, _, rest⟩ := exceptBind_ok run
      obtain ⟨⟨fields, residual⟩, recursive, result⟩ := exceptBind_ok rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
      obtain ⟨length, tail⟩ := normalized_fields_tailShape recursive
      rw [telescopeTailShape_instantiate] at tail
      exact ⟨by simp only [List.length_cons, length], tail⟩
    | _ => cases run

private theorem reclosed_tailShape {md : Mode} :
    ∀ (binders : List (Expr md × BinderMeta)) (depth : Nat) (body : Expr md),
      telescopeTailShape binders.length (closeTelescope binders depth body) = some (applicationShape body)
  | [], _, _ => rfl
  | (_, _) :: binders, depth, body => by
    simp only [closeTelescope, List.length_cons, telescopeTailShape, telescopeTailShape_abstract]
    exact reclosed_tailShape binders (depth + 1) body

/-- The exact rebuild retains the constructor result's constant head, level arguments, and arity. -/
theorem ConstructorRebuildRun.tailShape {md : Mode} {env : Env md} {fuel nP nF : Nat} {T : Key md}
    {initial rebuilt : Expr md} (rebuild : ConstructorRebuildRun env fuel T nP nF initial rebuilt) :
    telescopeTailShape (nP + nF) rebuilt = telescopeTailShape (nP + nF) initial := by
  obtain ⟨parameters, _, parameterVars, openedBody, fields, residual, stripped, opened, normalized, rfl⟩ := rebuild
  have originalTail := opened_tailShape opened nF
  obtain ⟨fieldCount, normalizedTail⟩ := normalized_fields_tailShape normalized
  rw [normalizedTail] at originalTail
  have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ opened
  have binderCount := Expr.stripPis_length _ stripped
  have reclosed := reclosed_tailShape
    (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) parameterVars parameters ++ fields)
    0 residual
  simp only [List.length_append, List.length_zipWith, parameterCount, binderCount, fieldCount, Nat.min_self] at reclosed
  exact reclosed.trans originalTail.symm

end IxVM.Refinement.Decl
