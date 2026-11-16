import IxVMRefinement.Decl.NativeConstructorTail
import IxVMRefinement.Decl.NativeFormerChecked

/-! # The constructor result shape through final reannotation

An annotation result has no let on its product/application spine. Domain normalization
preserves that fact and the result shape. The final annotation can change binder data and
normalize domains, but cannot change the constructor result's constant head or arity.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- No let occurs on the product-body or application-function spine. -/
def constructorSpineClean {md : Mode} : Expr md → Bool
  | .forallE _ body _ => constructorSpineClean body
  | .app fn _ => constructorSpineClean fn
  | .letE .. => false
  | _ => true

private theorem spineClean_instantiate {md : Mode} (index : Nat) (type : Expr md) :
    ∀ (e : Expr md) (cut : Nat),
      constructorSpineClean (e.instantiate1 (.fvar index type) cut) = constructorSpineClean e
  | .bvar _, _ => by simp only [Expr.instantiate1]; split <;> first | rfl | (split <;> rfl)
  | .app fn argument, cut => by
    simp only [Expr.instantiate1, constructorSpineClean, spineClean_instantiate index type fn cut]
  | .forallE domain body bm, cut => by
    simp only [Expr.instantiate1, constructorSpineClean, spineClean_instantiate index type body (cut + 1)]
  | .fvar .., _ | .sort .., _ | .const .., _ | .lam .., _ | .letE .., _ | .lit .., _ | .proj .., _ => rfl

private theorem spineClean_abstract {md : Mode} (index : Nat) :
    ∀ (e : Expr md) (cut : Nat), constructorSpineClean (e.abstract1 index cut) = constructorSpineClean e
  | .fvar .., _ => by simp only [Expr.abstract1]; split <;> rfl
  | .app fn argument, cut => by
    simp only [Expr.abstract1, constructorSpineClean, spineClean_abstract index fn cut]
  | .forallE domain body bm, cut => by
    simp only [Expr.abstract1, constructorSpineClean, spineClean_abstract index body (cut + 1)]
  | .bvar .., _ | .sort .., _ | .const .., _ | .lam .., _ | .letE .., _ | .lit .., _ | .proj .., _ => rfl

private theorem spineClean_opened {md : Mode} :
    ∀ {count depth : Nat} {e body : Expr md} {fvars : List (Expr md)},
      openPisAtFvars count e depth = some (fvars, body) → constructorSpineClean e = constructorSpineClean body
  | 0, _, _, _, _, opened => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    rfl
  | count + 1, depth, e, _, _, opened => by
    cases e with
    | forallE domain body bm =>
      simp only [openPisAtFvars] at opened
      cases next : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
      | none => rw [next] at opened; cases opened
      | some pair =>
        obtain ⟨vars, output⟩ := pair
        rw [next] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        have clean := spineClean_opened next
        rw [spineClean_instantiate] at clean
        exact clean
    | _ => cases opened

private theorem spineClean_normalized_fields {md : Mode} {env : Env md} {fuel : Nat} {T : Key md} :
    ∀ {count depth : Nat} {e residual : Expr md} {binders : List (Expr md × BinderMeta)},
      normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (binders, residual) →
      constructorSpineClean e = constructorSpineClean residual
  | 0, _, _, _, _, run => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    rfl
  | count + 1, depth, e, _, _, run => by
    cases e with
    | forallE domain body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨_, _, rest⟩ := exceptBind_ok run
      obtain ⟨⟨fields, residual⟩, recursive, result⟩ := exceptBind_ok rest
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
      have clean := spineClean_normalized_fields recursive
      rw [spineClean_instantiate] at clean
      exact clean
    | _ => cases run

private theorem spineClean_reclosed {md : Mode} :
    ∀ (binders : List (Expr md × BinderMeta)) (depth : Nat) (body : Expr md),
      constructorSpineClean (closeTelescope binders depth body) = constructorSpineClean body
  | [], _, _ => rfl
  | (_, _) :: binders, depth, body => by
    simp only [closeTelescope, constructorSpineClean, spineClean_abstract]
    exact spineClean_reclosed binders (depth + 1) body

/-- The actual rebuilt expression retains the original result spine's lack of lets. -/
theorem ConstructorRebuildRun.spineClean {md : Mode} {env : Env md} {fuel nP nF : Nat} {T : Key md}
    {initial rebuilt : Expr md} (rebuild : ConstructorRebuildRun env fuel T nP nF initial rebuilt) :
    constructorSpineClean rebuilt = constructorSpineClean initial := by
  obtain ⟨_, _, _, _, _, _, _, opened, normalized, rfl⟩ := rebuild
  rw [spineClean_reclosed]
  exact (spineClean_opened opened).trans (spineClean_normalized_fields normalized) |>.symm

/-- An actual annotation's result contains no let along its result spine. -/
theorem annotated_spine_clean {out input : Expr .anon} (annotation : IxVM.Consistency.Annotates out input) :
    constructorSpineClean out = true := by
  induction annotation with
  | app _ _ ih _ => exact ih
  | forallE _ _ _ ih => exact ih
  | letE _ ih => exact ih
  | _ => rfl

private theorem annotated_application_shape {out input : Expr .anon}
    (annotation : IxVM.Consistency.Annotates out input) :
    constructorSpineClean input = true → applicationShape out = applicationShape input := by
  induction annotation with
  | app _ _ ih _ =>
    intro clean
    simp only [constructorSpineClean] at clean
    simp only [applicationShape, ih clean]
  | letE => intro impossible; cases impossible
  | _ => intro _; rfl

/-- On a clean result spine, annotation preserves its constant head, levels and argument count. -/
theorem annotated_telescope_tail_shape :
    ∀ (count : Nat) {out input : Expr .anon}, IxVM.Consistency.Annotates out input →
      constructorSpineClean input = true → telescopeTailShape count out = telescopeTailShape count input
  | 0, _, _, annotation, clean => congrArg some (annotated_application_shape annotation clean)
  | count + 1, _, _, annotation, clean => by
    cases annotation with
    | forallE _ body => exact annotated_telescope_tail_shape count body clean
    | letE => cases clean
    | _ => rfl

/-- The first and final successful checks have the same constructor result head, level arguments,
and arity, even when normalization changed dependent field domains and annotation metadata. -/
theorem normCtorVal_result_shape {env : Env .anon} {fuel nP nF : Nat} {T : Key .anon}
    {raw initial checked : ConstantVal .anon}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked) :
    telescopeTailShape (nP + nF) checked.type = telescopeTailShape (nP + nF) initial.type := by
  obtain ⟨rebuilt, rebuild, same | checkedAgain⟩ := normCtorVal_rebuild_trace normalized
  · rw [same]
  · have firstShape := NativeFormerRestore.initiallyStored first
    have originalClean := annotated_spine_clean firstShape.2.2
    have rebuiltClean : constructorSpineClean rebuilt = true := by rw [rebuild.spineClean, originalClean]
    have finalShape := NativeFormerRestore.initiallyStored checkedAgain
    exact (annotated_telescope_tail_shape (nP + nF) finalShape.2.2 rebuiltClean).trans rebuild.tailShape

end IxVM.Refinement.Decl
