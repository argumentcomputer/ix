import IxVMRefinement.Decl.NativeFormerRestore
import IxC.Kernel.Model.Open.Core

/-! # Restoring declared native formers through actual definition unfolding

A stored definition determines the reading of its instantiated body. This lets a table-free
former's normalized type be replaced by its original constant-headed expression, including
universe instantiations and argument spines, without changing the valuation.
-/

namespace IxVM.Refinement.Decl.NativeFormerRestore

open Ix.Kernel

universe u

variable {md : Mode} {V : Type u} [SetTheory V] {env : Env md}

/-- Replacing a spine's head by a term with the same readings preserves its readings and grading. -/
private theorem replace_head {cval : Key md → (LevelParam → Nat) → V}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} :
    ∀ (args : List (Expr md)) {f g : Expr md},
      (∀ value, Denotes cval env φ ρ f value → Denotes cval env φ ρ g value) →
      (GradedBy (Denotes cval env φ) ρ f → GradedBy (Denotes cval env φ) ρ g) →
      (∀ value, Denotes cval env φ ρ (Expr.mkAppN f args) value →
        Denotes cval env φ ρ (Expr.mkAppN g args) value) ∧
      (GradedBy (Denotes cval env φ) ρ (Expr.mkAppN f args) →
        GradedBy (Denotes cval env φ) ρ (Expr.mkAppN g args)) := by
  intro args
  induction args with
  | nil => intro f g readings grading; exact ⟨readings, grading⟩
  | cons arg args ih =>
    intro f g readings grading
    apply ih
    · intro value read
      cases read with
      | app hf ha => exact .app (readings _ hf) ha
    · intro graded
      simp only [GradedBy] at graded ⊢
      obtain ⟨hf, ha, regime, A, F, X, B, readF, readX, member, argument, proofValue⟩ := graded
      exact ⟨grading hf, ha, regime, A, F, X, B, readings _ readF, readX, member, argument, proofValue⟩

/-- A real definition lookup restores its original head from the instantiated checked body. -/
private theorem definition_head (M : Model V env) {name : Key md} {cv : ConstantVal md}
    {value : Expr md} {hint : ReducibilityHint} {levels : List Level}
    (found : env.find? name = some (.defnInfo cv value hint))
    (arity : levels.length = cv.levelParams.length) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    {result : V} (read : Denotes M.cval env φ ρ (value.instantiateLevelParams cv.levelParams levels) result) :
    Denotes M.cval env φ ρ (.const name levels) result := by
  have nameEq : cv.name = name := Ix.Kernel.Open.find?_name found
  have bodyRead := M.defn_value cv value hint (List.mem_of_find?_eq_some found)
    (Level.substFn φ cv.levelParams levels) ρ
  have instantiated := (DenotesO.instantiateLevelParams (σ := ρ) M.cval_params
    cv.levelParams levels value ρ _).2 (DenotesO.of_denotes bodyRead)
  have same := DenotesO.functional (DenotesO.of_denotes (σ := ρ) read) instantiated
  rw [same, nameEq]
  exact Denotes.const found arity

/-- Pull both the reading and grading back through the actual definition unfolding operation. -/
theorem unfolding_reads (M : Model V env) {declared checked : Expr md}
    (unfolded : unfoldDefinition env declared = some checked)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    (∀ value, Denotes M.cval env φ ρ checked value → Denotes M.cval env φ ρ declared value) ∧
      (GradedBy (Denotes M.cval env φ) ρ checked →
        GradedBy (Denotes M.cval env φ) ρ declared) := by
  obtain ⟨name, levels, cv, value, hint, head, found, arity, rfl⟩ :=
    Ix.Kernel.Open.unfoldDefinition_inv unfolded
  have replaced := replace_head declared.getAppArgs
    (fun _ read => definition_head M found arity φ ρ read)
    (fun _ => True.intro)
  rw [← head, Expr.mkAppN_getApp] at replaced
  exact replaced

/-- Actual delta normalization supplies the replacement reading and grading required by the model. -/
def unfoldingModel (cv : ConstantVal md) (caps : IndCaps md) (declared : Expr md)
    (M : Model V env) (stored : .indInfo cv caps ∈ env.consts)
    (notEta : caps.eta = false) (notUnit : caps.unitlike = false)
    (noTable : ∀ i, env.findProj? cv.name i = none)
    (unfolded : unfoldDefinition env declared = some cv.type) :
    Model V (environment cv caps declared env) :=
  model cv caps declared M notEta notUnit noTable
    (fun φ ρ => (unfolding_reads M unfolded φ ρ).1)
    (fun φ ρ => (unfolding_reads M unfolded φ ρ).2 (M.graded (.indInfo cv caps) stored φ ρ).1)

end IxVM.Refinement.Decl.NativeFormerRestore
