import IxVMRefinement.Decl.NativeConstructorConversion
import IxVMRefinement.Decl.NativeConstructorSemantics
import IxVMRefinement.Decl.TelescopeConversionFrames

/-! # Complete dependent constructor frames at the recorded rebuild

The same actual rebuild trace supplies both conversion and graded readings. Their telescope
prefixes therefore have equivalent dependent contexts and fitting value spines, including
all original parameters and normalized fields. Final reannotation is a later operation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame)

universe u

private theorem stripPis_abstract1_shape {md : Mode} :
    ∀ (count : Nat) (e : Expr md) (depth cut : Nat),
      (e.stripPis count).isSome = true → ((e.abstract1 depth cut).stripPis count).isSome = true
  | 0, _, _, _, _ => rfl
  | count + 1, e, depth, cut, shape => by
    cases e with
    | forallE domain body bm =>
      simp only [Expr.stripPis, Option.isSome_map] at shape
      simp only [Expr.abstract1, Expr.stripPis, Option.isSome_map]
      exact stripPis_abstract1_shape count body depth (cut + 1) shape
    | _ => cases shape

private theorem closeTelescope_shape {md : Mode} :
    ∀ (binders : List (Expr md × BinderMeta)) (depth : Nat) (body : Expr md),
      ((closeTelescope binders depth body).stripPis binders.length).isSome = true
  | [], _, _ => rfl
  | (_, _) :: binders, depth, body => by
    simp only [closeTelescope, List.length_cons, Expr.stripPis, Option.isSome_map]
    exact stripPis_abstract1_shape _ _ _ _ (closeTelescope_shape binders (depth + 1) body)

/-- The actual rebuild preserves the complete parameter-and-field telescope length. -/
theorem ConstructorRebuildRun.telescopes {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel nP nF : Nat} {T : Key md} {raw initial : ConstantVal md} {rebuilt : Expr md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (rebuild : ConstructorRebuildRun env fuel T nP nF initial.type rebuilt) :
    (initial.type.stripPis (nP + nF)).isSome = true ∧ (rebuilt.stripPis (nP + nF)).isSome = true := by
  obtain ⟨parameters, closedResidual, parameterVars, openedResidual, fields, residual,
      stripped, opened, fieldRun, rfl⟩ := rebuild
  obtain ⟨closed, _, _, bounded⟩ := checkConstantVal_typeWF first
  have scope := Expr.WScoped.of_not_hasFvar (d := 0) closed
  have openedScope : Expr.WScoped nP openedResidual := by
    simpa only [Nat.zero_add] using (openPisAtFvars_WScoped nP initial.type 0 opened scope).2
  have openedBounded := (openPisAtFvars_bounded nP opened bounded).1
  obtain ⟨fieldVars, fieldOpen, _, fieldCount, _⟩ :=
    normFieldDoms_sound wellFormed fieldRun openedScope openedBounded
  have wholeOpen := openPisAtFvars_add nP opened (by rw [Nat.zero_add]; exact fieldOpen)
  obtain ⟨_, _, wholeStrip, _, _, _⟩ := openPisAtFvars_stripPis (nP + nF) wholeOpen
  refine ⟨by rw [wholeStrip]; rfl, ?_⟩
  have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ opened
  have binderCount := Expr.stripPis_length _ stripped
  have rebuiltShape := closeTelescope_shape
    (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) parameterVars parameters ++ fields)
    0 residual
  simpa only [List.length_append, List.length_zipWith, parameterCount, binderCount, fieldCount, Nat.min_self]
    using rebuiltShape

/-- Both complete dependent frames and their spine equivalence come from one actual constructor
rebuild trace and the first check of the reader header. -/
theorem ConstructorRebuildRun.frames {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel nP nF : Nat} {T : Key md}
    {raw initial : ConstantVal md} {rebuilt : Expr md}
    (first : checkConstantVal (fueledOps .verified fuel) env raw = .ok initial)
    (rebuild : ConstructorRebuildRun env fuel T nP nF initial.type rebuilt)
    (φ : LevelParam → Nat) :
    ∃ originalReading rebuiltReading originalContext rebuiltContext originalResidual rebuiltResidual,
      denoteMeta model.base2.acval env φ 0 initial.type = some originalReading ∧
      denoteMeta model.base2.acval env φ 0 rebuilt = some rebuiltReading ∧
      PiTeleAV (nP + nF) originalReading originalContext originalResidual ∧
      PiTeleAV (nP + nF) rebuiltReading rebuiltContext rebuiltResidual ∧
      (∀ ρ : Nat → V, Sat V originalContext ρ ↔ Sat V rebuiltContext ρ) ∧
      (∀ ρ : Nat → V, Sat V originalContext ρ → interp V ρ originalResidual = interp V ρ rebuiltResidual) ∧
      ∀ (ρ : Nat → V) (values : List V), values.length = nP + nF →
        (SpineFit ρ originalContext.reverse values ↔ SpineFit ρ rebuiltContext.reverse values) := by
  obtain ⟨originalReading, rebuiltReading, scope, bounded, originalRead, rebuiltRead, semantic⟩ :=
    rebuild.semantics model first φ
  obtain ⟨_, _, leaves, converted⟩ := rebuild.conversion model.base2.wf first
  obtain ⟨originalClosed, _, _, originalBounded⟩ := checkConstantVal_typeWF first
  have originalFrame : Frame 0 initial.type := .of_not_hasFvar originalClosed originalBounded
  have rebuiltFrame : Frame 0 rebuilt := ⟨scope, bounded, fun leaf present => originalFrame.2.2 leaf (leaves leaf present)⟩
  have originalContextOk := CtxOk.nil (m := model.base2) (φ := φ)
    (Expr.fvarLeaves_eq_nil_of_not_hasFvar originalClosed)
  have rebuiltContextOk := originalContextOk.of_subset leaves
  obtain ⟨originalShape, rebuiltShape⟩ := rebuild.telescopes model.base2.wf first
  obtain ⟨⟨originalBinders, originalBody⟩, originalStrip⟩ := Option.isSome_iff_exists.mp originalShape
  obtain ⟨⟨rebuiltBinders, rebuiltBody⟩, rebuiltStrip⟩ := Option.isSome_iff_exists.mp rebuiltShape
  obtain ⟨originalContext, originalResidual, originalTele, _, _, _⟩ :=
    stripPis_denotePTele (nP + nF) originalStrip originalRead
  obtain ⟨rebuiltContext, rebuiltResidual, rebuiltTele, _, _, _⟩ :=
    stripPis_denotePTele (nP + nF) rebuiltStrip rebuiltRead
  have related := converted_telescope_frames model (.symm converted) originalShape rebuiltShape
    originalFrame rebuiltFrame originalContextOk rebuiltContextOk originalRead rebuiltRead
    (fun ρ _ => (semantic ρ).1) (fun ρ _ => (semantic ρ).2.1) originalTele rebuiltTele
  refine ⟨originalReading, rebuiltReading, originalContext, rebuiltContext, originalResidual, rebuiltResidual,
    originalRead, rebuiltRead, originalTele, rebuiltTele, ?_, ?_, ?_⟩
  · simpa only [List.append_nil] using related.1
  · simpa only [List.append_nil] using related.2
  · intro ρ values length
    exact converted_telescope_spines model (.symm converted) originalShape rebuiltShape
      originalFrame rebuiltFrame originalContextOk rebuiltContextOk originalRead rebuiltRead
      (fun ρ _ => (semantic ρ).1) (fun ρ _ => (semantic ρ).2.1) originalTele rebuiltTele ρ values length

end IxVM.Refinement.Decl
