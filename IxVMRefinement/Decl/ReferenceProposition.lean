import IxC.Kernel.Verify.Rename.Frame
import IxC.Kernel.Verify.Mono
import IxC.Kernel.Verify.Extend.Inversions

/-! # Aligning a prefix type check with the final proposition check

The prefix run is transported forward through a genuine environment frame. Monotonicity in
fuel then identifies its annotation, inferred type, and universe with the final check's
outputs. This keeps proposition evidence tied to the original checked annotation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- The actual three type-checking calls keep their outputs across an environment frame. -/
theorem typeChecks_frame {md : Mode} {P : KeyScope md} {before after : Env md}
    (frame : EnvFrame P before after) {fuel : Nat} {raw type st : Expr md} {u : Level}
    (good : raw.Good P)
    (annotated : annotateCore .verified before fuel 0 raw = .ok type)
    (inferred : inferTypeCore .verified before fuel 0 type = .ok st)
    (sorted : ensureSortCore .verified before fuel 0 st = .ok u) :
    annotateCore .verified after fuel 0 raw = .ok type ∧
      inferTypeCore .verified after fuel 0 type = .ok st ∧
      ensureSortCore .verified after fuel 0 st = .ok u := by
  have ops := fueledOps_sim (P := P) (f := fun i => i) (L := TrueLink) .verified fuel
  obtain ⟨typeGood, nextAnnotation⟩ := ops.annotate frame 0 raw good type annotated
  obtain ⟨sortGood, nextInference⟩ := ops.inferType frame 0 type typeGood st inferred
  have nextSort := (ops.ensureSort frame 0 st sortGood u sorted).2
  exact ⟨by simpa only [fueledOps_annotate, Expr.mapKeys_id] using nextAnnotation,
    by simpa only [fueledOps_inferType, Expr.mapKeys_id] using nextInference,
    by simpa only [fueledOps_ensureSort, Expr.mapKeys_id, id] using nextSort⟩

/-- A final proposition check identifies the universe of the actual prefix check. -/
theorem proposition_at_prefix {md : Mode} {P : KeyScope md} {before after : Env md}
    (frame : EnvFrame P before after) {fuel propFuel : Nat}
    {raw type st propType propSt : Expr md} {u propU : Level}
    (good : raw.Good P)
    (annotated : annotateCore .verified before fuel 0 raw = .ok type)
    (inferred : inferTypeCore .verified before fuel 0 type = .ok st)
    (sorted : ensureSortCore .verified before fuel 0 st = .ok u)
    (propAnnotation : annotateCore .verified after propFuel 0 raw = .ok propType)
    (propInference : inferTypeCore .verified after propFuel 0 propType = .ok propSt)
    (propSort : ensureSortCore .verified after propFuel 0 propSt = .ok propU)
    (zero : propU.isZero = true) : u.isZero = true := by
  obtain ⟨sameAnnotation, sameInference, sameSort⟩ :=
    typeChecks_frame frame good annotated inferred sorted
  have firstAnn := annotateCore_mono (Nat.le_max_left fuel propFuel) sameAnnotation
  have finalAnn := annotateCore_mono (Nat.le_max_right fuel propFuel) propAnnotation
  have typeEq := Except.ok.inj (firstAnn.symm.trans finalAnn)
  subst propType
  have firstInfer := inferTypeCore_mono (Nat.le_max_left fuel propFuel) sameInference
  have finalInfer := inferTypeCore_mono (Nat.le_max_right fuel propFuel) propInference
  have sortEq := Except.ok.inj (firstInfer.symm.trans finalInfer)
  subst propSt
  have firstSort := ensureSortCore_mono (Nat.le_max_left fuel propFuel) sameSort
  have finalSort := ensureSortCore_mono (Nat.le_max_right fuel propFuel) propSort
  have levelEq := Except.ok.inj (firstSort.symm.trans finalSort)
  simpa only [levelEq] using zero

end IxVM.Refinement.Decl
