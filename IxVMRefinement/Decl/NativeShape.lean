import IxVMRefinement.Core.CallHeaps
import IxVMRefinement.Decl.NativePrelude
import IxVMRefinement.Decl.NativeStage

/-! # Native former shape observations at actual capability stages -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr ConstantVal)

/-- The actual former guard supplies either its raw telescope or a nonzero index count.
This is precisely the arity information needed to stage the actual native capabilities. -/
theorem former_decl_ok_shape {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {params indices : Nat} {type : KExpr}
    {typePtr count blockArg index sortLevel result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (bound : params + indices < 18446744069414584321)
    (represented : TmExact κ 0 Γ h 0 type typePtr)
    (observed : ObsFn W "KernelCheck::former_decl_ok"
      [typePtr, .field (params : F), .field (indices : F), count, blockArg, index, sortLevel]
      h result h' calls) :
    (∃ binders level, type.stripPis (params + indices) = some (binders, .sort level) ∧
      binders.length = params + indices) ∨ indices ≠ 0 := by
  match Obs.«KernelCheck::former_decl_ok».obs observed with
  | .n1 (v17 := sum) (op38 := added) (ev15 := telescope) .. =>
    rw [evalBinOp_add_nat params indices added] at telescope
    obtain ⟨_, binders, level, shape, length⟩ :=
      former_is_tele_one_bounded_spec (params + indices) bound represented telescope
    exact .inl ⟨binders, level, shape, length⟩
  | .other (ev78 := zeroTest) (heq93 := resultEq) .. =>
    subst resultEq
    obtain ⟨isZero, _⟩ := Lib.is_zero_spec zeroTest
    right
    intro zero
    subst indices
    simp at isZero

/-- The observed guard discharges the stage arity premise while retaining the supplied
native shape and recursion verdict. The base invariants and checked type properties are preserved. -/
theorem coreEnvFacts_consNativeCapsAt_of_guard {c : Ctx} {cv : ConstantVal .anon}
    {shape : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {typePtr count blockArg index sortLevel result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (facts : CoreEnvFacts c) (fresh : c.env.find? cv.name = none)
    (keyShape : cv.name.isProjFnShape = false)
    (typeShape : cv.type.hasFvar = false ∧ cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve c.env = true ∧ cv.type.looseBVarsBounded 0 = true)
    (bound : shape.nP + shape.nIdx < 18446744069414584321)
    (represented : TmExact c.κ 0 (fun _ => default) h 0 cv.type typePtr)
    (observed : ObsFn W "KernelCheck::former_decl_ok"
      [typePtr, .field (shape.nP : F), .field (shape.nIdx : F), count, blockArg, index, sortLevel]
      h result h' calls) :
    CoreEnvFacts { c with env := ⟨.indInfo cv (Ix.Kernel.nativeCapsAt shape isRec) :: c.env.consts⟩ } := by
  rcases former_decl_ok_shape bound represented observed with ⟨binders, level, telescope, _⟩ | indexed
  · exact coreEnvFacts_consNativeCapsAt facts fresh keyShape typeShape telescope
  · exact coreEnvFacts_consNativeCapsAt_indexed facts fresh keyShape typeShape indexed

/-- The actual native dispatch selects its zero modeled verdict and shape-check invocation. -/
structure NativeInductShapeCall (rc typePtr blockArg index safety : SourceValue F)
    (params indices count levels : Nat) (initial : Heap F) (rootCalls : List (Call F)) where
  modeBefore : Heap F
  modeAfter : Heap F
  modeCalls : List (Call F)
  modeRun : ObsFn W "KernelModeled::block_is_modeled" [blockArg] modeBefore (.field 0) modeAfter modeCalls
  modeMember : (⟨"KernelModeled::block_is_modeled", [blockArg], modeBefore⟩ : Call F) ∈ rootCalls
  modeSubset : ∀ call ∈ modeCalls, call ∈ rootCalls
  before : Heap F
  result : SourceValue F
  after : Heap F
  calls : List (Call F)
  observed : ObsFn W "KernelCheck::check_inductive_shape"
    [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
      .field (levels : F), blockArg, index, safety] before result after calls
  member : (⟨"KernelCheck::check_inductive_shape",
    [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
      .field (levels : F), blockArg, index, safety], before⟩ : Call F) ∈ rootCalls
  subset : ∀ call ∈ calls, call ∈ rootCalls
  initialToMode : Heap.Extends initial modeBefore
  initialToShape : Heap.Extends initial before

/-- An actual nonzero modeled verdict is retained for the other declaration route. -/
def ModeledInductCall (blockArg : SourceValue F) (initial : Heap F) (calls : List (Call F)) : Prop :=
  ∃ before result after children,
    ObsFn W "KernelModeled::block_is_modeled" [blockArg] before result after children ∧
    result ≠ .field 0 ∧ Heap.Extends initial before ∧
    (⟨"KernelModeled::block_is_modeled", [blockArg], before⟩ : Call F) ∈ calls ∧
    ∀ call ∈ children, call ∈ calls

/-- A successful inductive check exposes the actual route, without a universal unmodeled
witness or an assumption about either kernel parts recognizer. -/
theorem native_induct_dispatch {rc typePtr blockArg index safety addr result : SourceValue F}
    {params indices count levels : Nat} {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Induct"
        [.field (levels : F), typePtr, .field (params : F), .field (indices : F),
          .field (count : F), safety, blockArg, index], addr] h result h' calls) :
    Nonempty (NativeInductShapeCall rc typePtr blockArg index safety params indices count levels h calls) ∨
      ModeledInductCall blockArg h calls := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Ctor_n0_n0 (hne1879 := notInduct) ..
  | .Ctor_n0_other (hne1879 := notInduct) ..
  | .Ctor_other_n0 (hne1879 := notInduct) ..
  | .Ctor_other_other (hne1879 := notInduct) ..
  | .Rec_n0 (hne1879 := notInduct) ..
  | .Rec_other (hne1879 := notInduct) .. =>
    exact (notInduct [_, _, _, _, _, _, _, _] rfl rfl).elim
  | .Induct_other_n0 (m1470 := before) (m1492 := after) (v1491 := value) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hne1635 := notNative) (hc1869 := allCalls) ..
  | .Induct_other_other (m1470 := before) (m1492 := after) (v1491 := value) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hne1635 := notNative) (hc1878 := allCalls) .. =>
    injection fields with _ _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with _ fields
    injection fields with blockEq _
    subst blockEq
    have member : (⟨"KernelModeled::block_is_modeled", [blockArg], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inr ⟨before, value, after, children, modeRun, notNative,
      (observed.call_heap_bounds member).1, member, fun call inside => by rw [allCalls]; simp [inside]⟩
  | .Induct_n0 (m1470 := modeBefore) (m1492 := before) (cs1503 := modeCalls)
      (m1519 := after) (v1518 := value) (cs1529 := children)
      (hv1240 := fields) (ev1505 := modeRun) (ev1531 := shapeRun) (hc1634 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    have modeMember : (⟨"KernelModeled::block_is_modeled", [blockArg], modeBefore⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    have shapeMember : (⟨"KernelCheck::check_inductive_shape",
        [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
          .field (levels : F), blockArg, index, safety], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inl ⟨{
      modeBefore := modeBefore, modeAfter := before, modeCalls := modeCalls, modeRun := modeRun
      modeMember := modeMember, modeSubset := fun call member => by rw [allCalls]; simp [member]
      before := before, result := value, after := after, calls := children, observed := shapeRun
      member := shapeMember, subset := fun call member => by rw [allCalls]; simp [member]
      initialToMode := (observed.call_heap_bounds modeMember).1
      initialToShape := (observed.call_heap_bounds shapeMember).1 }⟩

/-- The three actual calls inside the native shape stage. -/
structure NativeShapeCalls (rc typePtr blockArg index safety : SourceValue F)
    (params indices count levels : Nat) (initial : Heap F) (rootCalls : List (Call F)) where
  sortBefore : Heap F
  sortAfter : Heap F
  sortLevel : SourceValue F
  sortCalls : List (Call F)
  nilTypes : sortBefore = initial ++ [.construct kexprListEnum "Nil" []]
  sortRun : ObsFn W "KernelCheck::get_result_sort_level"
    [rc, typePtr, .field ((params + indices : Nat) : F), .ptr (.enum kexprListEnum) initial.length]
    sortBefore sortLevel sortAfter sortCalls
  guardResult : SourceValue F
  ctorBefore : Heap F
  guardCalls : List (Call F)
  guardRun : ObsFn W "KernelCheck::former_decl_ok"
    [typePtr, .field (params : F), .field (indices : F), .field (count : F), blockArg, index, sortLevel]
    sortAfter guardResult ctorBefore guardCalls
  result : SourceValue F
  after : Heap F
  ctorCalls : List (Call F)
  ctorRun : ObsFn W "KernelCheck::check_inductive_shape_ctors"
    [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
      .field (levels : F), blockArg, index, sortLevel, safety, .field 0] ctorBefore result after ctorCalls
  sortSubset : ∀ call ∈ sortCalls, call ∈ rootCalls
  guardSubset : ∀ call ∈ guardCalls, call ∈ rootCalls
  ctorSubset : ∀ call ∈ ctorCalls, call ∈ rootCalls

/-- Extract the exact shape-stage calls, retaining the actual member index and safety value. -/
theorem native_shape_calls {rc typePtr blockArg index safety result : SourceValue F}
    {params indices count levels : Nat} {h h' : Heap F} {calls rootCalls : List (Call F)}
    (observed : ObsFn W "KernelCheck::check_inductive_shape"
      [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
        .field (levels : F), blockArg, index, safety] h result h' calls)
    (subset : ∀ call ∈ calls, call ∈ rootCalls) :
    Nonempty (NativeShapeCalls rc typePtr blockArg index safety params indices count levels h rootCalls) := by
  match Obs.«KernelCheck::check_inductive_shape».obs observed with
  | .run (v1 := level) (m2 := sortAfter) (cs12 := sortCalls) (m50 := sortBefore)
      (v62 := guardResult) (m63 := ctorBefore) (cs73 := guardCalls) (cs135 := ctorCalls)
      (op46 := sum) (hm58 := nilTypes) (ev14 := sortRun) (ev75 := guardRun)
      (ev137 := ctorRun) (hc225 := allCalls) =>
    rw [evalBinOp_add_nat params indices sum] at sortRun
    exact ⟨{
      sortBefore := sortBefore, sortAfter := sortAfter, sortLevel := level, sortCalls := sortCalls
      nilTypes := nilTypes, sortRun := sortRun, guardResult := guardResult, ctorBefore := ctorBefore
      guardCalls := guardCalls, guardRun := guardRun, result := result, after := h', ctorCalls := ctorCalls
      ctorRun := ctorRun
      sortSubset := fun call member => subset call (by rw [allCalls]; simp [member])
      guardSubset := fun call member => subset call (by rw [allCalls]; simp [member])
      ctorSubset := fun call member => subset call (by rw [allCalls]; simp [member]) }⟩


/-- The shape stage allocates the empty type context before determining the result sort. -/
theorem NativeShapeCalls.initial_to_sort {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial calls) :
    Heap.Extends initial shape.sortBefore := by
  rw [shape.nilTypes]
  exact Heap.Extends.snoc _ _

theorem NativeShapeCalls.initial_to_guard {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial calls) :
    Heap.Extends initial shape.sortAfter :=
  shape.initial_to_sort.trans shape.sortRun.heap_extends

theorem NativeShapeCalls.initial_to_ctors {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial calls) :
    Heap.Extends initial shape.ctorBefore :=
  shape.initial_to_guard.trans shape.guardRun.heap_extends

/-- Only actual result-sort helper children belong to this semantic load scope. -/
def nativeShapeSortCtx (base : Ctx) {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial calls) :
    ScopedCtx := { toCtx := base, allowed := fun call => call ∈ shape.sortCalls }

/-- The actual result-sort call supplies the level used by the following constructor loop. -/
theorem NativeShapeCalls.resultSort {base : Ctx} {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial calls)
    {type : KExpr} (bound : params + indices < 18446744069414584321)
    (roles : RCRep base.t base.lim initial rc)
    (represented : Tm base.κ 0 (fun _ => default) initial 0 type typePtr)
    (facts : CoreEnvFacts base) (good : Good base calls)
    (loads : ScopedLoadFacts (nativeShapeSortCtx base shape)) :
    ∃ level : KLevel, KernelLevels.RepKLevel shape.ctorBefore level shape.sortLevel ∧
      ∀ binders sort, type.stripPis (params + indices) = some (binders, .sort sort) → LvEq sort level := by
  have types : TypesRep base.κ (fun _ => default) shape.sortBefore 0
      (.ptr (.enum kexprListEnum) initial.length) := by
    rw [shape.nilTypes]
    exact typesRep_alloc_nil base.κ (fun _ => default) initial
  have covered : CoreGood (nativeShapeSortCtx base shape) shape.sortCalls :=
    CoreGood.ofRaw (good.sub shape.sortSubset) (fun _ member => member)
  obtain ⟨level, levelRep, sameSort⟩ := get_result_sort_level_scoped_bounded_spec
    (c := nativeShapeSortCtx base shape) (params + indices) bound
    (roles.mono shape.initial_to_sort) types (ghostScoped_zero _) facts loads covered
    (represented.mono shape.initial_to_sort) shape.sortRun
  exact ⟨level, KernelLevels.repKLevel_heapMono₂ shape.guardRun.heap_extends levelRep, sameSort⟩

/-- The observed native guard supplies the shape needed to preserve the base facts at the
actual capability record, including indexed aliases. -/
theorem NativeShapeCalls.stageFacts {base : Ctx} {rc typePtr blockArg index safety : SourceValue F}
    {count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    {parts : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (shape : NativeShapeCalls rc typePtr blockArg index safety parts.nP parts.nIdx count levels initial calls)
    {cv : ConstantVal .anon} (facts : CoreEnvFacts base) (fresh : base.env.find? cv.name = none)
    (keyShape : cv.name.isProjFnShape = false)
    (typeShape : cv.type.hasFvar = false ∧ cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve base.env = true ∧ cv.type.looseBVarsBounded 0 = true)
    (bound : parts.nP + parts.nIdx < 18446744069414584321)
    (represented : TmExact base.κ 0 (fun _ => default) initial 0 cv.type typePtr) :
    CoreEnvFacts { base with env := ⟨.indInfo cv (Ix.Kernel.nativeCapsAt parts isRec) :: base.env.consts⟩ } :=
  coreEnvFacts_consNativeCapsAt_of_guard facts fresh keyShape typeShape bound
    (represented.mono shape.initial_to_guard) shape.guardRun


end IxVM.Refinement.Decl
