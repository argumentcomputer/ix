import IxVMRefinement.Decl.NativeFront

/-! # Actual inductive prelude observations and scoped former checking

Every successful inductive arm checks scope, excludes its own family from the declared type,
and checks the former's sort before dispatching to native or modeled constructor checking.
These observations supply the exact initial typing scope independently of semantic loads.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (ConstantVal)
open Ix.Kernel.Rules (Infer Red)
open Ix.Kernel.Semantics (ConstantValCheckJ)
open Ix.Kernel.Model (rulesJ)

/-- The concrete common prelude of a checked inductive, before its route dispatch. -/
structure NativePreludeCalls (rc nl ty blockArg : SourceValue F) (initial : Heap F)
    (rootCalls : List (Call F)) where
  scopeBefore : Heap F
  scopeResult : SourceValue F
  scopeAfter : Heap F
  scopeCalls : List (Call F)
  blocksNil : Heap F
  mentionsBefore : Heap F
  mentionsAfter : Heap F
  mentionsCalls : List (Call F)
  sortBefore : Heap F
  sortResult : SourceValue F
  sortAfter : Heap F
  sortCalls : List (Call F)
  initialExtended : Heap.Extends initial scopeBefore
  scopeRun : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl]
    scopeBefore scopeResult scopeAfter scopeCalls
  nilBlocks : blocksNil = scopeAfter ++ [.construct addrListEnum "Nil" []]
  consBlocks : mentionsBefore = blocksNil ++ [.construct addrListEnum "Cons"
    [blockArg, .ptr (.enum addrListEnum) scopeAfter.length]]
  mentionsRun : ObsFn W "KernelCheck::expr_mentions_block"
    [ty, .ptr (.enum addrListEnum) blocksNil.length] mentionsBefore (.field 0) mentionsAfter mentionsCalls
  nilTypes : sortBefore = mentionsAfter ++ [.construct kexprListEnum "Nil" []]
  sortRun : ObsFn W "KernelInfer::k_ensure_sort"
    [rc, ty, .ptr (.enum kexprListEnum) mentionsAfter.length] sortBefore sortResult sortAfter sortCalls
  scopeMember : (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, nl], scopeBefore⟩ : Call F) ∈ rootCalls
  mentionsMember : (⟨"KernelCheck::expr_mentions_block",
    [ty, .ptr (.enum addrListEnum) blocksNil.length], mentionsBefore⟩ : Call F) ∈ rootCalls
  sortMember : (⟨"KernelInfer::k_ensure_sort",
    [rc, ty, .ptr (.enum kexprListEnum) mentionsAfter.length], sortBefore⟩ : Call F) ∈ rootCalls
  scopeSubset : ∀ call ∈ scopeCalls, call ∈ rootCalls
  mentionsSubset : ∀ call ∈ mentionsCalls, call ∈ rootCalls
  sortSubset : ∀ call ∈ sortCalls, call ∈ rootCalls

/-- Preserve the exact observed prelude while locating it in a larger actual trace. -/
def NativePreludeCalls.mono {rc nl ty blockArg : SourceValue F} {initial : Heap F}
    {calls rootCalls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls)
    (subset : ∀ call ∈ calls, call ∈ rootCalls) : NativePreludeCalls rc nl ty blockArg initial rootCalls where
  scopeBefore := prelude.scopeBefore
  scopeResult := prelude.scopeResult
  scopeAfter := prelude.scopeAfter
  scopeCalls := prelude.scopeCalls
  blocksNil := prelude.blocksNil
  mentionsBefore := prelude.mentionsBefore
  mentionsAfter := prelude.mentionsAfter
  mentionsCalls := prelude.mentionsCalls
  sortBefore := prelude.sortBefore
  sortResult := prelude.sortResult
  sortAfter := prelude.sortAfter
  sortCalls := prelude.sortCalls
  initialExtended := prelude.initialExtended
  scopeRun := prelude.scopeRun
  nilBlocks := prelude.nilBlocks
  consBlocks := prelude.consBlocks
  mentionsRun := prelude.mentionsRun
  nilTypes := prelude.nilTypes
  sortRun := prelude.sortRun
  scopeMember := subset _ prelude.scopeMember
  mentionsMember := subset _ prelude.mentionsMember
  sortMember := subset _ prelude.sortMember
  scopeSubset := fun call member => subset call (prelude.scopeSubset call member)
  mentionsSubset := fun call member => subset call (prelude.mentionsSubset call member)
  sortSubset := fun call member => subset call (prelude.sortSubset call member)

/-- The allocated block list is reached before the raw occurrence check. -/
theorem NativePreludeCalls.scope_to_mentions {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls) :
    Heap.Extends prelude.scopeBefore prelude.mentionsBefore := by
  have nilBlocks : Heap.Extends prelude.scopeAfter prelude.blocksNil := by
    rw [prelude.nilBlocks]
    exact Heap.Extends.snoc _ _
  have consBlocks : Heap.Extends prelude.blocksNil prelude.mentionsBefore := by
    rw [prelude.consBlocks]
    exact Heap.Extends.snoc _ _
  exact prelude.scopeRun.heap_extends.trans (nilBlocks.trans consBlocks)

/-- The occurrence checker receives the actual singleton parent-block list. -/
theorem NativePreludeCalls.blocksRep {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls)
    {block : Bytes.Address} (represented : Bytes.RepAddressRef addrTy initial block blockArg) :
    RepList addrListEnum (Bytes.RepAddressRef addrTy) prelude.mentionsBefore [block]
      (.ptr (.enum addrListEnum) prelude.blocksNil.length) := by
  have consExtended : Heap.Extends prelude.blocksNil prelude.mentionsBefore := by
    rw [prelude.consBlocks]
    exact Heap.Extends.snoc _ _
  have nilCell : prelude.mentionsBefore[prelude.scopeAfter.length]? =
      some (.construct addrListEnum "Nil" []) :=
    consExtended.getElem?_eq (by rw [prelude.nilBlocks]; simp)
  have consCell : prelude.mentionsBefore[prelude.blocksNil.length]? =
      some (.construct addrListEnum "Cons"
        [blockArg, .ptr (.enum addrListEnum) prelude.scopeAfter.length]) := by
    rw [prelude.consBlocks]
    simp
  exact RepLinkedList.cons consCell
    (Bytes.repAddressRef_heapMono₂ addrTy
      (prelude.initialExtended.trans prelude.scope_to_mentions) represented)
    (RepLinkedList.nil nilCell)

/-- The observed occurrence guard excludes the native former from its checked declared type.
Raw query facts and coverage are supplied by the actual root trace. -/
theorem NativePreludeCalls.noSelf {raw : ScopedCtx} [raw.TableKeyed] {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls)
    {block : Bytes.Address} {T : KKey} {levels params indices ctors : Nat} {i : F} {type : KExpr}
    (peer : OneTypePeerReads raw block T levels params indices ctors i)
    (records : RawRecordFacts raw) (good : Good raw.toCtx calls)
    (covered : RawRecordCoverage raw calls)
    (represented : TmExact raw.κ 0 (fun _ => default) initial 0 type ty)
    (noProjection : noProjAt T type = true)
    (blockRep : Bytes.RepAddressRef addrTy initial block blockArg) : type.mentionsConst T = false :=
  expr_mentions_block_zero_observed_spec peer records (good.sub prelude.mentionsSubset)
    (covered.sub prelude.mentionsSubset)
    (represented.mono (prelude.initialExtended.trans prelude.scope_to_mentions))
    noProjection (prelude.blocksRep blockRep) prelude.mentionsRun

/-- The actual allocations and calls connect the scope check to the sort check. -/
theorem NativePreludeCalls.scope_to_sort {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls) :
    Heap.Extends prelude.scopeBefore prelude.sortBefore := by
  have nilBlocks : Heap.Extends prelude.scopeAfter prelude.blocksNil := by
    rw [prelude.nilBlocks]
    exact Heap.Extends.snoc _ _
  have consBlocks : Heap.Extends prelude.blocksNil prelude.mentionsBefore := by
    rw [prelude.consBlocks]
    exact Heap.Extends.snoc _ _
  have nilTypes : Heap.Extends prelude.mentionsAfter prelude.sortBefore := by
    rw [prelude.nilTypes]
    exact Heap.Extends.snoc _ _
  exact prelude.scopeRun.heap_extends.trans
    (nilBlocks.trans (consBlocks.trans (prelude.mentionsRun.heap_extends.trans nilTypes)))

/-- The fresh context used by the observed former sort check is empty. -/
theorem NativePreludeCalls.typesRep {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls)
    (κ : _root_.Address → KKey) (Γ : Nat → KExpr) :
    TypesRep κ Γ prelude.sortBefore 0 (.ptr (.enum kexprListEnum) prelude.mentionsAfter.length) := by
  rw [prelude.nilTypes]
  exact typesRep_alloc_nil κ Γ prelude.mentionsAfter

/-- Only children of the actual former sort check are selected for semantic loads. -/
def nativeFormerCheckCtx (base : Ctx) {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls) :
    ScopedCtx := { toCtx := base, allowed := fun call => call ∈ prelude.sortCalls }

instance (base : Ctx) {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)} (prelude : NativePreludeCalls rc nl ty blockArg initial calls) :
    (nativeFormerCheckCtx base prelude).TableKeyed := ⟨rfl⟩

/-- The common prelude is extracted from every successful inductive dispatch arm. -/
theorem native_prelude_calls {rc nl ty np ni nc unsafeFlag blockArg index addr result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn W "KernelCheck::check_const"
      [rc, .construct kciEnum "Induct" [nl, ty, np, ni, nc, unsafeFlag, blockArg, index], addr]
      h result h' calls) : Nonempty (NativePreludeCalls rc nl ty blockArg h calls) := by
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
  | .Ctor_n0_n0 (hne1883 := notInduct) ..
  | .Ctor_n0_other (hne1883 := notInduct) ..
  | .Ctor_other (hne1883 := notInduct) ..
  | .Rec_n0 (hne1883 := notInduct) ..
  | .Rec_other (hne1883 := notInduct) .. =>
    exact (notInduct [nl, ty, np, ni, nc, unsafeFlag, blockArg, index] rfl rfl).elim
  | .Induct_n0 (m2 := scopeBefore) (m1283 := scopeAfter) (m1333 := mentionsAfter)
      (m1354 := mentionsBefore) (m1376 := blocksNil) (m1396 := sortAfter) (m1427 := sortBefore)
      (ev14 := unsafeRun) (hv1240 := shape) (ev1295 := scopeRun)
      (hm1362 := consBlocks) (hm1384 := nilBlocks) (ev1343 := mentionsRun)
      (heq1394 := noMention) (hm1435 := nilTypes) (ev1408 := sortRun) (hc1634 := allCalls) ..
  | .Induct_other (m2 := scopeBefore) (m1283 := scopeAfter) (m1333 := mentionsAfter)
      (m1354 := mentionsBefore) (m1376 := blocksNil) (m1396 := sortAfter) (m1427 := sortBefore)
      (ev14 := unsafeRun) (hv1240 := shape) (ev1295 := scopeRun)
      (hm1362 := consBlocks) (hm1384 := nilBlocks) (ev1343 := mentionsRun)
      (heq1394 := noMention) (hm1435 := nilTypes) (ev1408 := sortRun) (hc1882 := allCalls) .. =>
    injection shape with _ _ entries
    injection entries with levelEq entries
    injection entries with typeEq entries
    injection entries with _ entries
    injection entries with _ entries
    injection entries with _ entries
    injection entries with _ entries
    injection entries with blockEq _
    subst levelEq typeEq blockEq
    rw [noMention] at mentionsRun
    exact ⟨{
      scopeBefore := scopeBefore, scopeResult := _, scopeAfter := scopeAfter, scopeCalls := _
      blocksNil := blocksNil, mentionsBefore := mentionsBefore, mentionsAfter := mentionsAfter
      mentionsCalls := _, sortBefore := sortBefore, sortResult := _, sortAfter := sortAfter, sortCalls := _
      initialExtended := unsafeRun.heap_extends
      scopeRun := scopeRun, nilBlocks := nilBlocks, consBlocks := consBlocks
      mentionsRun := mentionsRun, nilTypes := nilTypes, sortRun := sortRun
      scopeMember := by rw [allCalls]; simp
      mentionsMember := by rw [allCalls]; simp
      sortMember := by rw [allCalls]; simp
      scopeSubset := by intro call member; rw [allCalls]; simp [member]
      mentionsSubset := by intro call member; rw [allCalls]; simp [member]
      sortSubset := by intro call member; rw [allCalls]; simp [member] }⟩

/-- The exact former representation retains the type field used by its prelude. -/
theorem CIRepExact.induct_valRep {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty np ni nc safety parent index : SourceValue F} {cv : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon}
    (represented : CIRepExact κ h
      (.construct kciEnum "Induct" [nl, ty, np, ni, nc, safety, parent, index]) (.indInfo cv caps)) :
    ValRepExact κ h nl ty cv := by
  generalize shape : (Value.construct kciEnum "Induct"
    [nl, ty, np, ni, nc, safety, parent, index] : SourceValue F) = value at represented
  generalize kind : Ix.Kernel.ConstantInfo.indInfo cv caps = info at represented
  cases represented
  case induct exactValue _ _ =>
    injection shape with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    obtain ⟨rfl, rfl⟩ := Ix.Kernel.ConstantInfo.indInfo.inj kind
    exact exactValue
  all_goals (injection shape with _ tag _; exact absurd tag (by decide))

/-- The observed former sort check yields its constant check in the precise selected scope.
The declared level positions and annotation come from the actual record reader/converter. -/
theorem NativePreludeCalls.checked {base : Ctx} {rc nl ty blockArg : SourceValue F}
    {initial : Heap F} {calls : List (Call F)}
    (prelude : NativePreludeCalls rc nl ty blockArg initial calls)
    {name : KKey} {levels : Nat} {rawType : KExpr} {annotated : ConstantVal .anon}
    (stored : IxVM.Consistency.ValStored annotated ⟨name, List.range levels, rawType⟩)
    (represented : ValRepExact base.κ initial nl ty annotated)
    (varsBounded : rawType.looseBVarsBounded 0 = true) (noFvars : rawType.hasFvar = false)
    (fresh : base.env.find? name = none)
    (notBasis : Ix.Kernel.reservedBasisNames.contains name = false)
    (notProjection : name.isProjFnShape = false)
    (facts : CoreEnvFacts base) (good : Good base calls)
    (roles : RCRep base.t base.lim initial rc)
    (loads : ScopedLoadFacts (nativeFormerCheckCtx base prelude)) :
    ConstantValCheckJ rulesJ base.env ⟨name, List.range levels, rawType⟩ annotated ∧
      ∃ type level observedLevel,
        Infer base.env .full 0 annotated.type type ∧ Red base.env 0 type (.sort level) ∧
        RepKLevel prelude.sortAfter observedLevel prelude.sortResult ∧ LvEq level observedLevel := by
  have fullExtended := prelude.initialExtended.trans prelude.scope_to_sort
  have coreGood : CoreGood (nativeFormerCheckCtx base prelude) prelude.sortCalls :=
    CoreGood.ofRaw (good.sub prelude.sortSubset) (fun _ member => member)
  have levelParams : annotated.levelParams = List.range levels := stored.2.1
  obtain ⟨checked, type, level, observedLevel, inferred, reduced, representedLevel, sameLevel⟩ :=
    constantValCheckJ_of_scoped (c := nativeFormerCheckCtx base prelude) stored
      (represented.mono prelude.initialExtended) varsBounded noFvars fresh notBasis notProjection
      facts.store (PosSortLift.of_range levelParams) prelude.scopeRun prelude.scope_to_sort
      (roles.mono fullExtended) (prelude.typesRep base.κ (fun _ => default)) facts loads coreGood prelude.sortRun
  rw [levelParams, posOf_range] at inferred
  exact ⟨checked, type, level, observedLevel, inferred, reduced, representedLevel, sameLevel⟩

end IxVM.Refinement.Decl
