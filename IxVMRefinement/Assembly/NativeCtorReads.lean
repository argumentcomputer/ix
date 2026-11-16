import IxVMRefinement.Assembly.NativeCtorInputs
import IxVMRefinement.Assembly.NativeReaderInputs
import IxVMRefinement.Core.CallHeaps

/-! # Constructor load and scope observations from the native loop

The successful loop itself supplies one concrete constructor load and scope check at every
slot. These observations carry no semantic installation or typing premise.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual load, header guards, and scope check for one constructor slot. -/
structure CtorScopeRead (block : Bytes.Address) (indIndex ctorIndex safety : F)
    (params levels : Nat) (calls : List (Call F)) where
  blockArg : SourceValue F
  ptr : SourceValue F
  result : SourceValue F
  before : Heap F
  after : Heap F
  scopeBefore : Heap F
  scopeAfter : Heap F
  loadCalls : List (Call F)
  scopeCalls : List (Call F)
  nl : SourceValue F
  ty : SourceValue F
  parent : SourceValue F
  member : SourceValue F
  slot : SourceValue F
  numParams : SourceValue F
  numFields : SourceValue F
  unsafeFlag : SourceValue F
  loaded : ObsFn Core.W "Ingress::get_ci_cprj" [blockArg, .field indIndex, .field ctorIndex]
    before ptr after loadCalls
  blockRep : Bytes.RepAddressRef Core.addrTy before block blockArg
  tag : loadValue after ptr = .ok (.construct Core.kciEnum "Ctor"
    [nl, ty, parent, member, slot, numParams, numFields, unsafeFlag])
  memberChecked : member = .field indIndex
  slotChecked : slot = .field ctorIndex
  levelsChecked : nl = .field (levels : F)
  paramsChecked : numParams = .field (params : F)
  safetyChecked : unsafeFlag = .field safety
  extended : Heap.Extends after scopeBefore
  scopeRun : ObsFn Core.W "KernelCheck::validate_expr_well_scoped"
    [ty, .field 0, nl] scopeBefore result scopeAfter scopeCalls
  loadSubset : ∀ call ∈ loadCalls, call ∈ calls
  scopeMember : (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, nl], scopeBefore⟩ : Call F) ∈ calls

/-- Every slot covered by a successful native constructor loop has an actual guarded load
and scope check. The natural index is kept below the checked constructor-count bound. -/
theorem native_ctor_scope_reads {block : Bytes.Address} {indIndex safety : F}
    {params indices count levels : Nat} (countBound : count < 549755813888)
    {rootCalls : List (Call F)} :
    ∀ (remaining start : Nat) {rc former blockArg sortLevel result : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      remaining + start = count →
      Bytes.RepAddressRef Core.addrTy h block blockArg →
      (∀ call ∈ calls, call ∈ rootCalls) →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, former, .field (params : F), .field (indices : F), .field (count : F),
          .field (levels : F), blockArg, .field indIndex, sortLevel, .field safety, .field (start : F)]
        h result h' calls →
      ∀ offset < remaining, Nonempty (CtorScopeRead block indIndex ((start + offset : Nat) : F)
        safety params levels rootCalls)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    intro offset bound
    omega
  | remaining + 1, start, rc, former, blockArg, sortLevel, result, h, h', calls,
      total, blockRep, subset, evaluated => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs evaluated with
    | .n0 (op17 := operation) .. =>
      have zero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((count - start : Nat) : F)) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : start ≤ count) operation
      have equal := Decl.nat_eq_of_field_eq (by decide) (by omega) zero
      omega
    | .other (m34 := after) (p41 := ptr) (cs47 := loadCalls)
        (x_c_nlvls := nl) (x_cty := ty) (x_c_block := parent)
        (x_c_ind_idx := member) (x_c_cidx := slot) (x_c_np := np) (x_c_nf := nf)
        (x_c_unsafe := unsafeFlag) (v318 := scopeResult) (m144 := scopeBefore)
        (m319 := scopeAfter) (cs329 := scopeCalls) (m655 := nextHeap)
        (cs695 := nextCalls) (v708 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (ev154 := addressEq)
        (heq205 := memberChecked) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (heq317 := safetyChecked) (ev331 := scopeRun)
        (op792 := addition) (ev697 := nextRun) (hc794 := allCalls) .. =>
      have added := Decl.evalBinOp_add_nat start 1 addition
      subst nextIndex
      have nextMember : (⟨"KernelCheck::check_inductive_shape_ctors",
          [rc, former, .field (params : F), .field (indices : F), .field (count : F),
            .field (levels : F), blockArg, .field indIndex, sortLevel, .field safety,
            .field ((start + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ calls := by
        rw [allCalls]
        simp
      have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evaluated.call_heap_bounds nextMember).1 blockRep
      have rest := native_ctor_scope_reads countBound remaining (start + 1) (by omega)
        nextBlock (fun call member => subset call (by rw [allCalls]; simp [member])) nextRun
      have current : CtorScopeRead block indIndex (start : F) safety params levels rootCalls := {
        blockArg := blockArg, ptr := ptr, result := scopeResult
        before := h, after := after, scopeBefore := scopeBefore, scopeAfter := scopeAfter
        loadCalls := loadCalls, scopeCalls := scopeCalls
        nl := nl, ty := ty, parent := parent, member := member, slot := slot
        numParams := np, numFields := nf, unsafeFlag := unsafeFlag
        loaded := loaded, blockRep := blockRep, tag := tag
        memberChecked := memberChecked, slotChecked := slotChecked
        levelsChecked := levelsChecked, paramsChecked := paramsChecked, safetyChecked := safetyChecked
        extended := addressEq.heap_extends
        scopeRun := by simpa only [levelsChecked] using scopeRun
        loadSubset := fun call member => subset call (by rw [allCalls]; simp [member])
        scopeMember := by
          rw [levelsChecked]
          exact subset _ (by rw [allCalls]; simp) }
      intro offset bounded
      cases offset with
      | zero => simpa only [Nat.add_zero] using (⟨current⟩ : Nonempty _)
      | succ offset =>
        have picked := rest offset (by omega)
        simpa only [show start + 1 + offset = start + (offset + 1) by omega] using picked

/-- A produced Source observation and the actual reader row construct one constructor's
reload contract. The declared member name is fixed by the reader context's key agreement. -/
theorem CtorScopeRead.load_contract {base : Core.Ctx} {block : Bytes.Address} {i j : F}
    {params levels : Nat} {calls : List (Call F)}
    (checked : CtorScopeRead block i j 0 params levels calls)
    (paramsBound : params < 72057594037927936) (levelsBound : levels < 4294967296)
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    (ctorAt : ind.ctors.toList[ZMod.val j]? = some ctor)
    {cx : Ix.Kernel.Reader.Ctx .anon} {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {row : NativeCtorRow}
    (reader : NativeCtorReaderCheckedFrame cx (Core.ixAddr block)
      (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self) (ZMod.val i, ctor, ZMod.val j) row)
    (nameKeyed : row.1.name = base.κ (Core.cprjAddr (Core.ixAddr block) (ZMod.val i) (ZMod.val j)))
    (good : Core.Good base calls)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a → cx.blob a = some bytes) :
    ∃ (annotated : Ix.Kernel.ConstantVal .anon) (rawSyntax : Core.KExpr),
      IxVM.Consistency.ValStored annotated row.1 ∧
      row.2.1 = params ∧ row.1.levelParams = List.range levels ∧
      ∀ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
        (∀ call ∈ cs, call ∈ calls) → Bytes.RepAddressRef Core.addrTy h block bp →
        ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs →
        ∃ (ty parentPtr : SourceValue F) (parent : Bytes.Address),
          loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor"
            [.field (levels : F), ty, parentPtr, .field i, .field j,
              .field (params : F), .field (row.2.2 : F), .field 0]) ∧
          Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block ∧
          (∀ d Γ, Decl.RawTmExact base.κ d Γ h' 0 rawSyntax
            (Core.posOf annotated.levelParams annotated.type) ty) ∧
          Decl.CIRepExact base.κ h' (.construct Core.kciEnum "Ctor"
            [.field (levels : F), ty, parentPtr, .field i, .field j,
              .field (params : F), .field (row.2.2 : F), .field 0])
            (.ctorInfo annotated params row.2.2) := by
  obtain ⟨frame, _, safe⟩ := reader
  change ctor.isUnsafe = false at safe
  obtain ⟨annotated, rawSyntax, stored, exactValue, _, _, varsBounded, levelsDefined, _,
    tree, plan, built, planned, image, ctorIndex, rawImage⟩ :=
    observed_native_ctor_input_raw_origin source blockShape memberAt ctorAt checked.loaded
      (good.sub checked.loadSubset) checked.blockRep checked.tag checked.slotChecked checked.extended
      good.2 checked.scopeRun checked.scopeMember frame.2.1 keyed selfKeyed
      (fun a bytes hashed hashEq => blobReads a bytes (Core.hashed_mono checked.loadSubset hashed) hashEq)
  have levelCount : ctor.lvls.toNat = levels := by
    have exactBound := exactValue.2.1
    have equal := Decl.nat_eq_of_field_eq (by omega) (by omega)
      (exactValue.1.symm.trans checked.levelsChecked)
    simpa only [stored.2.1, List.length_range] using equal
  obtain ⟨value, valueAt, _, _, ctorParamsBound, _, typePtr, parentPtr, parent,
    valueShape, _, _⟩ := native_ctor_raw_reload_with_shape source blockShape memberAt ctorAt ctorIndex
      stored built planned image rawImage frame.2.1 varsBounded levelsDefined checked.loaded
      (good.sub checked.loadSubset) checked.blockRep keyed selfKeyed
      (fun a bytes hashed hashEq => blobReads a bytes (Core.hashed_mono checked.loadSubset hashed) hashEq)
  have payload := Except.ok.inj (checked.tag.symm.trans (valueAt.trans (congrArg Except.ok valueShape)))
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at payload
  have paramField := payload.2.2.2.2.2.1.symm.trans checked.paramsChecked
  have paramCount : ctor.params.toNat = params := by
    have equal := congrArg (fun field : F => ZMod.val field) (Value.field.inj paramField)
    rw [ZMod.val_natCast_of_lt (Nat.lt_trans ctorParamsBound (by decide)),
      ZMod.val_natCast_of_lt (Nat.lt_trans paramsBound (by decide))] at equal
    exact equal
  have storedRow : IxVM.Consistency.ValStored annotated row.1 :=
    ⟨stored.1.trans nameKeyed.symm, stored.2.1.trans frame.2.2.1.symm, stored.2.2⟩
  have rowParams : row.2.1 = params := frame.2.2.2.1.trans paramCount
  have rowLevels : row.1.levelParams = List.range levels := frame.2.2.1.trans (congrArg List.range levelCount)
  have fieldsCount : ctor.fields.toNat = row.2.2 := frame.2.2.2.2.symm
  refine ⟨annotated, rawSyntax, storedRow, rowParams, rowLevels, ?_⟩
  intro bp ptr h h' cs subset blockRep loaded
  obtain ⟨value, valueAt, represented, rawAt, _, _, typePtr, parentPtr, parent,
    valueShape, parentRep, parentEq⟩ := native_ctor_raw_reload_with_shape source blockShape memberAt ctorAt ctorIndex
      stored built planned image rawImage frame.2.1 varsBounded levelsDefined loaded
      (good.sub subset) blockRep keyed selfKeyed
      (fun a bytes hashed hashEq => blobReads a bytes (Core.hashed_mono subset hashed) hashEq)
  have shape : value = .construct Core.kciEnum "Ctor"
      [.field (levels : F), typePtr, parentPtr, .field i, .field j,
        .field (params : F), .field (row.2.2 : F), .field 0] := by
    simpa [levelCount, paramCount, fieldsCount, safe, L1.repBoolField] using valueShape
  refine ⟨typePtr, parentPtr, parent, valueAt.trans (congrArg Except.ok shape), parentRep, parentEq, ?_, ?_⟩
  · intro d Γ
    simpa only [stored.2.1, Decl.posOf_range] using rawAt _ _ _ _ _ _ _ _ shape d Γ
  · simpa only [shape, paramCount, fieldsCount] using represented

end IxVM.Refinement.Assembly
