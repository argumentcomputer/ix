import IxVMRefinement.Assembly.NativeFormerInputs
import IxVMRefinement.Assembly.ClaimsL1L6
import IxVMRefinement.Assembly.RawQueryCoverage
import IxVMRefinement.Assembly.NativePeerInputs
import IxVMRefinement.Decl.NativePrelude

/-! # Native inductive inputs from actual walked member checks

A walked member check already computes and hashes its projection address before loading and
checking the member. Retaining that hash identifies the actual inductive projection record
without a separately supplied projection-shape premise.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The actual walked member projection hashes the canonical inductive wrapper. -/
theorem native_member_projection_hashed {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (bounded : IxVM.Consistency.Bounded calls) :
    Hashed calls (Ixon.serConstant ⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩) := by
  obtain ⟨_, projectionBefore, _, _, _, _, membersPtr, blockPtr, _, _, _, _,
    projectionCalls, _, _, represented, blockRep, projected, projectionMember, projectionSubset, _⟩ := checked
  have memberCount : members.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt bounded projectionMember (List.Mem.head _) represented
  have slotBound : slot < members.toList.length := by
    simpa only [Array.length_toList] using (Array.getElem?_eq_some_iff.mp memberAt).1
  have slotValue : ZMod.val (slot : F) = slot :=
    ZMod.val_natCast_of_lt (by
      have modulus : (2 ^ 39 : Nat) < Aiur.Library.U32.Goldilocks.modulus := by decide
      omega)
  obtain ⟨actualBlock, actualBlockRep, sameBlock⟩ := blockRep
  have same : actualBlock = block := Decl.ixAddr_inj sameBlock
  subst actualBlock
  obtain ⟨_, _, _, actualMember, _, found, _, _, hashed⟩ :=
    L1.projection_addr_hashed_spec represented actualBlockRep projected
  rw [slotValue] at found hashed
  have foundExpected : members.toList[slot]? = some (.indc ind) := by simpa using memberAt
  rw [foundExpected] at found
  injection found with sameMember
  subst actualMember
  exact Core.hashed_mono projectionSubset hashed

/-- The actual member check supplies both a checked projection invocation and its canonical
source record in the trace-backed metadata store. -/
theorem native_member_checked_source {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (good : Core.Good base calls)
    (coverage : L1.CanonicalHashCoverage base.E calls) :
    ∃ projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) slot),
      projection.value = ⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩ ∧
      Claim.CheckedAtFull calls bindingAddr base.t (Core.iprjAddr (Core.ixAddr block) slot) := by
  have hashed := native_member_projection_hashed (base := base) (block := block)
    (members := members) (slot := slot) (ind := ind) checked memberAt good.2
  have fullGeneric := mutsMemberCheckedAtFull_to_checkedAtFull (addr := Core.ixAddr block)
    (ms := members) (k := slot) (mc := .indc ind) good.2 checked memberAt
  have full : Claim.CheckedAtFull calls bindingAddr base.t (Core.iprjAddr (Core.ixAddr block) slot) := by
    simpa only [Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using fullGeneric
  have fullProof := full
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, addressRep, _, loaded, _, loadSubset, _, _, _, _⟩ := full
  obtain ⟨address, represented, addressEq⟩ := addressRep
  obtain ⟨_, _, _, verified, verifiedSubset⟩ := L1.get_ci_verified_subcall loaded
  obtain ⟨source⟩ := L1.canonicalRecordAt_of_verified coverage represented verified
    (fun call member => loadSubset call (verifiedSubset call member))
  let projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) slot) :=
    source.reindex addressEq.symm
  have bytesEq := Core.load_escape (E := base.E) (x := Core.iprjAddr (Core.ixAddr block) slot)
    projection.stored good.1
    (Ixon.serConstant ⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩) hashed rfl
  have decoded := projection.decoded
  rw [← bytesEq] at decoded
  have canonical := Ixon.Verify.deConstantExact_serConstant
    (⟨.iPrj ⟨slot.toUInt64, Core.ixAddr block⟩, #[], #[], #[], #[]⟩ : Ixon.Constant)
    (L1.projConstant_wireWF_iPrj slot.toUInt64 block)
  exact ⟨projection, Except.ok.inj (decoded.symm.trans canonical), fullProof⟩

/-- A former value and its actual check prelude, retaining the annotation's conversion origin. -/
structure NativeFormerRunInput (base : Core.Ctx) (block : Bytes.Address) (i : F)
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (members : Array Ixon.MutConst) (ind : Ixon.Inductive) (rawType : Core.KExpr)
    (calls : List (Call F)) where
  limit : Nat
  rc : SourceValue F
  typePtr : SourceValue F
  blockPtr : SourceValue F
  heap : Heap F
  annotated : Ix.Kernel.ConstantVal .anon
  prelude : Decl.NativePreludeCalls rc (.field (ind.lvls.toNat : F)) typePtr blockPtr heap calls
  roles : Core.RCRep base.t (some limit) heap rc
  blockRep : Bytes.RepAddressRef Core.addrTy heap block blockPtr
  stored : IxVM.Consistency.ValStored annotated
    ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩
  represented : Decl.ValRepExact base.κ heap (.field (ind.lvls.toNat : F)) typePtr annotated
  varsBounded : rawType.looseBVarsBounded 0 = true
  levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true
  noFvars : rawType.hasFvar = false
  tree : L1.BinderTreeData
  plan : List Core.KLevel
  built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree
  planned : L1.binderRootPlan tree source.value.sharing.toList
    ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan
  image : L1.applyBinderTrace
    (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
      some (annotated.type, [])

/-- The paired actual load/check witness constructs the former's annotation and prelude.
Capability data is passed through the representation proof; no stage capability is inferred. -/
theorem native_former_input_of_checked {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {index : UInt64} {calls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (projection : L1.CanonicalRecordAt base.E (Core.iprjAddr (Core.ixAddr block) index.toNat))
    (projectionShape : projection.value.info = .iPrj ⟨index, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[index.toNat]? = some (.indc ind))
    (checked : Claim.CheckedAtFull calls bindingAddr base.t
      (Core.iprjAddr (Core.ixAddr block) index.toNat))
    (good : Core.Good base calls)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ slot address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[slot]? = some address →
      self slot = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    Nonempty (NativeFormerRunInput base block (index.toNat : F) source members ind rawType calls) := by
  obtain ⟨limit, beforeLoad, checkHeap, afterCheck, rc, addr, ptr, value, result, loadCalls, checkCalls,
    _, roles, addressRep, _, loaded, _, loadSubset, valueAt, checkedRun, _, checkSubset⟩ := checked
  obtain ⟨address, addressRep, addressEq⟩ := addressRep
  let projectionAt := projection.reindex addressEq
  have projectionAtShape : projectionAt.value.info = .iPrj ⟨index, Core.ixAddr block⟩ := projectionShape
  obtain ⟨parent, parentArg, middle, inner, parentEq, indexBound, parentRep, directLoad, innerSubset, _⟩ :=
    L1.get_ci_iPrj_subcall (base := base) projectionAt projectionAtShape addressRep
      (good.sub loadSubset) loaded
  have parentSame : parent = block := Decl.ixAddr_inj parentEq
  subst parent
  have indexValue : ZMod.val (index.toNat : F) = index.toNat :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have memberAtField : members.toList[ZMod.val (index.toNat : F)]? = some (.indc ind) := by
    rw [indexValue]
    simpa only [Array.getElem?_toList] using memberAt
  have directSubset : ∀ call ∈ inner, call ∈ calls :=
    fun call member => loadSubset call (innerSubset call member)
  obtain ⟨typePtr, blockPtr, actualBlock, payload, blockRep, blockEq⟩ :=
    native_former_header_exact (base := base) source blockShape memberAtField
      (good.sub directSubset) parentRep directLoad
  have blockSame : actualBlock = block := Decl.ixAddr_inj blockEq
  subst actualBlock
  have valueEq := Except.ok.inj (valueAt.symm.trans payload)
  subst value
  obtain ⟨localPrelude⟩ := Decl.native_prelude_calls checkedRun
  let prelude := localPrelude.mono checkSubset
  obtain ⟨annotated, tree, plan, stored, exactInput, built, planned, image,
    varsBounded, levelsDefined, noFvars⟩ :=
    observed_native_former_input (base := base) (calls := calls) source blockShape memberAtField caps
      directLoad (good.sub directSubset) parentRep payload prelude.initialExtended good.2
      prelude.scopeRun prelude.scopeMember read keyed selfKeyed
      (fun address bytes hashed hashEq => blobReads address bytes (Core.hashed_mono directSubset hashed) hashEq)
  obtain ⟨exactValue, exactAt, exactInfo⟩ := exactInput
  have sameValue := Except.ok.inj (exactAt.symm.trans payload)
  subst exactValue
  exact ⟨{
    limit := limit, rc := rc, typePtr := typePtr, blockPtr := blockPtr, heap := checkHeap
    annotated := annotated, prelude := prelude, roles := roles.toRCRep, blockRep := blockRep
    stored := stored, represented := Decl.CIRepExact.induct_valRep exactInfo
    varsBounded := varsBounded, levelsDefined := levelsDefined, noFvars := noFvars
    tree := tree, plan := plan, built := built, planned := planned, image := image }⟩


/-- The walked member's actual list representation bounds its natural slot. -/
theorem native_member_slot_bound {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (memberAt : members[slot]? = some (.indc ind)) (bounded : IxVM.Consistency.Bounded calls) :
    slot < 549755813888 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, represented, _, _, member, _⟩ := checked
  have length : members.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt bounded member (List.Mem.head _) represented
  have index : slot < members.toList.length := by
    simpa only [Array.length_toList] using (Array.getElem?_eq_some_iff.mp memberAt).1
  exact Nat.lt_trans index length

set_option maxRecDepth 4096 in
/-- The actual walked inductive member constructs its former input without a supplied
projection source, header representation, annotation or prelude witness. -/
theorem native_former_input_of_member {base : Core.Ctx} {bindingAddr : _root_.Address}
    {block : Bytes.Address} {members : Array Ixon.MutConst} {slot : Nat} {ind : Ixon.Inductive}
    {calls : List (Call F)}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (blockShape : source.value.info = .muts members)
    (memberAt : members[slot]? = some (.indc ind))
    (checked : Claim.MutsMemberCheckedAtFull calls bindingAddr base.t (Core.ixAddr block) members slot)
    (good : Core.Good base calls) (coverage : L1.CanonicalHashCoverage base.E calls)
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)} {rawType : Core.KExpr}
    (caps : Ix.Kernel.IndCaps .anon)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (keyed : ∀ address key, cx.keyAt address = .ok key → key = base.κ address)
    (selfKeyed : ∀ index address reading key,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[index]? = some address →
      self index = some reading → reading = .ok key → key = base.κ address)
    (blobReads : ∀ address bytes, Hashed calls bytes → Address.blake3Pure bytes = address →
      cx.blob address = some bytes) :
    Nonempty (NativeFormerRunInput base block (slot : F) source members ind rawType calls) := by
  have slotBound := native_member_slot_bound (base := base) checked memberAt good.2
  have indexNat : slot.toUInt64.toNat = slot :=
    UInt64.toNat_ofNat_of_lt (Nat.lt_trans slotBound (by decide))
  obtain ⟨projection, shape, full⟩ := native_member_checked_source (base := base) checked memberAt good coverage
  let indexedProjection := projection.reindex
    (congrArg (Core.iprjAddr (Core.ixAddr block)) indexNat)
  have projectedInfo : indexedProjection.value.info = .iPrj ⟨slot.toUInt64, Core.ixAddr block⟩ :=
    congrArg Ixon.Constant.info shape
  have indexedMember : members[slot.toUInt64.toNat]? = some (.indc ind) := by
    rwa [indexNat]
  have indexedFull : Claim.CheckedAtFull calls bindingAddr base.t
      (Core.iprjAddr (Core.ixAddr block) slot.toUInt64.toNat) :=
    (congrArg (fun index => Claim.CheckedAtFull calls bindingAddr base.t
      (Core.iprjAddr (Core.ixAddr block) index)) indexNat).mpr full
  have produced := native_former_input_of_checked (base := base) (block := block) (index := slot.toUInt64)
    source indexedProjection projectedInfo
    blockShape indexedMember indexedFull good caps read keyed selfKeyed blobReads
  simpa only [indexNat] using produced

/-- The constructed input checks the former at the actual role limit of its observed run. -/
theorem NativeFormerRunInput.checked {base : Core.Ctx} {block : Bytes.Address} {i : F}
    {source : L1.CanonicalRecordAt base.E (Core.ixAddr block)}
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive} {rawType : Core.KExpr} {calls : List (Call F)}
    (input : NativeFormerRunInput base block i source members ind rawType calls)
    (facts : Core.CoreEnvFacts { base with lim := some input.limit }) (good : Core.Good base calls)
    (fresh : base.env.find? (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = none)
    (notBasis : Ix.Kernel.reservedBasisNames.contains
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = false)
    (loads : Core.ScopedLoadFacts
      (Decl.nativeFormerCheckCtx { base with lim := some input.limit } input.prelude)) :
    Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ base.env
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩
      input.annotated ∧
      ∃ type level observedLevel,
        Ix.Kernel.Rules.Infer base.env .full 0 input.annotated.type type ∧
        Ix.Kernel.Rules.Red base.env 0 type (.sort level) ∧
        KernelLevels.RepKLevel input.prelude.sortAfter observedLevel input.prelude.sortResult ∧
        Core.LvEq level observedLevel :=
  input.prelude.checked (base := { base with lim := some input.limit })
    input.stored input.represented input.varsBounded input.noFvars fresh notBasis
    (Decl.nat_keyOf_isProjFnShape_false base.t _) facts good input.roles loads


end IxVM.Refinement.Assembly
