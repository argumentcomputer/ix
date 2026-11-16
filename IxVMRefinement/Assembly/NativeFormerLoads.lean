import IxVMRefinement.Assembly.NativeFormerInputs
import IxVMRefinement.Assembly.ProjSafe

/-! # Actual former loads in the native stage

The decoder guard fixes an observed former projection's canonical address. Repeated reads
then agree with the former installed at the constructor stage, using its supplied capability
data and the annotation already derived from the original conversion trace.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KKey KExpr)

/-- A successful former projection load has the canonical empty-table projection address
and the checked member-index bound. -/
theorem native_former_projection_address {base : Core.Ctx} {address : Bytes.Address}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr address))
    {projection : Ixon.InductiveProj} (shape : source.value.info = .iPrj projection)
    {addr ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (loaded : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' calls)
    (good : Core.Good base calls) (addressRep : Bytes.RepAddressRef Core.addrTy h address addr) :
    projection.idx.toNat < 72057594037927936 ∧
      Core.ixAddr address = Core.iprjAddr projection.block projection.idx.toNat := by
  obtain ⟨_, bytes, value, _, hashed, hashEq, decoded, _, tables, _, result⟩ :=
    L1.get_ci_spec good.2 addressRep loaded
  have bytesEq := Core.load_escape source.stored good.1 bytes hashed hashEq
  rw [bytesEq, source.decoded] at decoded
  injection decoded with valueEq
  subst value
  have tableFields := tables
  rw [L1.ConstantTablesValid, shape] at tableFields
  have empty : Ix.Kernel.Reader.emptyTables source.value = true := by
    simp [Ix.Kernel.Reader.emptyTables, tableFields.1, tableFields.2.1,
      tableFields.2.2.1, tableFields.2.2.2]
  have encoded := (deConstantExact_proj_eq_serConstant source.decoded empty
    (by rw [shape]; trivial)).1
  have constantShape := Ix.Cert.ReadingKeys.empty_constant empty
  rw [shape] at constantShape
  have atProjection : Core.ixAddr address = Core.projAddr (.iPrj projection) := by
    rw [bytesEq, encoded, constantShape] at hashEq
    exact hashEq.symm
  have indexRoundtrip : projection.idx.toNat.toUInt64 = projection.idx :=
    UInt64.toNat_inj.mp (UInt64.toNat_ofNat_of_lt projection.idx.toNat_lt)
  have infoEq : Ixon.ConstantInfo.iPrj projection =
      .iPrj ⟨projection.idx.toNat.toUInt64, projection.block⟩ := by
    rw [indexRoundtrip]
  unfold L1.GetCIRawResult at result
  rw [shape] at result
  exact ⟨result.1, atProjection.trans (congrArg Core.projAddr infoEq)⟩

/-- The actual repeated former reading supplies the semantic load result in its installed stage. -/
theorem native_former_reload_staged {base : Core.Ctx} {block : Bytes.Address} {i : F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)), List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val i) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {blockArg ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [blockArg, .field i] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (blockRep : Bytes.RepAddressRef Core.addrTy h block blockArg)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ ci, (⟨.indInfo cv caps :: base.env.consts⟩ : Ix.Kernel.Env .anon).find?
      (base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i))) = some ci ∧ Core.CIPtrRep base.κ h' ptr ci := by
  have represented := native_former_reload (base := base) source blockShape memberAt stored built planned image
    read varsBounded levelsDefined caps loaded goodLoad blockRep keyed selfKeyed blobReads
  refine ⟨.indInfo cv caps, ?_, represented.toCIPtrRep⟩
  rw [Ix.Kernel.Env.find?_cons]
  apply ite_eq_left
  exact stored.1

/-- The actual repeated former reading supplies the semantic load result in its installed stage. -/
theorem native_former_getCI_reload_staged {base : Core.Ctx} {block address : Bytes.Address}
    {index : UInt64}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    (projectionSource : L1.CanonicalRecordAt base.E (Core.ixAddr address))
    (projectionShape : projectionSource.value.info = .iPrj ⟨index, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val (index.toNat : F)]? = some (.indc ind))
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {rawType : KExpr}
    {cv : Ix.Kernel.ConstantVal .anon} {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (stored : IxVM.Consistency.ValStored cv
      ⟨base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val (index.toNat : F))),
        List.range ind.lvls.toNat, rawType⟩)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData source.value.binders.toList) tree)
    (planned : L1.binderRootPlan tree source.value.sharing.toList
      ((L1.mutsRootOffset members.toList (ZMod.val (index.toNat : F)) : Nat) : F) ind.typ = some plan)
    (image : L1.applyBinderTrace
      (fun level => Core.bmeta (L1.invPosLevel (List.range ind.lvls.toNat) level)) rawType plan =
        some (cv.type, []))
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx source.value id self).read ind.typ = .ok rawType)
    (varsBounded : rawType.looseBVarsBounded 0 = true)
    (levelsDefined : rawType.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    {h h' : Heap F} {addr ptr : SourceValue F} {calls : List (Call F)}
    (caps : Ix.Kernel.IndCaps .anon)
    (loaded : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' calls)
    (goodLoad : Core.Good base calls)
    (addressRep : Bytes.RepAddressRef Core.addrTy h address addr)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = base.κ a)
    (selfKeyed : ∀ k a m name,
      (L1.blockRecurAddrs (Core.ixAddr block) members.toList)[k]? = some a →
      self k = some m → m = .ok name → name = base.κ a)
    (blobReads : ∀ a bytes, Hashed calls bytes → Address.blake3Pure bytes = a →
      cx.blob a = some bytes) :
    ∃ ci, (⟨.indInfo cv caps :: base.env.consts⟩ : Ix.Kernel.Env .anon).find?
      (base.κ (Core.ixAddr address)) = some ci ∧ Core.CIPtrRep base.κ h' ptr ci := by
  have represented := native_former_getCI_reload (base := base) source projectionSource projectionShape
    blockShape memberAt stored built planned image read varsBounded levelsDefined caps
    loaded goodLoad addressRep keyed selfKeyed blobReads
  obtain ⟨indexBound, atProjection⟩ := native_former_projection_address (base := base)
    projectionSource projectionShape loaded goodLoad addressRep
  have indexValue : ZMod.val (index.toNat : F) = index.toNat :=
    ZMod.val_natCast_of_lt (Nat.lt_trans indexBound (by decide))
  have keyEq : base.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val (index.toNat : F))) =
      base.κ (Core.ixAddr address) :=
    congrArg base.κ ((congrArg (Core.iprjAddr (Core.ixAddr block)) indexValue).trans atProjection.symm)
  have nameEq : cv.name = base.κ (Core.ixAddr address) := stored.1.trans keyEq
  refine ⟨.indInfo cv caps, ?_, represented.toCIPtrRep⟩
  rw [Ix.Kernel.Env.find?_cons]
  apply ite_eq_left
  exact nameEq

end IxVM.Refinement.Assembly
