import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Assembly.NativeBlockShape
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.L1.NativeBounds

/-! # Native peer facts from actual projection reads

Canonical parent bytes fix the loaded member. The successful outer projection read supplies
its empty-table guard and hash, so only existing inductive members can be peers of the unique
native family. No condition is imposed on unrelated stored projection records.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- A successful direct former read has the exact header of its canonical member. -/
theorem native_former_header_of_record {base : Core.Ctx} {block : Bytes.Address} {i : F}
    (source : L1.CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : Core.Good base calls) (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' calls) :
    ∃ (ty unsafeFlag parentPtr : SourceValue F) (parent : Bytes.Address),
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [.field (ind.lvls.toNat : F), ty, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F), unsafeFlag, parentPtr, .field i]) ∧
      Bytes.RepAddressRef Core.addrTy h' parent parentPtr ∧ Core.ixAddr parent = Core.ixAddr block := by
  obtain ⟨_, _, bytes, src, ms, member, _, value, hashed, address, decoded, _,
    shape, atMember, _, valueAt, raw⟩ := L1.get_ci_iprj_spec good.2 blockRep loaded
  have bytesEq := Core.load_escape source.stored good.1 bytes hashed address
  rw [bytesEq, source.decoded] at decoded
  injection decoded with sourceEq
  subst src
  rw [blockShape] at shape
  injection shape with membersEq
  subst ms
  rw [memberAt] at atMember
  injection atMember with memberEq
  injection memberEq with memberEq
  subst member
  obtain ⟨_, _, _, _, _, ty, parentPtr, parent, parentEq, parentRep, valueShape, _⟩ := raw
  refine ⟨ty, L1.repBoolField ind.isUnsafe, parentPtr, parent, ?_, parentRep, parentEq⟩
  simpa only [ZMod.natCast_zmod_val] using valueAt.trans (congrArg Except.ok valueShape)

set_option maxHeartbeats 800000 in
/-- The actual one-family block and canonical former projection supply raw peer facts at
its real member index. Projection identities use the successful read's decoder guard. -/
theorem native_peer_reads {raw : Core.ScopedCtx} {block : Bytes.Address} {i : F}
    (source : L1.CanonicalRecordAt raw.E (Core.ixAddr block))
    (former : L1.CanonicalRecordAt raw.E (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
    (formerShape : former.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩)
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (blockShape : source.value.info = .muts members)
    (memberAt : members[ZMod.val i]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(ZMod.val i, ind)])
    (tableWf : raw.t.wf = true) :
    Decl.OneTypePeerReads raw block (raw.κ (Core.iprjAddr (Core.ixAddr block) (ZMod.val i)))
      ind.lvls.toNat ind.params.toNat ind.indices.toNat ind.ctors.size i := by
  refine ⟨rfl, ?_, ?_⟩
  ·
    intro addr ptr h h' calls a loaded good addressRep sameKey
    have addressEq : Core.ixAddr a = Core.iprjAddr (Core.ixAddr block) (ZMod.val i) :=
      Decl.nat_keyOf_injective (t := raw.t) tableWf
        (a₁ := Core.ixAddr a) (a₂ := Core.iprjAddr (Core.ixAddr block) (ZMod.val i)) sameKey
    have formerAt : L1.CanonicalRecordAt raw.E (Core.ixAddr a) :=
      { entry := former.entry, value := former.value
        stored := (congrArg (fun address => raw.E.consts.get? address) addressEq).trans former.stored
        cached := former.cached, decoded := former.decoded }
    have projection : formerAt.value.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr block⟩ := by
      change former.value.info = _
      exact formerShape
    obtain ⟨parent, blockArg, middle, inner, parentEq, _, parentRep, observed, subset, _⟩ :=
      L1.get_ci_iPrj_subcall (base := raw.toCtx) formerAt projection addressRep good loaded
    have parentSame : parent = block := Decl.ixAddr_inj parentEq
    subst parent
    have index64 : ZMod.val i < UInt64.size :=
      Nat.lt_trans (ZMod.val_lt i) (by decide)
    have castIndex : (((ZMod.val i).toUInt64.toNat : Nat) : F) = i := by
      rw [UInt64.toNat_ofNat_of_lt index64]
      exact ZMod.natCast_zmod_val i
    rw [castIndex] at observed
    exact native_former_header_of_record (base := raw.toCtx) source blockShape
      (by simpa only [Array.getElem?_toList] using memberAt) (good.sub subset) parentRep observed
  ·
    intro addr ptr h h' calls a nl ty np ni nc u blk idx parent loaded _ good addressRep
      payload parentRep parentEq
    obtain ⟨bytes, blockBytes, cm, cb, xs, actual, parent', actualIndex, hashed, address,
      decoded, _, blockHashed, blockAddress, blockDecoded, _, parentRep', _, _,
      projection, blockInfo, atMember, tables⟩ :=
      L1.inductRecord_raw_tables_of_get_ci loaded good.2 addressRep payload
    have parentSame : parent' = parent :=
      Bytes.repAddressRef_inj U32.Goldilocks.compatible parentRep' parentRep
    subst parent'
    have blockBytesEq := Core.load_escape source.stored good.1 blockBytes blockHashed
      (blockAddress.trans parentEq)
    rw [blockBytesEq, source.decoded] at blockDecoded
    injection blockDecoded with sameBlock
    subst cb
    rw [blockShape] at blockInfo
    injection blockInfo with sameMembers
    subst xs
    have present : (ZMod.val actualIndex, actual) ∈ Ix.CompileCert.ReaderIndex.inductives members := by
      apply Array.mem_filterMap.mpr
      exact ⟨(.indc actual, ZMod.val actualIndex), Array.mk_mem_zipIdx_iff_getElem?.mpr atMember, rfl⟩
    rw [one] at present
    have sameEntry : (ZMod.val actualIndex, actual) = (ZMod.val i, ind) := by simpa using present
    have sameIndex := congrArg Prod.fst sameEntry
    have tableFields := tables
    rw [L1.ConstantTablesValid, projection] at tableFields
    have empty : Ix.Kernel.Reader.emptyTables cm = true := by
      simp [Ix.Kernel.Reader.emptyTables, tableFields.1, tableFields.2.1,
        tableFields.2.2.1, tableFields.2.2.2]
    have encoded := (deConstantExact_proj_eq_serConstant decoded empty
      (by rw [projection]; trivial)).1
    have constantShape := Ix.Cert.ReadingKeys.empty_constant empty
    rw [projection] at constantShape
    have projectionAddress : Core.ixAddr a = Core.iprjAddr (Core.ixAddr parent) (ZMod.val actualIndex) := by
      rw [encoded, constantShape] at address
      exact address.symm
    exact congrArg raw.κ (projectionAddress.trans (congrArg₂ Core.iprjAddr parentEq sameIndex))

end IxVM.Refinement.Assembly
