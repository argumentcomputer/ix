import IxVMRefinement.Assembly.NativeReaderShape
import IxVMRefinement.Ingress.ScopedRecords
import IxVMRefinement.Callees.Modeled

/-! # One-family shape from the actual native route

The unmodeled answer and canonical block load establish that the block has at most one
inductive. A known inductive member then fixes the reader's unique indexed family.
-/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- The native route's actual answer bounds the decoded block's inductive count. -/
theorem native_block_inductive_count {base : Core.Ctx} {block : Bytes.Address}
    (source : Ingress.CanonicalRecordAt base.E (Core.ixAddr block)) {members : Array Ixon.MutConst}
    (shape : source.value.info = .muts members)
    {bp : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : Core.Good base calls) (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (observed : ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' calls) :
    (members.toList.filter Core.isIndc).length ≤ 1 := by
  have loadedShape : ∀ {value : SourceValue F} {middle : Heap F} {cs : List (Call F)},
      ObsFn Core.W "Ingress::load_verified_constant" [bp] h value middle cs →
      (∀ call ∈ cs, call ∈ calls) → Core.Specs.Callees.ConstShapeRep middle source.value value := by
    intro value middle cs loaded subset
    exact (Ingress.load_verified_constant_of_record source blockRep (good.sub subset) loaded).2.toConstShapeRep
  have memberRep : ∀ {middle : Heap F} {cs : List (Call F)}
      {sharing refs univs binders ptr : SourceValue F},
      ObsFn Core.W "Ingress::load_verified_constant" [bp] h
        (.construct "Ixon::Constant" "Mk"
          [.construct "Ixon::ConstantInfo" "Muts" [ptr], sharing, refs, univs, binders]) middle cs →
      (∀ call ∈ cs, call ∈ calls) → Core.Specs.Callees.MembersRep middle members.toList ptr := by
    intro middle cs sharing refs univs binders ptr loaded subset
    obtain ⟨info, sh, rf, un, bd, fields, infoRep⟩ := loadedShape loaded subset
    injection fields with _ _ entries
    injection entries with infoEq _
    subst info
    obtain ⟨actual, actualShape, rep⟩ := Core.ModeledAux.infoShape_muts_inv infoRep
    have same := Ixon.ConstantInfo.muts.inj (actualShape.symm.trans shape)
    subst actual
    exact rep
  match Obs.«KernelModeled::block_is_modeled».obs observed with
  | .Muts_n0 (m2 := middle) (x_members := ptr) (ev14 := loaded) (ev103 := counted)
      (hc118 := allCalls) .. =>
    have rep := memberRep loaded (by rw [allCalls]; intro call member; simp [member])
    have countCall : (⟨"KernelModeled::muts_indc_count", [ptr], middle⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    have length := RomBound.bounded_length_lt good.2 countCall (by simp) rep
    have filtered := Nat.lt_of_le_of_lt (List.length_filter_le Core.isIndc members.toList) length
    obtain ⟨countedEq, _⟩ := Core.ModeledAux.muts_indc_count_spec rep counted
    have zero : (members.toList.filter Core.isIndc).length = 0 :=
      (Core.ModeledAux.natCast_inj_lt (a := 0) (by decide) filtered
        (by simpa using Value.field.inj countedEq)).symm
    omega
  | .Muts_n1 (m2 := middle) (x_members := ptr) (ev14 := loaded) (ev103 := counted)
      (hc241 := allCalls) .. =>
    have rep := memberRep loaded (by rw [allCalls]; intro call member; simp [member])
    have countCall : (⟨"KernelModeled::muts_indc_count", [ptr], middle⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    have length := RomBound.bounded_length_lt good.2 countCall (by simp) rep
    have filtered := Nat.lt_of_le_of_lt (List.length_filter_le Core.isIndc members.toList) length
    obtain ⟨countedEq, _⟩ := Core.ModeledAux.muts_indc_count_spec rep counted
    have one := (Core.ModeledAux.natCast_inj_lt (a := 1) (by decide) filtered
      (by simpa using Value.field.inj countedEq)).symm
    omega
  | .Muts_other (he246 := answer) .. =>
    exact (zero_ne_one (Value.field.inj answer)).elim
  | .other (ev14 := loaded) (hne249 := notMuts) (hc255 := allCalls) .. =>
    obtain ⟨info, sh, rf, un, bd, fields, infoRep⟩ :=
      loadedShape loaded (by rw [allCalls]; intro call member; simp [member])
    injection fields with _ _ entries
    injection entries with infoEq _
    subst info
    exact (Core.ModeledAux.infoShape_not_muts infoRep notMuts members shape).elim

private theorem native_inductives_count (members : List Ixon.MutConst) (start : Nat) :
    ((members.zipIdx start).filterMap (fun
      | (.indc ind, index) => some (index, ind)
      | _ => none)).length = (members.filter Core.isIndc).length := by
  induction members generalizing start with
  | nil => simp
  | cons head tail ih =>
    cases head <;> simp [List.zipIdx_cons, List.filter_cons, Core.isIndc, ih]

/-- The actual count bound and a present member identify the unique indexed inductive. -/
theorem native_inductives_singleton {members : Array Ixon.MutConst} {index : Nat} {ind : Ixon.Inductive}
    (few : (members.toList.filter Core.isIndc).length ≤ 1)
    (memberAt : members[index]? = some (.indc ind)) :
    Ix.CompileCert.ReaderIndex.inductives members = #[(index, ind)] := by
  have length : (Ix.CompileCert.ReaderIndex.inductives members).size =
      (members.toList.filter Core.isIndc).length := by
    rw [← Array.length_toList, Ix.CompileCert.ReaderIndex.inductives,
      Array.toList_filterMap, Array.toList_zipIdx]
    refine Eq.trans ?_ (native_inductives_count members.toList 0)
    apply congrArg List.length
    apply congrArg (fun project : Ixon.MutConst × Nat → Option (Nat × Ixon.Inductive) =>
      List.filterMap project members.toList.zipIdx)
    funext item
    rcases item with ⟨value, index⟩
    cases value <;> rfl
  have present : (index, ind) ∈ Ix.CompileCert.ReaderIndex.inductives members := by
    apply Array.mem_filterMap.mpr
    exact ⟨(.indc ind, index), Array.mk_mem_zipIdx_iff_getElem?.mpr memberAt, rfl⟩
  have nonempty : (Ix.CompileCert.ReaderIndex.inductives members).toList ≠ [] := by
    intro empty
    have member := Array.mem_toList_iff.mpr present
    rw [empty] at member
    cases member
  have positive := List.length_pos_iff.mpr nonempty
  have count : (Ix.CompileCert.ReaderIndex.inductives members).size = 1 := by
    simp only [Array.length_toList] at positive
    omega
  obtain ⟨entry, entries⟩ := Ix.CompileCert.ReaderIndex.array_one _ count
  rw [entries] at present
  have same : (index, ind) = entry := by simpa using present
  rwa [← same] at entries

end IxVM.Refinement.Assembly
