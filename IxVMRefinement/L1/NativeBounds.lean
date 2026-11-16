import IxVMRefinement.L1.ScopedRecords
import IxVMRefinement.Core.CallHeaps

/-! # Native header bounds from actual conversion

The converter checks level and count words, while the observed constructor-list count is
bounded by the trace's ROM. These are data bounds, independent of semantic installation.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Deserialize

/-- An actual inductive conversion supplies its header bounds and the tighter ROM bound on
its constructor count. -/
theorem convert_inductive_header_bounds {ind : Ixon.Inductive}
    {indValue blockArg index sharing refs recur univs table root result : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (bounded : IxVM.Consistency.Bounded calls) (represented : RepInductive h ind indValue)
    (converted : ObsFn Core.W "Convert::convert_inductive"
      [indValue, blockArg, index, sharing, refs, recur, univs, table, root] h result h' calls) :
    ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
      ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 549755813888 := by
  obtain ⟨typePtr, ctorPtr, rfl, _, ctors⟩ := represented
  match Obs.«Convert::convert_inductive».obs converted with
  | .run (x_lvls := levelArg) (x_params := paramsArg) (x_indices := indicesArg)
      (x_ctors := ctorsArg) (m177 := countHeap) (hv15 := fields)
      (ev140 := levelRun) (ev167 := paramsRun) (ev187 := indicesRun) (ev207 := countRun)
      (hc238 := allCalls) .. =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at fields
    obtain ⟨_, _, _, levelEq, paramsEq, indicesEq, _, ctorsEq⟩ := fields
    subst levelArg paramsArg indicesArg ctorsArg
    have levels := (lvls_to_field_spec ind.lvls.toNat_lt levelRun).1
    have params := (Lib.u64_to_field_spec (repU64_u64Value _ ind.params) paramsRun).1
    have indices := (Lib.u64_to_field_spec (repU64_u64Value _ ind.indices) indicesRun).1
    have member : (⟨"Convert::count_ctors", [ctorPtr], countHeap⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    have present := ctors.mono repConstructor_heapMono₂ (converted.call_heap_bounds member).1
    have count := RomBound.bounded_length_lt bounded member (by simp) present
    exact ⟨levels, params, indices, by simpa only [Array.length_toList] using count⟩

/-- The actual former projection load provides all native header bounds for its canonical
member; no separately supplied count certificate is needed. -/
theorem get_ci_iprj_header_bounds {base : Core.Ctx} {block : Bytes.Address} {i : F}
    (source : CanonicalRecordAt base.E (Core.ixAddr block))
    {members : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (shape : source.value.info = .muts members)
    (memberAt : members.toList[ZMod.val i]? = some (.indc ind))
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : Core.Good base calls) (blockRep : Bytes.RepAddressRef Core.addrTy h block bp)
    (loaded : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' calls) :
    ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
      ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 549755813888 := by
  match Obs.«Ingress::get_ci_iprj».obs loaded with
  | .run (m86 := afterMember) (ev14 := decoded) (ev98 := memberRun) (ev149 := recurRun)
      (ev246 := tableRun) (ev266 := offsetRun) (ev176 := converted) (hc283 := allCalls) .. =>
    obtain ⟨_, info, sh, rf, un, bd, fields, infoRep, _, _, _, _⟩ :=
      load_verified_constant_of_record source blockRep
        (good.sub (by rw [allCalls]; intro call member; simp [member])) decoded
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at fields
    obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩ := fields
    rw [shape] at infoRep
    obtain ⟨membersPtr, infoShape, membersRep⟩ := infoRep
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at infoShape
    subst membersPtr
    obtain ⟨sameHeap, _, actual, found, actualRep⟩ := muts_member_at_spec membersRep memberRun
    subst afterMember
    rw [memberAt] at found
    injection found with same
    subst actual
    obtain ⟨value, valueShape, indRep⟩ := actualRep
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at valueShape
    subst value
    have extended := recurRun.heap_extends.trans (tableRun.heap_extends.trans offsetRun.heap_extends)
    exact convert_inductive_header_bounds
      (RomBound.bounded_mono good.2 (by rw [allCalls]; intro call member; simp [member]))
      (indRep.mono extended) converted

end IxVM.Refinement.L1
