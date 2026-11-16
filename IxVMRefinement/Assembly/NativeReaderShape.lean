import IxVMRefinement.Assembly.NativeReaderInputs
import Ix.CompileCert.ReaderIndex

/-! # Reader order for a block with one inductive member

The index builder validates its motive order against the stored member list. For a block
with one inductive, that order is the actual member index, including a nonzero index.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel.Reader

/-- A validated singleton order is the singleton member's actual position. -/
theorem native_singleton_order (member : Nat) (ind : Ixon.Inductive) (order : Array Nat)
    (firstIndex : Nat)
    (valid : Ix.CompileCert.ReaderIndex.orderValid firstIndex #[(member, ind)] order = true) :
    order = #[member] := by
  simp only [Ix.CompileCert.ReaderIndex.orderValid, Bool.and_eq_true] at valid
  have count : order.size = 1 := by simpa using valid.1.1.1
  obtain ⟨index, rfl⟩ := Ix.CompileCert.ReaderIndex.array_one order count
  have position : member = index := by simpa using valid.1.2
  rw [← position]

/-- The actual index, or the reader's unindexed singleton case, fixes the one-family order. -/
theorem native_reader_one_order {cx : Ctx .anon} {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {shape : BlockShape}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (shapeRun : blockShapeOf cx.index owner members = some shape) : shape.order = #[member] := by
  unfold blockShapeOf at shapeRun
  cases indexed : cx.index.blocks[owner]? with
  | some actual =>
    rw [indexed] at shapeRun
    injection shapeRun with shapeEq
    subst actual
    have built : (buildIndex cx.store records).blocks[owner]? = some shape := by
      simpa only [indexBuilt] using indexed
    obtain ⟨constant, ms, firstIndex, first, found, info, _, initialIndex, guarded⟩ :=
      Ix.CompileCert.ReaderIndex.buildIndex_shapes cx.store records owner shape built
    have constantEq := Option.some.inj (found.symm.trans stored)
    subst constant
    have membersEq := Ixon.ConstantInfo.muts.inj (info.symm.trans kind)
    subst ms
    rw [one] at guarded
    exact native_singleton_order member ind shape.order initialIndex guarded
  | none =>
    rw [indexed] at shapeRun
    rcases members with ⟨values⟩
    cases values with
    | nil => simp [unindexedShape] at shapeRun
    | cons head tail =>
      cases tail with
      | cons _ _ => simp [unindexedShape] at shapeRun
      | nil =>
        cases head with
        | defn _ | recr _ => simp [unindexedShape] at shapeRun
        | indc first =>
          simp only [unindexedShape, Option.some.injEq] at shapeRun
          subst shape
          rw [Ix.CompileCert.ReaderIndex.singleton_inductives] at one
          have pair : (0, first) = (member, ind) :=
            (List.cons.inj (congrArg Array.toList one)).1
          have position := congrArg Prod.fst pair
          cases position
          rfl

/-- A successful full reader supplies the exact constructor frames of its one native family,
with no caller-selected motive order. -/
theorem readInductive_one_family_frames {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon) (block : BlockRead .anon),
      result.decls.toList = generated ++ bare.decls.toList ∧ lowerInductiveBare block = .ok bare ∧
      List.Forall₂
        (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots [(member, ind)]) block.ctors.toList := by
  obtain ⟨generated, bare, shape, block, declarations, shapeRun, lowered, frames⟩ :=
    readInductive_checked_ctor_frames read
  have order := native_reader_one_order indexBuilt stored kind one shapeRun
  refine ⟨generated, bare, block, declarations, lowered, ?_⟩
  rw [order, Array.toList_filterMap] at frames
  simpa only [List.filterMap_cons, List.filterMap_nil, memberAt] using frames

end IxVM.Refinement.Assembly
