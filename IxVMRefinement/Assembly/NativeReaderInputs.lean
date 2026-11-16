import IxVMRefinement.Assembly.InductiveRead
import Ix.CompileCert.Loop

/-! # Constructor rows from the actual inductive reader

These frames expose the constructor expression reads, names, level parameters, and counts
before lowering. They are derived from the successful reader loops without a kernel-model premise.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_inv_array forall₂_append)
open Ix.Cert.ReaderUnits (ite_ok fail_bind throw_ok)

abbrev NativeCtorSlot := Nat × Ixon.Constructor × Nat
abbrev NativeCtorRow := Ix.Kernel.ConstantVal .anon × Nat × Nat

def nativeCtorSlots (members : List (Nat × Ixon.Inductive)) : List NativeCtorSlot :=
  members.flatMap fun member => member.2.ctors.zipIdx.toList.map fun slot =>
    (member.1, slot.1, slot.2)

def NativeCtorReaderFrame (cx : Ctx .anon) (owner : _root_.Address) (mr : MemberReader .anon)
    (slot : NativeCtorSlot) (row : NativeCtorRow) : Prop :=
  cx.memberKey (.ctor owner slot.1 slot.2.2) = .ok row.1.name ∧
  mr.read slot.2.1.typ = .ok row.1.type ∧
  row.1.levelParams = List.range slot.2.1.lvls.toNat ∧
  row.2.1 = slot.2.1.params.toNat ∧ row.2.2 = slot.2.1.fields.toNat

/-- The same row frame with the slot and safety guards retained from the reader. -/
def NativeCtorReaderCheckedFrame (cx : Ctx .anon) (owner : _root_.Address) (mr : MemberReader .anon)
    (slot : NativeCtorSlot) (row : NativeCtorRow) : Prop :=
  NativeCtorReaderFrame cx owner mr slot row ∧ slot.2.1.cidx.toNat = slot.2.2 ∧
    slot.2.1.isUnsafe = false

/-- The bare reader's constructor rows agree position by position with the source slots it
actually visits. The resulting block is the one passed to the real lowering function. -/
theorem readInductiveBare_checked_ctor_frames {cx : Ctx .anon} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {result : Read .anon}
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (shape : BlockShape) (block : BlockRead .anon),
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok result ∧
      List.Forall₂
        (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.ctors.toList := by
  cases shapeRun : blockShapeOf cx.index owner members with
  | none =>
    simp only [readInductiveBare, shapeRun] at read
    exact (throw_ok read).elim
  | some shape =>
    unfold readInductiveBare at read
    rw [shapeRun] at read
    dsimp only at read
    let indcs := shape.order.filterMap fun i => match (members[i]? : Option Ixon.MutConst) with
      | some (.indc ind) => some (i, ind)
      | _ => none
    let mr := MemberReader.mk' cx source id
      (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)
    let frame := NativeCtorReaderCheckedFrame cx owner mr
    rcases ite_ok read with read | read
    · split at read
      · rcases ite_ok read with read | read
        · exact (fail_bind read).elim
        · rcases ite_ok read with read | read
          · obtain ⟨types, _, read⟩ := except_bind_ok.mp read
            obtain ⟨ctors, ctorRun, read⟩ := except_bind_ok.mp read
            have frames : List.Forall₂ frame (nativeCtorSlots indcs.toList) ctors.1.toList := by
              apply forIn_inv_array
                (fun pre (state : Array NativeCtorRow × Array (List (Ix.Kernel.Key .anon))) =>
                  List.Forall₂ frame (nativeCtorSlots pre) state.1.toList)
                _ indcs ?_ (by exact .nil) ctorRun
              intro pre entry post state out _ held ran
              rcases entry with ⟨member, ind⟩
              obtain ⟨inside, innerRun, returned⟩ := except_bind_ok.mp ran
              simp only [pure, Except.pure, Except.ok.injEq] at returned
              subst out
              refine ⟨_, rfl, ?_⟩
              have innerFrames : List.Forall₂ frame
                  (nativeCtorSlots pre ++ ind.ctors.zipIdx.toList.map (fun slot => (member, slot.1, slot.2)))
                  inside.1.toList := by
                apply forIn_inv_array
                  (fun preSlots (current : Array NativeCtorRow × List (Ix.Kernel.Key .anon)) =>
                    List.Forall₂ frame
                      (nativeCtorSlots pre ++ preSlots.map (fun slot => (member, slot.1, slot.2)))
                      current.1.toList)
                  _ ind.ctors.zipIdx ?_ (by simpa using held) innerRun
                intro preSlots slot suffix current step _ prefixHeld stepped
                rcases slot with ⟨ctor, position⟩
                rcases Ix.Cert.CtxAgree.ite_ok' stepped with ⟨indexChecked, stepped⟩ | ⟨_, stepped⟩
                · rcases Ix.Cert.CtxAgree.ite_ok' stepped with ⟨_, stepped⟩ | ⟨safetyChecked, stepped⟩
                  · exact (fail_bind stepped).elim
                  · obtain ⟨key, keyRead, stepped⟩ := except_bind_ok.mp stepped
                    obtain ⟨type, typeRead, stepped⟩ := except_bind_ok.mp stepped
                    rcases ite_ok stepped with stepped | stepped
                    · simp only [pure, Except.pure, Except.ok.injEq] at stepped
                      subst step
                      refine ⟨_, rfl, ?_⟩
                      have one : frame (member, ctor, position)
                          (⟨key, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat) :=
                        ⟨⟨keyRead, typeRead, rfl, rfl, rfl⟩,
                          by simpa using indexChecked, by simpa using safetyChecked⟩
                      simpa only [Array.toList_push, List.map_append, List.map_singleton, List.append_assoc]
                        using forall₂_append prefixHeld (.cons one .nil)
                    · exact (fail_bind stepped).elim
                · exact (fail_bind stepped).elim
              simpa [nativeCtorSlots] using innerFrames
            obtain ⟨recs, _, read⟩ := except_bind_ok.mp read
            exact ⟨shape, _, rfl, read, frames⟩
          · exact (fail_bind read).elim
      · exact (throw_ok read).elim
    · exact (fail_bind read).elim

/-- The constructor row frames, omitting the additional checked slot and safety facts. -/
theorem readInductiveBare_ctor_frames {cx : Ctx .anon} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {result : Read .anon}
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (shape : BlockShape) (block : BlockRead .anon),
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok result ∧
      List.Forall₂
        (NativeCtorReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.ctors.toList := by
  obtain ⟨shape, block, shapeRead, lowered, frames⟩ := readInductiveBare_checked_ctor_frames read
  exact ⟨shape, block, shapeRead, lowered, frames.imp (fun _ _ frame => frame.1)⟩

/-- Full inductive reading exposes the same constructor frames through its proved bare
reading, after separating the actual generated declaration prefix. -/
theorem readInductive_ctor_frames {cx : Ctx .anon} {state : State .anon}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read .anon} (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (shape : BlockShape) (block : BlockRead .anon),
      result.decls.toList = generated ++ bare.decls.toList ∧
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok bare ∧
      List.Forall₂
        (NativeCtorReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.ctors.toList := by
  obtain ⟨generated, bare, bareRead, declarations, _, _, _⟩ := readInductive_full_bare read
  obtain ⟨shape, block, shapeRead, lowered, frames⟩ := readInductiveBare_ctor_frames bareRead
  exact ⟨generated, bare, shape, block, declarations, shapeRead, lowered, frames⟩

/-- Full reading also preserves the actual constructor slot and safety guards. -/
theorem readInductive_checked_ctor_frames {cx : Ctx .anon} {state : State .anon}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read .anon} (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (shape : BlockShape) (block : BlockRead .anon),
      result.decls.toList = generated ++ bare.decls.toList ∧
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok bare ∧
      List.Forall₂
        (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.ctors.toList := by
  obtain ⟨generated, bare, bareRead, declarations, _, _, _⟩ := readInductive_full_bare read
  obtain ⟨shape, block, shapeRead, lowered, frames⟩ := readInductiveBare_checked_ctor_frames bareRead
  exact ⟨generated, bare, shape, block, declarations, shapeRead, lowered, frames⟩

end IxVM.Refinement.Assembly
