import IxVMRefinement.Assembly.NativeReaderShape

/-! # Former rows from actual inductive reading

The former loop retains its expression read, selected member key, level parameters and header
counts. The full reader has the same rows after its generated declaration prefix is separated.
These facts do not identify pruned reader keys with the kernel role table.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_inv_array forall₂_append)
open Ix.Cert.ReaderUnits (ite_ok fail_bind throw_ok)

private theorem singleton_frame {α β : Type} {relation : α → β → Prop}
    {entry : α} {rows : List β} (frames : List.Forall₂ relation [entry] rows) :
    ∃ row, rows = [row] ∧ relation entry row := by
  cases frames with
  | cons frame rest =>
    cases rest
    exact ⟨_, rfl, frame⟩

abbrev NativeFormerRow := Ix.Kernel.ConstantVal .anon × Nat × Nat

/-- The actual former row before lowering, including its original expression read. -/
def NativeFormerReaderFrame (cx : Ctx .anon) (owner : _root_.Address) (mr : MemberReader .anon)
    (entry : Nat × Ixon.Inductive) (row : NativeFormerRow) : Prop :=
  cx.memberKey (.member owner entry.1) = .ok row.1.name ∧
  mr.read entry.2.typ = .ok row.1.type ∧
  row.1.levelParams = List.range entry.2.lvls.toNat ∧
  row.2.1 = entry.2.params.toNat ∧ row.2.2 = entry.2.indices.toNat

/-- Successful bare reading retains former and constructor rows in the same actual block. -/
theorem readInductiveBare_native_frames {cx : Ctx .anon} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {result : Read .anon}
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (shape : BlockShape) (block : BlockRead .anon),
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok result ∧
      List.Forall₂
        (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        ((shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.types.toList ∧
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
    let frame := NativeFormerReaderFrame cx owner mr
    let ctorFrame := NativeCtorReaderCheckedFrame cx owner mr
    rcases ite_ok read with read | read
    · split at read
      · rcases ite_ok read with read | read
        · exact (fail_bind read).elim
        · rcases ite_ok read with read | read
          · obtain ⟨types, typeRun, read⟩ := except_bind_ok.mp read
            have frames : List.Forall₂ frame indcs.toList types.toList := by
              apply forIn_inv_array
                (fun pre (current : Array NativeFormerRow) => List.Forall₂ frame pre current.toList)
                _ indcs ?_ (by exact .nil) typeRun
              intro pre entry post current out _ held ran
              rcases entry with ⟨index, ind⟩
              obtain ⟨key, keyRead, ran⟩ := except_bind_ok.mp ran
              obtain ⟨type, typeRead, ran⟩ := except_bind_ok.mp ran
              simp only [pure, Except.pure, Except.ok.injEq] at ran
              subst out
              refine ⟨_, rfl, ?_⟩
              have one : frame (index, ind)
                  (⟨key, List.range ind.lvls.toNat, type⟩, ind.params.toNat, ind.indices.toNat) :=
                ⟨keyRead, typeRead, rfl, rfl, rfl⟩
              simpa only [Array.toList_push] using forall₂_append held (.cons one .nil)
            obtain ⟨ctors, ctorRun, read⟩ := except_bind_ok.mp read
            have ctorFrames : List.Forall₂ ctorFrame (nativeCtorSlots indcs.toList) ctors.1.toList := by
              apply forIn_inv_array
                (fun pre (state : Array NativeCtorRow × Array (List (Ix.Kernel.Key .anon))) =>
                  List.Forall₂ ctorFrame (nativeCtorSlots pre) state.1.toList)
                _ indcs ?_ (by exact .nil) ctorRun
              intro pre entry post state out _ held ran
              rcases entry with ⟨member, ind⟩
              obtain ⟨inside, innerRun, returned⟩ := except_bind_ok.mp ran
              simp only [pure, Except.pure, Except.ok.injEq] at returned
              subst out
              refine ⟨_, rfl, ?_⟩
              have innerFrames : List.Forall₂ ctorFrame
                  (nativeCtorSlots pre ++ ind.ctors.zipIdx.toList.map (fun slot => (member, slot.1, slot.2)))
                  inside.1.toList := by
                apply forIn_inv_array
                  (fun preSlots (current : Array NativeCtorRow × List (Ix.Kernel.Key .anon)) =>
                    List.Forall₂ ctorFrame
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
                      have one : ctorFrame (member, ctor, position)
                          (⟨key, List.range ctor.lvls.toNat, type⟩, ctor.params.toNat, ctor.fields.toNat) :=
                        ⟨⟨keyRead, typeRead, rfl, rfl, rfl⟩,
                          by simpa using indexChecked, by simpa using safetyChecked⟩
                      simpa only [Array.toList_push, List.map_append, List.map_singleton, List.append_assoc]
                        using forall₂_append prefixHeld (.cons one .nil)
                    · exact (fail_bind stepped).elim
                · exact (fail_bind stepped).elim
              simpa [nativeCtorSlots] using innerFrames
            obtain ⟨recs, _, read⟩ := except_bind_ok.mp read
            exact ⟨shape, _, rfl, read, frames, ctorFrames⟩
          · exact (fail_bind read).elim
      · exact (throw_ok read).elim
    · exact (fail_bind read).elim

/-- Compatibility projection retaining the actual former rows. -/
theorem readInductiveBare_former_frames {cx : Ctx .anon} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {result : Read .anon}
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (shape : BlockShape) (block : BlockRead .anon),
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok result ∧
      List.Forall₂
        (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        ((shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.types.toList := by
  obtain ⟨shape, block, shapeRead, lowered, frames, _⟩ := readInductiveBare_native_frames read
  exact ⟨shape, block, shapeRead, lowered, frames⟩

/-- The full reader exposes the same actual former rows after its generated prefix. -/
theorem readInductive_former_frames {cx : Ctx .anon} {state : State .anon}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read .anon} (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (shape : BlockShape) (block : BlockRead .anon),
      result.decls.toList = generated ++ bare.decls.toList ∧
      blockShapeOf cx.index owner members = some shape ∧
      lowerInductiveBare block = .ok bare ∧
      List.Forall₂
        (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        ((shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.types.toList := by
  obtain ⟨generated, bare, bareRead, declarations, _, _, _⟩ := readInductive_full_bare read
  obtain ⟨shape, block, shapeRead, lowered, frames⟩ := readInductiveBare_former_frames bareRead
  exact ⟨generated, bare, shape, block, declarations, shapeRead, lowered, frames⟩

/-- For the actual singleton native family, the former row is the one at its real member
index. Its name remains the selected reader key, without a global role-key assumption. -/
theorem readInductive_one_former_frame {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (block : BlockRead .anon) (row : NativeFormerRow),
      result.decls.toList = generated ++ bare.decls.toList ∧
      lowerInductiveBare block = .ok bare ∧ block.types.toList = [row] ∧
      NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
        (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none))
        (member, ind) row := by
  obtain ⟨generated, bare, shape, block, declarations, shapeRun, lowered, frames⟩ :=
    readInductive_former_frames read
  have order := native_reader_one_order indexBuilt stored kind one shapeRun
  have frames' : List.Forall₂
      (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
        (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
      [(member, ind)] block.types.toList := by
    rw [order, Array.toList_filterMap] at frames
    simpa only [List.filterMap_cons, List.filterMap_nil, memberAt] using frames
  obtain ⟨row, rowsEq, frame⟩ := singleton_frame frames'
  exact ⟨generated, bare, block, row, declarations, lowered, rowsEq, frame⟩

/-- Full reading preserves the former and constructor frames of the same lowered block. -/
theorem readInductive_native_frames {cx : Ctx .anon} {state : State .anon}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read .anon} (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (shape : BlockShape) (block : BlockRead .anon),
      result.decls.toList = generated ++ bare.decls.toList ∧
      blockShapeOf cx.index owner members = some shape ∧ lowerInductiveBare block = .ok bare ∧
      List.Forall₂
        (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        ((shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.types.toList ∧
      List.Forall₂
        (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
          | some (.indc ind) => some (i, ind)
          | _ => none)).toList) block.ctors.toList := by
  obtain ⟨generated, bare, bareRead, declarations, _, _, _⟩ := readInductive_full_bare read
  obtain ⟨shape, block, shapeRead, lowered, formers, ctors⟩ := readInductiveBare_native_frames bareRead
  exact ⟨generated, bare, shape, block, declarations, shapeRead, lowered, formers, ctors⟩

/-- The actual singleton native family has its former row and all constructor rows in one
reader block, with the original read and slot/safety guards retained together. -/
theorem readInductive_one_native_frames {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Ix.Kernel.Declaration .anon)) (bare : Read .anon)
      (block : BlockRead .anon) (row : NativeFormerRow),
      result.decls.toList = generated ++ bare.decls.toList ∧
      lowerInductiveBare block = .ok bare ∧ block.types.toList = [row] ∧
      NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
        (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none))
        (member, ind) row ∧
      List.Forall₂
        (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
          (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
        (nativeCtorSlots [(member, ind)]) block.ctors.toList := by
  obtain ⟨generated, bare, shape, block, declarations, shapeRun, lowered, formers, ctors⟩ :=
    readInductive_native_frames read
  have order := native_reader_one_order indexBuilt stored kind one shapeRun
  have formers' : List.Forall₂
      (NativeFormerReaderFrame cx owner (MemberReader.mk' cx source id
        (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
      [(member, ind)] block.types.toList := by
    rw [order, Array.toList_filterMap] at formers
    simpa only [List.filterMap_cons, List.filterMap_nil, memberAt] using formers
  have ctors' : List.Forall₂
      (NativeCtorReaderCheckedFrame cx owner (MemberReader.mk' cx source id
        (fun i => if i < members.size then some (cx.memberKey (.member owner i)) else none)))
      (nativeCtorSlots [(member, ind)]) block.ctors.toList := by
    rw [order, Array.toList_filterMap] at ctors
    simpa only [List.filterMap_cons, List.filterMap_nil, memberAt] using ctors
  obtain ⟨row, rowsEq, frame⟩ := singleton_frame formers'
  exact ⟨generated, bare, block, row, declarations, lowered, rowsEq, frame, ctors'⟩


end IxVM.Refinement.Assembly
