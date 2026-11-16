import IxVMRefinement.Assembly.RecursorReadInputs
import IxVMRefinement.Assembly.InductiveRead

/-! # Recursor rows from actual inductive reading

The recursor loop retains the chosen canonical entry and its successful payload read.
Its level mapping comes from the first actual former in the selected block shape. Full
reading supplies the same rows after separating the generated declaration prefix.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_push_array)
open Ix.Cert.ReaderUnits (ite_ok fail_bind throw_ok)

def RecursorIndexedReadFrame {md : Mode} (cx : Ctx md) (blockLps : List LevelParam)
    (ref : ConstRef _root_.Address) (row : CVal md × RecCounts × List (RecRule md)) : Prop :=
  ∃ entry, cx.index.recs[ref]? = some entry ∧ readRecursor cx blockLps ref entry = .ok row

theorem RecursorIndexedReadFrame.inputs {md : Mode} {cx : Ctx md} {blockLps : List LevelParam}
    {ref : ConstRef _root_.Address} {row : CVal md × RecCounts × List (RecRule md)}
    (frame : RecursorIndexedReadFrame cx blockLps ref row) :
    ∃ entry, cx.index.recs[ref]? = some entry ∧ Nonempty (RecursorReadInputs cx blockLps ref entry row) := by
  obtain ⟨entry, indexed, read⟩ := frame
  exact ⟨entry, indexed, readRecursor_inputs read⟩

theorem readInductiveBare_rec_frames {md : Mode} {cx : Ctx md} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {result : Read md}
    (read : readInductiveBare cx owner source members = .ok result) :
    ∃ (shape : BlockShape) (firstSlot : Nat) (first : Ixon.Inductive) (block : BlockRead md),
      blockShapeOf cx.index owner members = some shape ∧
      (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
        | some (.indc ind) => some (i, ind)
        | _ => none))[0]? = some (firstSlot, first) ∧
      block.numParams = first.params.toNat ∧
      lowerInductiveBare block = .ok result ∧
      List.Forall₂ (RecursorIndexedReadFrame cx (List.range first.lvls.toNat))
        shape.recs.toList block.recs.toList := by
  cases shapeRun : blockShapeOf cx.index owner members with
  | none =>
    simp only [readInductiveBare, shapeRun] at read
    exact (throw_ok read).elim
  | some shape =>
    unfold readInductiveBare at read
    rw [shapeRun] at read
    dsimp only at read
    rcases ite_ok read with read | read
    · split at read
      · rename_i firstSlot first firstRun
        rcases ite_ok read with read | read
        · exact (fail_bind read).elim
        · rcases ite_ok read with read | read
          · obtain ⟨types, _, read⟩ := except_bind_ok.mp read
            obtain ⟨ctors, _, read⟩ := except_bind_ok.mp read
            obtain ⟨recs, recRead, read⟩ := except_bind_ok.mp read
            have frames : List.Forall₂ (RecursorIndexedReadFrame cx (List.range first.lvls.toNat))
                shape.recs.toList recs.toList := by
              apply forIn_push_array shape.recs _ _ ?_ recRead
              intro ref current out ran
              cases indexed : cx.index.recs[ref]? with
              | none =>
                rw [indexed] at ran
                exact (throw_ok ran).elim
              | some entry =>
                rw [indexed] at ran
                dsimp only at ran
                obtain ⟨row, rowRead, returned⟩ := except_bind_ok.mp ran
                simp only [pure, Except.pure, Except.ok.injEq] at returned
                subst out
                exact ⟨row, rfl, entry, indexed, rowRead⟩
            exact ⟨shape, firstSlot, first, _, rfl, firstRun, rfl, read, frames⟩
          · exact (fail_bind read).elim
      · exact (throw_ok read).elim
    · exact (fail_bind read).elim

theorem readInductive_rec_frames {md : Mode} {cx : Ctx md} {state : State md}
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read md} (read : readInductive cx state owner source members = .ok result) :
    ∃ (generated : List (Declaration md)) (bare : Read md)
      (shape : BlockShape) (firstSlot : Nat) (first : Ixon.Inductive) (block : BlockRead md),
      result.decls.toList = generated ++ bare.decls.toList ∧
      blockShapeOf cx.index owner members = some shape ∧
      (shape.order.filterMap (fun i => match (members[i]? : Option Ixon.MutConst) with
        | some (.indc ind) => some (i, ind)
        | _ => none))[0]? = some (firstSlot, first) ∧
      block.numParams = first.params.toNat ∧
      lowerInductiveBare block = .ok bare ∧
      List.Forall₂ (RecursorIndexedReadFrame cx (List.range first.lvls.toNat))
        shape.recs.toList block.recs.toList := by
  obtain ⟨generated, bare, bareRead, declarations, _, _, _⟩ := readInductive_full_bare read
  obtain ⟨shape, firstSlot, first, block, selected, firstRun, params, lower, frames⟩ :=
    readInductiveBare_rec_frames bareRead
  exact ⟨generated, bare, shape, firstSlot, first, block, declarations, selected,
    firstRun, params, lower, frames⟩

/-- Every twin in a nonempty successful family read supplies its own actual recursor run.
The local motive position is retained in its own entry; no global-order equality is used. -/
theorem lowerTwin_rec_frames {md : Mode} {cx : Ctx md}
    {twins : Array (ConstRef _root_.Address × RecEntry)} {firstRef : ConstRef _root_.Address}
    {firstEntry : RecEntry} {result : Read md}
    (firstRun : twins[0]? = some (firstRef, firstEntry))
    (read : lowerTwin cx twins = .ok result) :
    ∃ blockLps rows, List.Forall₂
      (fun selected row => readRecursor cx blockLps selected.1 selected.2 = .ok row)
      twins.toList rows := by
  simp only [lowerTwin, firstRun] at read
  rcases ite_ok read with read | read
  · split at read
    · split at read
      · split at read
        · dsimp only at read
          rcases ite_ok read with read | read
          · split at read
            · rename_i firstSlot first selectedFirst
              rcases ite_ok read with read | read
              · exact (fail_bind read).elim
              · rcases ite_ok read with read | read
                · obtain ⟨_, _, read⟩ := except_bind_ok.mp read
                  obtain ⟨rows, rowsRead, _⟩ := except_bind_ok.mp read
                  refine ⟨List.range first.lvls.toNat, rows.toList, ?_⟩
                  apply forIn_push_array twins _ _ ?_ rowsRead
                  intro selected current out ran
                  obtain ⟨row, rowRead, returned⟩ := except_bind_ok.mp ran
                  simp only [pure, Except.pure, Except.ok.injEq] at returned
                  subst out
                  exact ⟨row, rfl, rowRead⟩
                · exact (fail_bind read).elim
            · exact (throw_ok read).elim
          · exact (fail_bind read).elim
        · exact (throw_ok read).elim
      · exact (throw_ok read).elim
    · exact (throw_ok read).elim
  · exact (fail_bind read).elim

private theorem paired_member {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ relation left right)
    {entry : α} (member : entry ∈ left) : ∃ row ∈ right, relation entry row := by
  induction paired with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨row, present, frame⟩ := ih later
      exact ⟨row, List.mem_cons_of_mem _ present, frame⟩

theorem lowerTwin_rec_read {md : Mode} {cx : Ctx md}
    {twins : Array (ConstRef _root_.Address × RecEntry)} {result : Read md}
    (read : lowerTwin cx twins = .ok result) {selected : ConstRef _root_.Address × RecEntry}
    (member : selected ∈ twins) :
    ∃ blockLps row, readRecursor cx blockLps selected.1 selected.2 = .ok row := by
  cases firstRun : twins[0]? with
  | none =>
    have empty := Array.getElem?_eq_none_iff.mp firstRun
    obtain ⟨index, bound, _⟩ := Array.mem_iff_getElem.mp member
    omega
  | some first =>
    rcases first with ⟨firstRef, firstEntry⟩
    obtain ⟨blockLps, rows, paired⟩ := lowerTwin_rec_frames firstRun read
    obtain ⟨row, _, rowRead⟩ := paired_member paired (Array.mem_toList_iff.mpr member)
    exact ⟨blockLps, row, rowRead⟩

/-- Family partitioning retains a successful payload read for every original twin. -/
theorem lowerTwins_rec_read {md : Mode} {cx : Ctx md}
    {twins : Array (ConstRef _root_.Address × RecEntry)} {result : Read md}
    (read : lowerTwins cx twins = .ok result) {selected : ConstRef _root_.Address × RecEntry}
    (member : selected ∈ twins) :
    ∃ blockLps row, readRecursor cx blockLps selected.1 selected.2 = .ok row := by
  cases firstRun : twins[0]? with
  | none =>
    have empty := Array.getElem?_eq_none_iff.mp firstRun
    obtain ⟨index, bound, _⟩ := Array.mem_iff_getElem.mp member
    omega
  | some first =>
    rcases first with ⟨firstRef, firstEntry⟩
    simp only [lowerTwins, firstRun] at read
    split at read
    · exact lowerTwin_rec_read read member
    · obtain ⟨decls, loop, _⟩ := except_bind_ok.mp read
      have runs : ∀ family ∈ (groupTwins twins).toList, ∃ chunk, lowerTwin cx family = .ok chunk := by
        apply Ix.CompileCert.Loop.forIn_inv_array
          (fun processed (_ : Array (Declaration md)) =>
            ∀ family ∈ processed, ∃ chunk, lowerTwin cx family = .ok chunk)
          _ (groupTwins twins) ?_ (by simp) loop
        intro processed family suffix current out _ held ran
        obtain ⟨chunk, chunkRead, returned⟩ := except_bind_ok.mp ran
        simp only [pure, Except.pure, Except.ok.injEq] at returned
        subst out
        refine ⟨_, rfl, ?_⟩
        intro next present
        rcases List.mem_append.mp present with old | added
        · exact held next old
        · have same : next = family := List.mem_singleton.mp added
          subst next
          exact ⟨chunk, chunkRead⟩
      obtain ⟨family, inGroups, inFamily⟩ := groupTwins_coverage member
      obtain ⟨chunk, chunkRead⟩ := runs family (Array.mem_toList_iff.mpr inGroups)
      exact lowerTwin_rec_read chunkRead inFamily

end IxVM.Refinement.Assembly
