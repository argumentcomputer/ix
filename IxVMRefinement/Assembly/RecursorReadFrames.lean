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
  dsimp only at read
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

end IxVM.Refinement.Assembly
