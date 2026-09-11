import Ix.Compiler.IxIR2.ReuseHeapMap
import Ix.Compiler.IxIR1.EvalIso

/-!
# Executable heap operations under allocation history

Successful baseline observations transport through the live part of the
history map. Destruction retains old names; allocation appends one name,
whether the target uses fresh storage or fills a suspended reservation.
-/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Ix.Compiler.IxIR2.Eval
open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim (NodeIso NodeBoxIso RValIso RValsIso)

private theorem get_setBox {store : Store} {location : Nat} {old new : NodeBox}
    (found : store.get? location = some old) (other : Nat) :
    (store.setBox location new).get? other =
      if other = location then some new else store.get? other := by
  have bound := (Array.getElem?_eq_some_iff.mp (IxIR1.Sim.nodes_get?_of_get? found)).1
  by_cases same : other = location
  · subst other
    simp [Store.setBox, Store.get?, IxIR1.Store.setBox, IxIR1.Store.get?,
      Array.set!_eq_setIfInBounds, bound]
  · simp [Store.setBox, Store.get?, IxIR1.Store.setBox, IxIR1.Store.get?,
      Array.set!_eq_setIfInBounds, same, Ne.symm same]

private theorem get_kill (store : Store) (location other : Nat) :
    (store.kill location).get? other =
      if other = location then none else store.get? other := by
  by_cases same : other = location
  · subst other
    simp [Store.kill, Store.get?, IxIR1.Store.kill, IxIR1.Store.get?,
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  · simp [Store.kill, Store.get?, IxIR1.Store.kill, IxIR1.Store.get?,
      Array.set!_eq_setIfInBounds, same, Ne.symm same]

private theorem get_alloc (store : Store) (world : Owned) (node : Node) (location : Nat) :
    (store.allocNode world node).1.get? location =
      if location = store.heap.nodes.size then some ⟨world, 1, node⟩
      else store.get? location := by
  simp only [Store.get?, Store.allocNode_heap, IxIR1.Store.allocNode,
    IxIR1.Store.get?, Array.getElem?_push]
  split <;> rfl

theorem setRc_world {store : Store} {location rc : Nat} {box : NodeBox}
    (found : store.get? location = some box) (world : Owned) (value : RVal) :
    RVal.hasWorld (store.setBox location { box with rc }) world value =
      RVal.hasWorld store world value := by
  cases value with
  | lit => rfl
  | erased => rfl
  | loc other =>
      by_cases same : other = location
      · subst other
        simp only [RVal.hasWorld, get_setBox found, ↓reduceIte, found]
      · simp only [RVal.hasWorld, get_setBox found, same, ↓reduceIte]

theorem retain_world {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) :
    RVal.hasWorld store .shared value = true ∧
      ∀ world observed, RVal.hasWorld output world observed = RVal.hasWorld store world observed := by
  cases value with
  | lit => cases run; exact ⟨rfl, fun _ _ => rfl⟩
  | erased => cases run; exact ⟨rfl, fun _ _ => rfl⟩
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp only [retainShared, found, shared, bne_self_eq_false, Bool.false_eq_true,
              ↓reduceIte, Except.ok.injEq] at run
            subst output
            refine ⟨by simp [RVal.hasWorld, found, shared], ?_⟩
            intro world observed
            change RVal.hasWorld (store.setBox location _) world observed = _
            simpa only [shared] using setRc_world (rc := box.rc + 1) found world observed
          · simp [retainShared, found, shared] at run

theorem retainMany_world {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) :
    ∀ value ∈ values.toList, RVal.hasWorld store .shared value = true := by
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output →
      ∀ value ∈ values, RVal.hasWorld store .shared value = true := by
    intro values
    induction values with
    | nil => simp
    | cons head tail ih =>
        intro store output run value member
        rw [List.foldlM_cons] at run
        cases first : retainShared store head with
        | error error => simp [first, bind, Except.bind] at run
        | ok middle =>
            simp only [first, bind, Except.bind] at run
            have worlds := retain_world first
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact worlds.1
            · rw [← worlds.2 .shared value]
              exact ih run value member
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  exact loop values.toList run

namespace HeapMap

theorem rcTick {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) : HeapMap left.rcTick right.rcTick mapping :=
  heap.congr rfl rfl

theorem setBox {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {oldLeft newLeft newRight : NodeBox}
    (mapped : MapRel mapping l r) (leftAt : left.get? l = some oldLeft)
    (boxes : NodeBoxIso (MapRel mapping) newLeft newRight) :
    HeapMap (left.setBox l newLeft) (right.setBox r newRight) mapping := by
  obtain ⟨oldRight, rightAt, _⟩ := heap.forward mapped leftAt
  exact heap.replace mapped leftAt (.present boxes)
    (by simp [Store.setBox, IxIR1.Store.setBox])
    (by simp [Store.setBox, IxIR1.Store.setBox])
    (get_setBox leftAt) (get_setBox rightAt)

theorem kill {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {oldLeft : NodeBox}
    (mapped : MapRel mapping l r) (leftAt : left.get? l = some oldLeft) :
    HeapMap (left.kill l) (right.kill r) mapping :=
  heap.replace mapped leftAt .absent
    (by simp [Store.kill, IxIR1.Store.kill])
    (by simp [Store.kill, IxIR1.Store.kill])
    (get_kill left l) (get_kill right r)

theorem reserve {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {oldLeft : NodeBox}
    (mapped : MapRel mapping l r) (leftAt : left.get? l = some oldLeft) :
    HeapMap (left.kill l) (right.reserve r) mapping :=
  (heap.kill mapped leftAt).congr rfl (by
    simp only [Store.reserve, Store.kill, IxIR1.Store.kill, Array.set!_eq_setIfInBounds])

theorem alloc {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {world : Owned} {leftNode rightNode : Node}
    (nodes : NodeIso (MapRel mapping) leftNode rightNode) :
    HeapMap (left.allocNode world leftNode).1 (right.allocNode world rightNode).1
      (mapping.push right.heap.nodes.size) := by
  apply heap.extend (target := right.heap.nodes.size) (newLeft := ⟨world, 1, leftNode⟩)
    (newRight := ⟨world, 1, rightNode⟩)
  · simp [Store.get?, IxIR1.Store.get?]
  · exact ⟨rfl, rfl, nodes⟩
  · simp [IxIR1.Store.allocNode]
  · simp [IxIR1.Store.allocNode]
  · simp [IxIR1.Store.allocNode]
  · exact get_alloc left world leftNode
  · exact get_alloc right world rightNode

theorem reuse {left right rightOut : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {target payload : Nat} {world : Owned}
    {leftNode rightNode : Node} (nodes : NodeIso (MapRel mapping) leftNode rightNode)
    (run : right.reuseReservation target world rightNode payload = .ok rightOut) :
    HeapMap (left.allocNode world leftNode).1 rightOut (mapping.push target) := by
  unfold Store.reuseReservation at run
  split at run
  · rename_i empty
    cases run
    have bound := (Array.getElem?_eq_some_iff.mp empty).1
    apply heap.extend (newLeft := ⟨world, 1, leftNode⟩)
      (newRight := ⟨world, 1, rightNode⟩)
    · exact Store.EmptySlot.not_live empty
    · exact ⟨rfl, rfl, nodes⟩
    · simp [IxIR1.Store.allocNode]
    · simp only [Store.withPeak_heap, Array.size_setIfInBounds, Nat.le_refl]
    · simpa only [Store.withPeak_heap, Array.size_setIfInBounds] using bound
    · exact get_alloc left world leftNode
    · intro location
      by_cases same : location = target
      · subst location
        simp [Store.get?, Store.withPeak_heap, IxIR1.Store.get?, bound]
      · simp [Store.get?, Store.withPeak_heap, IxIR1.Store.get?, same, Ne.symm same]
  · cases run

/-- Only successful source observations are required. A dead historical name
may now refer to reused storage, but successful source code cannot inspect it. -/
theorem hasWorld {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {leftValue rightValue : RVal} {world : Owned}
    (related : RValIso (MapRel mapping) leftValue rightValue)
    (valid : RVal.hasWorld left world leftValue = true) :
    RVal.hasWorld right world rightValue = true := by
  cases related with
  | lit => exact valid
  | erased => exact valid
  | @loc l r mapped =>
      cases found : left.get? l with
      | none => simp [RVal.hasWorld, found] at valid
      | some box =>
          obtain ⟨targetBox, rightAt, boxes⟩ := heap.forward mapped found
          simpa only [RVal.hasWorld, found, rightAt, ← boxes.world] using valid

theorem constructorView {left right : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {l r : Nat} {world : Owned} {cid : CtorId}
    {leftBox : NodeBox} {leftFields : Array RVal} (mapped : MapRel mapping l r)
    (view : ConstructorView left l world cid leftBox leftFields) :
    ∃ rightBox rightFields,
      ConstructorView right r world cid rightBox rightFields ∧
      NodeBoxIso (MapRel mapping) leftBox rightBox ∧
      RValsIso (MapRel mapping) leftFields.toList rightFields.toList := by
  obtain ⟨leftAt, leftWorld, leftNode⟩ := view.parts
  obtain ⟨rightBox, rightAt, boxes⟩ := heap.forward mapped leftAt
  have nodes := boxes.node
  rw [leftNode] at nodes
  cases rightNode : rightBox.node with
  | papN address arity arguments => rw [rightNode] at nodes; cases nodes
  | ctorN targetCid rightFields =>
      rw [rightNode] at nodes
      cases nodes with
      | ctor fields =>
          exact ⟨rightBox, rightFields,
            .of_box rightAt (boxes.world.symm.trans leftWorld) rightNode, boxes, fields⟩

theorem retain {left right leftOut : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {leftValue rightValue : RVal}
    (related : RValIso (MapRel mapping) leftValue rightValue)
    (run : retainShared left leftValue = .ok leftOut) :
    ∃ rightOut, retainShared right rightValue = .ok rightOut ∧
      HeapMap leftOut rightOut mapping := by
  cases related with
  | lit => cases run; exact ⟨right, rfl, heap⟩
  | erased => cases run; exact ⟨right, rfl, heap⟩
  | @loc l r mapped =>
      cases found : left.get? l with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst leftOut
            obtain ⟨targetBox, rightAt, boxes⟩ := heap.forward mapped found
            refine ⟨(right.setBox r { targetBox with rc := targetBox.rc + 1 }).rcTick, ?_, ?_⟩
            · simp [retainShared, rightAt, ← boxes.world, shared]
            · apply HeapMap.rcTick
              apply heap.setBox mapped found
              exact ⟨shared.symm.trans boxes.world, by simp only [boxes.rc], boxes.node⟩
          · simp [retainShared, found, shared] at run

theorem retainMany {left right leftOut : Store} {mapping : Array Nat}
    (heap : HeapMap left right mapping) {leftValues rightValues : Array RVal}
    (related : RValsIso (MapRel mapping) leftValues.toList rightValues.toList)
    (run : RetainSharedMany left leftValues leftOut) :
    ∃ rightOut, RetainSharedMany right rightValues rightOut ∧
      HeapMap leftOut rightOut mapping := by
  have loop : ∀ {leftValues rightValues : List RVal},
      RValsIso (MapRel mapping) leftValues rightValues →
      ∀ {left right leftOut : Store}, HeapMap left right mapping →
      leftValues.foldlM retainShared left = .ok leftOut →
      ∃ rightOut, rightValues.foldlM retainShared right = .ok rightOut ∧
        HeapMap leftOut rightOut mapping := by
    intro leftValues rightValues related
    induction related with
    | nil => intro left right leftOut heap run; cases run; exact ⟨right, rfl, heap⟩
    | @cons lval rval ls rs head tail ih =>
        intro left right leftOut heap run
        rw [List.foldlM_cons] at run
        cases first : retainShared left lval with
        | error error => simp [first, bind, Except.bind] at run
        | ok middle =>
            simp only [first, bind, Except.bind] at run
            obtain ⟨rightMiddle, rightFirst, middleHeap⟩ := heap.retain head first
            obtain ⟨rightOut, rest, final⟩ := ih middleHeap run
            exact ⟨rightOut, by simpa only [List.foldlM_cons, rightFirst, bind, Except.bind]
              using rest, final⟩
  change leftValues.foldlM retainShared left = .ok leftOut at run
  rw [← Array.foldlM_toList] at run
  obtain ⟨rightOut, rightRun, final⟩ := loop related heap run
  refine ⟨rightOut, ?_, final⟩
  change rightValues.foldlM retainShared right = .ok rightOut
  simpa only [← Array.foldlM_toList] using rightRun

end HeapMap

theorem nodeChildren_iso {mapping : Array Nat} {left right : Node}
    (nodes : NodeIso (MapRel mapping) left right) :
    RValsIso (MapRel mapping) (IxIR1.Sim.nodeChildren left) (IxIR1.Sim.nodeChildren right) := by
  cases nodes <;> assumption

theorem HeapMap.releaseWork {fuel remaining : Nat} {left right leftOut : Store}
    {mapping : Array Nat} (heap : HeapMap left right mapping)
    {leftValues rightValues : List RVal}
    (related : RValsIso (MapRel mapping) leftValues rightValues)
    (run : releaseSharedWork fuel left leftValues = .ok (leftOut, remaining)) :
    ∃ rightOut, releaseSharedWork fuel right rightValues = .ok (rightOut, remaining) ∧
      HeapMap leftOut rightOut mapping := by
  induction fuel generalizing left right leftValues rightValues with
  | zero =>
      cases related with
      | nil => cases run; exact ⟨right, rfl, heap⟩
      | cons head tail => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases related with
      | nil => cases run; exact ⟨right, rfl, heap⟩
      | @cons lval rval ls rs head tail =>
          cases head with
          | lit => exact ih heap tail run
          | erased => exact ih heap tail run
          | @loc l r mapped =>
              cases found : left.get? l with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · obtain ⟨targetBox, rightAt, boxes⟩ := heap.forward mapped found
                    by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true] at run
                        have bothKilled := heap.rcTick.kill mapped (show left.rcTick.get? l =
                          some box from found)
                        have children := (nodeChildren_iso boxes.node).append tail
                        obtain ⟨rightOut, rightRun, output⟩ := ih bothKilled children run
                        refine ⟨rightOut, ?_, output⟩
                        cases targetNode : targetBox.node <;>
                          simpa only [releaseSharedWork, rightAt, ← boxes.world, shared,
                            bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ← boxes.rc,
                            unitRC, beq_self_eq_true, Nat.reduceBEq,
                            IxIR1.Sim.nodeChildren, targetNode] using rightRun
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        have bothSet := heap.rcTick.setBox mapped
                          (show left.rcTick.get? l = some box from found)
                          (show NodeBoxIso (MapRel mapping)
                            { box with rc := box.rc - 1 }
                            { targetBox with rc := targetBox.rc - 1 } from
                            ⟨boxes.world, congrArg (· - 1) boxes.rc, boxes.node⟩)
                        obtain ⟨rightOut, rightRun, output⟩ := ih bothSet tail (by
                          simpa only [shared] using run)
                        refine ⟨rightOut, ?_, output⟩
                        simpa only [releaseSharedWork, rightAt, ← boxes.world, shared,
                          bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ← boxes.rc,
                          beq_iff_eq, zero, unitRC] using rightRun
                  · simp [releaseSharedWork, found, shared] at run

theorem HeapMap.dropWork {fuel remaining : Nat} {left right leftOut : Store}
    {mapping : Array Nat} (heap : HeapMap left right mapping)
    {leftValues rightValues : List RVal}
    (related : RValsIso (MapRel mapping) leftValues rightValues)
    (run : dropUniqueWork fuel left leftValues = .ok (leftOut, remaining)) :
    ∃ rightOut, dropUniqueWork fuel right rightValues = .ok (rightOut, remaining) ∧
      HeapMap leftOut rightOut mapping := by
  induction fuel generalizing left right leftValues rightValues with
  | zero =>
      cases related with
      | nil => cases run; exact ⟨right, rfl, heap⟩
      | cons head tail => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases related with
      | nil => cases run; exact ⟨right, rfl, heap⟩
      | @cons lval rval ls rs head tail =>
          cases head with
          | lit => exact ih heap tail run
          | erased => exact ih heap tail run
          | @loc l r mapped =>
              cases found : left.get? l with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · obtain ⟨targetBox, rightAt, boxes⟩ := heap.forward mapped found
                    have nodes := boxes.node
                    cases node : box.node with
                    | papN address arity arguments =>
                        simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        rw [node] at nodes
                        cases targetNode : targetBox.node with
                        | papN address arity arguments => rw [targetNode] at nodes; cases nodes
                        | ctorN targetCid targetFields =>
                            rw [targetNode] at nodes
                            cases nodes with
                            | ctor children =>
                                obtain ⟨rightOut, rightRun, output⟩ :=
                                  ih (heap.kill mapped found) (children.append tail) run
                                refine ⟨rightOut, ?_, output⟩
                                simpa only [dropUniqueWork, rightAt, ← boxes.world, unique,
                                  bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, targetNode]
                                  using rightRun
                  · simp [dropUniqueWork, found, unique] at run

end Ix.Compiler.IxIR2.CallReuse.Sim
