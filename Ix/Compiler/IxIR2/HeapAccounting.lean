import Ix.Compiler.IxIR2.Eval
import Ix.Compiler.IxIR1.Reclamation
import Init.Data.Array.Count

/-!
# Allocation accounting for physical heap operations

A reserved slot is absent from the live-node array but has not been freed.
The machine accounting theorem adds its live credit to the heap balance.
These lemmas describe actual successful heap operations, independently of
the semantic heap relation and of any optimization savings claim.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1 (Node NodeBox RVal)

private theorem foldl_countP {α : Type} (p : α → Bool) (values : List α)
    (initial : Nat) :
    values.foldl (fun total value => if p value then total + 1 else total) initial =
      initial + values.countP p := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih =>
      simp only [List.foldl_cons, List.countP_cons, ih]
      split <;> omega

theorem Store.live_eq_countP (store : Store) :
    store.live = store.heap.nodes.countP Option.isSome := by
  rw [Store.live, IxIR1.Store.live, ← Array.foldl_toList, foldl_countP]
  simp

private theorem countP_update {α : Type} {values : Array α} {index : Nat}
    {old new : α} (p : α → Bool) (found : values[index]? = some old) :
    (values.setIfInBounds index new).countP p + (if p old then 1 else 0) =
      values.countP p + (if p new then 1 else 0) := by
  have bound : index < values.size := (Array.getElem?_eq_some_iff.mp found).1
  have atIndex : values[index] = old := (Array.getElem?_eq_some_iff.mp found).2
  have lower := Array.boole_getElem_le_countP (p := p) bound
  rw [atIndex] at lower
  simp only [Array.setIfInBounds, bound, ↓reduceDIte, Array.countP_set, atIndex]
  omega

theorem Store.live_setBox {store : Store} {location : Nat} {old new : NodeBox}
    (found : store.get? location = some old) :
    (store.setBox location new).live = store.live := by
  have slot : store.heap.nodes[location]? = some (some old) :=
    IxIR1.Sim.nodes_get?_of_get? found
  have update := countP_update (new := some new) Option.isSome slot
  simpa [Store.live_eq_countP, Store.setBox, IxIR1.Store.setBox] using update

theorem Store.live_reserve {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (store.reserve location).live + 1 = store.live := by
  have slot : store.heap.nodes[location]? = some (some box) :=
    IxIR1.Sim.nodes_get?_of_get? found
  simpa [Store.live_eq_countP, Store.reserve] using
    (countP_update (new := none) Option.isSome slot)

theorem Store.live_kill {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (store.kill location).live + 1 = store.live := by
  simpa [Store.live_eq_countP, Store.kill, IxIR1.Store.kill, Store.reserve] using
    Store.live_reserve found

theorem Store.live_allocNode (store : Store) (world : Owned) (node : Node) :
    (store.allocNode world node).1.live = store.live + 1 := by
  simp [Store.live_eq_countP, IxIR1.Store.allocNode]

/-- Ordinary heap operations preserve live nodes plus completed frees,
relative to fresh allocations. This relation permits different RC counters. -/
def HeapBalance (before after : Store) : Prop :=
  after.live + after.heap.frees + before.heap.allocs =
    before.live + before.heap.frees + after.heap.allocs

namespace HeapBalance

theorem refl (store : Store) : HeapBalance store store := rfl

theorem trans {first second third : Store}
    (left : HeapBalance first second) (right : HeapBalance second third) :
    HeapBalance first third := by
  unfold HeapBalance at *
  omega

theorem allocNode (store : Store) (world : Owned) (node : Node) :
    HeapBalance store (store.allocNode world node).1 := by
  unfold HeapBalance
  rw [Store.live_allocNode]
  simp only [Store.allocNode_heap, IxIR1.Store.allocNode]
  omega

theorem setBox {store : Store} {location : Nat} {old new : NodeBox}
    (found : store.get? location = some old) :
    HeapBalance store (store.setBox location new) := by
  unfold HeapBalance
  rw [Store.live_setBox found]
  rfl

theorem kill {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    HeapBalance store (store.kill location) := by
  have live := Store.live_kill found
  unfold HeapBalance
  simp only [Store.kill_heap, IxIR1.Store.kill]
  omega

theorem rcTick (store : Store) : HeapBalance store store.rcTick := rfl

end HeapBalance

theorem retainShared_heapBalance {store output : Store} {value : RVal}
    (run : retainShared store value = .ok output) : HeapBalance store output := by
  cases value with
  | lit literal => cases run; exact .refl _
  | erased => cases run; exact .refl _
  | loc location =>
      cases found : store.get? location with
      | none => simp [retainShared, found] at run
      | some box =>
          by_cases shared : box.world = .shared
          · simp [retainShared, found, shared] at run
            subst output
            exact (HeapBalance.setBox found).trans (.rcTick _)
          · simp [retainShared, found, shared] at run

theorem RetainSharedMany.heapBalance {store output : Store} {values : Array RVal}
    (run : RetainSharedMany store values output) : HeapBalance store output := by
  change values.foldlM retainShared store = .ok output at run
  rw [← Array.foldlM_toList] at run
  have loop : ∀ (values : List RVal) {store output : Store},
      values.foldlM retainShared store = .ok output → HeapBalance store output := by
    intro values
    induction values with
    | nil => intro store output run; cases run; exact .refl _
    | cons value rest ih =>
        intro store output run
        rw [List.foldlM_cons] at run
        cases head : retainShared store value with
        | error error => simp [head, bind, Except.bind] at run
        | ok middle =>
            simp only [head, bind, Except.bind] at run
            exact (retainShared_heapBalance head).trans (ih run)
  exact loop values.toList run

theorem releaseSharedWork_heapBalance {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : releaseSharedWork fuel store values = .ok (output, remaining)) :
    HeapBalance store output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest => simp [releaseSharedWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [releaseSharedWork, found] at run
              | some box =>
                  by_cases shared : box.world = .shared
                  · by_cases zero : box.rc = 0
                    · simp [releaseSharedWork, found, shared, zero] at run
                    · by_cases unitRC : box.rc = 1
                      · simp only [releaseSharedWork, found, shared, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, unitRC, beq_self_eq_true] at run
                        have tickAt : store.rcTick.get? location = some box := found
                        exact (HeapBalance.rcTick store).trans
                          ((HeapBalance.kill tickAt).trans (ih run))
                      · simp [releaseSharedWork, found, shared, zero, unitRC] at run
                        have tickAt : store.rcTick.get? location = some box := found
                        exact (HeapBalance.rcTick store).trans
                          ((HeapBalance.setBox tickAt).trans (ih run))
                  · simp [releaseSharedWork, found, shared] at run

theorem releaseShared_heapBalance {fuel remaining : Nat} {store output : Store}
    {value : RVal} (run : releaseShared fuel store value = .ok (output, remaining)) :
    HeapBalance store output := releaseSharedWork_heapBalance run

theorem dropUniqueWork_heapBalance {fuel remaining : Nat} {store output : Store}
    {values : List RVal}
    (run : dropUniqueWork fuel store values = .ok (output, remaining)) :
    HeapBalance store output := by
  induction fuel generalizing store values with
  | zero =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest => simp [dropUniqueWork] at run
  | succ fuel ih =>
      cases values with
      | nil => cases run; exact .refl _
      | cons value rest =>
          cases value with
          | lit literal => exact ih run
          | erased => exact ih run
          | loc location =>
              cases found : store.get? location with
              | none => simp [dropUniqueWork, found] at run
              | some box =>
                  by_cases unique : box.world = .unique
                  · cases node : box.node with
                    | papN address arity captured => simp [dropUniqueWork, found, unique, node] at run
                    | ctorN cid fields =>
                        simp only [dropUniqueWork, found, unique, bne_self_eq_false,
                          Bool.false_eq_true, ↓reduceIte, node] at run
                        exact (HeapBalance.kill found).trans (ih run)
                  · simp [dropUniqueWork, found, unique] at run

theorem dropUnique_heapBalance {fuel remaining : Nat} {store output : Store}
    {value : RVal} (run : dropUnique fuel store value = .ok (output, remaining)) :
    HeapBalance store output := dropUniqueWork_heapBalance run

theorem Store.releaseReservation_accounting {store output : Store} {location : Nat}
    (run : store.releaseReservation location = .ok output) :
    output.live = store.live ∧ output.heap.allocs = store.heap.allocs ∧
      output.heap.frees = store.heap.frees + 1 := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.releaseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.releaseReservation, found] at run
      | none =>
          simp only [Store.releaseReservation, found, Except.ok.injEq] at run
          subst output
          exact ⟨rfl, rfl, rfl⟩

theorem Store.reuseReservation_accounting {store output : Store}
    {location payloadUnits : Nat} {world : Owned} {node : Node}
    (run : store.reuseReservation location world node payloadUnits = .ok output) :
    output.live = store.live + 1 ∧ output.heap.allocs = store.heap.allocs ∧
      output.heap.frees = store.heap.frees := by
  cases found : store.heap.nodes[location]? with
  | none => simp [Store.reuseReservation, found] at run
  | some slot =>
      cases slot with
      | some box => simp [Store.reuseReservation, found] at run
      | none =>
          simp only [Store.reuseReservation, found, Except.ok.injEq] at run
          subst output
          refine ⟨?_, rfl, rfl⟩
          simpa [Store.live_eq_countP] using
            (countP_update (new := some (NodeBox.mk world 1 node)) Option.isSome found)

/-! ## Credits retained by frames and continuations -/

def Credit.weight (credit : Credit) : Nat := if credit.isPresent then 1 else 0

theorem Credit.weight_absent {credit : Credit} (absent : credit.presence = .absent) :
    credit.weight = 0 := by
  rcases credit with ⟨layout, presence⟩
  cases absent
  rfl

theorem Credit.weight_present {credit : Credit} {reservation : Option Nat}
    (present : credit.presence = .present reservation) : credit.weight = 1 := by
  rcases credit with ⟨layout, presence⟩
  cases present
  rfl

theorem creditPresentCount_eq_countP (credits : Array (Option Credit)) :
    creditPresentCount credits = credits.countP (·.any Credit.isPresent) := by
  have worker : (fun (total : Nat) (credit : Option Credit) =>
      match credit with
      | some credit => if credit.isPresent then total + 1 else total
      | none => total) =
      (fun total credit => if credit.any Credit.isPresent then total + 1 else total) := by
    funext total credit
    cases credit <;> rfl
  unfold creditPresentCount
  calc
    _ = credits.foldl
        (fun total credit => if credit.any Credit.isPresent then total + 1 else total) 0 :=
      congrArg (fun f : Nat → Option Credit → Nat => credits.foldl f 0) worker
    _ = _ := by
      rw [← Array.foldl_toList, foldl_countP]
      simp

@[simp] theorem creditPresentCount_empty : creditPresentCount #[] = 0 := rfl

@[simp] theorem creditPresentCount_push (credits : Array (Option Credit)) (credit : Credit) :
    creditPresentCount (credits.push (some credit)) =
      creditPresentCount credits + credit.weight := by
  simp [creditPresentCount_eq_countP, ← Array.countP_toList, Credit.weight]

theorem creditPresentCount_map_some (credits : Array Credit) :
    creditPresentCount (credits.map some) = (credits.toList.map Credit.weight).sum := by
  rw [creditPresentCount_eq_countP, ← Array.countP_toList]
  simp only [Array.toList_map, List.countP_map]
  have listCount : ∀ credits : List Credit,
      credits.countP (fun credit => (some credit).any Credit.isPresent) =
        (credits.map Credit.weight).sum := by
    intro credits
    induction credits with
    | nil => rfl
    | cons credit rest ih =>
        simp only [Option.any_some] at ih
        simp [List.countP_cons, Credit.weight, ih, Nat.add_comm]
  exact listCount credits.toList

theorem CreditTake.presentCredits {frame target : Frame} {id : CreditId}
    {credit : Credit} (taken : CreditTake frame id target credit) :
    target.presentCredits + credit.weight = frame.presentCredits := by
  obtain ⟨targetEq, found⟩ := taken.target_eq
  rw [targetEq]
  simpa [Frame.presentCredits, creditPresentCount_eq_countP, Credit.weight] using
    (countP_update (new := none) (·.any Credit.isPresent) found)

theorem CreditTakeSequence.presentCredits {frame target : Frame}
    {ids : List CreditId} {credits : List Credit}
    (taken : CreditTakeSequence frame ids target credits) :
    target.presentCredits + (credits.map Credit.weight).sum = frame.presentCredits := by
  induction taken with
  | nil => simp
  | cons head tail ih =>
      have first := head.presentCredits
      simp only [List.map_cons, List.sum_cons]
      omega

theorem CreditTakeMany.presentCredits {frame target : Frame}
    {ids : Array CreditId} {credits : Array Credit}
    (taken : CreditTakeMany frame ids target credits) :
    target.presentCredits + creditPresentCount (credits.map some) = frame.presentCredits := by
  rw [creditPresentCount_map_some]
  exact taken.sequence.presentCredits

theorem NoLiveCredits.presentCredits {frame : Frame} (cleared : NoLiveCredits frame) :
    frame.presentCredits = 0 := by
  rw [Frame.presentCredits, creditPresentCount_eq_countP, Array.countP_eq_zero]
  intro slot member
  have absent := (Array.any_eq_false'.mp cleared) slot member
  cases slot <;> simp_all

theorem EdgeTransfer.presentCredits {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal} (transfer : EdgeTransfer frame edge implicitValues target) :
    target.presentCredits = frame.presentCredits := by
  obtain ⟨values, credits, after, block, _, taken, cleared, _, _, _, targetEq⟩ := transfer.parts
  have count := taken.presentCredits
  rw [cleared.presentCredits, Nat.zero_add] at count
  subst target
  exact count

private theorem foldl_weight {α : Type} (weight : α → Nat) (values : List α) (initial : Nat) :
    values.foldl (fun total value => total + weight value) initial =
      initial + (values.map weight).sum := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih => simp [ih, Nat.add_assoc]

theorem Machine.presentCredits_running (store : Store) (heapFuel : Nat)
    (frame : Frame) (stack : List Continuation) :
    (Machine.mk store heapFuel (.running frame stack)).presentCredits =
      frame.presentCredits + (stack.map Continuation.presentCredits).sum := by
  simp [Machine.presentCredits, foldl_weight]

end Ix.Compiler.IxIR2.Eval
