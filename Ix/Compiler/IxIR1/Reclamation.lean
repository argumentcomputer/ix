import Ix.Compiler.IxIR1.Progress

/-!
# IxIR₁ reclamation

`Sim.RootOwnership` deliberately records exact external and internal owner
counts without imposing a heap topology.  That is the right interface for
semantic simulation, but by itself it admits an unreachable cycle (and even
an isolated shared node with reference count zero).

The executable lowerer currently allocates by appending and emits no in-place
`reuse`.  Its runtime heaps therefore satisfy the separate history invariant
below: every live reference count is positive and every owning edge points
from a newer allocation to an older one.  Exact ownership plus this finite
allocation order is enough to rule out every live node once the root list is
empty.
-/

namespace Ix.Compiler.IxIR1.Reclamation

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Sim

private theorem bindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem bindErr {error α β : Type} (err : error)
    (next : α → Except error β) :
    ((Except.error err : Except error α) >>= next) = .error err := rfl

/-- The trace-level heap fact maintained by append-only IxIR₁ execution.

It is intentionally separate from `RootOwnership`: ownership proofs remain
insensitive to allocation history and `HeapIso`, while reclamation uses the
concrete append order of the current no-reuse lowerer. -/
structure AllocationOrderInvariant (store : Store) : Prop where
  rc_pos : ∀ {loc box}, store.get? loc = some box → 0 < box.rc
  child_lt : ∀ {parent box childLoc},
    store.get? parent = some box →
    RVal.loc childLoc ∈ nodeChildren box.node →
    childLoc < parent

/-- Every live partial-application node is genuinely partial: its stored
capture is strictly shorter than the arity at which it dispatches.  The
source evaluator establishes this at both PAP allocation sites, but its
unchecked heap type cannot express the fact directly. -/
structure PAPsUnder (store : Store) : Prop where
  captured_lt : ∀ {location world rc address arity captured},
    store.get? location =
      some ⟨world, rc, .papN address arity captured⟩ →
    captured.size < arity

namespace PAPsUnder

/-- The empty heap contains no malformed PAP. -/
theorem empty : PAPsUnder ({} : Store) := by
  constructor
  intro location world rc address arity captured found
  simp [Store.get?] at found

/-- Removing live nodes or changing only their reference counts preserves
PAP under-saturation. -/
theorem ofRestricts {before after : Store} (h : PAPsUnder before)
    (restricts : StoreGraphRestricts before after) : PAPsUnder after := by
  constructor
  intro location world rc address arity captured found
  obtain ⟨beforeRc, beforeFound⟩ := restricts found
  exact h.captured_lt beforeFound

/-- A shared retain changes only the selected reference count. -/
theorem incRcStore {store : Store} {location rc : Nat} {node : Node}
    (h : PAPsUnder store)
    (found : store.get? location = some ⟨.shared, rc, node⟩) :
    PAPsUnder (Sim.incRcStore store location ⟨.shared, rc, node⟩) :=
  h.ofRestricts (StoreGraphRestricts.incRcStore found)

/-- Killing a live slot cannot expose a malformed PAP. -/
theorem kill {store : Store} {location : Nat} {box : NodeBox}
    (h : PAPsUnder store) (found : store.get? location = some box) :
    PAPsUnder (store.kill location) :=
  h.ofRestricts (StoreGraphRestricts.kill found)

/-- Retaining a vector of shared values cannot change PAP payloads. -/
theorem dupVals {store store' : Store} {values : List RVal}
    (h : PAPsUnder store) (run : dupVals store values = .ok store') :
    PAPsUnder store' := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except Err Store) = .ok store' at run
      injection run with storeEq
      subst store'
      exact h
  | cons head tail ih =>
      cases head with
      | lit literal =>
          simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at run
          exact ih h run
      | erased =>
          simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at run
          exact ih h run
      | loc location =>
          simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at run
          cases found : store.get? location with
          | none => simp [found, bindErr] at run
          | some box =>
              cases box with
              | mk world rc node =>
                  cases world with
                  | unique => simp [found, bindErr] at run
                  | shared =>
                      simp only [found] at run
                      exact ih (h.incRcStore found) run

/-- Appending a constructor preserves all existing PAP payloads. -/
theorem allocCtor {store : Store} (h : PAPsUnder store)
    (world : Ixon.Owned) (cid : CtorId) (fields : Array RVal) :
    PAPsUnder (store.allocNode world (.ctorN cid fields)).1 := by
  constructor
  intro location boxWorld rc address arity captured found
  by_cases fresh : location = store.nodes.size
  · subst location
    have allocated := HeapIso.get?_allocNode_new store world
      (.ctorN cid fields)
    have impossible :
        (⟨boxWorld, rc, .papN address arity captured⟩ : NodeBox) =
          ⟨world, 1, .ctorN cid fields⟩ :=
      Option.some.inj (found.symm.trans allocated)
    cases impossible
  · exact h.captured_lt (HeapIso.get?_of_allocNode_old fresh found)

/-- Appending a checked under-saturated PAP preserves the global property. -/
theorem allocPap {store : Store} (h : PAPsUnder store)
    (world : Ixon.Owned) (address : Ixon.Address) (arity : Nat)
    (captured : Array RVal) (under : captured.size < arity) :
    PAPsUnder (store.allocNode world (.papN address arity captured)).1 := by
  constructor
  intro location boxWorld rc foundAddress foundArity foundCaptured found
  by_cases fresh : location = store.nodes.size
  · subst location
    have allocated := HeapIso.get?_allocNode_new store world
      (.papN address arity captured)
    have boxEq :
        (⟨boxWorld, rc, .papN foundAddress foundArity foundCaptured⟩ :
          NodeBox) = ⟨world, 1, .papN address arity captured⟩ :=
      Option.some.inj (found.symm.trans allocated)
    cases boxEq
    exact under
  · exact h.captured_lt (HeapIso.get?_of_allocNode_old fresh found)

/-- Shared and unique recursive releases only remove nodes or alter RCs. -/
theorem dropVal {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} (h : PAPsUnder store)
    (run : Ix.Compiler.IxIR1.dropVal ctx fuel store value = .ok store') :
    PAPsUnder store' :=
  h.ofRestricts (dropVal_restricts run)

theorem dropMany {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal} (h : PAPsUnder store)
    (run : Ix.Compiler.IxIR1.dropMany ctx fuel store values = .ok store') :
    PAPsUnder store' :=
  h.ofRestricts (dropMany_restricts run)

theorem dropUVal {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} (h : PAPsUnder store)
    (run : Ix.Compiler.IxIR1.dropUVal ctx fuel store value = .ok store') :
    PAPsUnder store' :=
  h.ofRestricts (dropUVal_restricts run)

theorem dropManyU {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal} (h : PAPsUnder store)
    (run : Ix.Compiler.IxIR1.dropManyU ctx fuel store values = .ok store') :
    PAPsUnder store' :=
  h.ofRestricts (dropManyU_restricts run)

end PAPsUnder

/-- A runtime value names only a slot already present in the store.  Unlike
`LiveRVal`, this deliberately permits a dead-but-allocated slot: stale values
can remain in an evaluator environment after their final release, but they
still cannot predict a future append location. -/
def ValueInBounds (store : Store) : RVal → Prop
  | .loc loc => loc < store.nodes.size
  | .lit _ | .erased => True

def ValuesInBounds (store : Store) (values : List RVal) : Prop :=
  ∀ value ∈ values, ValueInBounds store value

theorem ValueInBounds.mono {before after : Store} {value : RVal}
    (hsize : before.nodes.size ≤ after.nodes.size)
    (h : ValueInBounds before value) : ValueInBounds after value := by
  cases value with
  | loc loc => exact Nat.lt_of_lt_of_le h hsize
  | lit literal => trivial
  | erased => trivial

theorem ValuesInBounds.mono {before after : Store} {values : List RVal}
    (hsize : before.nodes.size ≤ after.nodes.size)
    (h : ValuesInBounds before values) : ValuesInBounds after values := by
  intro value hvalue
  exact (h value hvalue).mono hsize

theorem ValuesInBounds.nil (store : Store) : ValuesInBounds store [] := by
  simp [ValuesInBounds]

theorem ValuesInBounds.cons {store : Store} {value : RVal}
    {values : List RVal} (hvalue : ValueInBounds store value)
    (hvalues : ValuesInBounds store values) :
    ValuesInBounds store (value :: values) := by
  intro found hfound
  rcases List.mem_cons.mp hfound with rfl | htail
  · exact hvalue
  · exact hvalues found htail

theorem ValuesInBounds.append {store : Store} {left right : List RVal}
    (hleft : ValuesInBounds store left)
    (hright : ValuesInBounds store right) :
    ValuesInBounds store (left ++ right) := by
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact hleft value hvalue
  · exact hright value hvalue

theorem ValuesInBounds.reverse {store : Store} {values : List RVal}
    (h : ValuesInBounds store values) :
    ValuesInBounds store values.reverse := by
  intro value hvalue
  exact h value (by simpa using hvalue)

theorem ValuesInBounds.take {store : Store} {values : List RVal}
    (h : ValuesInBounds store values) (n : Nat) :
    ValuesInBounds store (values.take n) := by
  intro value hvalue
  exact h value (List.mem_of_mem_take hvalue)

theorem ValuesInBounds.drop {store : Store} {values : List RVal}
    (h : ValuesInBounds store values) (n : Nat) :
    ValuesInBounds store (values.drop n) := by
  intro value hvalue
  exact h value (List.mem_of_mem_drop hvalue)

private theorem ValuesInBounds.foldlPrependList {store : Store}
    {values env : List RVal} (hvalues : ValuesInBounds store values)
    (henv : ValuesInBounds store env) :
    ValuesInBounds store (values.foldl (fun acc value => value :: acc) env) := by
  induction values generalizing env with
  | nil => exact henv
  | cons value values ih =>
    simp only [List.foldl_cons]
    exact ih
      (fun found hfound =>
        hvalues found (List.mem_cons_of_mem value hfound))
      (henv.cons (hvalues value (List.mem_cons_self)))

theorem ValuesInBounds.foldlPrepend {store : Store} {values : Array RVal}
    {env : List RVal} (hvalues : ValuesInBounds store values.toList)
    (henv : ValuesInBounds store env) :
    ValuesInBounds store (values.foldl (fun acc value => value :: acc) env) := by
  rw [← Array.foldl_toList]
  exact hvalues.foldlPrependList henv

theorem RVal.inBounds_of_get? {store : Store} {loc : Nat} {box : NodeBox}
    (hget : store.get? loc = some box) :
    ValueInBounds store (RVal.loc loc) :=
  (Array.getElem?_eq_some_iff.mp (nodes_get?_of_get? hget)).1

/-- Backward edges in a live node are automatically allocated and bounded. -/
theorem AllocationOrderInvariant.childrenInBounds {store : Store}
    (h : AllocationOrderInvariant store) {parent : Nat} {box : NodeBox}
    (hget : store.get? parent = some box) :
    ValuesInBounds store (nodeChildren box.node) := by
  intro child hchild
  cases child with
  | loc childLoc =>
    exact Nat.lt_trans (h.child_lt hget hchild)
      (RVal.inBounds_of_get? hget)
  | lit literal => trivial
  | erased => trivial

theorem resolveAtom_inBounds {store : Store} {env : List RVal}
    {atom : Atom} {value : RVal} (henv : ValuesInBounds store env)
    (hresolve : resolveAtom env atom = .ok value) :
    ValueInBounds store value := by
  cases atom with
  | var idx =>
    cases hget : env[idx]? with
    | none => simp [resolveAtom, hget] at hresolve
    | some found =>
      simp [resolveAtom, hget] at hresolve
      subst value
      exact henv found (List.mem_of_getElem? hget)
  | lit literal =>
    simp [resolveAtom] at hresolve
    subst value
    trivial
  | erased =>
    simp [resolveAtom] at hresolve
    subst value
    trivial

private theorem resolveAtomsList_inBounds {store : Store}
    {env : List RVal} (henv : ValuesInBounds store env) :
    ∀ (atoms : List Atom) (acc values : List RVal),
      ValuesInBounds store acc →
      atoms.foldlM
          (fun acc atom => do
            pure (acc ++ [← resolveAtom env atom])) acc = .ok values →
      ValuesInBounds store values
  | [], acc, values, hacc, heval => by
      change (Except.ok acc : Except Err (List RVal)) = .ok values at heval
      injection heval with hvalues
      subst values
      exact hacc
  | atom :: atoms, acc, values, hacc, heval => by
      simp only [List.foldlM_cons] at heval
      cases hresolve : resolveAtom env atom with
      | error err => simp [hresolve, bindErr] at heval
      | ok value =>
        rw [hresolve, bindOk] at heval
        apply resolveAtomsList_inBounds henv atoms (acc ++ [value]) values
        · exact hacc.append
            ((ValuesInBounds.nil store).cons
              (resolveAtom_inBounds henv hresolve))
        · exact heval

theorem resolveAtoms_inBounds {store : Store} {env : List RVal}
    {atoms : Array Atom} {values : List RVal}
    (henv : ValuesInBounds store env)
    (heval : resolveAtoms env atoms = .ok values) :
    ValuesInBounds store values := by
  rw [resolveAtoms, ← Array.foldlM_toList] at heval
  exact resolveAtomsList_inBounds henv atoms.toList [] values
    (ValuesInBounds.nil store) heval

/-! ## Counter and live-slot accounting -/

private def liveCountList {alpha : Type} : List (Option alpha) → Nat
  | [] => 0
  | none :: rest => liveCountList rest
  | some _ :: rest => liveCountList rest + 1

private theorem liveCountList_eq_zero_iff_no_some {alpha : Type} :
    ∀ values : List (Option alpha),
      liveCountList values = 0 ↔ ∀ value, some value ∉ values
  | [] => by simp [liveCountList]
  | none :: rest => by
      simp [liveCountList, liveCountList_eq_zero_iff_no_some rest]
  | some head :: rest => by
      constructor
      · intro hzero
        simp [liveCountList] at hzero
      · intro hnone
        exact False.elim (hnone head (by simp))

private theorem foldl_live_eq {alpha : Type}
    (values : List (Option alpha)) (acc : Nat) :
    values.foldl (fun n value => if value.isSome then n + 1 else n) acc =
      acc + liveCountList values := by
  induction values generalizing acc with
  | nil => simp [liveCountList]
  | cons head tail ih =>
      cases head <;> simp [liveCountList, ih] <;> omega

private theorem Store.live_eq_liveCountList (store : Store) :
    store.live = liveCountList store.nodes.toList := by
  rw [Store.live, ← Array.foldl_toList]
  simpa using foldl_live_eq store.nodes.toList 0

/-- A store has no live nodes exactly when its slot array contains no live
box.  This representation bridge is useful when a heap is related by a
location bijection rather than by literal array equality. -/
theorem Store.live_eq_zero_iff_no_live_slot (store : Store) :
    store.live = 0 ↔ ∀ box, some box ∉ store.nodes := by
  rw [Store.live_eq_liveCountList]
  simpa using liveCountList_eq_zero_iff_no_some store.nodes.toList

private theorem liveCountList_set_none {alpha : Type} :
    ∀ {values : List (Option alpha)} {index : Nat} {value : alpha},
      values[index]? = some (some value) →
      liveCountList (values.set index none) + 1 = liveCountList values
  | [], index, value, hget => by simp at hget
  | head :: tail, 0, value, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      simp [liveCountList]
  | head :: tail, index + 1, value, hget => by
      simp only [List.getElem?_cons_succ] at hget
      have ih := liveCountList_set_none hget
      cases head <;> simp [liveCountList] at ih ⊢ <;> omega

private theorem liveCountList_set_some {alpha : Type} :
    ∀ {values : List (Option alpha)} {index : Nat} {old new : alpha},
      values[index]? = some (some old) →
      liveCountList (values.set index (some new)) = liveCountList values
  | [], index, old, new, hget => by simp at hget
  | head :: tail, 0, old, new, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      simp [liveCountList]
  | head :: tail, index + 1, old, new, hget => by
      simp only [List.getElem?_cons_succ] at hget
      have ih := liveCountList_set_some (new := new) hget
      cases head <;> simp [liveCountList] at ih ⊢ <;> omega

private theorem Store.live_allocNode (store : Store) (world : Ixon.Owned)
    (node : Node) :
    (store.allocNode world node).1.live = store.live + 1 := by
  simp [Store.live, Store.allocNode]

private theorem Store.live_kill {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    (store.kill loc).live + 1 = store.live := by
  have hnodes := nodes_get?_of_get? hget
  have hlist : store.nodes.toList[loc]? = some (some box) := by
    simpa using hnodes
  rw [Store.live_eq_liveCountList, Store.live_eq_liveCountList]
  simp only [Store.kill, Array.toList_set!]
  exact liveCountList_set_none hlist

private theorem Store.live_setBox {store : Store} {loc : Nat}
    {old new : NodeBox} (hget : store.get? loc = some old) :
    (store.setBox loc new).live = store.live := by
  have hnodes := nodes_get?_of_get? hget
  have hlist : store.nodes.toList[loc]? = some (some old) := by
    simpa using hnodes
  rw [Store.live_eq_liveCountList, Store.live_eq_liveCountList]
  simp only [Store.setBox, Array.toList_set!]
  exact liveCountList_set_some hlist

/-- The store-history facts preserved by every successful evaluator entry.
Besides monotone slot capacity and reuse count, the two balance equations say
that allocation exactly accounts for new slots and for the sum of live nodes
and completed frees. -/
structure StoreFootprint (before after : Store) : Prop where
  nodes_size : before.nodes.size ≤ after.nodes.size
  reuses : before.reuses ≤ after.reuses
  allocation_balance :
    after.nodes.size + before.allocs = before.nodes.size + after.allocs
  live_balance :
    after.live + after.frees + before.allocs =
      before.live + before.frees + after.allocs

theorem StoreFootprint.refl (store : Store) : StoreFootprint store store := by
  constructor <;> omega

theorem StoreFootprint.trans {first second third : Store}
    (h₁ : StoreFootprint first second) (h₂ : StoreFootprint second third) :
    StoreFootprint first third := by
  constructor
  · exact Nat.le_trans h₁.nodes_size h₂.nodes_size
  · exact Nat.le_trans h₁.reuses h₂.reuses
  · have hfirst := h₁.allocation_balance
    have hsecond := h₂.allocation_balance
    omega
  · have hfirst := h₁.live_balance
    have hsecond := h₂.live_balance
    omega

private theorem footprint_allocNode (store : Store) (world : Ixon.Owned)
    (node : Node) :
    StoreFootprint store (store.allocNode world node).1 := by
  constructor
  · simp [Store.allocNode]
  · simp [Store.allocNode]
  · simp [Store.allocNode]
    omega
  · rw [Store.live_allocNode]
    simp [Store.allocNode]
    omega

private theorem footprint_setBox {store : Store} {loc : Nat}
    {old new : NodeBox} (hget : store.get? loc = some old) :
    StoreFootprint store (store.setBox loc new) := by
  constructor
  · simp [Store.setBox]
  · simp [Store.setBox]
  · simp [Store.setBox]
  · rw [Store.live_setBox hget]
    simp [Store.setBox]

private theorem footprint_kill {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    StoreFootprint store (store.kill loc) := by
  constructor
  · simp [Store.kill]
  · simp [Store.kill]
  · simp [Store.kill]
  · have hlive := Store.live_kill hget
    have hfrees : (store.kill loc).frees = store.frees + 1 := rfl
    have hallocs : (store.kill loc).allocs = store.allocs := rfl
    rw [hfrees, hallocs]
    omega

private theorem footprint_rcTick (store : Store) :
    StoreFootprint store store.rcTick := by
  constructor
  · simp [Store.rcTick]
  · simp [Store.rcTick]
  · simp [Store.rcTick]
  · change store.live + store.frees + store.allocs =
      store.live + store.frees + store.allocs
    rfl

private theorem footprint_reuse {store : Store} {loc : Nat}
    {old : NodeBox} (hget : store.get? loc = some old) (node : Node) :
    StoreFootprint store
      { store.setBox loc ⟨.unique, 1, node⟩ with
        reuses := (store.setBox loc ⟨.unique, 1, node⟩).reuses + 1 } := by
  have hset := footprint_setBox (new := ⟨.unique, 1, node⟩) hget
  constructor
  · simpa using hset.nodes_size
  · simp [Store.setBox]
  · simpa using hset.allocation_balance
  · change (store.setBox loc ⟨.unique, 1, node⟩).live +
      (store.setBox loc ⟨.unique, 1, node⟩).frees + store.allocs =
        store.live + store.frees +
          (store.setBox loc ⟨.unique, 1, node⟩).allocs
    exact hset.live_balance

private theorem footprint_incRcStore {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    StoreFootprint store (Sim.incRcStore store loc box) := by
  unfold Sim.incRcStore
  exact (footprint_setBox (new := { box with rc := box.rc + 1 }) hget).trans
    (footprint_rcTick _)

private theorem footprint_decRcStore {store : Store} {loc : Nat}
    {box : NodeBox} (hget : store.get? loc = some box) :
    StoreFootprint store (Sim.decRcStore store loc box) := by
  unfold Sim.decRcStore
  apply (footprint_rcTick store).trans
  apply footprint_setBox
  simpa using hget

/-- The pap-retain helper only updates RC state. -/
theorem dupVals_footprint {store store' : Store} {values : List RVal}
    (heval : dupVals store values = .ok store') :
    StoreFootprint store store' := by
  induction values generalizing store with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    exact StoreFootprint.refl store
  | cons head tail ih =>
    cases head with
    | lit literal =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih heval
    | erased =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih heval
    | loc loc =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      cases hget : store.get? loc with
      | none => simp [hget, bindErr] at heval
      | some box =>
        cases box with
        | mk world rc node =>
          cases world with
          | unique => simp [hget, bindErr] at heval
          | shared =>
            simp only [hget] at heval
            exact (footprint_incRcStore hget).trans
              (ih heval)

private def FootprintAt (fuel : Nat) : Prop :=
  (∀ ctx cur store env code store' value,
    runCode ctx fuel cur store env code = .ok (store', value) →
      StoreFootprint store store') ∧
  (∀ ctx cur store env op store' value,
    runOp ctx fuel cur store env op = .ok (store', value) →
      StoreFootprint store store') ∧
  (∀ ctx address args store store' value,
    invoke ctx fuel address args store = .ok (store', value) →
      StoreFootprint store store') ∧
  (∀ ctx store function args store' value,
    applyGo ctx fuel store function args = .ok (store', value) →
      StoreFootprint store store') ∧
  (∀ ctx store value store',
    dropVal ctx fuel store value = .ok store' →
      StoreFootprint store store') ∧
  (∀ ctx store values store',
    dropMany ctx fuel store values = .ok store' →
      StoreFootprint store store') ∧
  (∀ ctx store value store',
    dropUVal ctx fuel store value = .ok store' →
      StoreFootprint store store') ∧
  (∀ ctx store values store',
    dropManyU ctx fuel store values = .ok store' →
      StoreFootprint store store')

/-- Every successful evaluator entry is monotone in allocated slot capacity
and in the reuse counter.  This history theorem is independent of ownership
and is what lets an equal endpoint reuse count rule out reuse in every
intermediate call. -/
private theorem footprintAt : ∀ fuel, FootprintAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value h
      rw [runCode.eq_def] at h
      simp at h
    · intro ctx cur store env op store' value h
      rw [runOp.eq_def] at h
      simp at h
    · intro ctx address args store store' value h
      rw [invoke.eq_def] at h
      simp at h
    · intro ctx store function args store' value h
      rw [applyGo.eq_def] at h
      simp at h
    · intro ctx store value store' h
      rw [dropVal.eq_def] at h
      simp at h
    · intro ctx store values store' h
      rw [dropMany.eq_def] at h
      simp at h
    · intro ctx store value store' h
      rw [dropUVal.eq_def] at h
      simp at h
    · intro ctx store values store' h
      rw [dropManyU.eq_def] at h
      simp at h
  | succ fuel ih =>
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply, ihDrop, ihDropMany,
      ihDropU, ihDropManyU⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value h
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at h
        dsimp only at h
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at h; contradiction
        | ok result =>
          rw [hresolve, bindOk] at h
          have hpair := Except.ok.inj h
          cases hpair
          exact StoreFootprint.refl store
      | letOp op rest =>
        rw [runCode.eq_def] at h
        dsimp only at h
        cases hop : runOp ctx fuel cur store env op with
        | error err => rw [hop, bindErr] at h; contradiction
        | ok opOut =>
          rcases opOut with ⟨middle, opValue⟩
          rw [hop, bindOk] at h
          exact (ihOp _ _ _ _ _ _ _ hop).trans
            (ihCode _ _ _ _ _ _ _ h)
      | case scrut peelNat alts =>
        rw [runCode.eq_def] at h
        dsimp only at h
        cases hscrut : resolveAtom env scrut with
        | error err => rw [hscrut, bindErr] at h; contradiction
        | ok scrutValue =>
          rw [hscrut, bindOk] at h
          cases scrutValue with
          | loc loc =>
            dsimp only at h
            cases hbox : store.get? loc with
            | none => simp [hbox] at h
            | some box =>
              simp only [hbox] at h
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => simp at h
                | ctorN cid fields =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == cid.cidx) with
                  | none => simp [halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at h
                        exact ihCode _ _ _ _ _ _ _ h
                      · simp [halt, hsize] at h
          | lit literal =>
            cases literal with
            | str string => simp at h
            | nat n =>
              cases hpeel : peelNat with
              | false => simp [hpeel] at h
              | true =>
                cases n with
                | zero =>
                  cases halt : alts.find? (fun alt => alt.cidx == 0) with
                  | none => simp [hpeel, halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at h
                        exact ihCode _ _ _ _ _ _ _ h
                      | succ fieldCount => simp [hpeel, halt] at h
                | succ n =>
                  cases halt : alts.find? (fun alt => alt.cidx == 1) with
                  | none => simp [hpeel, halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero => simp [hpeel, halt] at h
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at h
                          exact ihCode _ _ _ _ _ _ _ h
                        | succ fieldCount => simp [hpeel, halt] at h
          | erased => simp at h
    · intro ctx cur store env op store' value h
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at h; contradiction
        | ok result =>
          rw [hresolve, bindOk] at h
          have hpair := Except.ok.inj h
          cases hpair
          exact StoreFootprint.refl store
      | alloc world cid atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          have hpair := Except.ok.inj h
          cases hpair
          exact footprint_allocNode store world (.ctorN cid values.toArray)
      | reuse target cid atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          cases htarget : resolveAtom env target with
          | error err => rw [htarget, bindErr] at h; contradiction
          | ok targetValue =>
            rw [htarget, bindOk] at h
            cases targetValue with
            | lit literal => simp at h
            | erased => simp at h
            | loc loc =>
              cases hbox : store.get? loc with
              | none => simp [hbox] at h
              | some box =>
                simp only [hbox] at h
                cases box with
                | mk world rc node =>
                  cases world with
                  | shared => simp at h
                  | unique =>
                    dsimp only at h
                    have hpair := Except.ok.inj h
                    cases hpair
                    exact footprint_reuse hbox
                      (.ctorN cid values.toArray)
      | free target =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at h; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          cases targetValue with
          | lit literal => simp at h
          | erased => simp at h
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at h
            | some box =>
              simp only [hbox] at h
              cases box with
              | mk world rc node =>
                cases world with
                | shared => simp at h
                | unique =>
                  have hpair := Except.ok.inj h
                  cases hpair
                  exact footprint_kill hbox
      | dup target =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at h; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | erased =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at h
            | some box =>
              simp only [hbox] at h
              cases box with
              | mk world rc node =>
                cases world with
                | unique => simp at h
                | shared =>
                  have hpair := Except.ok.inj h
                  cases hpair
                  exact footprint_incRcStore hbox
      | drop target =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at h; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | erased =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | loc loc =>
            dsimp only at h
            cases hdrop : dropVal ctx fuel store (.loc loc) with
            | error err => rw [hdrop, bindErr] at h; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at h
              have hpair := Except.ok.inj h
              cases hpair
              exact ihDrop _ _ _ _ hdrop
      | dropU target =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at h; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | erased =>
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
          | loc loc =>
            dsimp only at h
            cases hdrop : dropUVal ctx fuel store (.loc loc) with
            | error err => rw [hdrop, bindErr] at h; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at h
              have hpair := Except.ok.inj h
              cases hpair
              exact ihDropU _ _ _ _ hdrop
      | fetch target field =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at h; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          cases targetValue with
          | lit literal => simp at h
          | erased => simp at h
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at h
            | some box =>
              simp only [hbox] at h
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => simp at h
                | ctorN cid fields =>
                  cases hfield : fields[field]? with
                  | none => simp [hfield] at h
                  | some result =>
                    simp only [hfield] at h
                    have hpair := Except.ok.inj h
                    cases hpair
                    exact StoreFootprint.refl store
      | call address atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          exact ihInvoke _ _ _ _ _ _ h
      | callSelf atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h
            cases hcode : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err => rw [hcode, bindErr] at h; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hcode, bindOk] at h
              obtain ⟨hresult, _⟩ := checkResultWorld_ok h
              cases hresult
              exact ihCode _ _ _ _ _ _ _ hcode
          · simp [harity] at h
      | papp address atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          cases hdecl : ctx.decls address with
          | none => simp [hdecl] at h
          | some decl =>
            simp only [hdecl] at h
            by_cases hlen : values.length < declArity decl
            · simp only [hlen, if_true] at h
              have hpair := Except.ok.inj h
              cases hpair
              exact footprint_allocNode store .shared
                (.papN address (declArity decl) values.toArray)
            · simp only [hlen, if_false] at h
              contradiction
      | apply function atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hfunction : resolveAtom env function with
        | error err => rw [hfunction, bindErr] at h; contradiction
        | ok functionValue =>
          rw [hfunction, bindOk] at h
          cases hargs : resolveAtoms env atoms with
          | error err => rw [hargs, bindErr] at h; contradiction
          | ok values =>
            rw [hargs, bindOk] at h
            exact ihApply _ _ _ _ _ _ h
      | extern address atoms =>
        rw [runOp.eq_def] at h
        dsimp only at h
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at h; contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          cases hcall : callScalarOracle ctx address values with
          | error err => rw [hcall, bindErr] at h; contradiction
          | ok result =>
            rw [hcall, bindOk] at h
            have hpair := Except.ok.inj h
            cases hpair
            exact StoreFootprint.refl store
    · intro ctx address args store store' value h
      rw [invoke.eq_def] at h
      dsimp only at h
      cases hdecl : ctx.decls address with
      | none => simp [hdecl] at h
      | some decl =>
        simp only [hdecl] at h
        cases decl with
        | extern arity =>
          cases harity : args.length != arity
          · simp only [harity, Bool.false_eq_true, if_false] at h
            cases hcall : callScalarOracle ctx address args with
            | error err => simp [hcall] at h
            | ok result =>
              simp only [hcall] at h
              have hpair := Except.ok.inj h
              cases hpair
              exact StoreFootprint.refl store
          · simp [harity] at h
        | fn d =>
          cases harity : args.length != d.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h
            cases hcode : runCode ctx fuel d store args.reverse d.body with
            | error err => rw [hcode, bindErr] at h; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hcode, bindOk] at h
              obtain ⟨hresult, _⟩ := checkResultWorld_ok h
              cases hresult
              exact ihCode _ _ _ _ _ _ _ hcode
          · simp [harity] at h
    · intro ctx store function args store' value h
      rw [applyGo.eq_def] at h
      dsimp only at h
      cases function with
      | lit literal => simp at h
      | erased =>
        dsimp only at h
        cases hdrop : dropMany ctx fuel store args with
        | error err => rw [hdrop, bindErr] at h; contradiction
        | ok dropped =>
          rw [hdrop, bindOk] at h
          have hpair := Except.ok.inj h
          cases hpair
          exact ihDropMany _ _ _ _ hdrop
      | loc loc =>
        dsimp only at h
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields =>
              dsimp only at h
              simp at h
            | papN address arity captured =>
              dsimp only at h
              cases hdup : dupVals store captured.toList with
              | error err => rw [hdup, bindErr] at h; contradiction
              | ok duplicated =>
                rw [hdup, bindOk] at h
                cases hdrop : dropVal ctx fuel duplicated (.loc loc) with
                | error err => rw [hdrop, bindErr] at h; contradiction
                | ok ready =>
                  rw [hdrop, bindOk] at h
                  have hprefix := (dupVals_footprint hdup).trans
                    (ihDrop _ _ _ _ hdrop)
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder] at h
                    have hpair := Except.ok.inj h
                    cases hpair
                    exact hprefix.trans
                      (footprint_allocNode ready .shared
                        (.papN address arity
                          (captured.toList ++ args).toArray))
                  · simp only [hunder] at h
                    cases hexact :
                        (captured.toList ++ args).length == arity
                    · simp only [hexact, Bool.false_eq_true, if_false] at h
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at h
                            contradiction
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at h
                            exact hprefix.trans
                              ((ihInvoke _ _ _ _ _ _ hinvoke).trans
                                (ihApply _ _ _ _ _ _ h))
                    · simp only [hexact, if_true] at h
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h
                          exact hprefix.trans (ihInvoke _ _ _ _ _ _ h)
    · intro ctx store value store' h
      rw [dropVal.eq_def] at h
      dsimp only at h
      cases value with
      | lit literal =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | erased =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | loc loc =>
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at h
            | shared =>
              cases hrc : rc == 1
              · simp only [hrc, Bool.false_eq_true, if_false] at h
                injection h with hstore
                subst store'
                exact footprint_decRcStore hbox
              · simp only [hrc, if_true] at h
                have hprefix := (footprint_rcTick store).trans
                  (footprint_kill (by simpa using hbox))
                cases node with
                | ctorN cid fields =>
                  exact hprefix.trans (ihDropMany _ _ _ _ h)
                | papN address arity args =>
                  exact hprefix.trans (ihDropMany _ _ _ _ h)
    · intro ctx store values store' h
      rw [dropMany.eq_def] at h
      dsimp only at h
      cases values with
      | nil =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | cons value rest =>
        dsimp only at h
        cases hdrop : dropVal ctx fuel store value with
        | error err => rw [hdrop, bindErr] at h; contradiction
        | ok middle =>
          rw [hdrop, bindOk] at h
          exact (ihDrop _ _ _ _ hdrop).trans
            (ihDropMany _ _ _ _ h)
    · intro ctx store value store' h
      rw [dropUVal.eq_def] at h
      dsimp only at h
      cases value with
      | lit literal =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | erased =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | loc loc =>
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at h
            | unique =>
              cases node with
              | papN address arity args => simp at h
              | ctorN cid fields =>
                exact (footprint_kill hbox).trans
                  (ihDropManyU _ _ _ _ h)
    · intro ctx store values store' h
      rw [dropManyU.eq_def] at h
      dsimp only at h
      cases values with
      | nil =>
        injection h with hstore
        subst store'
        exact StoreFootprint.refl store
      | cons value rest =>
        dsimp only at h
        cases hdrop : dropUVal ctx fuel store value with
        | error err => rw [hdrop, bindErr] at h; contradiction
        | ok middle =>
          rw [hdrop, bindOk] at h
          exact (ihDropU _ _ _ _ hdrop).trans
            (ihDropManyU _ _ _ _ h)

theorem runCode_footprint {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {code : Code} {value : RVal}
    (heval : runCode ctx fuel cur store env code = .ok (store', value)) :
    StoreFootprint store store' :=
  (footprintAt fuel).1 ctx cur store env code store' value heval

theorem runOp_footprint {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {op : Op} {value : RVal}
    (heval : runOp ctx fuel cur store env op = .ok (store', value)) :
    StoreFootprint store store' :=
  (footprintAt fuel).2.1 ctx cur store env op store' value heval

theorem invoke_footprint {ctx : Ctx} {fuel : Nat} {address : Ixon.Address}
    {args : List RVal} {store store' : Store} {value : RVal}
    (heval : invoke ctx fuel address args store = .ok (store', value)) :
    StoreFootprint store store' :=
  (footprintAt fuel).2.2.1 ctx address args store store' value heval

theorem applyGo_footprint {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {function : RVal} {args : List RVal} {value : RVal}
    (heval : applyGo ctx fuel store function args = .ok (store', value)) :
    StoreFootprint store store' :=
  (footprintAt fuel).2.2.2.1 ctx store function args store' value heval

theorem runMain_footprint {ctx : Ctx} {fuel : Nat} {code : Code}
    {store : Store} {value : RVal}
    (heval : runMain ctx code fuel = .ok (store, value)) :
    StoreFootprint ({} : Store) store :=
  runCode_footprint heval

/-- Every slot in a fresh successful run comes from exactly one allocation.
Reuse overwrites an existing live slot and therefore changes neither side. -/
theorem runMain_nodes_size_eq_allocs {ctx : Ctx} {fuel : Nat} {code : Code}
    {store : Store} {value : RVal}
    (heval : runMain ctx code fuel = .ok (store, value)) :
    store.nodes.size = store.allocs := by
  have hbalance := (runMain_footprint heval).allocation_balance
  simpa using hbalance

/-- Fresh successful execution exactly partitions allocations into live nodes
and completed frees.  In-place reuse preserves liveness and does not count as
either allocation or free. -/
theorem runMain_live_add_frees_eq_allocs
    {ctx : Ctx} {fuel : Nat} {code : Code}
    {store : Store} {value : RVal}
    (heval : runMain ctx code fuel = .ok (store, value)) :
    store.live + store.frees = store.allocs := by
  have hbalance := (runMain_footprint heval).live_balance
  have hemptyLive : ({} : Store).live = 0 := rfl
  rw [hemptyLive, Nat.zero_add] at hbalance
  simpa using hbalance

/-- A counter-only consequence of exact live-slot accounting. -/
theorem runMain_frees_le_allocs {ctx : Ctx} {fuel : Nat} {code : Code}
    {store : Store} {value : RVal}
    (heval : runMain ctx code fuel = .ok (store, value)) :
    store.frees ≤ store.allocs := by
  have hbalance := runMain_live_add_frees_eq_allocs heval
  omega

theorem AllocationOrderInvariant.empty :
    AllocationOrderInvariant ({} : Store) := by
  constructor <;> intro <;> simp [Store.get?] at *

/-- Membership in the flattened edge multiset has a concrete live parent.
This is the converse direction to `Sim.child_location_mem_edgeLocations`.
-/
theorem parent_of_mem_edgeLocations {store : Store} {childLoc : Nat}
    (h : childLoc ∈ edgeLocations store) :
    ∃ parent box, store.get? parent = some box ∧
      RVal.loc childLoc ∈ nodeChildren box.node := by
  rw [edgeLocations, List.mem_flatMap] at h
  obtain ⟨slot, hslot, hedge⟩ := h
  cases slot with
  | none => simp [slotEdgeLocations] at hedge
  | some box =>
    have harray : some box ∈ store.nodes := by simpa using hslot
    obtain ⟨parent, hparentArray⟩ :=
      (Array.mem_iff_getElem?).mp harray
    have hparent : store.get? parent = some box := by
      rw [Store.get?, hparentArray]
      rfl
    change childLoc ∈ (nodeChildren box.node).filterMap rvalLocation?
      at hedge
    rw [List.mem_filterMap] at hedge
    obtain ⟨child, hchild, hloc⟩ := hedge
    cases child with
    | loc loc =>
      simp [rvalLocation?] at hloc
      subst loc
      exact ⟨parent, box, hparent, hchild⟩
    | lit literal => simp [rvalLocation?] at hloc
    | erased => simp [rvalLocation?] at hloc

/-- With no external roots, a live node satisfying exact ownership has at
least one incoming heap edge.  Positivity is needed only for the shared
case; unique ownership already fixes the incoming count at one. -/
theorem incoming_pos_of_live {store : Store}
    (hown : RootOwnership store [])
    (horder : AllocationOrderInvariant store)
    {loc : Nat} {box : NodeBox} (hget : store.get? loc = some box) :
    0 < incoming store [] loc := by
  have hpos := horder.rc_pos hget
  have hcount := hown.counts hget
  cases box with
  | mk world rc node =>
    cases world with
    | shared =>
      change 0 < rc at hpos
      change rc = incoming store [] loc at hcount
      omega
    | unique =>
      change 0 < rc at hpos
      change rc = 1 ∧ incoming store [] loc = 1 at hcount
      omega

/-- Exact empty-root ownership and allocation order admit no live slot.

Following the mandatory incoming edge moves to a strictly newer live parent.
The measure is the parent's remaining distance to the finite array bound, so
the impossible infinite ascent is rejected directly by Lean's termination
checker. -/
theorem no_live_of_empty_roots {store : Store}
    (hown : RootOwnership store [])
    (horder : AllocationOrderInvariant store)
    {loc : Nat} {box : NodeBox} (hget : store.get? loc = some box) : False := by
  have hincoming := incoming_pos_of_live hown horder hget
  have hedge : loc ∈ edgeLocations store := by
    apply List.count_pos_iff.mp
    simpa [incoming] using hincoming
  obtain ⟨parent, parentBox, hparent, hchild⟩ :=
    parent_of_mem_edgeLocations hedge
  have hlt : loc < parent := horder.child_lt hparent hchild
  exact no_live_of_empty_roots hown horder hparent
termination_by store.nodes.size - loc
decreasing_by
  have hlocBound : loc < store.nodes.size :=
    (Array.getElem?_eq_some_iff.mp (nodes_get?_of_get? hget)).1
  have hparentBound : parent < store.nodes.size :=
    (Array.getElem?_eq_some_iff.mp (nodes_get?_of_get? hparent)).1
  omega

private theorem foldl_live_eq_acc_of_no_some :
    ∀ (slots : List (Option NodeBox)) (acc : Nat),
      (∀ box, some box ∉ slots) →
      slots.foldl
          (fun count slot => if slot.isSome then count + 1 else count)
          acc = acc
  | [], acc, _ => rfl
  | none :: slots, acc, hnone => by
      simp only [List.foldl_cons, Option.isSome_none, Bool.false_eq_true,
        if_false]
      apply foldl_live_eq_acc_of_no_some slots acc
      intro box hbox
      exact hnone box (by simp [hbox])
  | some head :: slots, acc, hnone => by
      exact False.elim (hnone head (by simp))

/-- The finite empty-root reclamation theorem: exact ownership plus the
append-only trace invariant leaves the concrete store with zero live slots.
-/
theorem live_eq_zero_of_empty_roots {store : Store}
    (hown : RootOwnership store [])
    (horder : AllocationOrderInvariant store) :
    store.live = 0 := by
  have hnoSome : ∀ box : NodeBox, some box ∉ store.nodes.toList := by
    intro box hmem
    have harray : some box ∈ store.nodes := by simpa using hmem
    obtain ⟨loc, hloc⟩ := (Array.mem_iff_getElem?).mp harray
    have hget : store.get? loc = some box := by
      rw [Store.get?, hloc]
      rfl
    exact no_live_of_empty_roots hown horder hget
  rw [Store.live, ← Array.foldl_toList]
  exact foldl_live_eq_acc_of_no_some store.nodes.toList 0 hnoSome

/-! ## Primitive preservation

The current lowering is append-only.  The lemmas in this section cover every
store mutation used by its allocation and release paths.  There is
deliberately no preservation theorem for `reuseNodeStore`: overwriting an old
slot with references to newer slots invalidates the concrete location order.
-/

theorem AllocationOrderInvariant.rcTick {store : Store}
    (h : AllocationOrderInvariant store) :
    AllocationOrderInvariant store.rcTick := by
  constructor
  · intro loc box hget
    exact h.rc_pos (by simpa using hget)
  · intro parent box childLoc hget hchild
    exact h.child_lt (by simpa using hget) hchild

/-- Updating only the count of one live slot preserves allocation order when
the replacement count remains positive. -/
theorem AllocationOrderInvariant.setRc {store : Store} {loc : Nat}
    {box : NodeBox} {newRc : Nat}
    (h : AllocationOrderInvariant store)
    (hget : store.get? loc = some box) (hpos : 0 < newRc) :
    AllocationOrderInvariant
      (store.setBox loc { box with rc := newRc }) := by
  constructor
  · intro other otherBox hother
    by_cases heq : loc = other
    · subst other
      have hupdated := get?_setBox_same
        (new := { box with rc := newRc }) hget
      have hboxeq : otherBox = { box with rc := newRc } :=
        Option.some.inj (hother.symm.trans hupdated)
      subst otherBox
      exact hpos
    · exact h.rc_pos
        (get?_of_setBox_other heq hget hother)
  · intro parent parentBox childLoc hparent hchild
    by_cases heq : loc = parent
    · subst parent
      have hupdated := get?_setBox_same
        (new := { box with rc := newRc }) hget
      have hboxeq : parentBox = { box with rc := newRc } :=
        Option.some.inj (hparent.symm.trans hupdated)
      subst parentBox
      exact h.child_lt hget hchild
    · exact h.child_lt
        (get?_of_setBox_other heq hget hparent) hchild

theorem AllocationOrderInvariant.kill {store : Store} {loc : Nat}
    {box : NodeBox} (h : AllocationOrderInvariant store)
    (hget : store.get? loc = some box) :
    AllocationOrderInvariant (store.kill loc) := by
  constructor
  · intro other otherBox hother
    by_cases heq : loc = other
    · subst other
      rw [get?_kill_same hget] at hother
      contradiction
    · exact h.rc_pos (get?_of_kill_other heq hget hother)
  · intro parent parentBox childLoc hparent hchild
    by_cases heq : loc = parent
    · subst parent
      rw [get?_kill_same hget] at hparent
      contradiction
    · exact h.child_lt
        (get?_of_kill_other heq hget hparent) hchild

theorem AllocationOrderInvariant.incRcStore {store : Store} {loc : Nat}
    {box : NodeBox} (h : AllocationOrderInvariant store)
    (hget : store.get? loc = some box) :
    AllocationOrderInvariant (incRcStore store loc box) := by
  rw [Sim.incRcStore]
  exact (h.setRc hget (by omega)).rcTick

theorem AllocationOrderInvariant.decRcStore {store : Store} {loc rc : Nat}
    {world : Ixon.Owned} {node : Node}
    (h : AllocationOrderInvariant store) (hrc : 1 < rc)
    (hget : store.get? loc = some ⟨world, rc, node⟩) :
    AllocationOrderInvariant
      (decRcStore store loc ⟨world, rc, node⟩) := by
  rw [Sim.decRcStore]
  apply h.rcTick.setRc (by simpa using hget)
  change 0 < rc - 1
  omega

/-- Appending a node whose location children are already allocated preserves
the concrete order: every child lies below the old array size, which is
exactly the fresh parent location. -/
theorem AllocationOrderInvariant.allocNodeOfInBounds {store : Store}
    {world : Ixon.Owned} {node : Node}
    (h : AllocationOrderInvariant store)
    (hchildren : ValuesInBounds store (nodeChildren node)) :
    AllocationOrderInvariant (store.allocNode world node).1 := by
  constructor
  · intro loc box hget
    by_cases hnew : loc = store.nodes.size
    · subst loc
      have hfresh := HeapIso.get?_allocNode_new store world node
      have hboxeq : box = ⟨world, 1, node⟩ :=
        Option.some.inj (hget.symm.trans hfresh)
      subst box
      simp
    · exact h.rc_pos (HeapIso.get?_of_allocNode_old hnew hget)
  · intro parent box childLoc hget hchild
    by_cases hnew : parent = store.nodes.size
    · subst parent
      have hfresh := HeapIso.get?_allocNode_new store world node
      have hboxeq : box = ⟨world, 1, node⟩ :=
        Option.some.inj (hget.symm.trans hfresh)
      subst box
      exact hchildren (.loc childLoc) hchild
    · exact h.child_lt
        (HeapIso.get?_of_allocNode_old hnew hget) hchild

/-- Ownership-facing allocation form: liveness is stronger than the allocated
location bound required by `allocNodeOfInBounds`. -/
theorem AllocationOrderInvariant.allocNode {store : Store}
    {world : Ixon.Owned} {node : Node}
    (h : AllocationOrderInvariant store)
    (hchildren : ∀ child ∈ nodeChildren node, LiveRVal store child) :
    AllocationOrderInvariant (store.allocNode world node).1 := by
  apply h.allocNodeOfInBounds
  intro child hchild
  cases child with
  | loc childLoc =>
    obtain ⟨box, hget⟩ := hchildren (.loc childLoc) hchild
    exact RVal.inBounds_of_get? hget
  | lit literal => trivial
  | erased => trivial

private def SharedDropOrderAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (store' : Store),
    AllocationOrderInvariant store →
    dropVal ctx fuel store value = .ok store' →
    AllocationOrderInvariant store') ∧
  (∀ (store : Store) (values : List RVal) (store' : Store),
    AllocationOrderInvariant store →
    dropMany ctx fuel store values = .ok store' →
    AllocationOrderInvariant store')

/-- Successful shared deep release preserves positivity and allocation order,
including every recursive final-owner child release. -/
private theorem sharedDropOrderAt (ctx : Ctx) :
    ∀ fuel, SharedDropOrderAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value store' horder heval
      rw [dropVal.eq_def] at heval
      simp at heval
    · intro store values store' horder heval
      rw [dropMany.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value store' horder heval
      cases value with
      | lit literal =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | erased =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | loc loc =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at heval
            | shared =>
              dsimp only at heval
              by_cases hrc : rc = 1
              · subst rc
                have hbeq : ((1 : Nat) == 1) = true := by decide
                rw [hbeq] at heval
                have htickGet :
                    store.rcTick.get? loc = some ⟨.shared, 1, node⟩ := by
                  simpa using hget
                have hprefix := horder.rcTick.kill htickGet
                cases node with
                | ctorN cid fields =>
                  exact ihMany _ fields.toList store' hprefix heval
                | papN fn arity args =>
                  exact ihMany _ args.toList store' hprefix heval
              · have hbeq : (rc == 1) = false := by simp [hrc]
                rw [hbeq] at heval
                have hpos : 0 < rc := horder.rc_pos hget
                have hmany : 1 < rc := by omega
                injection heval with hstore
                subst store'
                exact horder.decRcStore hmany hget
    · intro store values store' horder heval
      cases values with
      | nil =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | cons value values =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact ihMany middle values store'
            (ihVal store value middle horder hfirst) heval

theorem AllocationOrderInvariant.dropVal {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {value : RVal}
    (h : AllocationOrderInvariant store)
    (heval : dropVal ctx fuel store value = .ok store') :
    AllocationOrderInvariant store' :=
  (sharedDropOrderAt ctx fuel).1 store value store' h heval

theorem AllocationOrderInvariant.dropMany {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {values : List RVal}
    (h : AllocationOrderInvariant store)
    (heval : dropMany ctx fuel store values = .ok store') :
    AllocationOrderInvariant store' :=
  (sharedDropOrderAt ctx fuel).2 store values store' h heval

private def UniqueDropOrderAt (ctx : Ctx) (fuel : Nat) : Prop :=
  (∀ (store : Store) (value : RVal) (store' : Store),
    AllocationOrderInvariant store →
    dropUVal ctx fuel store value = .ok store' →
    AllocationOrderInvariant store') ∧
  (∀ (store : Store) (values : List RVal) (store' : Store),
    AllocationOrderInvariant store →
    dropManyU ctx fuel store values = .ok store' →
    AllocationOrderInvariant store')

/-- Successful unique deep release only kills slots, so it preserves the
append order through its complete recursive constructor traversal. -/
private theorem uniqueDropOrderAt (ctx : Ctx) :
    ∀ fuel, UniqueDropOrderAt ctx fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro store value store' horder heval
      rw [dropUVal.eq_def] at heval
      simp at heval
    · intro store values store' horder heval
      rw [dropManyU.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany⟩ := ih
    refine ⟨?_, ?_⟩
    · intro store value store' horder heval
      cases value with
      | lit literal =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | erased =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | loc loc =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? loc with
        | none =>
          rw [hget] at heval
          simp at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at heval
            | unique =>
              cases node with
              | ctorN cid fields =>
                exact ihMany _ fields.toList store'
                  (horder.kill hget) heval
              | papN fn arity args => simp at heval
    · intro store values store' horder heval
      cases values with
      | nil =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        exact horder
      | cons value values =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropUVal ctx fuel store value with
        | error err =>
          rw [hfirst, bindErr] at heval
          simp at heval
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact ihMany middle values store'
            (ihVal store value middle horder hfirst) heval

theorem AllocationOrderInvariant.dropUVal {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {value : RVal}
    (h : AllocationOrderInvariant store)
    (heval : dropUVal ctx fuel store value = .ok store') :
    AllocationOrderInvariant store' :=
  (uniqueDropOrderAt ctx fuel).1 store value store' h heval

theorem AllocationOrderInvariant.dropManyU {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {values : List RVal}
    (h : AllocationOrderInvariant store)
    (heval : dropManyU ctx fuel store values = .ok store') :
    AllocationOrderInvariant store' :=
  (uniqueDropOrderAt ctx fuel).2 store values store' h heval

/-- Retaining any sequence of shared values changes only positive reference
counts and therefore preserves the trace invariant. -/
theorem AllocationOrderInvariant.dupVals {store store' : Store}
    {values : List RVal} (h : AllocationOrderInvariant store)
    (heval : dupVals store values = .ok store') :
    AllocationOrderInvariant store' := by
  induction values generalizing store with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    exact h
  | cons head tail ih =>
    cases head with
    | lit literal =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih h heval
    | erased =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih h heval
    | loc loc =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      cases hget : store.get? loc with
      | none => simp [hget, bindErr] at heval
      | some box =>
        cases box with
        | mk world rc node =>
          cases world with
          | unique => simp [hget, bindErr] at heval
          | shared =>
            simp only [hget] at heval
            exact ih (h.incRcStore hget) heval

private structure OrderResult (before after : Store) (value : RVal) : Prop where
  order : AllocationOrderInvariant after
  valueInBounds : ValueInBounds after value
  papsUnder : PAPsUnder before → PAPsUnder after

private def OrderAt (fuel : Nat) : Prop :=
  (∀ ctx cur store env code store' value,
    AllocationOrderInvariant store → ValuesInBounds store env →
    store'.reuses = store.reuses →
    runCode ctx fuel cur store env code = .ok (store', value) →
    OrderResult store store' value) ∧
  (∀ ctx cur store env op store' value,
    AllocationOrderInvariant store → ValuesInBounds store env →
    store'.reuses = store.reuses →
    runOp ctx fuel cur store env op = .ok (store', value) →
    OrderResult store store' value) ∧
  (∀ ctx address args store store' value,
    AllocationOrderInvariant store → ValuesInBounds store args →
    store'.reuses = store.reuses →
    invoke ctx fuel address args store = .ok (store', value) →
    OrderResult store store' value) ∧
  (∀ ctx store function args store' value,
    AllocationOrderInvariant store → ValueInBounds store function →
    ValuesInBounds store args → store'.reuses = store.reuses →
    applyGo ctx fuel store function args = .ok (store', value) →
    OrderResult store store' value)

/-- A successful trace whose endpoint reuse count is unchanged preserves the
append allocation order.  The proof also establishes that its result cannot
name a future slot.  `StoreFootprint` forces the same reuse equality at every
intermediate call, so even dynamically unreachable `reuse` instructions are
harmless and an executed one is contradictory. -/
private theorem orderAt : ∀ fuel, OrderAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value horder henv hreuses heval
      rw [runCode.eq_def] at heval
      simp at heval
    · intro ctx cur store env op store' value horder henv hreuses heval
      rw [runOp.eq_def] at heval
      simp at heval
    · intro ctx address args store store' value horder hargs hreuses heval
      rw [invoke.eq_def] at heval
      simp at heval
    · intro ctx store function args store' value horder hfunction hargs
        hreuses heval
      rw [applyGo.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value horder henv hreuses heval
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact ⟨horder, resolveAtom_inBounds henv hresolve, id⟩
      | letOp op rest =>
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hop : runOp ctx fuel cur store env op with
        | error err => rw [hop, bindErr] at heval; contradiction
        | ok opOut =>
          rcases opOut with ⟨middle, opValue⟩
          rw [hop, bindOk] at heval
          have hopFoot := runOp_footprint hop
          have hrestFoot := runCode_footprint heval
          have hopReusesLe : store.reuses ≤ middle.reuses := by
            simpa using hopFoot.reuses
          have hrestReusesLe : middle.reuses ≤ store'.reuses := by
            simpa using hrestFoot.reuses
          have hopReuses : middle.reuses = store.reuses := by omega
          have hrestReuses : store'.reuses = middle.reuses := by omega
          obtain ⟨hmiddleOrder, hopBound, hopPaps⟩ :=
            ihOp _ _ _ _ _ _ _ horder henv hopReuses hop
          have henvMiddle : ValuesInBounds middle env :=
            henv.mono hopFoot.nodes_size
          have tail := ihCode _ _ _ _ _ _ _ hmiddleOrder
            (henvMiddle.cons hopBound) hrestReuses heval
          exact ⟨tail.order, tail.valueInBounds,
            fun hpaps => tail.papsUnder (hopPaps hpaps)⟩
      | case scrut peelNat alts =>
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hscrut : resolveAtom env scrut with
        | error err => rw [hscrut, bindErr] at heval; contradiction
        | ok scrutValue =>
          rw [hscrut, bindOk] at heval
          cases scrutValue with
          | loc loc =>
            dsimp only at heval
            cases hbox : store.get? loc with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => simp at heval
                | ctorN cid fields =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == cid.cidx) with
                  | none => simp [halt] at heval
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at heval
                        have hfields := horder.childrenInBounds hbox
                        exact ihCode _ _ _ _ _ _ _ horder
                          (hfields.foldlPrepend henv) hreuses heval
                      · simp [halt, hsize] at heval
          | lit literal =>
            cases literal with
            | str string => simp at heval
            | nat n =>
              cases hpeel : peelNat with
              | false => simp [hpeel] at heval
              | true =>
                cases n with
                | zero =>
                  cases halt : alts.find? (fun alt => alt.cidx == 0) with
                  | none => simp [hpeel, halt] at heval
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at heval
                        exact ihCode _ _ _ _ _ _ _ horder henv hreuses heval
                      | succ fieldCount => simp [hpeel, halt] at heval
                | succ n =>
                  cases halt : alts.find? (fun alt => alt.cidx == 1) with
                  | none => simp [hpeel, halt] at heval
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero => simp [hpeel, halt] at heval
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at heval
                          exact ihCode _ _ _ _ _ _ _ horder
                            (henv.cons (by trivial)) hreuses heval
                        | succ fieldCount => simp [hpeel, halt] at heval
          | erased => simp at heval
    · intro ctx cur store env op store' value horder henv hreuses heval
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact ⟨horder, resolveAtom_inBounds henv hresolve, id⟩
      | alloc world cid atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtoms env atoms with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok values =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          have hvalues := resolveAtoms_inBounds henv hresolve
          refine ⟨?_, ?_, ?_⟩
          · apply horder.allocNodeOfInBounds
            simpa [nodeChildren] using hvalues
          · simp [ValueInBounds, Store.allocNode]
          · intro hpaps
            exact hpaps.allocCtor world cid values.toArray
      | reuse target cid atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases htarget : resolveAtom env target with
          | error err => rw [htarget, bindErr] at heval; contradiction
          | ok targetValue =>
            rw [htarget, bindOk] at heval
            cases targetValue with
            | lit literal => simp at heval
            | erased => simp at heval
            | loc loc =>
              cases hbox : store.get? loc with
              | none => simp [hbox] at heval
              | some box =>
                simp only [hbox] at heval
                cases box with
                | mk world rc node =>
                  cases world with
                  | shared => simp at heval
                  | unique =>
                    have hpair := Except.ok.inj heval
                    cases hpair
                    simp [Store.setBox] at hreuses
      | free target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | shared => simp at heval
                | unique =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  exact ⟨horder.kill hbox, by trivial,
                    fun hpaps => hpaps.kill hbox⟩
      | dup target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | unique => simp at heval
                | shared =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  refine ⟨horder.incRcStore hbox,
                    (RVal.inBounds_of_get? hbox).mono
                      (footprint_incRcStore hbox).nodes_size, ?_⟩
                  intro hpaps
                  simpa [Sim.incRcStore] using hpaps.incRcStore hbox
      | drop target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | loc loc =>
            dsimp only at heval
            cases hdrop : dropVal ctx fuel store (.loc loc) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact ⟨horder.dropVal hdrop, by trivial,
                fun hpaps => hpaps.dropVal hdrop⟩
      | dropU target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact ⟨horder, by trivial, id⟩
          | loc loc =>
            dsimp only at heval
            cases hdrop : dropUVal ctx fuel store (.loc loc) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact ⟨horder.dropUVal hdrop, by trivial,
                fun hpaps => hpaps.dropUVal hdrop⟩
      | fetch target field =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc loc =>
            cases hbox : store.get? loc with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => simp at heval
                | ctorN cid fields =>
                  cases hfield : fields[field]? with
                  | none => simp [hfield] at heval
                  | some result =>
                    simp only [hfield] at heval
                    have hpair := Except.ok.inj heval
                    have hstoreEq : store = store' :=
                      congrArg Prod.fst hpair
                    have hvalueEq : result = value :=
                      congrArg Prod.snd hpair
                    subst store'
                    subst value
                    have hmember : result ∈ fields.toList := by
                      simpa using
                        (Array.mem_iff_getElem?).2 ⟨field, hfield⟩
                    exact ⟨horder,
                      horder.childrenInBounds hbox result
                        (by simpa [nodeChildren] using hmember), id⟩
      | call address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtoms env atoms with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok values =>
          rw [hresolve, bindOk] at heval
          exact ihInvoke _ _ _ _ _ _ horder
            (resolveAtoms_inBounds henv hresolve) hreuses heval
      | callSelf atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtoms env atoms with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok values =>
          rw [hresolve, bindOk] at heval
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hcode : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err => rw [hcode, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hcode, bindOk] at heval
              obtain ⟨hresult, _⟩ := checkResultWorld_ok heval
              cases hresult
              exact ihCode _ _ _ _ _ _ _ horder
                (resolveAtoms_inBounds henv hresolve).reverse
                hreuses hcode
          · simp [harity] at heval
      | papp address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtoms env atoms with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok values =>
          rw [hresolve, bindOk] at heval
          cases hdecl : ctx.decls address with
          | none => simp [hdecl] at heval
          | some decl =>
            simp only [hdecl] at heval
            by_cases hlen : values.length < declArity decl
            · simp only [hlen, if_true] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              have hvalues := resolveAtoms_inBounds henv hresolve
              refine ⟨?_, ?_, ?_⟩
              · apply horder.allocNodeOfInBounds
                simpa [nodeChildren] using hvalues
              · simp [ValueInBounds, Store.allocNode]
              · intro hpaps
                exact hpaps.allocPap .shared address (declArity decl)
                  values.toArray (by simpa using hlen)
            · simp [hlen] at heval
      | apply function atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hfunction : resolveAtom env function with
        | error err => rw [hfunction, bindErr] at heval; contradiction
        | ok functionValue =>
          rw [hfunction, bindOk] at heval
          cases hresolve : resolveAtoms env atoms with
          | error err => rw [hresolve, bindErr] at heval; contradiction
          | ok values =>
            rw [hresolve, bindOk] at heval
            exact ihApply _ _ _ _ _ _ horder
              (resolveAtom_inBounds henv hfunction)
              (resolveAtoms_inBounds henv hresolve) hreuses heval
      | extern address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtoms env atoms with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok values =>
          rw [hresolve, bindOk] at heval
          cases hcall : callScalarOracle ctx address values with
          | error err => rw [hcall, bindErr] at heval; contradiction
          | ok result =>
            rw [hcall, bindOk] at heval
            have hpair := Except.ok.inj heval
            have hstoreEq : store = store' :=
              congrArg Prod.fst hpair
            have hvalueEq : result = value :=
              congrArg Prod.snd hpair
            subst store'
            subst value
            have hscalar := (callScalarOracle_ok hcall).2
            refine ⟨horder, ?_, id⟩
            cases result <;> simp_all [RVal.isScalar, ValueInBounds]
    · intro ctx address args store store' value horder hargs hreuses heval
      rw [invoke.eq_def] at heval
      dsimp only at heval
      cases hdecl : ctx.decls address with
      | none => simp [hdecl] at heval
      | some decl =>
        simp only [hdecl] at heval
        cases decl with
        | extern arity =>
          cases harity : args.length != arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hcall : callScalarOracle ctx address args with
            | error err => simp [hcall] at heval
            | ok result =>
              simp only [hcall] at heval
              have hpair := Except.ok.inj heval
              have hstoreEq : store = store' :=
                congrArg Prod.fst hpair
              have hvalueEq : result = value :=
                congrArg Prod.snd hpair
              subst store'
              subst value
              have hscalar := (callScalarOracle_ok hcall).2
              refine ⟨horder, ?_, id⟩
              cases result <;> simp_all [RVal.isScalar, ValueInBounds]
          · simp [harity] at heval
        | fn d =>
          cases harity : args.length != d.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hcode : runCode ctx fuel d store args.reverse d.body with
            | error err => rw [hcode, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hcode, bindOk] at heval
              obtain ⟨hresult, _⟩ := checkResultWorld_ok heval
              cases hresult
              exact ihCode _ _ _ _ _ _ _ horder hargs.reverse
                hreuses hcode
          · simp [harity] at heval
    · intro ctx store function args store' value horder hfunction hargs
        hreuses heval
      rw [applyGo.eq_def] at heval
      dsimp only at heval
      cases function with
      | lit literal => simp at heval
      | erased =>
        dsimp only at heval
        cases hdrop : dropMany ctx fuel store args with
        | error err => rw [hdrop, bindErr] at heval; contradiction
        | ok dropped =>
          rw [hdrop, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact ⟨horder.dropMany hdrop, by trivial,
            fun hpaps => hpaps.dropMany hdrop⟩
      | loc loc =>
        dsimp only at heval
        cases hbox : store.get? loc with
        | none => simp [hbox] at heval
        | some box =>
          simp only [hbox] at heval
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields =>
              dsimp only at heval
              simp at heval
            | papN address arity captured =>
              dsimp only at heval
              cases hdup : dupVals store captured.toList with
              | error err => rw [hdup, bindErr] at heval; contradiction
              | ok duplicated =>
                rw [hdup, bindOk] at heval
                cases hdrop : dropVal ctx fuel duplicated (.loc loc) with
                | error err => rw [hdrop, bindErr] at heval; contradiction
                | ok ready =>
                  rw [hdrop, bindOk] at heval
                  have hdupFoot := dupVals_footprint hdup
                  have hdropFoot := (footprintAt fuel).2.2.2.2.1
                    ctx duplicated (.loc loc) ready hdrop
                  have hprefix := hdupFoot.trans hdropFoot
                  have hreadyOrder := (horder.dupVals hdup).dropVal hdrop
                  have hcaptured := horder.childrenInBounds hbox
                  have htotal :
                      ValuesInBounds ready (captured.toList ++ args) :=
                    (hcaptured.append hargs).mono hprefix.nodes_size
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder] at heval
                    have hpair := Except.ok.inj heval
                    cases hpair
                    refine ⟨?_, ?_, ?_⟩
                    · apply hreadyOrder.allocNodeOfInBounds
                      simpa [nodeChildren] using htotal
                    · simp [ValueInBounds, Store.allocNode]
                    · intro hpaps
                      exact ((hpaps.dupVals hdup).dropVal hdrop).allocPap
                        .shared address arity
                        (captured.toList ++ args).toArray
                        (by simpa using hunder)
                  · simp only [hunder] at heval
                    cases hexact :
                        (captured.toList ++ args).length == arity
                    · simp only [hexact, Bool.false_eq_true, if_false]
                        at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at heval
                            contradiction
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at heval
                            have hinvokeFoot := invoke_footprint hinvoke
                            have happlyFoot := applyGo_footprint heval
                            have hprefixReuseLe :
                                store.reuses ≤ ready.reuses :=
                              hprefix.reuses
                            have hinvokeReuseLe :
                                ready.reuses ≤ calledStore.reuses := by
                              simpa using hinvokeFoot.reuses
                            have happlyReuseLe :
                                calledStore.reuses ≤ store'.reuses := by
                              simpa using happlyFoot.reuses
                            have hreadyReuse :
                                ready.reuses = store.reuses := by
                              omega
                            have hcalledReuse :
                                calledStore.reuses = ready.reuses := by omega
                            have hfinalReuse :
                                store'.reuses = calledStore.reuses := by omega
                            obtain ⟨hcalledOrder, hcalledValue,
                              hcalledPaps⟩ :=
                              ihInvoke _ _ _ _ _ _ hreadyOrder
                                (htotal.take arity) hcalledReuse hinvoke
                            have hrestBounds : ValuesInBounds calledStore
                                ((captured.toList ++ args).drop arity) :=
                              (htotal.drop arity).mono hinvokeFoot.nodes_size
                            have tail := ihApply _ _ _ _ _ _ hcalledOrder
                              hcalledValue hrestBounds hfinalReuse heval
                            exact ⟨tail.order, tail.valueInBounds,
                              fun hpaps => tail.papsUnder (hcalledPaps
                                ((hpaps.dupVals hdup).dropVal hdrop))⟩
                    · simp only [hexact, if_true] at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          have hinvokeFoot := invoke_footprint heval
                          have hprefixReuseLe :
                              store.reuses ≤ ready.reuses :=
                            hprefix.reuses
                          have hinvokeReuseLe :
                              ready.reuses ≤ store'.reuses := by
                            simpa using hinvokeFoot.reuses
                          have hreadyReuse : ready.reuses = store.reuses := by
                            omega
                          have hfinalReuse :
                              store'.reuses = ready.reuses := by
                            omega
                          have called := ihInvoke _ _ _ _ _ _ hreadyOrder
                            htotal hfinalReuse heval
                          exact ⟨called.order, called.valueInBounds,
                            fun hpaps => called.papsUnder
                              ((hpaps.dupVals hdup).dropVal hdrop)⟩

theorem runCode_order_of_reuses_eq {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {code : Code} {value : RVal}
    (horder : AllocationOrderInvariant store)
    (henv : ValuesInBounds store env)
    (hreuses : store'.reuses = store.reuses)
    (heval : runCode ctx fuel cur store env code = .ok (store', value)) :
    AllocationOrderInvariant store' ∧ ValueInBounds store' value := by
  have result := (orderAt fuel).1 ctx cur store env code store' value
    horder henv hreuses heval
  exact ⟨result.order, result.valueInBounds⟩

/-- The same dynamic no-reuse premise preserves strict PAP shape. -/
theorem runCode_papsUnder_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal} {code : Code}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (henv : ValuesInBounds store env) (hpaps : PAPsUnder store)
    (hreuses : store'.reuses = store.reuses)
    (heval : runCode ctx fuel cur store env code = .ok (store', value)) :
    PAPsUnder store' :=
  ((orderAt fuel).1 ctx cur store env code store' value
    horder henv hreuses heval).papsUnder hpaps

/-- The operation-level projection of `runCode_order_of_reuses_eq`.  This is
the compositional boundary used by local operation contracts: once a
primitive proves that it did not execute `reuse`, the shared evaluator
induction supplies allocation order and result boundedness. -/
theorem runOp_order_of_reuses_eq {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {op : Op} {value : RVal}
    (horder : AllocationOrderInvariant store)
    (henv : ValuesInBounds store env)
    (hreuses : store'.reuses = store.reuses)
    (heval : runOp ctx fuel cur store env op = .ok (store', value)) :
    AllocationOrderInvariant store' ∧ ValueInBounds store' value := by
  have result := (orderAt fuel).2.1 ctx cur store env op store' value
    horder henv hreuses heval
  exact ⟨result.order, result.valueInBounds⟩

theorem runOp_papsUnder_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {cur : FnDef} {store store' : Store} {env : List RVal} {op : Op}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (henv : ValuesInBounds store env) (hpaps : PAPsUnder store)
    (hreuses : store'.reuses = store.reuses)
    (heval : runOp ctx fuel cur store env op = .ok (store', value)) :
    PAPsUnder store' :=
  ((orderAt fuel).2.1 ctx cur store env op store' value
    horder henv hreuses heval).papsUnder hpaps

/-- Declared-call projection of the allocation-order induction.  Exposing
this alongside the code and operation forms lets run-indexed cost contracts
sequence a dynamically selected callee without rebuilding the evaluator
induction. -/
theorem invoke_order_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {address : Ixon.Address} {args : List RVal} {store store' : Store}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (hargs : ValuesInBounds store args)
    (hreuses : store'.reuses = store.reuses)
    (heval : invoke ctx fuel address args store = .ok (store', value)) :
    AllocationOrderInvariant store' ∧ ValueInBounds store' value := by
  have result := (orderAt fuel).2.2.1 ctx address args store store' value
    horder hargs hreuses heval
  exact ⟨result.order, result.valueInBounds⟩

theorem invoke_papsUnder_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {address : Ixon.Address} {args : List RVal} {store store' : Store}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (hargs : ValuesInBounds store args) (hpaps : PAPsUnder store)
    (hreuses : store'.reuses = store.reuses)
    (heval : invoke ctx fuel address args store = .ok (store', value)) :
    PAPsUnder store' :=
  ((orderAt fuel).2.2.1 ctx address args store store' value
    horder hargs hreuses heval).papsUnder hpaps

/-- Higher-order-application projection of the allocation-order induction. -/
theorem applyGo_order_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {function : RVal} {args : List RVal}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (hfunction : ValueInBounds store function)
    (hargs : ValuesInBounds store args)
    (hreuses : store'.reuses = store.reuses)
    (heval : applyGo ctx fuel store function args = .ok (store', value)) :
    AllocationOrderInvariant store' ∧ ValueInBounds store' value := by
  have result := (orderAt fuel).2.2.2 ctx store function args store' value
    horder hfunction hargs hreuses heval
  exact ⟨result.order, result.valueInBounds⟩

theorem applyGo_papsUnder_of_reuses_eq {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {function : RVal} {args : List RVal}
    {value : RVal} (horder : AllocationOrderInvariant store)
    (hfunction : ValueInBounds store function)
    (hargs : ValuesInBounds store args) (hpaps : PAPsUnder store)
    (hreuses : store'.reuses = store.reuses)
    (heval : applyGo ctx fuel store function args = .ok (store', value)) :
    PAPsUnder store' :=
  ((orderAt fuel).2.2.2 ctx store function args store' value
    horder hfunction hargs hreuses heval).papsUnder hpaps

/-- A fresh successful evaluator run with zero executed reuses is
allocation-ordered.  No syntactic no-reuse scan is required: monotonicity of
the counter proves that every dynamically reached operation was append-only.
-/
theorem runMain_order_of_reuses_eq_zero {ctx : Ctx} {fuel : Nat}
    {code : Code} {store : Store} {value : RVal}
    (heval : runMain ctx code fuel = .ok (store, value))
    (hreuses : store.reuses = 0) :
    AllocationOrderInvariant store ∧ ValueInBounds store value := by
  have result := (orderAt fuel).1 ctx ⟨0, .shared, false, code⟩
    ({} : Store) [] code
    store value AllocationOrderInvariant.empty
    (ValuesInBounds.nil ({} : Store)) hreuses heval
  exact ⟨result.order, result.valueInBounds⟩

/-! ## Final-root release

These are the reusable bridge from the existing exact-ownership simulation
to concrete leak freedom.  The ownership proof consumes the sole root; the
parallel trace proof preserves allocation order; the empty-root theorem then
rules out every remaining slot.
-/

theorem shared_release_live_eq_zero {ctx : Ctx} {fuel : Nat}
    {store released : Store} {value : RVal}
    (hown : RootOwnership store [⟨.shared, value⟩])
    (horder : AllocationOrderInvariant store)
    (heval : dropVal ctx fuel store value = .ok released) :
    released.live = 0 := by
  apply live_eq_zero_of_empty_roots
  · exact Sim.dropVal_preserves hown heval
  · exact horder.dropVal heval

theorem unique_release_live_eq_zero {ctx : Ctx} {fuel : Nat}
    {store released : Store} {value : RVal}
    (hown : RootOwnership store [⟨.unique, value⟩])
    (horder : AllocationOrderInvariant store)
    (heval : dropUVal ctx fuel store value = .ok released) :
    released.live = 0 := by
  apply live_eq_zero_of_empty_roots
  · exact Sim.dropUVal_preserves hown heval
  · exact horder.dropUVal heval

/-- A well-owned, allocation-ordered shared result always has enough release
fuel, and that release empties the concrete heap. -/
theorem shared_reclamation {ctx : Ctx} {store : Store} {value : RVal}
    (hown : RootOwnership store [⟨.shared, value⟩])
    (horder : AllocationOrderInvariant store) :
    ∃ fuel released,
      dropVal ctx fuel store value = .ok released ∧ released.live = 0 := by
  obtain ⟨fuel, released, heval, _⟩ :=
    dropVal_progress (ctx := ctx) hown
  exact ⟨fuel, released, heval,
    shared_release_live_eq_zero hown horder heval⟩

/-- The corresponding theorem for a unique final result. -/
theorem unique_reclamation {ctx : Ctx} {store : Store} {value : RVal}
    (hown : RootOwnership store [⟨.unique, value⟩])
    (horder : AllocationOrderInvariant store) :
    ∃ fuel released,
      dropUVal ctx fuel store value = .ok released ∧ released.live = 0 := by
  obtain ⟨fuel, released, heval, _⟩ :=
    dropUVal_progress (ctx := ctx) hown
  exact ⟨fuel, released, heval,
    unique_release_live_eq_zero hown horder heval⟩

end Ix.Compiler.IxIR1.Reclamation
