import Ix.Compiler.Borrow.RuntimeSim

/-! Caller-side input construction, separate from the compiler and selector.
The construction proof covers every finite constructor chain and scalar
payload, not only the regression matrix. -/

namespace Ix.Compiler.Borrow.Runtime

open Ix.Compiler.Ixon (Address)
open IxIR2.Eval
open IxIR2.Borrow.Open (Schema Major Input)
open Ix.Compiler.IxIR1.Sim (RootOwnership rootsFor nodeChildren)
open Ix.Compiler.IxIR1.Reclamation (AllocationOrderInvariant)

inductive Tree where
  | scalar (value : Nat)
  | zero
  | succ (tail : Tree)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Tree.nodes : Tree → Nat
  | .scalar _ => 0
  | .zero => 1
  | .succ tail => tail.nodes + 1

def Tree.nested : Nat → Tree → Tree
  | 0, tail => tail
  | count + 1, tail => .succ (nested count tail)

def Tree.make (schema : Schema) : Tree → Store × RVal
  | .scalar value => ({}, .lit (.nat value))
  | .zero =>
      let allocated := ({} : Store).allocNode .shared (.ctorN schema.zero #[])
      (allocated.1, .loc allocated.2)
  | .succ tail =>
      let input := tail.make schema
      let allocated := input.1.allocNode .shared (.ctorN schema.succ #[input.2])
      (allocated.1, .loc allocated.2)

def Tree.sourceValue (block : Address) : Tree → Ixon.Eval.Value
  | .scalar value => .litV (.natL value)
  | .zero => .ctorV block 0 0 []
  | .succ tail => .ctorV block 0 1 [tail.sourceValue block]

def Tree.rawValue (schema : Schema) : Tree → IxIR0.Value
  | .scalar value => .lit (.nat value)
  | .zero => .ctor schema.zero.block 0 []
  | .succ tail => .ctor schema.succ.block 1 [tail.rawValue schema]

structure Ready (store : Store) (value : RVal) : Prop where
  owned : RootOwnership store.heap [⟨.shared, value⟩]
  ordered : AllocationOrderInvariant store.heap
  accounted : store.heap.allocs = store.live + store.heap.frees
  peak : store.live ≤ store.peakLiveNodes

private theorem allocatedReady (store : Store) (cid : IxIR2.CtorId) (values : Array RVal)
    (owned : RootOwnership store.heap (rootsFor .shared values.toList))
    (ordered : AllocationOrderInvariant store.heap)
    (accounted : store.heap.allocs = store.live + store.heap.frees) :
    Ready (store.allocNode .shared (.ctorN cid values)).1 (.loc (store.allocNode .shared (.ctorN cid values)).2) := by
  have children : ∀ child ∈ nodeChildren (.ctorN cid values), IxIR1.Sim.LiveRVal store.heap child := by
    intro child member
    exact IxIR2.CreditRefinement.live_of_world
      (owned.roots_world ⟨.shared, child⟩ (by simpa [rootsFor, nodeChildren] using member))
  refine ⟨?_, ordered.allocNode children, ?_, ?_⟩
  · exact RootOwnership.allocNode (rest := []) (by simpa [nodeChildren] using owned) trivial
  · rw [Store.live_allocNode]
    simp only [Store.allocNode_heap, IxIR1.Store.allocNode]
    omega
  · rw [Store.peakLive_allocNode]
    exact Nat.le_max_right _ _

theorem Tree.ready (schema : Schema) (tree : Tree) : Ready (tree.make schema).1 (tree.make schema).2 := by
  induction tree with
  | scalar value =>
      exact ⟨RootOwnership.addNoLocation rfl RootOwnership.empty, .empty, rfl, Nat.le_refl _⟩
  | zero =>
      exact allocatedReady {} schema.zero #[] RootOwnership.empty .empty rfl
  | succ tail ih =>
      exact allocatedReady (tail.make schema).1 schema.succ #[(tail.make schema).2]
        (by simpa [rootsFor] using ih.owned) ih.ordered ih.accounted

theorem Tree.counts (schema : Schema) (tree : Tree) :
    (tree.make schema).1.heap.allocs = tree.nodes ∧
    (tree.make schema).1.heap.frees = 0 ∧
    (tree.make schema).1.heap.rcops = 0 ∧
    (tree.make schema).1.live = tree.nodes ∧
    (tree.make schema).1.peakLiveNodes = tree.nodes := by
  induction tree with
  | scalar => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ tail ih =>
      rcases ih with ⟨allocs, frees, rcops, live, peak⟩
      refine ⟨?_, frees, rcops, ?_, ?_⟩
      · simp [Tree.make, Tree.nodes, IxIR1.Store.allocNode, allocs]
      · simpa [Tree.make, Tree.nodes, Store.live_allocNode] using live
      · simp only [Tree.make, Store.peakLive_allocNode, Store.live_allocNode, peak, live, Tree.nodes]
        omega

inductive Argument where
  | zero
  | succ (payload : Tree)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def Argument.tree : Argument → Tree
  | .zero => .zero
  | .succ payload => .succ payload

def Argument.make (schema : Schema) : Argument → Store × Nat
  | .zero => ({} : Store).allocNode .shared (.ctorN schema.zero #[])
  | .succ payload =>
      let input := payload.make schema
      input.1.allocNode .shared (.ctorN schema.succ #[input.2])

def Argument.major (schema : Schema) : Argument → Major
  | .zero => .zero
  | .succ payload => .succ (payload.make schema).2

def Argument.source (schema : Schema) : Argument → Source.Argument
  | .zero => .zero schema.zero.block
  | .succ payload => .succ schema.succ.block (payload.rawValue schema)

theorem Argument.input (schema : Schema) (argument : Argument) :
    Input schema (argument.major schema) (argument.make schema).1 (argument.make schema).2 1 := by
  have ready := argument.tree.ready schema
  cases argument with
  | zero =>
      exact ⟨IxIR1.Sim.HeapIso.get?_allocNode_new .., ready.owned, ready.ordered, ready.accounted, ready.peak⟩
  | succ payload =>
      exact ⟨IxIR1.Sim.HeapIso.get?_allocNode_new .., ready.owned, ready.ordered, ready.accounted, ready.peak⟩

end Ix.Compiler.Borrow.Runtime
