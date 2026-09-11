import Ix.Compiler.UniqueReuse.Lower
import Ix.Compiler.IxIR0.UniqueReverseSim
import Ix.Compiler.IxIR1.Reclamation

/-! Exact unique-list heap views and the existing root/edge ownership
algebra. The views record full constructor identities, unit reference counts,
and finite list contents. Shallow destruction transports surviving views via
the post-state ownership invariant. -/

namespace Ix.Compiler.UniqueReuse

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema)

inductive ListAt (schema : Schema) (store : Store) : List Nat → RVal → Prop where
  | nil {location : Nat}
      (found : store.get? location = some ⟨.unique, 1, .ctorN (nilId schema) #[]⟩) :
      ListAt schema store [] (.loc location)
  | cons {head : Nat} {tail : List Nat} {location : Nat} {rest : RVal}
      (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), rest]⟩)
      (next : ListAt schema store tail rest) : ListAt schema store (head :: tail) (.loc location)

theorem ListAt.hasWorld {schema : Schema} {store : Store} {values : List Nat} {value : RVal}
    (list : ListAt schema store values value) : HasWorld store .unique value := by
  cases list with
  | nil found => exact ⟨_, found, rfl⟩
  | cons found _ => exact ⟨_, found, rfl⟩

theorem ListAt.graph {schema : Schema} {store : Store} {values : List Nat} {value : RVal}
    (list : ListAt schema store values value) (functions : FunctionRel) :
    ValueGraph functions store (IxIR0.UniqueReverse.listValue schema values) value := by
  induction list with
  | nil found => exact .ctor found rfl rfl .nil
  | cons found _ ih => exact .ctor found rfl rfl (.cons .lit (.cons ih .nil))

theorem ListAt.mono {schema : Schema} {before after : Store} {values : List Nat} {value : RVal}
    (preserved : ∀ {location box}, before.get? location = some box → after.get? location = some box)
    (list : ListAt schema before values value) : ListAt schema after values value := by
  induction list with
  | nil found => exact .nil (preserved found)
  | cons found _ ih => exact .cons (preserved found) ih

theorem ListAt.allocNode {schema : Schema} {store : Store} {values : List Nat} {value : RVal}
    (list : ListAt schema store values value) (world : Owned) (node : Node) :
    ListAt schema (store.allocNode world node).1 values value :=
  list.mono (fun found => HeapIso.get?_allocNode_old found)

private theorem unique_shape_after_restriction {before after : Store} {roots : List Root}
    {location : Nat} {node : Node} (restricted : StoreGraphRestricts before after)
    (owned : RootOwnership after roots) (world : HasWorld after .unique (.loc location))
    (found : before.get? location = some ⟨.unique, 1, node⟩) :
    after.get? location = some ⟨.unique, 1, node⟩ := by
  obtain ⟨⟨actualWorld, rc, actualNode⟩, afterGet, worldEq⟩ := world
  dsimp at worldEq
  subst actualWorld
  obtain ⟨oldRc, oldGet⟩ := restricted afterGet
  have same := Option.some.inj (oldGet.symm.trans found)
  cases same
  have unit : rc = 1 := (owned.counts afterGet).1
  subst rc
  exact afterGet

theorem ListAt.ofRestricts {schema : Schema} {before after : Store} {roots : List Root}
    {values : List Nat} {value : RVal} (restricted : StoreGraphRestricts before after)
    (owned : RootOwnership after roots) (world : HasWorld after .unique value)
    (list : ListAt schema before values value) : ListAt schema after values value := by
  induction list with
  | nil found => exact .nil (unique_shape_after_restriction restricted owned world found)
  | cons found next ih =>
      have afterGet := unique_shape_after_restriction restricted owned world found
      exact .cons afterGet (ih (owned.edges_world afterGet _ (by simp [nodeChildren])))

def uniqueRoots (values : List RVal) : List Root := rootsFor .unique values

theorem uniqueRoots_cons (value : RVal) (values : List RVal) :
    uniqueRoots (value :: values) = ⟨.unique, value⟩ :: uniqueRoots values := rfl

theorem ownedNilAllocation {store : Store} {rest : List Root}
    (owned : RootOwnership store rest) (schema : Schema) :
    RootOwnership (store.allocNode .unique (.ctorN (nilId schema) #[])).1
      (⟨.unique, .loc store.nodes.size⟩ :: rest) := by
  exact (show RootOwnership store (rootsFor .unique (nodeChildren (.ctorN (nilId schema) #[])) ++ rest)
    from owned).allocNode trivial

theorem nilAllocated (store : Store) (schema : Schema) :
    ListAt schema (store.allocNode .unique (.ctorN (nilId schema) #[])).1 [] (.loc store.nodes.size) :=
  .nil (HeapIso.get?_allocNode_new store .unique _)

theorem consAllocated {store : Store} {schema : Schema} {tail : List Nat} {value : RVal}
    (next : ListAt schema store tail value) (head : Nat) :
    ListAt schema (store.allocNode .unique (.ctorN (consId schema) #[.lit (.nat head), value])).1
      (head :: tail) (.loc store.nodes.size) :=
  .cons (HeapIso.get?_allocNode_new store .unique _) (next.allocNode .unique _)

theorem nilConsumed {store : Store} {schema : Schema} {location : Nat}
    {accumulator : RVal} {accValues : List Nat}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (nilId schema) #[]⟩)
    (owned : RootOwnership store [⟨.unique, .loc location⟩, ⟨.unique, accumulator⟩])
    (acc : ListAt schema store accValues accumulator) :
    RootOwnership (store.kill location) [⟨.unique, accumulator⟩] ∧
      ListAt schema (store.kill location) accValues accumulator := by
  have after : RootOwnership (store.kill location) [⟨.unique, accumulator⟩] := owned.killUniqueOne found
  exact ⟨after, acc.ofRestricts (StoreGraphRestricts.kill found) after
    (after.roots_world ⟨.unique, accumulator⟩ (by simp))⟩

structure TakenCons (schema : Schema) (store : Store) (location head : Nat)
    (tail accumulator : RVal) (tailValues accValues : List Nat) : Prop where
  owned : RootOwnership (store.kill location)
    [⟨.unique, .lit (.nat head)⟩, ⟨.unique, accumulator⟩, ⟨.unique, tail⟩]
  tailAt : ListAt schema (store.kill location) tailValues tail
  accAt : ListAt schema (store.kill location) accValues accumulator

theorem consTaken {store : Store} {schema : Schema} {location head : Nat}
    {tail accumulator : RVal} {tailValues accValues : List Nat}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (owned : RootOwnership store [⟨.unique, .loc location⟩, ⟨.unique, accumulator⟩])
    (next : ListAt schema store tailValues tail) (acc : ListAt schema store accValues accumulator) :
    TakenCons schema store location head tail accumulator tailValues accValues := by
  have after := owned.killUniqueOne found
  have after' : RootOwnership (store.kill location)
      [⟨.unique, .lit (.nat head)⟩, ⟨.unique, tail⟩, ⟨.unique, accumulator⟩] := after
  refine ⟨after'.perm ((List.Perm.swap _ _ []).cons _), ?_, ?_⟩
  · exact next.ofRestricts (StoreGraphRestricts.kill found) after'
      (after'.roots_world ⟨.unique, tail⟩ (by simp))
  · exact acc.ofRestricts (StoreGraphRestricts.kill found) after'
      (after'.roots_world ⟨.unique, accumulator⟩ (by simp))

theorem TakenCons.allocate {store : Store} {schema : Schema} {location head : Nat}
    {tail accumulator : RVal} {tailValues accValues : List Nat}
    (taken : TakenCons schema store location head tail accumulator tailValues accValues) :
    let output := ((store.kill location).allocNode .unique
      (.ctorN (consId schema) #[.lit (.nat head), accumulator]))
    RootOwnership output.1 [⟨.unique, tail⟩, ⟨.unique, .loc output.2⟩] ∧
      ListAt schema output.1 tailValues tail ∧
      ListAt schema output.1 (head :: accValues) (.loc output.2) := by
  dsimp only
  have allocated := (show RootOwnership (store.kill location)
    (rootsFor .unique (nodeChildren (.ctorN (consId schema) #[.lit (.nat head), accumulator])) ++
      [⟨.unique, tail⟩]) from taken.owned).allocNode (by trivial)
  exact ⟨allocated.perm (List.Perm.swap _ _ []), taken.tailAt.allocNode .unique _, consAllocated taken.accAt head⟩

private theorem revive_preserves_killed {store : Store} {location other : Nat} {oldBox box : NodeBox}
    {node : Node} (found : store.get? location = some oldBox)
    (kept : (store.kill location).get? other = some box) :
    (reuseNodeStore store location node).get? other = some box := by
  have different : location ≠ other := by
    intro h; subst other
    rw [get?_kill_same found] at kept
    cases kept
  exact get?_reuseNodeStore_other different found (get?_of_kill_other different found kept)

theorem TakenCons.reuse {store : Store} {schema : Schema} {location head : Nat}
    {tail accumulator : RVal} {tailValues accValues : List Nat}
    (found : store.get? location = some ⟨.unique, 1, .ctorN (consId schema) #[.lit (.nat head), tail]⟩)
    (taken : TakenCons schema store location head tail accumulator tailValues accValues) :
    let output := reuseNodeStore store location (.ctorN (consId schema) #[.lit (.nat head), accumulator])
    RootOwnership output [⟨.unique, tail⟩, ⟨.unique, .loc location⟩] ∧
      ListAt schema output tailValues tail ∧
      ListAt schema output (head :: accValues) (.loc location) := by
  dsimp only
  have ready : RootOwnership (store.kill location)
      (rootsFor .unique (nodeChildren (.ctorN (consId schema) #[.lit (.nat head), accumulator])) ++
        [⟨.unique, tail⟩]) := taken.owned
  have revived := ready.reviveUnique found (by trivial)
  refine ⟨revived.perm (List.Perm.swap _ _ []), taken.tailAt.mono (revive_preserves_killed found), ?_⟩
  exact .cons (get?_reuseNodeStore_same found)
    (taken.accAt.mono (revive_preserves_killed found))

end Ix.Compiler.UniqueReuse
