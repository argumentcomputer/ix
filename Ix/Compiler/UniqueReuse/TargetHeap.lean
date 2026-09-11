import Ix.Compiler.UniqueReuse.Heap
import Ix.Compiler.IxIR2.UniqueLower
import Ix.Compiler.IxIR2.ReservationHeap
import Ix.Compiler.IxIR2.CostObservations

namespace Ix.Compiler.UniqueReuse.Target

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Sim
open Ix.Compiler.IxIR0.UniqueReverse (Schema Plan)
open Ix.Compiler.IxIR2
open Ix.Compiler.IxIR2.Eval

def nilSchema (schema : Schema) : CtorSchema :=
  { layout := Pipeline.baselineLayout .unique (nilId schema), fields := #[] }

def consSchema (schema : Schema) : CtorSchema :=
  { layout := Pipeline.baselineLayout .unique (consId schema), fields := #[.unique, .unique] }

theorem nilSchemaAt (schema : Schema) :
    UniqueLower.schemas schema .unique (nilId schema) = some (nilSchema schema) := by
  simp [UniqueLower.schemas, nilSchema]

theorem cons_ne_nil (schema : Schema) : consId schema ≠ nilId schema := by
  intro same
  have := congrArg IxIR1.CtorId.cidx same
  simp [consId, nilId, IxIR1.Lower.ctorIdOf] at this

theorem consSchemaAt (schema : Schema) :
    UniqueLower.schemas schema .unique (consId schema) = some (consSchema schema) := by
  simp [UniqueLower.schemas, consSchema, cons_ne_nil]

theorem listWorld {schema : Schema} {store : Store} {values : List Nat} {value : RVal}
    (list : ListAt schema store.heap values value) : value.hasWorld store .unique = true := by
  exact IxIR1.Sim.rval_hasWorld_eq_true_iff.mpr list.hasWorld

theorem nilFields (schema : Schema) (store : Store) : FieldWorlds store (nilSchema schema) #[] := by
  apply FieldWorlds.of_replicate (world := .unique) (count := 0) rfl rfl
  simp

theorem consFields {schema : Schema} {store : Store} {values : List Nat} {value : RVal}
    (list : ListAt schema store.heap values value) (head : Nat) :
    FieldWorlds store (consSchema schema) #[.lit (.nat head), value] := by
  apply FieldWorlds.of_replicate (world := .unique) (count := 2) rfl rfl
  intro candidate member
  simp at member
  rcases member with rfl | rfl
  · rfl
  · exact listWorld list

theorem reserveRelease {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) :
    (store.reserve location).releaseReservation location = .ok (store.kill location) := by
  have empty := Store.reserve_empty found
  unfold Store.EmptySlot at empty
  simp only [Store.releaseReservation, empty]
  rfl

/-- The exact result of reserving and reusing a unique slot, including the
physical payload and peak observations. -/
def reuseAt (store : Store) (location : Nat) (node : Node) (payload : Nat) : Store :=
  let heap := reuseNodeStore store.heap location node
  { store with
    heap := heap
    reusedPayloadUnits := store.reusedPayloadUnits + payload
    peakLiveNodes := max store.peakLiveNodes heap.live }

theorem reserveReuse {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (node : Node) (payload : Nat) :
    (store.reserve location).reuseReservation location .unique node payload =
      .ok (reuseAt store location node payload) := by
  have empty := Store.reserve_empty found
  unfold Store.EmptySlot at empty
  simp only [Store.reuseReservation, empty]
  simp [Store.reserve, reuseAt, reuseNodeStore, IxIR1.Store.kill, IxIR1.Store.setBox,
    Array.set!_eq_setIfInBounds]
  rfl

theorem reuseAt_live {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (node : Node) (payload : Nat) :
    (reuseAt store location node payload).live = store.live := by
  have reused := (Store.reuseReservation_accounting (reserveReuse found node payload)).1
  have reserved := Store.live_reserve found
  omega

theorem reuseAt_peak {store : Store} {location : Nat} {box : NodeBox}
    (found : store.get? location = some box) (node : Node) (payload : Nat)
    (peak : store.live ≤ store.peakLiveNodes) :
    (reuseAt store location node payload).peakLiveNodes = store.peakLiveNodes := by
  have live := reuseAt_live found node payload
  change max store.peakLiveNodes (reuseAt store location node payload).live = _
  rw [live, Nat.max_eq_left peak]

end Ix.Compiler.UniqueReuse.Target
