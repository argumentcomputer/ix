import Ix.Compiler.IxIR1.Sim
import Ix.Compiler.IxIR1.ReaddressSim

/-!
# Ownership invariance under IxIR₁ address renaming

Readdressing changes declaration identities retained by constructor and PAP
nodes, but it leaves locations, ownership worlds, reference counts, and heap
edges unchanged.  This file exposes that fact at the exact `RootOwnership`
boundary used by compiler simulations.
-/

namespace Ix.Compiler.IxIR1.Sim

@[simp] theorem nodeChildren_mapAddresses
    (rename : Ixon.Address → Ixon.Address) (node : IxIR1.Node) :
    nodeChildren (IxIR1.Readdress.Node.mapAddresses rename node) =
      nodeChildren node := by
  cases node <;> rfl

@[simp] theorem slotEdgeLocations_mapAddresses
    (rename : Ixon.Address → Ixon.Address)
    (slot : Option IxIR1.NodeBox) :
    slotEdgeLocations
        (slot.map (IxIR1.Readdress.NodeBox.mapAddresses rename)) =
      slotEdgeLocations slot := by
  cases slot with
  | none => rfl
  | some box =>
      simp [slotEdgeLocations, IxIR1.Readdress.NodeBox.mapAddresses,
        nodeChildren_mapAddresses]

@[simp] theorem edgeLocations_mapAddresses
    (rename : Ixon.Address → Ixon.Address) (store : IxIR1.Store) :
    edgeLocations (IxIR1.Readdress.Store.mapAddresses rename store) =
      edgeLocations store := by
  simp only [edgeLocations, IxIR1.Readdress.Store.mapAddresses,
    Array.toList_map, List.flatMap_map]
  apply congrArg (fun visit => List.flatMap visit store.nodes.toList)
  funext slot
  exact slotEdgeLocations_mapAddresses rename slot

@[simp] theorem incoming_mapAddresses
    (rename : Ixon.Address → Ixon.Address) (store : IxIR1.Store)
    (roots : List Root) (location : Nat) :
    incoming (IxIR1.Readdress.Store.mapAddresses rename store) roots location =
      incoming store roots location := by
  simp [incoming, edgeLocations_mapAddresses]

/-- Heap-world evidence ignores the declaration identities stored below a
live node. -/
theorem hasWorld_mapAddresses_iff
    (rename : Ixon.Address → Ixon.Address) (store : IxIR1.Store)
    (world : Ixon.Owned) (value : IxIR1.RVal) :
    HasWorld (IxIR1.Readdress.Store.mapAddresses rename store) world value ↔
      HasWorld store world value := by
  cases value with
  | lit literal => simp [HasWorld]
  | erased => simp [HasWorld]
  | loc location =>
      simp only [HasWorld, IxIR1.Readdress.Store.get?_mapAddresses]
      constructor
      · rintro ⟨mapped, mappedAt, mappedWorld⟩
        cases originalAt : store.get? location with
        | none => simp [originalAt] at mappedAt
        | some original =>
            simp only [originalAt, Option.map_some,
              Option.some.injEq] at mappedAt
            subst mapped
            exact ⟨original, rfl, by simpa using mappedWorld⟩
      · rintro ⟨original, originalAt, originalWorld⟩
        exact ⟨IxIR1.Readdress.NodeBox.mapAddresses rename original,
          by simp [originalAt], by simpa using originalWorld⟩

/-- Exact root ownership is invariant under arbitrary declaration-address
renaming.  Constructor/PAP identities are operational metadata rather than
heap edges; all ownership-relevant structure is unchanged. -/
theorem rootOwnership_mapAddresses_iff
    (rename : Ixon.Address → Ixon.Address) (store : IxIR1.Store)
    (roots : List Root) :
    RootOwnership (IxIR1.Readdress.Store.mapAddresses rename store) roots ↔
      RootOwnership store roots := by
  constructor
  · intro mappedOwnership
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro root member
      exact (hasWorld_mapAddresses_iff rename store root.world
        root.value).mp (mappedOwnership.roots_world root member)
    · intro location box boxAt child childMember
      have mappedAt :
          (IxIR1.Readdress.Store.mapAddresses rename store).get? location =
            some (IxIR1.Readdress.NodeBox.mapAddresses rename box) := by
        simp [boxAt]
      have mappedChild : child ∈ nodeChildren
          (IxIR1.Readdress.NodeBox.mapAddresses rename box).node := by
        simpa using childMember
      exact (hasWorld_mapAddresses_iff rename store box.world child).mp
        (by simpa using mappedOwnership.edges_world mappedAt child mappedChild)
    · intro location box function arity arguments boxAt node
      have mappedAt :
          (IxIR1.Readdress.Store.mapAddresses rename store).get? location =
            some (IxIR1.Readdress.NodeBox.mapAddresses rename box) := by
        simp [boxAt]
      have mappedNode :
          (IxIR1.Readdress.NodeBox.mapAddresses rename box).node =
            .papN (rename function) arity arguments := by
        rw [IxIR1.Readdress.NodeBox.mapAddresses_node, node]
        rfl
      simpa using mappedOwnership.pap_shared mappedAt mappedNode
    · intro location box boxAt
      have mappedAt :
          (IxIR1.Readdress.Store.mapAddresses rename store).get? location =
            some (IxIR1.Readdress.NodeBox.mapAddresses rename box) := by
        simp [boxAt]
      simpa using mappedOwnership.counts mappedAt
  · intro ownership
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro root member
      exact (hasWorld_mapAddresses_iff rename store root.world
        root.value).mpr (ownership.roots_world root member)
    · intro location mappedBox mappedAt child childMember
      cases boxAt : store.get? location with
      | none => simp [boxAt] at mappedAt
      | some box =>
          simp only [IxIR1.Readdress.Store.get?_mapAddresses, boxAt,
            Option.map_some, Option.some.injEq] at mappedAt
          subst mappedBox
          have originalChild : child ∈ nodeChildren box.node := by
            simpa using childMember
          exact (hasWorld_mapAddresses_iff rename store box.world child).mpr
            (ownership.edges_world boxAt child originalChild)
    · intro location mappedBox function arity arguments mappedAt mappedNode
      cases boxAt : store.get? location with
      | none => simp [boxAt] at mappedAt
      | some box =>
          simp only [IxIR1.Readdress.Store.get?_mapAddresses, boxAt,
            Option.map_some, Option.some.injEq] at mappedAt
          subst mappedBox
          cases nodeEq : box.node with
          | ctorN cid fields =>
              simp [IxIR1.Readdress.NodeBox.mapAddresses,
                IxIR1.Readdress.Node.mapAddresses, nodeEq] at mappedNode
          | papN originalFunction originalArity originalArguments =>
              have originalShared : box.world = .shared :=
                ownership.pap_shared (loc := location) (box := box)
                  (f := originalFunction) (arity := originalArity)
                  (args := originalArguments) boxAt nodeEq
              simpa using originalShared
    · intro location mappedBox mappedAt
      cases boxAt : store.get? location with
      | none => simp [boxAt] at mappedAt
      | some box =>
          simp only [IxIR1.Readdress.Store.get?_mapAddresses, boxAt,
            Option.map_some, Option.some.injEq] at mappedAt
          subst mappedBox
          simpa using ownership.counts boxAt

end Ix.Compiler.IxIR1.Sim
