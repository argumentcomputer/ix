import Ix.Compiler.IxIR1.Sim

namespace Ix.Compiler.IxIR1.CostTrace

/-! ## Reference-count potential

Raw reference-count traffic is not locally compositional across deep drop:
one source-level release may recursively visit an arbitrarily large heap.
The missing state is the outstanding shared reference-count mass.  Each
successful shared `drop` trades exactly one unit of that potential for one
executed RC instruction, while a retain creates one unit and executes one RC
instruction.  This makes deep release free in the amortized measure and
explains the tariff's factor of two for retained values. -/

def slotSharedRcPotential : Option NodeBox → Nat
  | some ⟨.shared, rc, _⟩ => rc
  | some ⟨.unique, _, _⟩ | none => 0

def sharedRcPotentialList : List (Option NodeBox) → Nat
  | [] => 0
  | slot :: rest => slotSharedRcPotential slot + sharedRcPotentialList rest

theorem sharedRcPotentialList_append (left right) :
    sharedRcPotentialList (left ++ right) =
      sharedRcPotentialList left + sharedRcPotentialList right := by
  induction left with
  | nil => simp [sharedRcPotentialList]
  | cons head tail ih =>
      simp [sharedRcPotentialList, ih, Nat.add_assoc]

/-- Sum of the reference counts in all live shared heap slots. -/
def sharedRcPotential (store : Store) : Nat :=
  sharedRcPotentialList store.nodes.toList

@[simp] theorem sharedRcPotential_rcTick (store : Store) :
    sharedRcPotential store.rcTick = sharedRcPotential store := rfl

/-- Executed RC instructions plus the shared ownership they leave pending. -/
def amortizedRc (store : Store) : Nat :=
  store.rcops + sharedRcPotential store

/-- Growth of the RC potential across a target-store transition. -/
def RcPotentialGrowthLE (before after : Store) (allowance : Nat) : Prop :=
  amortizedRc after ≤ amortizedRc before + allowance

theorem RcPotentialGrowthLE.refl (store : Store) :
    RcPotentialGrowthLE store store 0 := by
  simp [RcPotentialGrowthLE]

theorem RcPotentialGrowthLE.trans {first middle last : Store} {left right}
    (hleft : RcPotentialGrowthLE first middle left)
    (hright : RcPotentialGrowthLE middle last right) :
    RcPotentialGrowthLE first last (left + right) := by
  simp only [RcPotentialGrowthLE] at hleft hright ⊢
  omega

theorem RcPotentialGrowthLE.monoAllowance {before after : Store}
    {smaller larger : Nat} (h : RcPotentialGrowthLE before after smaller)
    (hle : smaller ≤ larger) :
    RcPotentialGrowthLE before after larger := by
  simp only [RcPotentialGrowthLE] at h ⊢
  omega

/-- A potential bound started from an empty heap is an ordinary bound on
executed RC instructions. -/
theorem RcPotentialGrowthLE.rcops_of_initial_zero
    {before after : Store} {allowance : Nat}
    (hgrowth : RcPotentialGrowthLE before after allowance)
    (hpotential : sharedRcPotential before = 0) :
    after.rcops ≤ before.rcops + allowance := by
  simp only [RcPotentialGrowthLE, amortizedRc, hpotential, Nat.add_zero]
    at hgrowth
  omega

theorem sharedRcPotentialList_set :
    ∀ {slots : List (Option NodeBox)} {index : Nat} {old new},
      slots[index]? = some old →
      sharedRcPotentialList (slots.set index new) +
          slotSharedRcPotential old =
        sharedRcPotentialList slots + slotSharedRcPotential new
  | [], index, old, new, hget => by simp at hget
  | head :: rest, 0, old, new, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst head
      simp [sharedRcPotentialList]
      omega
  | head :: rest, index + 1, old, new, hget => by
      simp only [List.getElem?_cons_succ] at hget
      have ih := sharedRcPotentialList_set (new := new) hget
      simp only [List.set, sharedRcPotentialList]
      omega

theorem sharedRcPotential_setBox {store : Store} {location : Nat}
    {old new : NodeBox} (hget : store.get? location = some old) :
    sharedRcPotential (store.setBox location new) +
        slotSharedRcPotential (some old) =
      sharedRcPotential store + slotSharedRcPotential (some new) := by
  have hnodes := Sim.nodes_get?_of_get? hget
  have hlist : store.nodes.toList[location]? = some (some old) := by
    simpa using hnodes
  simp only [sharedRcPotential, Store.setBox, Array.toList_set!]
  exact sharedRcPotentialList_set hlist

theorem sharedRcPotential_kill {store : Store} {location : Nat}
    {box : NodeBox} (hget : store.get? location = some box) :
    sharedRcPotential (store.kill location) +
        slotSharedRcPotential (some box) = sharedRcPotential store := by
  have hnodes := Sim.nodes_get?_of_get? hget
  have hlist : store.nodes.toList[location]? = some (some box) := by
    simpa using hnodes
  have hset := sharedRcPotentialList_set
    (new := none) hlist
  simpa [sharedRcPotential, Store.kill, Array.toList_set!,
    slotSharedRcPotential] using hset

theorem RcPotentialGrowthLE.allocNode (store : Store)
    (world : Ixon.Owned) (node : Node) :
    RcPotentialGrowthLE store (store.allocNode world node).1 1 := by
  cases world <;>
    simp [RcPotentialGrowthLE, amortizedRc, sharedRcPotential,
      sharedRcPotentialList_append, sharedRcPotentialList,
      slotSharedRcPotential, Store.allocNode] <;>
    omega

theorem amortizedRc_incRcStore {store : Store} {location rc : Nat}
    {node : Node}
    (hget : store.get? location = some ⟨.shared, rc, node⟩) :
    amortizedRc
        (Sim.incRcStore store location ⟨.shared, rc, node⟩) =
      amortizedRc store + 2 := by
  have hset := sharedRcPotential_setBox
    (new := (⟨.shared, rc + 1, node⟩ : NodeBox))
    (by simpa using hget)
  simp [slotSharedRcPotential] at hset
  simp only [Sim.incRcStore, amortizedRc, sharedRcPotential_rcTick]
  change store.rcops + 1 +
      sharedRcPotential
        (store.setBox location ⟨.shared, rc + 1, node⟩) =
    store.rcops + sharedRcPotential store + 2
  omega

theorem amortizedRc_tickKillSharedOne {store : Store}
    {location : Nat} {node : Node}
    (hget : store.get? location = some ⟨.shared, 1, node⟩) :
    amortizedRc (store.rcTick.kill location) = amortizedRc store := by
  have hgetTick :
      store.rcTick.get? location = some ⟨.shared, 1, node⟩ := by
    simpa using hget
  have hkill := sharedRcPotential_kill hgetTick
  have hpotential :
      sharedRcPotential (store.rcTick.kill location) + 1 =
        sharedRcPotential store := by
    simpa [slotSharedRcPotential] using hkill
  change store.rcops + 1 +
      sharedRcPotential (store.rcTick.kill location) =
    store.rcops + sharedRcPotential store
  omega

theorem amortizedRc_decRcStore {store : Store} {location rc : Nat}
    {node : Node} (hrc : 1 < rc)
    (hget : store.get? location = some ⟨.shared, rc, node⟩) :
    amortizedRc
        (Sim.decRcStore store location ⟨.shared, rc, node⟩) =
      amortizedRc store := by
  have hgetTick :
      store.rcTick.get? location = some ⟨.shared, rc, node⟩ := by
    simpa using hget
  have hset := sharedRcPotential_setBox
    (new := (⟨.shared, rc - 1, node⟩ : NodeBox)) hgetTick
  have hpotential :
      sharedRcPotential
          (Sim.decRcStore store location ⟨.shared, rc, node⟩) + 1 =
        sharedRcPotential store := by
    simp only [Sim.decRcStore]
    simp [slotSharedRcPotential] at hset
    omega
  change store.rcops + 1 +
      sharedRcPotential
        (Sim.decRcStore store location ⟨.shared, rc, node⟩) =
    store.rcops + sharedRcPotential store
  omega

theorem amortizedRc_killUnique {store : Store} {location rc : Nat}
    {node : Node}
    (hget : store.get? location = some ⟨.unique, rc, node⟩) :
    amortizedRc (store.kill location) = amortizedRc store := by
  have hkill := sharedRcPotential_kill hget
  have hpotential : sharedRcPotential (store.kill location) =
      sharedRcPotential store := by
    simpa [slotSharedRcPotential] using hkill
  unfold amortizedRc
  rw [hpotential]
  rfl

end Ix.Compiler.IxIR1.CostTrace
