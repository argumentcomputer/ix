import IxCC.Own.Rc.Release

/-! Focused kernel-evaluated alias/drop controls. These will move into a
test-only module if the heap primitives are promoted to production. -/
namespace IxCCTests.Own.Plain.HeapTests

open IxCC IxCC.Own IxCC.Own.Rc

private def leaf : Body :=
  { ctor := { key := .src 700, tag := 0, nobj := 1, fieldKinds := [.shared] }
    fields := [.lit (.nat 7)] }

private def parent : Body :=
  { ctor := { key := .src 701, tag := 1, nobj := 1, fieldKinds := [.shared] }
    fields := [.loc 0] }

/-- Cell zero is owned once externally and once by cell one's field. -/
private def shared : Heap := { cells := #[.live 2 .dyn leaf, .live 1 .dyn parent] }
private def kept : Heap := { cells := #[.live 1 .dyn leaf, .dead] }
private def released : Heap := { cells := #[.dead, .dead] }
private def external (l : Nat) : Nat := if l = 0 then 1 else 0

-- The external alias survives releasing its parent with its whole value.
example : dropAll shared [.loc 1] = some kept := by
  simp [dropAll, releaseOne, shared, kept, setCell, Heap.cell?, parent, leaf]
example : shared.value? (.loc 0) = kept.value? (.loc 0) := by
  simp [Heap.value?, Heap.size, toFir, toFirList, shared, kept, Heap.cell?, leaf]

-- Both release orders reclaim the shared subgraph exactly once.
example : dropAll shared [.loc 0, .loc 1] = some released := by
  simp [dropAll, releaseOne, shared, released, setCell, Heap.cell?, parent, leaf]
example : dropAll shared [.loc 1, .loc 0] = some released := by
  simp [dropAll, releaseOne, shared, released, setCell, Heap.cell?, parent, leaf]

-- A repeated parent drop and a dangling reference reject explicitly.
example : dropAll shared [.loc 1, .loc 1] = none := by
  simp [dropAll, releaseOne, shared, setCell, Heap.cell?, parent, leaf]
example : dropAll shared [.loc 9] = none := by
  simp [dropAll, releaseOne, shared, setCell, Heap.cell?]

-- Missing the duplication required by the parent/external alias is outside
-- Balance: the release algorithm alone cannot validate a producer's tokens.
private def missingDup : Heap := { cells := #[.live 1 .dyn leaf, .live 1 .dyn parent] }
example : ¬ Balance missingDup external [.loc 1] := by
  intro h
  have hc := h 0
  simp [dynCount, missingDup, Heap.cell?, external, refsIn, edgeCount,
    total, fieldRefs, parent, leaf] at hc

end IxCCTests.Own.Plain.HeapTests
