import Ix.Compiler.X86.UniqueRelease

/-! Observable native list ownership and complete main/release semantics.
The graph relation reads byte memory at actual native pointers. Its finite
footprint has no repeated node; tags are interpreted by the selected schema. -/

namespace Ix.Compiler.X86.UniqueExecution

open UniqueABI UniqueTarget

theorem cell_injective (layout : Layout) {left right : Nat} (leftBound : left < layout.capacity)
    (rightBound : right < layout.capacity) (equal : layout.cell left = layout.cell right) : left = right := by
  have slots := layout.address_injective (layout.cell_field_bound leftBound (by decide : 0 < cellWords))
    (layout.cell_field_bound rightBound (by decide : 0 < cellWords)) equal
  simp only [cellSlot, headerWords, cellWords] at slots
  omega

def chainNodes (layout : Layout) (start : Nat) : Nat → List Word
  | 0 => [layout.cell start]
  | length + 1 => layout.cell start :: chainNodes layout (start + 1) length

theorem chainNodes_mem {layout : Layout} {start length : Nat} {pointer : Word}
    (member : pointer ∈ chainNodes layout start length) :
    ∃ index, start ≤ index ∧ index ≤ start + length ∧ pointer = layout.cell index := by
  induction length generalizing start with
  | zero =>
      simp only [chainNodes, List.mem_singleton] at member
      exact ⟨start, Nat.le_refl _, by omega, member⟩
  | succ length ih =>
      simp only [chainNodes, List.mem_cons] at member
      rcases member with same | member
      · exact ⟨start, Nat.le_refl _, by omega, same⟩
      · obtain ⟨index, lower, upper, same⟩ := ih member
        exact ⟨index, by omega, by omega, same⟩

theorem chainNodes_fresh (layout : Layout) (start length : Nat)
    (bound : start + length + 1 < layout.capacity) :
    layout.cell start ∉ chainNodes layout (start + 1) length := by
  intro member
  obtain ⟨index, lower, upper, equal⟩ := chainNodes_mem member
  have same := cell_injective layout (by omega) (by omega) equal
  omega

/-- A read-only graph observation with an exclusive finite node footprint. -/
inductive NativeList (memory : Memory) : List Nat → Word → List Word → Prop where
  | nil {root : Word}
      (tagAt : memory.read64 root = nilTag)
      (headAt : memory.read64 (root + 8) = 0)
      (tailAt : memory.read64 (root + 16) = 0)
      (padding : memory.read64 (root + 24) = 0) : NativeList memory [] root [root]
  | cons {head : Nat} {tail : List Nat} {root next : Word} {nodes : List Word}
      (tagAt : memory.read64 root = consTag)
      (headAt : (memory.read64 (root + 8)).toNat = head)
      (tailAt : memory.read64 (root + 16) = next)
      (padding : memory.read64 (root + 24) = 0)
      (rest : NativeList memory tail next nodes) (fresh : root ∉ nodes) :
      NativeList memory (head :: tail) root (root :: nodes)

theorem NativeList.nodup {memory : Memory} {values : List Nat} {root : Word} {nodes : List Word}
    (list : NativeList memory values root nodes) : nodes.Nodup := by
  induction list with
  | nil => simp
  | cons _ _ _ _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

theorem NativeList.length {memory : Memory} {values : List Nat} {root : Word} {nodes : List Word}
    (list : NativeList memory values root nodes) : nodes.length = values.length + 1 := by
  induction list with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simp [ih]

theorem _root_.Ix.Compiler.X86.UniqueABI.Realizes.readCell {layout : Layout} {outside memory : Memory} {words : Words}
    (represented : Realizes layout outside words memory) {index field : Nat}
    (bound : index < layout.capacity) (fieldBound : field < cellWords) :
    memory.read64 (layout.cell index + UInt64.ofNat (8 * field)) = words (cellSlot index field) := by
  rw [layout.cell_offset]
  exact represented.view _ (layout.cell_field_bound bound fieldBound)

theorem UpChain.native {layout : Layout} {outside memory : Memory} {words : Words}
    {values : List Word} {start : Nat} (chain : UpChain layout words start values)
    (represented : Realizes layout outside words memory) (bound : start + values.length < layout.capacity) :
    NativeList memory (values.map UInt64.toNat) (layout.cell start) (chainNodes layout start values.length) := by
  induction values generalizing start with
  | nil =>
      have atCell : start < layout.capacity := by simpa using bound
      refine .nil ?_ ?_ ?_ ?_
      · simpa using (represented.readCell atCell (by decide : 0 < cellWords)).trans chain.tagAt
      · exact (represented.readCell atCell (by decide : 1 < cellWords)).trans chain.headAt
      · exact (represented.readCell atCell (by decide : 2 < cellWords)).trans chain.tailAt
      · exact (represented.readCell atCell (by decide : 3 < cellWords)).trans chain.padding
  | cons head tail ih =>
      have atCell : start < layout.capacity := by simp only [List.length_cons] at bound; omega
      refine .cons ?_ ?_ ?_ ?_ (ih chain.2 (by simp only [List.length_cons] at bound; omega))
        (chainNodes_fresh layout start tail.length (by simpa [Nat.add_assoc] using bound))
      · simpa using (represented.readCell atCell (by decide : 0 < cellWords)).trans chain.1.tagAt
      · exact congrArg UInt64.toNat ((represented.readCell atCell (by decide : 1 < cellWords)).trans chain.1.headAt)
      · exact (represented.readCell atCell (by decide : 2 < cellWords)).trans chain.1.tailAt
      · exact (represented.readCell atCell (by decide : 3 < cellWords)).trans chain.1.padding

def reclaimedCounts (length : Nat) : Counts := { mainCounts length with frees := length + 2, live := 0 }

@[simp] theorem mainCounts_dropped (length : Nat) : (mainCounts length).dropped length = reclaimedCounts length := by
  simp [mainCounts, Counts.dropped, reclaimedCounts]
  omega

structure Reclaimed (layout : Layout) (length : Nat) (before after : State) : Prop where
  countsAt : CountsAt layout (reclaimedCounts length) after.words
  freed : ∀ index < length + 2, CellAt after.words index freedTag 0 0
  result : after.registers .rax = 0
  saved : PreservesSaved before after

/-- Both calls terminate; every originally allocated cell is cleared and freed.
All surrounding bytes and System V callee-saved registers are preserved. -/
theorem mainAndRelease (layout : Layout) (values : List Word) (registers : Registers)
    (capacity : values.length + 2 ≤ layout.capacity) (context : registers .rdi = layout.base)
    (outside : Memory) (runtime : Runtime) (main release : Checked)
    (mainProduced : main.program = program values) (releaseProduced : release.program = releaseProgram) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      LoopResult layout values.reverse (mainCounts values.length) ⟨registers, initialWords layout⟩ returned ∧
      Realizes layout outside returned.words returnedMemory ∧
      NativeList returnedMemory ((values.map UInt64.toNat).reverse) (layout.cell 1)
        (chainNodes layout 1 values.length) ∧
      runFrom runtime main (controlCost values) ⟨registers, initialMemory layout outside⟩ =
        haltedLeaf (returned.core returnedMemory) 4 13 ∧
      Reclaimed layout values.length ⟨registers, initialWords layout⟩ reclaimed ∧
      Realizes layout outside reclaimed.words reclaimedMemory ∧
      runFrom runtime release (releaseCost values.length) (returned.core returnedMemory) =
        haltedLeaf (reclaimed.core reclaimedMemory) 2 13 := by
  obtain ⟨returned, returnedMemory, result, returnedView, mainRun⟩ :=
    mainRuns layout values registers capacity context outside runtime main mainProduced
  have graph := result.chain.native returnedView (by simp; omega)
  obtain ⟨reclaimed, reclaimedMemory, released, reclaimedView, releaseRun⟩ := releaseRuns layout values.reverse 1
    (mainCounts values.length) returned result.chain result.countsAt result.root result.context
    (by simp; omega) (by simp [mainCounts]) outside returnedMemory returnedView runtime release releaseProduced
  refine ⟨returned, returnedMemory, reclaimed, reclaimedMemory, result, returnedView,
    by simpa using graph, mainRun, ?_, reclaimedView, by simpa using releaseRun⟩
  refine ⟨by simpa using released.countsAt, ?_, released.result, result.saved.trans released.saved⟩
  intro index bound
  by_cases zero : index = 0
  · subst index
    apply result.freedNil.mono
    intro field fieldBound
    exact released.frame 0 (Or.inl (by decide)) field fieldBound
  · exact released.freed index (by omega) (by simp; omega)

end Ix.Compiler.X86.UniqueExecution
