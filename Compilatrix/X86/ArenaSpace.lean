import Compilatrix.X86.RuntimeExecution
import Compilatrix.X86.RuntimeReject

/-! Byte capacity of the actual unique-list ABI, including its descriptor.
This is independent of the explicit IxIR₂ machine's space model. -/

namespace Compilatrix.X86.UniqueABI

def Layout.bytes (layout : Layout) : Nat := 8 * layout.slots
def requiredBytes (length : Nat) : Nat := headerBytes + cellBytes * (length + 2)

/-- Whole cells available after reserving the descriptor. A partial final
cell is unusable; an absent descriptor is rejected separately by the caller. -/
def cellsForBytes (bytes : Nat) : Nat := (bytes - headerBytes) / cellBytes

theorem Layout.bytes_eq (layout : Layout) :
    layout.bytes = 80 + 32 * layout.capacity := by
  simp [Layout.bytes, Layout.slots, headerWords, cellWords, Nat.mul_add, ← Nat.mul_assoc]

theorem requiredBytes_eq (length : Nat) : requiredBytes length = 80 + 32 * (length + 2) := rfl

theorem Layout.enough_bytes_iff (layout : Layout) (length : Nat) :
    requiredBytes length ≤ layout.bytes ↔ length + 2 ≤ layout.capacity := by
  rw [layout.bytes_eq, requiredBytes_eq]
  omega

theorem enough_cells_iff (bytes length : Nat) :
    length + 2 ≤ cellsForBytes bytes ↔ requiredBytes length ≤ bytes := by
  unfold cellsForBytes requiredBytes headerBytes cellBytes
  omega

theorem one_byte_short (length : Nat) :
    cellsForBytes (requiredBytes length - 1) = length + 1 := by
  unfold cellsForBytes requiredBytes headerBytes cellBytes
  omega

end Compilatrix.X86.UniqueABI

namespace Compilatrix.X86.RuntimeExecution

open UniqueABI UniqueExecution UniqueTarget

theorem executes_of_bytes {foldCounters : Bool} (layout : Layout) (values : List Word) (state : State)
    (input : Input layout values state) (capacity : requiredBytes values.length ≤ layout.bytes)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    ∃ returned returnedMemory reclaimed reclaimedMemory,
      Execution layout values state memory outside runtime returned returnedMemory reclaimed reclaimedMemory foldCounters :=
  executes layout values state input ((layout.enough_bytes_iff _).mp capacity) outside memory represented runtime

end Compilatrix.X86.RuntimeExecution

namespace Compilatrix.X86.RuntimeExecution

open UniqueABI UniqueExecution UniqueTarget

theorem capacityRejects_of_bytes {foldCounters : Bool}
    (layout : Layout) (length : Nat) (state : State) (bounded : length ≤ 64)
    (insufficient : layout.bytes < requiredBytes length)
    (counts : CountsAt layout (readyCounts (length + 1)) state.words)
    (context : state.registers .rdi = layout.base) (argument : state.registers .rsi = UInt64.ofNat length)
    (outside memory : Memory) (represented : Realizes layout outside state.words memory) (runtime : Runtime) :
    runFrom runtime (RuntimeTarget.checked foldCounters) 15 (state.core memory) =
        haltedLeaf ((capacityRejectedState state).core memory) 6 1 ∧
      PreservesSaved state (capacityRejectedState state) := by
  apply capacityRejects layout length state bounded _ counts context argument outside memory represented runtime
  have := layout.enough_bytes_iff length
  omega

end Compilatrix.X86.RuntimeExecution
