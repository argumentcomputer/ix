import Compilatrix.X86.HeapSimulation

namespace Compilatrix.X86.HeapArena
open WordRegion

/-- One finite caller-provided allocation contains the leaf arena and all
activation records. The final two words hold the saved arena register and
the external return address. -/
structure Workspace where
  base : Word
  depth : Nat
  positive : 0 < depth
  aligned : base % 16 = 0
  fits : base.toNat + 8 * (heapWords + Scalar.frameStride * depth + 2) ≤ UInt64.size

def Workspace.layout (workspace : Workspace) : HeapArena.Layout where
  region := {
    base := workspace.base
    slots := heapWords + Scalar.frameStride * workspace.depth + 2
    aligned := by
      apply UInt64.toNat_inj.mp
      have aligned := congrArg UInt64.toNat workspace.aligned
      simp only [UInt64.toNat_mod] at aligned ⊢
      change workspace.base.toNat % 16 = 0 at aligned
      change workspace.base.toNat % 8 = 0
      omega
    fits := workspace.fits }
  enough := by change heapWords ≤ heapWords + Scalar.frameStride * workspace.depth + 2; omega

def Workspace.frame (workspace : Workspace) : Scalar.Frame workspace.layout.region where
  top := heapWords + Scalar.frameStride * workspace.depth - 1
  enough := by simp only [heapWords, headerWords, cellWords, capacity, Scalar.frameStride]; omega
  bound := by simp only [Workspace.layout]; omega
  aligned := by
    simp only [SysV.functionEntryAligned, beq_iff_eq]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod]
    change (workspace.layout.region.address (heapWords + Scalar.frameStride * workspace.depth - 1)).toNat % 16 = 8
    rw [workspace.layout.region.address_toNat (by simp only [Workspace.layout]; omega)]
    have aligned := congrArg UInt64.toNat workspace.aligned
    simp only [UInt64.toNat_mod] at aligned
    change workspace.base.toNat % 16 = 0 at aligned
    simp only [Workspace.layout, heapWords, headerWords, cellWords, capacity, Scalar.frameStride]
    omega
  partition := by simp only [Scalar.frameStride, heapWords, headerWords, cellWords, capacity]; omega

def Workspace.externalTop (workspace : Workspace) : Nat := workspace.frame.top + 2
def Workspace.savedTop (workspace : Workspace) : Nat := workspace.frame.top + 1

theorem Workspace.external_bound (workspace : Workspace) : workspace.externalTop < workspace.layout.region.slots := by
  simp only [Workspace.externalTop, Workspace.frame, Workspace.layout, heapWords, headerWords, cellWords, capacity]
  omega

theorem Workspace.saved_bound (workspace : Workspace) : workspace.savedTop < workspace.layout.region.slots := by
  have := workspace.external_bound
  simp only [Workspace.externalTop, Workspace.savedTop] at *
  omega

theorem Workspace.separate (workspace : Workspace) : heapWords ≤ workspace.frame.stackIndex := by
  have := workspace.positive
  simp only [Workspace.frame, Scalar.Frame.stackIndex, heapWords, headerWords, cellWords, capacity, Scalar.frameStride]
  omega

theorem Workspace.rank_capacity (workspace : Workspace) {index : Nat} (depth : index < workspace.depth) :
    heapWords + Scalar.frameStride * (index + 1) - 1 ≤ workspace.frame.top := by
  simp only [Workspace.frame, Scalar.frameStride]
  omega

theorem Workspace.saved_ordinary (workspace : Workspace) : workspace.savedTop % Scalar.frameStride ≠ 33 := by
  have partition := workspace.frame.partition
  simp only [Workspace.savedTop, Scalar.frameStride] at *
  omega

theorem Workspace.push_address (workspace : Workspace) :
    workspace.layout.region.address workspace.externalTop - 8 = workspace.layout.region.address workspace.savedTop := by
  have shift := workspace.layout.region.subtract (slot := workspace.externalTop) (count := 1)
    (by simp only [Workspace.externalTop]; omega)
  simpa [Workspace.externalTop, Workspace.savedTop] using shift

theorem Workspace.call_address (workspace : Workspace) :
    workspace.layout.region.address workspace.savedTop - 8 = workspace.layout.region.address workspace.frame.top := by
  have shift := workspace.layout.region.subtract (slot := workspace.savedTop) (count := 1)
    (by simp only [Workspace.savedTop]; omega)
  simpa [Workspace.savedTop] using shift

theorem Workspace.pop_address (workspace : Workspace) :
    workspace.layout.region.address workspace.savedTop + 8 = workspace.layout.region.address workspace.externalTop := by
  simpa [Workspace.externalTop, Workspace.savedTop, Nat.add_assoc] using workspace.layout.region.add workspace.savedTop 1

theorem Workspace.call_aligned (workspace : Workspace) :
    SysV.callSiteAligned (workspace.layout.region.address workspace.savedTop) = true := by
  have aligned := workspace.frame.aligned
  simp only [SysV.functionEntryAligned, beq_iff_eq] at aligned
  have aligned := congrArg UInt64.toNat aligned
  simp only [UInt64.toNat_mod] at aligned
  change (workspace.layout.region.address workspace.frame.top).toNat % 16 = 8 at aligned
  rw [workspace.layout.region.address_toNat workspace.frame.bound] at aligned
  simp only [SysV.callSiteAligned, beq_iff_eq]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mod]
  change (workspace.layout.region.address workspace.savedTop).toNat % 16 = 0
  rw [workspace.layout.region.address_toNat workspace.saved_bound]
  simp only [Workspace.savedTop]
  omega

end Compilatrix.X86.HeapArena
