import IxCCTests.Aiur.MemoryAIR.Fixtures
import IxCC.Aiur.AIR.Memory.Lookup
import IxCC.Aiur.AIR.Memory.Sound

namespace IxCCTests.Aiur.MemoryAIR

open _root_.IxCC.Vendor.Aiur (G)
open IxCC.Aiur.AIR.Memory

theorem arbitrary_checked : check [arbitraryStart] = true := by cbv
theorem wrapped_checked : check [wrapped] = true := by cbv
theorem signed_checked : check [signed] = true := by cbv
theorem self_pointer_checked : check [selfPointer] = true := by cbv
theorem repeated_contents_checked : check [repeatedContents] = true := by cbv
theorem distinct_buckets_checked : check distinctBuckets = true := by cbv
theorem zero_width_checked : check [zeroWidth] = true := by cbv
theorem padding_checked : check [allPadding] = true := by cbv
theorem duplicate_bucket_rejected : check [emptyTable, emptyTable] = false := by cbv
theorem inactive_provider_rejected : check [inactiveProvider] = false := by cbv
theorem invalid_selector_rejected : check [nonBoolean] = false := by cbv

theorem repeated_pointer_impossible (pointer left right : G) :
    ¬ (⟨1, #[realRow pointer left, realRow pointer right]⟩ : Table).Satisfied := by
  intro satisfied
  have different := Table.pointer_ne _ satisfied
    (by change 2 < _root_.IxCC.Vendor.Aiur.gSize.toNat; decide) 0 1 (by decide) (by change 1 < 2; decide) rfl
  exact different rfl

theorem padding_restart_impossible (pointer left right : G) :
    ¬ (⟨1, #[padding pointer left, realRow (pointer + 1) right]⟩ : Table).Satisfied := by
  intro satisfied
  have step := Table.consecutive _ satisfied 0 (by change 1 < 2; decide)
  have selected := (selected_predecessor step rfl).1
  exact G.one_ne_zero selected.symm

theorem wrapped_heap :
    IxCC.Aiur.Memory.heap (IxCC.Aiur.Memory.cells (project [wrapped])) 1 0 = some [52] := by
  exact Checked.heap_agrees ⟨wrapped_checked⟩ (table := wrapped) (by simp) 1 (by decide) rfl

theorem self_pointer_message (toplevel : _root_.IxCC.Vendor.Aiur.Bytecode.Toplevel)
    (oracle : IxCC.Aiur.OracleEval.AdviceOracle) :
    IxCC.Aiur.MessageEval toplevel
      (IxCC.Aiur.Memory.heap (IxCC.Aiur.Memory.cells (project [selfPointer]))) oracle
      (.memory 1 7 [7]) := by
  exact Checked.message_eval ⟨self_pointer_checked⟩ toplevel oracle
    (table := selfPointer) (by simp) 0 (by decide) rfl

theorem signed_activity : (project [signed]).Activity := Checked.activity ⟨signed_checked⟩

end IxCCTests.Aiur.MemoryAIR
