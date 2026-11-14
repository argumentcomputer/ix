import Ix.IxVM.Consistency.Statement
import Aiur.Optimized.ObservedROM

/-! # Obligation L0 holds

`L0` is the depth-grouped Goldilocks observed headline over a width ROM of at
most `2^39` entries, with the conjunct that the trace's memory has at most `2^39`
addresses. The headline gives everything but that conjunct; the conjunct holds
because every address of the trace's memory is the address of a width-ROM entry
(`Aiur.Optimized.GenericArtifact.traceROM_addresses`). -/

namespace IxVM.Consistency

/-- **Obligation L0 holds.** -/
theorem l0 : L0 := by
  intro id source entries specialized compiled prepared cfg certified bits plan activated name
    entry rom valid small args result wires output signed root rooted outside rows bound checked
    arguments decoded
  obtain ⟨value, heap, calls, observed, related, carried⟩ :=
    prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed compiled certified bits
      plan activated entry valid signed rooted outside bound checked arguments decoded
  obtain ⟨addrs, few, cover⟩ := compiled.traceROM_addresses rom
  exact ⟨value, heap, calls, observed, related, carried, ⟨addrs, few.trans small, cover⟩⟩

end IxVM.Consistency
