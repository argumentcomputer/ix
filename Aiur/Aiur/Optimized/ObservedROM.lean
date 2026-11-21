import Aiur.Optimized.Observed

/-!
# The trace's memory has no more addresses than the width ROM has entries

The observed headlines represent values in the trace's memory
(`GenericArtifact.traceROM`): the width ROM, viewed at the circuit's memory
types and decoded. Every address it holds is the address of a width-ROM entry
(`GenericArtifact.traceROM_address`), so it holds at most as many addresses as
the width ROM has entries (`GenericArtifact.traceROM_addresses`). A bound on the
width ROM's entries (the verifiers' batch row bound counts the memory circuits'
rows) is then a bound on the addresses of the memory the derivation's values are
read in. In a valid ROM the cells of a list, or of any chain of cells, are at
pairwise different addresses, so that bound bounds the sizes of the structures
the derivation handles.
-/

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- **Every address of the trace's memory is an address of the width ROM**: the
typed views and the decoding keep each entry's address. -/
theorem GenericArtifact.traceROM_address {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    {rom : WidthROM F} {entry : F × Value F} (member : entry ∈ (compiled.traceROM rom).entries) :
    entry.1 ∈ rom.entries.map Prod.fst := by
  obtain ⟨address, value⟩ := entry
  obtain ⟨wire, typed, -⟩ := WireROM.mem_decode.mp member
  obtain ⟨present, -, -⟩ := WidthROM.mem_toWireROM.mp typed
  exact List.mem_map.mpr ⟨(address, wire.words), present, rfl⟩

/-- **The trace's memory has at most as many addresses as the width ROM has
entries.** -/
theorem GenericArtifact.traceROM_addresses {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (rom : WidthROM F) :
    ∃ addrs : List F, addrs.length ≤ rom.entries.length ∧
      ∀ entry ∈ (compiled.traceROM rom).entries, entry.1 ∈ addrs :=
  ⟨rom.entries.map Prod.fst, by simp, fun _ member => compiled.traceROM_address member⟩

end Aiur.Optimized
