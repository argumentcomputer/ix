import Aiur.Optimized.Program
import Aiur.Optimized.LayoutWitness
import Aiur.Optimized.BranchFacts
import Aiur.Optimized.PrimitiveCorrectness
import Aiur.Optimized.ReferenceState

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

/-- The implemented deduplication pass preserves each public entry claim.
This theorem concerns the optimized system before and after deduplication;
`Equivalence.lean` composes it with the earlier passes and reference compiler. -/
theorem Artifact.dedup_derives_iff (compiled : Artifact F) {rom : WireROM F} {root : Circuit.Message F}
    (entry : root.channel ∈ compiled.entries) :
    Circuit.Derives compiled.unmerged rom root ↔ Circuit.Derives compiled.system rom root := by
  simpa only [compiled.deduplication.entry_fixed entry] using
    compiled.deduplication.derives_iff (rom := rom) (root := root)

theorem Artifact.dedup_memoDerives_iff (compiled : Artifact F) {rom : WireROM F} {root : Circuit.Message F}
    (entry : root.channel ∈ compiled.entries) :
    Circuit.MemoDerives compiled.unmerged rom root ↔ Circuit.MemoDerives compiled.system rom root := by
  simpa only [compiled.deduplication.entry_fixed entry] using
    compiled.deduplication.memoDerives_iff (rom := rom) (root := root)

theorem Artifact.dedup_acyclic_iff (compiled : Artifact F) {rom : WireROM F} {root : Circuit.Message F}
    (entry : root.channel ∈ compiled.entries) :
    (∃ graph : Circuit.MemoDerivation compiled.unmerged rom root, graph.Acyclic) ↔
      (∃ graph : Circuit.MemoDerivation compiled.system rom root, graph.Acyclic) := by
  have translated := compiled.deduplication.acyclic_iff (rom := rom) (root := root)
  rw [compiled.deduplication.entry_fixed entry] at translated
  exact translated

theorem Artifact.dedup_check_iff (compiled : Artifact F) {rom : WireROM F} {root : Circuit.Message F}
    (entry : root.channel ∈ compiled.entries) :
    (∃ rows, compiled.unmerged.check rom root rows = .ok ()) ↔
      (∃ rows, compiled.system.check rom root rows = .ok ()) :=
  compiled.deduplication.check_entry_iff entry

theorem Artifact.dedup_checkMemo_iff (compiled : Artifact F) {rom : WireROM F} {root : Circuit.Message F}
    (entry : root.channel ∈ compiled.entries) :
    (∃ rows, compiled.unmerged.checkMemo rom root rows = .ok ()) ↔
      (∃ rows, compiled.system.checkMemo rom root rows = .ok ()) :=
  compiled.deduplication.checkMemo_entry_iff entry

end Aiur.Optimized
