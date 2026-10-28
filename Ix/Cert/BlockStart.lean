import Ix.Cert.Schedule
import Ix.CompileCert.Emission
import Ix.CompileCert.WireTables

/-! # The state every block of the fold starts from (N-READS, N3)

The driver compiles every block from the empty `BlockState`
(`Ix.CompileM.runBlock`: `CompileM.run cenv … {}`),
and the preseed runs inside the compile actions; the reading theorems' `before`
is that empty state. Its premises about it:

* `clean_empty`: `Emission.Clean {} {}` (the bindings of the empty state
  are empty);
* `wire_empty`: `BlockWireTablesWF {}`.

The reading chain has no premise about the widths of resolved names: the
reference interner refuses an address that is not 32 bytes
(`Interning.internRef_narrow`; N3 (b)). -/

namespace Ix.Cert.BlockStart

open Ix.CompileM
open Ix.CompileCert

/-- **The empty block state is clean** for empty bindings. -/
theorem clean_empty : Emission.Clean ({} : ExpressionState.Bindings) ({} : BlockState) := by
  refine ⟨⟨?_, ?_, rfl⟩, rfl⟩
  · exact UniversePipeline.sound_empty ({} : BlockState)
  · exact Interning.refIndexSound_empty ({} : BlockState)

/-- **The empty block state's wire tables are well formed.** -/
theorem wire_empty : Ix.Sharing.Verify.BlockWireTablesWF ({} : BlockState) :=
  WireTables.empty ({} : BlockState)

end Ix.Cert.BlockStart
