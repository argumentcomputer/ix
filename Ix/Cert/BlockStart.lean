import Ix.Cert.Schedule
import Ix.CompileCert.Emission
import Ix.CompileCert.PreseedWire
import Ix.CompileCert.WireTables

/-! # The state every block of the fold starts from (N-READS, N3)

The driver compiles every block from the empty `BlockState`
(`Ix.CompileDriver.runBlockWithAux`, `compileConstNoAuxPure`: `CompileM.run cenv … {}`),
and the preseed runs inside the compile actions; the reading theorems' `before`
is that empty state. Its premises about it:

* `clean_empty`: `Emission.Clean ({}, {}) {}` (the bindings of the empty state
  are empty);
* `wire_empty`: `BlockWireTablesWF {}`;
* `lookupWidths_empty`: `PreseedWire.LookupWidths env {}` reduces to the
  widths of the environment's own maps (`EnvWidths`). That those hold at every
  block of the fold is N3 (b), still open. -/

namespace Ix.Cert.BlockStart

open Ix.CompileM
open Ix.CompileCert

/-- **The empty block state is clean** for empty bindings. -/
theorem clean_empty : Emission.Clean ({}, {}) ({} : BlockState) := by
  refine ⟨⟨?_, ?_, rfl⟩, rfl⟩
  · exact UniversePipeline.sound_empty ({} : BlockState)
  · exact Interning.refIndexSound_empty ({} : BlockState)

/-- **The empty block state's wire tables are well formed.** -/
theorem wire_empty : Ix.Sharing.Verify.BlockWireTablesWF ({} : BlockState) :=
  WireTables.empty ({} : BlockState)

/-- Every address the environment resolves a name to is 32 bytes wide. -/
def EnvWidths (env : CompileEnv) : Prop :=
  (∀ name address, env.nameToAddr.get? name = some address → address.hash.size = 32) ∧
    ∀ name address, env.auxNameToAddr.get? name = some address → address.hash.size = 32

/-- **From the empty state, the lookups' widths are the environment's.** -/
theorem lookupWidths_empty {env : CompileEnv} (widths : EnvWidths env) :
    PreseedWire.LookupWidths env ({} : BlockState) := by
  intro name address found
  have e1 : ((({} : BlockState).blockNameToAddr).get? name : Option Address) = none :=
    Std.HashMap.get?_emptyWithCapacity
  unfold ExpressionState.lookupBinding ExpressionState.bindingView at found
  rw [e1] at found
  cases h : env.nameToAddr.get? name with
  | some a =>
    simp only [h, Option.orElse, Option.some.injEq] at found
    exact found ▸ widths.1 name a h
  | none =>
    simp only [h, Option.orElse] at found
    exact widths.2 name address found

end Ix.Cert.BlockStart
