import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export
import Aiur.Tiling.IxaTrace
import Lean.Data.Json

/-!
# `plonk_entry_fixture`: a two-function terminal for the root-entry checks

`plonk_entry_fixture DIR` writes `DIR/entry.ixa` and `DIR/schema.json`
(`tools/gnark/testdata/aiur-entry`). The program exports one entry, `run`,
which asserts `a = b` and returns `helper(a, b)`; `helper` is not an entry and
accepts any `(a, b)` with the same 18 output words. Both chips are laid out
with one row and the schema names `run` as its `callable`, so a PLONK system
rooted at `helper` would prove `(1, 2)` while one rooted at `run` cannot.
`TestAiurScsEntryRoot` uses it to check that `plonk_export` and
`plonk_check_stage` root the system at the schema's entry whatever the table
order, and reject a `callable` that is not an exported entry or whose
argument and output split differs from the schema's.
-/

namespace PlonkEntryFixture

open Aiur
open Lean (toJson)

abbrev F := Library.Field.BN254.F

def source : Modules.Program Nat := aiur⟦
module EntryRoot {
  fn helper(a: Field, b: Field) -> [Field;18] {
    [0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1]
  }
  fn run(a: Field, b: Field) -> [Field;18] {
    assert_eq!(a,b,"entry equality");
    helper(a,b)
  }
}
⟧

def main (args : List String) : IO Unit := do
  let some dir := args.head? | throw (IO.userError "usage: plonk_entry_fixture DIR")
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) ["EntryRoot::run"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let pkg ← IO.ofExcept (Tiling.Ixa.decodeChecked (F := F) Library.Field.BN254.modulus ZMod.val bytes)
  let chip (c : Tiling.Ixa.IChip F) : Lean.Json := Lean.Json.mkObj [
    ("name", toJson c.name), ("rows", toJson (1 : Nat)), ("main_width", toJson (c.activation + 2)),
    ("fixed_width", toJson (0 : Nat)), ("fixed", toJson ([] : List Nat)),
    ("nodes", toJson ([] : List Nat)), ("constraints", toJson ([] : List Nat)), ("lookups", toJson ([] : List Nat))]
  let schema := Lean.Json.mkObj [
    ("format", toJson "ix-aiur-plonk-terminal-v1"), ("callable", toJson (pkg.idOf "EntryRoot::run")),
    ("public_inputs", toJson (2 : Nat)), ("private_outputs", toJson (18 : Nat)),
    ("boolean_requests", toJson true), ("circuits", toJson (pkg.chips.toList.map chip))]
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (System.FilePath.mk dir / "entry.ixa") bytes
  IO.FS.writeFile (System.FilePath.mk dir / "schema.json") (schema.pretty ++ "\n")
  IO.println s!"entries {repr pkg.entries}, chips {pkg.chips.toList.map (·.name)}"

end PlonkEntryFixture

def main (args : List String) : IO Unit := PlonkEntryFixture.main args
