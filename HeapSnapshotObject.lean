import Compilatrix.X86.PhysicalHeapExport
import Compilatrix.IxIR2.WireIO
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.X86 Compilatrix.Tools.Check

private def rootOfHex (value : String) : Except String Ixon.Address := do
  let bytes ← unhex value
  if size : bytes.size = 32 then return ⟨bytes, size⟩
  else throw "expected a 32-byte content root"

/-- This consumer receives only persisted IxIR₂ bytes and explicit entry
metadata. It validates and selects the decoded CFG without source fixtures. -/
def main (args : List String) : IO UInt32 := cli "heap snapshot object failed" do
  let (args, name) := match args.reverse with
    | name :: "--name" :: rest => (rest.reverse, name)
    | _ => (args, "compilatrix_heap_cfg")
  let (args, emission) := match args with
    | [path, root, entry, mode, output, "shared"] =>
        ([path, root, entry, mode, output], HeapTarget.Emission.shared)
    | _ => (args, HeapTarget.Emission.tree)
  let [path, root, entry, mode, output] := args
    | throw (IO.userError "usage: heap-snapshot-object SNAPSHOT ROOT ENTRY source|physical|export OUTPUT [shared] [--name SYMBOL]")
  let bytes ← IxIR2.Wire.readBounded path ({} : IxIR.Bounded.Limits).maxBytes
  let root ← checked (rootOfHex root)
  let entry ← checked (rootOfHex entry)
  let loaded ← checked (IxIR2.Wire.Artifact.ingest {} IxIR2.Validate.defaultLimits bytes root)
  let object ← if mode == "source" || mode == "export" then do
      let exported ← checked (PhysicalHeap.compileSnapshotExport loaded.artifact loaded.checked (name := name) (emission := emission))
      need (exported.source.address == entry) "snapshot source export does not match the requested entry"
      pure exported.compiled.object.bytes
    else if mode == "physical" then do
      let compiled ← checked (PhysicalHeap.compileSnapshot loaded.artifact loaded.checked entry (name := name) (emission := emission))
      pure compiled.object.bytes
    else throw (IO.userError "unknown heap snapshot entry mode")
  need (!(← System.FilePath.pathExists output)) "snapshot compiler requires a fresh output file"
  IO.FS.writeBinFile output object
  IO.println s!"heap snapshot object ok: {root.toHex}, {object.size} bytes"
