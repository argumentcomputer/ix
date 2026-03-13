/-
  Kernel roundtrip test: compile Lean env to Ixon, convert to Kernel,
  decompile back to Lean, and structurally compare against the original.
-/
import Ix.Kernel
import Ix.Kernel.Convert
import Ix.Kernel.DecompileM
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Roundtrip

def testRoundtrip : TestSeq :=
  .individualIO "kernel roundtrip Lean→Ixon→Kernel→Lean" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel-roundtrip] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, _, _) =>
      -- Build Lean.Name → MetaId map from ixonEnv.named
      let mut nameToMid : Std.HashMap Lean.Name (Ix.Kernel.MetaId .meta) := {}
      for (ixName, named) in ixonEnv.named do
        let leanName := Ix.Kernel.Decompile.ixNameToLean ixName
        nameToMid := nameToMid.insert leanName (ixName, named.addr)
      -- Build work items using MetaId lookup
      let mut workItems : Array (Lean.Name × Lean.ConstantInfo × Ix.Kernel.ConstantInfo .meta) := #[]
      let mut notFound := 0
      for (leanName, origCI) in leanEnv.constants.toList do
        let some mid := nameToMid.get? leanName
          | do notFound := notFound + 1; continue
        let some kernelCI := kenv.find? mid
          | do notFound := notFound + 1; continue
        workItems := workItems.push (leanName, origCI, kernelCI)
      -- Chunked parallel comparison
      let numWorkers := 32
      let total := workItems.size
      let chunkSize := (total + numWorkers - 1) / numWorkers
      let mut tasks : Array (Task (Array (Lean.Name × Array (String × String × String)))) := #[]
      let mut offset := 0
      while offset < total do
        let endIdx := min (offset + chunkSize) total
        let chunk := workItems[offset:endIdx]
        let task := Task.spawn (prio := .dedicated) fun () => Id.run do
          let mut results : Array (Lean.Name × Array (String × String × String)) := #[]
          for (leanName, origCI, kernelCI) in chunk.toArray do
            let roundtrippedCI := Ix.Kernel.Decompile.decompileConstantInfo kernelCI
            let diffs := Ix.Kernel.Decompile.constInfoStructEq origCI roundtrippedCI
            if !diffs.isEmpty then
              results := results.push (leanName, diffs)
          results
        tasks := tasks.push task
        offset := endIdx
      -- Collect results
      let checked := total
      let mut mismatches := 0
      for task in tasks do
        for (leanName, diffs) in task.get do
          mismatches := mismatches + 1
          let diffMsgs := diffs.toList.map fun (path, lhs, rhs) =>
            s!"    {path}: {lhs} ≠ {rhs}"
          IO.println s!"[kernel-roundtrip] MISMATCH {leanName}:"
          for msg in diffMsgs do IO.println msg
      IO.println s!"[kernel-roundtrip] checked {checked}, mismatches {mismatches}, not found {notFound}"
      if mismatches == 0 then
        return (true, none)
      else
        return (false, some s!"{mismatches}/{checked} constants have structural mismatches")
  ) .done

def suite : List TestSeq := [testRoundtrip]

end Tests.Ix.Kernel.Roundtrip
