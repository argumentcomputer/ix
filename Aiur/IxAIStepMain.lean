import IxAIStep

/-! `ixai_step`: `all DIR N` exports the first `N` steps of the full run as execution packages,
`train` checks `Fixed::train` against `IxAICore.train`, `train-export FILE` exports the whole
full-configuration run as one `Fixed::train` execution package, `blocks DIR` exports it as 30
`Fixed::train_block` packages, and otherwise step 0 is checked
and exported to the given file (default `step0.ixa`). -/

namespace IxAIAiur
open Aiur

/-- `xs` without repeats, first occurrences in order. -/
def dedup (xs : List Int) : List Int := Id.run do
  let mut seen : Std.HashSet Int := {}
  let mut out : Array Int := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out.toList

/-- Export one `Fixed::train` execution of the full configuration to `out`: the program compiled
with `Fixed::train` as its only entry, the initial model, learning rate and the 600 gathered
batches as arguments (in `trainArgs` order), and the hint table of every step. `out.expected`
lists the trained parameters. -/
def exportTrain (out : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let cfg := fullConfig
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let batches := IxAICore.gather examples cfg.schedule (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  let m0 := cfg.init s
  discard <| get (trainArgs m0 lr batches)
  let mut m := m0
  let mut shr : Array Int := #[]
  let mut sign : Array Int := #[]
  let mut bound : Array Int := #[]
  for b in batches do
    let (k1, k2) := stepHintKeys m b lr
    let next := m.step lr b
    shr := shr ++ k1.toArray
    sign := sign ++ k2.toArray
    bound := bound ++ ((next.w1.flatten ++ next.b1 ++ next.w2.flatten ++ next.b2).map (·.raw)).toArray
    m := next
  unless decide (m = IxAICore.train s cfg) do throw (IO.userError "folded steps differ from IxAICore.train")
  let boundKeys := dedup bound.toList
  let bounds : Array (Execution.HintEntry F) := (boundKeys.map fun v =>
    (⟨.array .field 2, .field (ofInt v), .array .field ((boundWords v).map .field), "fx.bound"⟩ :
      Execution.HintEntry F)).toArray
  let entriesTable := hintTable (dedup shr.toList, dedup sign.toList) ++ bounds
  IO.println s!"hint keys: {entriesTable.size} ({(← IO.monoMsNow) - t0} ms)"
  let trainOnly ← get <| Modules.prepare (source.toField F) ["Fixed::train"]
  let execution ← get trainOnly.exportExecution
  let compiled ← get (trainOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program
    compiled.circuit.artifact execution)
  IO.println s!"compiled the train circuit in {(← IO.monoMsNow) - t0} ms, {compiled.circuit.system.chips.length} chips"
  let table ← get (execution.prepareHints entriesTable)
  let enc := fun (x : IxAICore.Fx) => (ofInt x.raw).val
  let args := (m0.w1.flatten ++ m0.b1 ++ m0.w2.flatten ++ m0.b2 ++ [lr] ++
    batches.flatMap (fun b => (b.map (·.1)).flatten) ++
    batches.flatMap (fun b => (b.map (·.2)).flatten)).map enc
  Artifact.write out (← get (Artifact.execution execution p ZMod.val (some trace) args [] table))
  IO.FS.writeFile s!"{out}.expected"
    (" ".intercalate ((m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2).map (toString ·.raw)) ++ "\n")
  IO.println s!"exported Fixed::train ({args.length} argument words, {table.size} hint entries) to {out} in {(← IO.monoMsNow) - t0} ms"

/-- The `fx.bound` hint entries of the parameter values `vs`, without repeats. -/
def boundEntries (vs : List Int) : Array (Execution.HintEntry F) :=
  ((dedup vs).map fun v =>
    (⟨.array .field 2, .field (ofInt v), .array .field ((boundWords v).map .field), "fx.bound"⟩ :
      Execution.HintEntry F)).toArray

/-- Export the full-configuration run as 30 `Fixed::train_block` execution packages
`DIR/block-NNN.ixa`, each continuing from the previous block's output: the program compiled once
with `Fixed::train_block` as its only entry, the block's model, learning rate and 20 gathered
batches as arguments (`model ‖ lr ‖ inputs ‖ targets`, the order of `trainArgs`), and the hint
table of its 20 steps. `DIR/expected.txt` lists each block's output parameters. -/
def exportBlocks (dir : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let cfg := fullConfig
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let batches := IxAICore.gather examples cfg.schedule (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  let blockOnly ← get <| Modules.prepare (source.toField F) ["Fixed::train_block"]
  let execution ← get blockOnly.exportExecution
  let compiled ← get (blockOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program
    compiled.circuit.artifact execution)
  IO.println s!"compiled the block circuit in {(← IO.monoMsNow) - t0} ms, {compiled.circuit.system.chips.length} chips"
  IO.FS.createDirAll dir
  let enc := fun (x : IxAICore.Fx) => (ofInt x.raw).val
  let params := fun (m : IxAICore.Model) => m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2
  let mut m := cfg.init s
  let mut expected : Array String := #[]
  for (group, i) in (blocks20 batches).zip (List.range 30) do
    let m0 := m
    let mut shr : Array Int := #[]
    let mut sign : Array Int := #[]
    let mut bound : Array Int := #[]
    for b in group do
      let (k1, k2) := stepHintKeys m b lr
      let next := m.step lr b
      shr := shr ++ k1.toArray
      sign := sign ++ k2.toArray
      bound := bound ++ ((params next).map (·.raw)).toArray
      m := next
    let table ← get (execution.prepareHints
      (hintTable (dedup shr.toList, dedup sign.toList) ++ boundEntries bound.toList))
    let args := (params m0 ++ [lr] ++ group.flatMap (fun b => (b.map (·.1)).flatten) ++
      group.flatMap (fun b => (b.map (·.2)).flatten)).map enc
    let name := s!"{dir}/block-{(toString (1000 + i)).drop 1}.ixa"
    Artifact.write name (← get (Artifact.execution execution p ZMod.val (some trace) args [] table))
    expected := expected.push (" ".intercalate ((params m).map (toString ·.raw)))
  unless decide (m = IxAICore.train s cfg) do throw (IO.userError "folded blocks differ from IxAICore.train")
  IO.FS.writeFile s!"{dir}/expected.txt" ("\n".intercalate expected.toList ++ "\n")
  IO.println s!"exported 30 blocks to {dir} in {(← IO.monoMsNow) - t0} ms"

end IxAIAiur

def main (args : List String) : IO Unit :=
  match args with
  | ["all", dir, n] => IxAIAiur.exportAll dir n.toNat!
  | ["train"] => IxAIAiur.checkTrain
  | ["train-export", out] => IxAIAiur.exportTrain out
  | ["blocks", dir] => IxAIAiur.exportBlocks dir
  | _ => IxAIAiur.run (args.headD "step0.ixa")
